import V185TrunkScan22Chunk305

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2729735 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 4]
def baseStart_2729735 : Nat := 118140960795 + 2729735 * 2 ^ 59
def prefixEnd_2729735 : Nat := 4983230072969 + 3 ^ 40 * 2729735 * 2
def baseEnd_2729735 : Nat := 311481358755773918435263

theorem tailTrace_2729735 : CollatzResearch.WordTrace tailWord_2729735 prefixEnd_2729735 311481358755773918435263 := by
  unfold tailWord_2729735
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561614765643771466902659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374409843762514311268439 99561614765643771466902659)
  ·
    refine ⟨149342422148465657200353989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99561614765643771466902659 149342422148465657200353989)
    ·
      refine ⟨28001704152837310725066373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149342422148465657200353989 28001704152837310725066373)
      ·
        refine ⟨5250319528656995760949945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28001704152837310725066373 5250319528656995760949945)
        ·
          refine ⟨3937739646492746820712459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5250319528656995760949945 3937739646492746820712459)
          ·
            refine ⟨5906609469739120231068689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937739646492746820712459 5906609469739120231068689)
            ·
              refine ⟨4429957102304340173301517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906609469739120231068689 4429957102304340173301517)
              ·
                refine ⟨1661233913364127564988069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4429957102304340173301517 1661233913364127564988069)
                ·
                  refine ⟨311481358755773918435263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661233913364127564988069 311481358755773918435263)
                  ·
                    rfl

theorem cell22_2729735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 4].length) (baseStart_2729735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729735 prefixEnd_2729735 := by exact prefixLift 2729735
  have htrace : WordTrace (prefixWord ++ tailWord_2729735) baseStart_2729735 baseEnd_2729735 := by
    simpa [prefixWord, tailWord_2729735, baseEnd_2729735] using wordTrace_append hprefix tailTrace_2729735
  have hstable : (prefixWord ++ tailWord_2729735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729735).length < 2 ^ (prefixWord ++ tailWord_2729735).sum := by decide
  have hdescent : baseEnd_2729735 < baseStart_2729735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729741 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2729741 : Nat := 118140960795 + 2729741 * 2 ^ 59
def prefixEnd_2729741 : Nat := 4983230072969 + 3 ^ 40 * 2729741 * 2
def baseEnd_2729741 : Nat := 311482043396646579885257

theorem tailTrace_2729741 : CollatzResearch.WordTrace tailWord_2729741 prefixEnd_2729741 311482043396646579885257 := by
  unfold tailWord_2729741
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561833603622034491621077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66374555735748022994414051 99561833603622034491621077)
  ·
    refine ⟨2333480475084891433397369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 99561833603622034491621077 2333480475084891433397369)
    ·
      refine ⟨1750110356313668575048027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2333480475084891433397369 1750110356313668575048027)
      ·
        refine ⟨2625165534470502862572041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750110356313668575048027 2625165534470502862572041)
        ·
          refine ⟨1968874150852877146929031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625165534470502862572041 1968874150852877146929031)
          ·
            refine ⟨2953311226279315720393547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968874150852877146929031 2953311226279315720393547)
            ·
              refine ⟨4429966839418973580590321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953311226279315720393547 4429966839418973580590321)
              ·
                refine ⟨3322475129564230185442741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429966839418973580590321 3322475129564230185442741)
                ·
                  refine ⟨311482043396646579885257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3322475129564230185442741 311482043396646579885257)
                  ·
                    rfl

theorem cell22_2729741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2729741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729741 prefixEnd_2729741 := by exact prefixLift 2729741
  have htrace : WordTrace (prefixWord ++ tailWord_2729741) baseStart_2729741 baseEnd_2729741 := by
    simpa [prefixWord, tailWord_2729741, baseEnd_2729741] using wordTrace_append hprefix tailTrace_2729741
  have hstable : (prefixWord ++ tailWord_2729741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729741).length < 2 ^ (prefixWord ++ tailWord_2729741).sum := by decide
  have hdescent : baseEnd_2729741 < baseStart_2729741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729778 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2729778 : Nat := 118140960795 + 2729778 * 2 ^ 59
def prefixEnd_2729778 : Nat := 4983230072969 + 3 ^ 40 * 2729778 * 2
def baseEnd_2729778 : Nat := 934458796046083976480657

theorem tailTrace_2729778 : CollatzResearch.WordTrace tailWord_2729778 prefixEnd_2729778 934458796046083976480657 := by
  unfold tailWord_2729778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24890795776121997452679497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66375455402991993207145325 24890795776121997452679497)
  ·
    refine ⟨18668096832091498089509623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24890795776121997452679497 18668096832091498089509623)
    ·
      refine ⟨28002145248137247134264435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18668096832091498089509623 28002145248137247134264435)
      ·
        refine ⟨42003217872205870701396653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002145248137247134264435 42003217872205870701396653)
        ·
          refine ⟨15751206702077201513023745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42003217872205870701396653 15751206702077201513023745)
          ·
            refine ⟨11813405026557901134767809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15751206702077201513023745 11813405026557901134767809)
            ·
              refine ⟨8860053769918425851075857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11813405026557901134767809 8860053769918425851075857)
              ·
                refine ⟨6645040327438819388306893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8860053769918425851075857 6645040327438819388306893)
                ·
                  refine ⟨2491890122789557270615085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6645040327438819388306893 2491890122789557270615085)
                  ·
                    refine ⟨934458796046083976480657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491890122789557270615085 934458796046083976480657)
                    ·
                      rfl

theorem cell22_2729778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2729778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729778 prefixEnd_2729778 := by exact prefixLift 2729778
  have htrace : WordTrace (prefixWord ++ tailWord_2729778) baseStart_2729778 baseEnd_2729778 := by
    simpa [prefixWord, tailWord_2729778, baseEnd_2729778] using wordTrace_append hprefix tailTrace_2729778
  have hstable : (prefixWord ++ tailWord_2729778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729778).length < 2 ^ (prefixWord ++ tailWord_2729778).sum := by decide
  have hdescent : baseEnd_2729778 < baseStart_2729778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729780 : List Nat := [2, 5, 1, 1, 2, 3, 2, 6]
def baseStart_2729780 : Nat := 118140960795 + 2729780 * 2 ^ 59
def prefixEnd_2729780 : Nat := 4983230072969 + 3 ^ 40 * 2729780 * 2
def baseEnd_2729780 : Nat := 103828831187439626436739

theorem tailTrace_2729780 : CollatzResearch.WordTrace tailWord_2729780 prefixEnd_2729780 103828831187439626436739 := by
  unfold tailWord_2729780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49781628025240372076145397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66375504033653829434860529 49781628025240372076145397)
  ·
    refine ⟨4667027627366284882138631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49781628025240372076145397 4667027627366284882138631)
    ·
      refine ⟨7000541441049427323207947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667027627366284882138631 7000541441049427323207947)
      ·
        refine ⟨10500812161574140984811921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000541441049427323207947 10500812161574140984811921)
        ·
          refine ⟨7875609121180605738608941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500812161574140984811921 7875609121180605738608941)
          ·
            refine ⟨2953353420442727151978353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7875609121180605738608941 2953353420442727151978353)
            ·
              refine ⟨2215015065332045363983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953353420442727151978353 2215015065332045363983765)
              ·
                refine ⟨103828831187439626436739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2215015065332045363983765 103828831187439626436739)
                ·
                  rfl

theorem cell22_2729780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_2729780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729780 prefixEnd_2729780 := by exact prefixLift 2729780
  have htrace : WordTrace (prefixWord ++ tailWord_2729780) baseStart_2729780 baseEnd_2729780 := by
    simpa [prefixWord, tailWord_2729780, baseEnd_2729780] using wordTrace_append hprefix tailTrace_2729780
  have hstable : (prefixWord ++ tailWord_2729780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729780).length < 2 ^ (prefixWord ++ tailWord_2729780).sum := by decide
  have hdescent : baseEnd_2729780 < baseStart_2729780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729795 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 1, 3]
def baseStart_2729795 : Nat := 118140960795 + 2729795 * 2 ^ 59
def prefixEnd_2729795 : Nat := 4983230072969 + 3 ^ 40 * 2729795 * 2
def baseEnd_2729795 : Nat := 934464615493501598805605

theorem tailTrace_2729795 : CollatzResearch.WordTrace tailWord_2729795 prefixEnd_2729795 934464615493501598805605 := by
  unfold tailWord_2729795
  simp only [CollatzResearch.WordTrace]
  refine ⟨99563803145426401714086839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66375868763617601142724559 99563803145426401714086839)
  ·
    refine ⟨149345704718139602571130259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99563803145426401714086839 149345704718139602571130259)
    ·
      refine ⟨224018557077209403856695389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149345704718139602571130259 224018557077209403856695389)
      ·
        refine ⟨84006958903953526446260771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224018557077209403856695389 84006958903953526446260771)
        ·
          refine ⟨126010438355930289669391157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84006958903953526446260771 126010438355930289669391157)
          ·
            refine ⟨11813478595868464656505421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126010438355930289669391157 11813478595868464656505421)
            ·
              refine ⟨4430054473450674246189533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11813478595868464656505421 4430054473450674246189533)
              ·
                refine ⟨1661270427544002842321075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430054473450674246189533 1661270427544002842321075)
                ·
                  refine ⟨2491905641316004263481613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661270427544002842321075 2491905641316004263481613)
                  ·
                    refine ⟨934464615493501598805605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491905641316004263481613 934464615493501598805605)
                    ·
                      rfl

theorem cell22_2729795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 3].length) (baseStart_2729795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729795 prefixEnd_2729795 := by exact prefixLift 2729795
  have htrace : WordTrace (prefixWord ++ tailWord_2729795) baseStart_2729795 baseEnd_2729795 := by
    simpa [prefixWord, tailWord_2729795, baseEnd_2729795] using wordTrace_append hprefix tailTrace_2729795
  have hstable : (prefixWord ++ tailWord_2729795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729795).length < 2 ^ (prefixWord ++ tailWord_2729795).sum := by decide
  have hdescent : baseEnd_2729795 < baseStart_2729795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729853 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2729853 : Nat := 118140960795 + 2729853 * 2 ^ 59
def prefixEnd_2729853 : Nat := 4983230072969 + 3 ^ 40 * 2729853 * 2
def baseEnd_2729853 : Nat := 311494823359602926951809

theorem tailTrace_2729853 : CollatzResearch.WordTrace tailWord_2729853 prefixEnd_2729853 311494823359602926951809 := by
  unfold tailWord_2729853
  simp only [CollatzResearch.WordTrace]
  refine ⟨99565918579216277619698213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66377279052810851746465475 99565918579216277619698213)
  ·
    refine ⟨18668609733603052053693415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99565918579216277619698213 18668609733603052053693415)
    ·
      refine ⟨28002914600404578080540123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18668609733603052053693415 28002914600404578080540123)
      ·
        refine ⟨42004371900606867120810185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002914600404578080540123 42004371900606867120810185)
        ·
          refine ⟨31503278925455150340607639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42004371900606867120810185 31503278925455150340607639)
          ·
            refine ⟨47254918388182725510911459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31503278925455150340607639 47254918388182725510911459)
            ·
              refine ⟨70882377582274088266367189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47254918388182725510911459 70882377582274088266367189)
              ·
                refine ⟨1661305724584548943742981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70882377582274088266367189 1661305724584548943742981)
                ·
                  refine ⟨311494823359602926951809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661305724584548943742981 311494823359602926951809)
                  ·
                    rfl

theorem cell22_2729853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2729853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729853 prefixEnd_2729853 := by exact prefixLift 2729853
  have htrace : WordTrace (prefixWord ++ tailWord_2729853) baseStart_2729853 baseEnd_2729853 := by
    simpa [prefixWord, tailWord_2729853, baseEnd_2729853] using wordTrace_append hprefix tailTrace_2729853
  have hstable : (prefixWord ++ tailWord_2729853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729853).length < 2 ^ (prefixWord ++ tailWord_2729853).sum := by decide
  have hdescent : baseEnd_2729853 < baseStart_2729853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729881 : List Nat := [1, 2, 1, 2, 1, 3, 5, 7]
def baseStart_2729881 : Nat := 118140960795 + 2729881 * 2 ^ 59
def prefixEnd_2729881 : Nat := 4983230072969 + 3 ^ 40 * 2729881 * 2
def baseEnd_2729881 : Nat := 103832672783447337906149

theorem tailTrace_2729881 : CollatzResearch.WordTrace tailWord_2729881 prefixEnd_2729881 103832672783447337906149 := by
  unfold tailWord_2729881
  simp only [CollatzResearch.WordTrace]
  refine ⟨99566939823114838401717497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66377959882076558934478331 99566939823114838401717497)
  ·
    refine ⟨74675204867336128801288123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99566939823114838401717497 74675204867336128801288123)
    ·
      refine ⟨112012807301004193201932185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74675204867336128801288123 112012807301004193201932185)
      ·
        refine ⟨84009605475753144901449139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112012807301004193201932185 84009605475753144901449139)
        ·
          refine ⟨126014408213629717352173709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84009605475753144901449139 126014408213629717352173709)
          ·
            refine ⟨47255403080111144007065141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126014408213629717352173709 47255403080111144007065141)
            ·
              refine ⟨4430194038760419750662357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47255403080111144007065141 4430194038760419750662357)
              ·
                refine ⟨103832672783447337906149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4430194038760419750662357 103832672783447337906149)
                ·
                  rfl

theorem cell22_2729881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 7].length) (baseStart_2729881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729881 prefixEnd_2729881 := by exact prefixLift 2729881
  have htrace : WordTrace (prefixWord ++ tailWord_2729881) baseStart_2729881 baseEnd_2729881 := by
    simpa [prefixWord, tailWord_2729881, baseEnd_2729881] using wordTrace_append hprefix tailTrace_2729881
  have hstable : (prefixWord ++ tailWord_2729881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729881).length < 2 ^ (prefixWord ++ tailWord_2729881).sum := by decide
  have hdescent : baseEnd_2729881 < baseStart_2729881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729885 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2729885 : Nat := 118140960795 + 2729885 * 2 ^ 59
def prefixEnd_2729885 : Nat := 4983230072969 + 3 ^ 40 * 2729885 * 2
def baseEnd_2729885 : Nat := 934495424332771364055329

theorem tailTrace_2729885 : CollatzResearch.WordTrace tailWord_2729885 prefixEnd_2729885 934495424332771364055329 := by
  unfold tailWord_2729885
  simp only [CollatzResearch.WordTrace]
  refine ⟨99567085715100347084863109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66378057143400231389908739 99567085715100347084863109)
  ·
    refine ⟨18668828571581315078411833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99567085715100347084863109 18668828571581315078411833)
    ·
      refine ⟨14001621428685986308808875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18668828571581315078411833 14001621428685986308808875)
      ·
        refine ⟨21002432143028979463213313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14001621428685986308808875 21002432143028979463213313)
        ·
          refine ⟨15751824107271734597409985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21002432143028979463213313 15751824107271734597409985)
          ·
            refine ⟨11813868080453800948057489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15751824107271734597409985 11813868080453800948057489)
            ·
              refine ⟨8860401060340350711043117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11813868080453800948057489 8860401060340350711043117)
              ·
                refine ⟨3322650397627631516641169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8860401060340350711043117 3322650397627631516641169)
                ·
                  refine ⟨2491987798220723637480877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322650397627631516641169 2491987798220723637480877)
                  ·
                    refine ⟨934495424332771364055329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491987798220723637480877 934495424332771364055329)
                    ·
                      rfl

theorem cell22_2729885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2729885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729885 prefixEnd_2729885 := by exact prefixLift 2729885
  have htrace : WordTrace (prefixWord ++ tailWord_2729885) baseStart_2729885 baseEnd_2729885 := by
    simpa [prefixWord, tailWord_2729885, baseEnd_2729885] using wordTrace_append hprefix tailTrace_2729885
  have hstable : (prefixWord ++ tailWord_2729885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729885).length < 2 ^ (prefixWord ++ tailWord_2729885).sum := by decide
  have hdescent : baseEnd_2729885 < baseStart_2729885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729913 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_2729913 : Nat := 118140960795 + 2729913 * 2 ^ 59
def prefixEnd_2729913 : Nat := 4983230072969 + 3 ^ 40 * 2729913 * 2
def baseEnd_2729913 : Nat := 934505009304988624355243

theorem tailTrace_2729913 : CollatzResearch.WordTrace tailWord_2729913 prefixEnd_2729913 934505009304988624355243 := by
  unfold tailWord_2729913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99568106958998907866882393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66378737972665938577921595 99568106958998907866882393)
  ·
    refine ⟨74676080219249180900161795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99568106958998907866882393 74676080219249180900161795)
    ·
      refine ⟨112014120328873771350242693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74676080219249180900161795 112014120328873771350242693)
      ·
        refine ⟨21002647561663832128170505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112014120328873771350242693 21002647561663832128170505)
        ·
          refine ⟨15751985671247874096127879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21002647561663832128170505 15751985671247874096127879)
          ·
            refine ⟨23627978506871811144191819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751985671247874096127879 23627978506871811144191819)
            ·
              refine ⟨35441967760307716716287729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23627978506871811144191819 35441967760307716716287729)
              ·
                refine ⟨26581475820230787537215797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35441967760307716716287729 26581475820230787537215797)
                ·
                  refine ⟨2492013358146636331613981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26581475820230787537215797 2492013358146636331613981)
                  ·
                    refine ⟨934505009304988624355243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492013358146636331613981 934505009304988624355243)
                    ·
                      rfl

theorem cell22_2729913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_2729913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729913 prefixEnd_2729913 := by exact prefixLift 2729913
  have htrace : WordTrace (prefixWord ++ tailWord_2729913) baseStart_2729913 baseEnd_2729913 := by
    simpa [prefixWord, tailWord_2729913, baseEnd_2729913] using wordTrace_append hprefix tailTrace_2729913
  have hstable : (prefixWord ++ tailWord_2729913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729913).length < 2 ^ (prefixWord ++ tailWord_2729913).sum := by decide
  have hdescent : baseEnd_2729913 < baseStart_2729913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729971 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 8]
def baseStart_2729971 : Nat := 118140960795 + 2729971 * 2 ^ 59
def prefixEnd_2729971 : Nat := 4983230072969 + 3 ^ 40 * 2729971 * 2
def baseEnd_2729971 : Nat := 311508287963431935468355

theorem tailTrace_2729971 : CollatzResearch.WordTrace tailWord_2729971 prefixEnd_2729971 311508287963431935468355 := by
  unfold tailWord_2729971
  simp only [CollatzResearch.WordTrace]
  refine ⟨99570222392788783772493767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66380148261859189181662511 99570222392788783772493767)
  ·
    refine ⟨149355333589183175658740651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99570222392788783772493767 149355333589183175658740651)
    ·
      refine ⟨224033000383774763488110977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149355333589183175658740651 224033000383774763488110977)
      ·
        refine ⟨168024750287831072616083233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224033000383774763488110977 168024750287831072616083233)
        ·
          refine ⟨126018562715873304462062425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168024750287831072616083233 126018562715873304462062425)
          ·
            refine ⟨94513922036904978346546819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126018562715873304462062425 94513922036904978346546819)
            ·
              refine ⟨141770883055357467519820229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94513922036904978346546819 141770883055357467519820229)
              ·
                refine ⟨26582040572879525159966293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141770883055357467519820229 26582040572879525159966293)
                ·
                  refine ⟨311508287963431935468355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26582040572879525159966293 311508287963431935468355)
                  ·
                    rfl

theorem cell22_2729971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_2729971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729971 prefixEnd_2729971 := by exact prefixLift 2729971
  have htrace : WordTrace (prefixWord ++ tailWord_2729971) baseStart_2729971 baseEnd_2729971 := by
    simpa [prefixWord, tailWord_2729971, baseEnd_2729971] using wordTrace_append hprefix tailTrace_2729971
  have hstable : (prefixWord ++ tailWord_2729971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729971).length < 2 ^ (prefixWord ++ tailWord_2729971).sum := by decide
  have hdescent : baseEnd_2729971 < baseStart_2729971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2729994 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_2729994 : Nat := 118140960795 + 2729994 * 2 ^ 59
def prefixEnd_2729994 : Nat := 4983230072969 + 3 ^ 40 * 2729994 * 2
def baseEnd_2729994 : Nat := 311510912420110471026665

theorem tailTrace_2729994 : CollatzResearch.WordTrace tailWord_2729994 prefixEnd_2729994 311510912420110471026665 := by
  unfold tailWord_2729994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24892765317926364675145259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66380707514470305800387357 24892765317926364675145259)
  ·
    refine ⟨37339147976889547012717889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24892765317926364675145259 37339147976889547012717889)
    ·
      refine ⟨28004360982667160259538417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37339147976889547012717889 28004360982667160259538417)
      ·
        refine ⟨21003270737000370194653813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28004360982667160259538417 21003270737000370194653813)
        ·
          refine ⟨1969056631593784705748795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21003270737000370194653813 1969056631593784705748795)
          ·
            refine ⟨2953584947390677058623193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969056631593784705748795 2953584947390677058623193)
            ·
              refine ⟨2215188710543007793967395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953584947390677058623193 2215188710543007793967395)
              ·
                refine ⟨3322783065814511690951093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215188710543007793967395 3322783065814511690951093)
                ·
                  refine ⟨311510912420110471026665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3322783065814511690951093 311510912420110471026665)
                  ·
                    rfl

theorem cell22_2729994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_2729994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2729994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2729994 prefixEnd_2729994 := by exact prefixLift 2729994
  have htrace : WordTrace (prefixWord ++ tailWord_2729994) baseStart_2729994 baseEnd_2729994 := by
    simpa [prefixWord, tailWord_2729994, baseEnd_2729994] using wordTrace_append hprefix tailTrace_2729994
  have hstable : (prefixWord ++ tailWord_2729994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2729994).length < 2 ^ (prefixWord ++ tailWord_2729994).sum := by decide
  have hdescent : baseEnd_2729994 < baseStart_2729994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2729994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730054 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2730054 : Nat := 118140960795 + 2730054 * 2 ^ 59
def prefixEnd_2730054 : Nat := 4983230072969 + 3 ^ 40 * 2730054 * 2
def baseEnd_2730054 : Nat := 934553276486511256579811

theorem tailTrace_2730054 : CollatzResearch.WordTrace tailWord_2730054 prefixEnd_2730054 934553276486511256579811 := by
  unfold tailWord_2730054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111664051609002779617663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66382166434325392631843477 3111664051609002779617663)
  ·
    refine ⟨4667496077413504169426495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111664051609002779617663 4667496077413504169426495)
    ·
      refine ⟨7001244116120256254139743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667496077413504169426495 7001244116120256254139743)
      ·
        refine ⟨10501866174180384381209615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001244116120256254139743 10501866174180384381209615)
        ·
          refine ⟨15752799261270576571814423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501866174180384381209615 15752799261270576571814423)
          ·
            refine ⟨23629198891905864857721635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15752799261270576571814423 23629198891905864857721635)
            ·
              refine ⟨35443798337858797286582453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23629198891905864857721635 35443798337858797286582453)
              ·
                refine ⟨3322856094174262245617105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35443798337858797286582453 3322856094174262245617105)
                ·
                  refine ⟨2492142070630696684212829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322856094174262245617105 2492142070630696684212829)
                  ·
                    refine ⟨934553276486511256579811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492142070630696684212829 934553276486511256579811)
                    ·
                      rfl

theorem cell22_2730054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2730054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730054 prefixEnd_2730054 := by exact prefixLift 2730054
  have htrace : WordTrace (prefixWord ++ tailWord_2730054) baseStart_2730054 baseEnd_2730054 := by
    simpa [prefixWord, tailWord_2730054, baseEnd_2730054] using wordTrace_append hprefix tailTrace_2730054
  have hstable : (prefixWord ++ tailWord_2730054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730054).length < 2 ^ (prefixWord ++ tailWord_2730054).sum := by decide
  have hdescent : baseEnd_2730054 < baseStart_2730054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730095 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 5]
def baseStart_2730095 : Nat := 118140960795 + 2730095 * 2 ^ 59
def prefixEnd_2730095 : Nat := 4983230072969 + 3 ^ 40 * 2730095 * 2
def baseEnd_2730095 : Nat := 311522437208133605434895

theorem tailTrace_2730095 : CollatzResearch.WordTrace tailWord_2730095 prefixEnd_2730095 311522437208133605434895 := by
  unfold tailWord_2730095
  simp only [CollatzResearch.WordTrace]
  refine ⟨99574745044339552950007739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66383163362893035300005159 99574745044339552950007739)
  ·
    refine ⟨149362117566509329425011609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99574745044339552950007739 149362117566509329425011609)
    ·
      refine ⟨112021588174881997068758707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149362117566509329425011609 112021588174881997068758707)
      ·
        refine ⟨168032382262322995603138061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112021588174881997068758707 168032382262322995603138061)
        ·
          refine ⟨63012143348371123351176773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168032382262322995603138061 63012143348371123351176773)
          ·
            refine ⟨11814776877819585628345645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63012143348371123351176773 11814776877819585628345645)
            ·
              refine ⟨4430541329182344610629617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11814776877819585628345645 4430541329182344610629617)
              ·
                refine ⟨3322905996886758457972213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430541329182344610629617 3322905996886758457972213)
                ·
                  refine ⟨311522437208133605434895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3322905996886758457972213 311522437208133605434895)
                  ·
                    rfl

theorem cell22_2730095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].length) (baseStart_2730095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730095 prefixEnd_2730095 := by exact prefixLift 2730095
  have htrace : WordTrace (prefixWord ++ tailWord_2730095) baseStart_2730095 baseEnd_2730095 := by
    simpa [prefixWord, tailWord_2730095, baseEnd_2730095] using wordTrace_append hprefix tailTrace_2730095
  have hstable : (prefixWord ++ tailWord_2730095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730095).length < 2 ^ (prefixWord ++ tailWord_2730095).sum := by decide
  have hdescent : baseEnd_2730095 < baseStart_2730095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730157 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2730157 : Nat := 118140960795 + 2730157 * 2 ^ 59
def prefixEnd_2730157 : Nat := 4983230072969 + 3 ^ 40 * 2730157 * 2
def baseEnd_2730157 : Nat := 311529511830484440418165

theorem tailTrace_2730157 : CollatzResearch.WordTrace tailWord_2730157 prefixEnd_2730157 311529511830484440418165 := by
  unfold tailWord_2730157
  simp only [CollatzResearch.WordTrace]
  refine ⟨99577006370114937538764725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66384670913409958359176483 99577006370114937538764725)
  ·
    refine ⟨9335344347198275394259193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99577006370114937538764725 9335344347198275394259193)
    ·
      refine ⟨7001508260398706545694395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9335344347198275394259193 7001508260398706545694395)
      ·
        refine ⟨10502262390598059818541593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001508260398706545694395 10502262390598059818541593)
        ·
          refine ⟨7876696792948544863906195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10502262390598059818541593 7876696792948544863906195)
          ·
            refine ⟨11815045189422817295859293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876696792948544863906195 11815045189422817295859293)
            ·
              refine ⟨4430641946033556485947235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11815045189422817295859293 4430641946033556485947235)
              ·
                refine ⟨6645962919050334728920853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430641946033556485947235 6645962919050334728920853)
                ·
                  refine ⟨311529511830484440418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6645962919050334728920853 311529511830484440418165)
                  ·
                    rfl

theorem cell22_2730157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2730157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730157 prefixEnd_2730157 := by exact prefixLift 2730157
  have htrace : WordTrace (prefixWord ++ tailWord_2730157) baseStart_2730157 baseEnd_2730157 := by
    simpa [prefixWord, tailWord_2730157, baseEnd_2730157] using wordTrace_append hprefix tailTrace_2730157
  have hstable : (prefixWord ++ tailWord_2730157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730157).length < 2 ^ (prefixWord ++ tailWord_2730157).sum := by decide
  have hdescent : baseEnd_2730157 < baseStart_2730157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730307 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 4, 3]
def baseStart_2730307 : Nat := 118140960795 + 2730307 * 2 ^ 59
def prefixEnd_2730307 : Nat := 4983230072969 + 3 ^ 40 * 2730307 * 2
def baseEnd_2730307 : Nat := 934639883556902930004035

theorem tailTrace_2730307 : CollatzResearch.WordTrace tailWord_2730307 prefixEnd_2730307 934639883556902930004035 := by
  unfold tailWord_2730307
  simp only [CollatzResearch.WordTrace]
  refine ⟨99582477319571513156725175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66388318213047675437816783 99582477319571513156725175)
  ·
    refine ⟨149373715979357269735087763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99582477319571513156725175 149373715979357269735087763)
    ·
      refine ⟨224060573969035904602631645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149373715979357269735087763 224060573969035904602631645)
      ·
        refine ⟨84022715238388464225986867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224060573969035904602631645 84022715238388464225986867)
        ·
          refine ⟨126034072857582696338980301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84022715238388464225986867 126034072857582696338980301)
          ·
            refine ⟨47262777321593511127117613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126034072857582696338980301 47262777321593511127117613)
            ·
              refine ⟨17723541495597566672669105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47262777321593511127117613 17723541495597566672669105)
              ·
                refine ⟨13292656121698175004501829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17723541495597566672669105 13292656121698175004501829)
                ·
                  refine ⟨2492373022818407813344093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13292656121698175004501829 2492373022818407813344093)
                  ·
                    refine ⟨934639883556902930004035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492373022818407813344093 934639883556902930004035)
                    ·
                      rfl

theorem cell22_2730307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].length) (baseStart_2730307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730307 prefixEnd_2730307 := by exact prefixLift 2730307
  have htrace : WordTrace (prefixWord ++ tailWord_2730307) baseStart_2730307 baseEnd_2730307 := by
    simpa [prefixWord, tailWord_2730307, baseEnd_2730307] using wordTrace_append hprefix tailTrace_2730307
  have hstable : (prefixWord ++ tailWord_2730307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730307).length < 2 ^ (prefixWord ++ tailWord_2730307).sum := by decide
  have hdescent : baseEnd_2730307 < baseStart_2730307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730320 : List Nat := [2, 1, 1, 1, 1, 6, 10]
def baseStart_2730320 : Nat := 118140960795 + 2730320 * 2 ^ 59
def prefixEnd_2730320 : Nat := 4983230072969 + 3 ^ 40 * 2730320 * 2
def baseEnd_2730320 : Nat := 34616456804539823312185

theorem tailTrace_2730320 : CollatzResearch.WordTrace tailWord_2730320 prefixEnd_2730320 34616456804539823312185 := by
  unfold tailWord_2730320
  simp only [CollatzResearch.WordTrace]
  refine ⟨49791475734262208188474207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66388634312349610917965609 49791475734262208188474207)
  ·
    refine ⟨74687213601393312282711311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49791475734262208188474207 74687213601393312282711311)
    ·
      refine ⟨112030820402089968424066967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74687213601393312282711311 112030820402089968424066967)
      ·
        refine ⟨168046230603134952636100451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112030820402089968424066967 168046230603134952636100451)
        ·
          refine ⟨252069345904702428954150677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168046230603134952636100451 252069345904702428954150677)
          ·
            refine ⟨11815750589282926357225813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252069345904702428954150677 11815750589282926357225813)
            ·
              refine ⟨34616456804539823312185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11815750589282926357225813 34616456804539823312185)
              ·
                rfl

theorem cell22_2730320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 10].length) (baseStart_2730320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730320 prefixEnd_2730320 := by exact prefixLift 2730320
  have htrace : WordTrace (prefixWord ++ tailWord_2730320) baseStart_2730320 baseEnd_2730320 := by
    simpa [prefixWord, tailWord_2730320, baseEnd_2730320] using wordTrace_append hprefix tailTrace_2730320
  have hstable : (prefixWord ++ tailWord_2730320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730320).length < 2 ^ (prefixWord ++ tailWord_2730320).sum := by decide
  have hdescent : baseEnd_2730320 < baseStart_2730320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730322 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2730322 : Nat := 118140960795 + 2730322 * 2 ^ 59
def prefixEnd_2730322 : Nat := 4983230072969 + 3 ^ 40 * 2730322 * 2
def baseEnd_2730322 : Nat := 934645018363447890878989

theorem tailTrace_2730322 : CollatzResearch.WordTrace tailWord_2730322 prefixEnd_2730322 934645018363447890878989 := by
  unfold tailWord_2730322
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895756103629292679630305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66388682943011447145680813 24895756103629292679630305)
  ·
    refine ⟨18671817077721969509722729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24895756103629292679630305 18671817077721969509722729)
    ·
      refine ⟨14003862808291477132292047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18671817077721969509722729 14003862808291477132292047)
      ·
        refine ⟨21005794212437215698438071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003862808291477132292047 21005794212437215698438071)
        ·
          refine ⟨31508691318655823547657107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005794212437215698438071 31508691318655823547657107)
          ·
            refine ⟨47263036977983735321485661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31508691318655823547657107 47263036977983735321485661)
            ·
              refine ⟨17723638866743900745557123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47263036977983735321485661 17723638866743900745557123)
              ·
                refine ⟨26585458300115851118335685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17723638866743900745557123 26585458300115851118335685)
                ·
                  refine ⟨4984773431271722084687941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26585458300115851118335685 4984773431271722084687941)
                  ·
                    refine ⟨934645018363447890878989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4984773431271722084687941 934645018363447890878989)
                    ·
                      rfl

theorem cell22_2730322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2730322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730322 prefixEnd_2730322 := by exact prefixLift 2730322
  have htrace : WordTrace (prefixWord ++ tailWord_2730322) baseStart_2730322 baseEnd_2730322 := by
    simpa [prefixWord, tailWord_2730322, baseEnd_2730322] using wordTrace_append hprefix tailTrace_2730322
  have hstable : (prefixWord ++ tailWord_2730322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730322).length < 2 ^ (prefixWord ++ tailWord_2730322).sum := by decide
  have hdescent : baseEnd_2730322 < baseStart_2730322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730324 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2730324 : Nat := 118140960795 + 2730324 * 2 ^ 59
def prefixEnd_2730324 : Nat := 4983230072969 + 3 ^ 40 * 2730324 * 2
def baseEnd_2730324 : Nat := 934645703004320552328983

theorem tailTrace_2730324 : CollatzResearch.WordTrace tailWord_2730324 prefixEnd_2730324 934645703004320552328983 := by
  unfold tailWord_2730324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49791548680254962530047013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66388731573673283373396017 49791548680254962530047013)
  ·
    refine ⟨9335915377547805474383815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49791548680254962530047013 9335915377547805474383815)
    ·
      refine ⟨14003873066321708211575723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9335915377547805474383815 14003873066321708211575723)
      ·
        refine ⟨21005809599482562317363585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003873066321708211575723 21005809599482562317363585)
        ·
          refine ⟨15754357199611921738022689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21005809599482562317363585 15754357199611921738022689)
          ·
            refine ⟨11815767899708941303517017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15754357199611921738022689 11815767899708941303517017)
            ·
              refine ⟨8861825924781705977637763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11815767899708941303517017 8861825924781705977637763)
              ·
                refine ⟨13292738887172558966456645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861825924781705977637763 13292738887172558966456645)
                ·
                  refine ⟨2492388541344854806210621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13292738887172558966456645 2492388541344854806210621)
                  ·
                    refine ⟨934645703004320552328983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492388541344854806210621 934645703004320552328983)
                    ·
                      rfl

theorem cell22_2730324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2730324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730324 prefixEnd_2730324 := by exact prefixLift 2730324
  have htrace : WordTrace (prefixWord ++ tailWord_2730324) baseStart_2730324 baseEnd_2730324 := by
    simpa [prefixWord, tailWord_2730324, baseEnd_2730324] using wordTrace_append hprefix tailTrace_2730324
  have hstable : (prefixWord ++ tailWord_2730324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730324).length < 2 ^ (prefixWord ++ tailWord_2730324).sum := by decide
  have hdescent : baseEnd_2730324 < baseStart_2730324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730341 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_2730341 : Nat := 118140960795 + 2730341 * 2 ^ 59
def prefixEnd_2730341 : Nat := 4983230072969 + 3 ^ 40 * 2730341 * 2
def baseEnd_2730341 : Nat := 934651522451738174653931

theorem tailTrace_2730341 : CollatzResearch.WordTrace tailWord_2730341 prefixEnd_2730341 934651522451738174653931 := by
  unfold tailWord_2730341
  simp only [CollatzResearch.WordTrace]
  refine ⟨99583717401448336963462877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66389144934298891308975251 99583717401448336963462877)
  ·
    refine ⟨37343894025543126361298579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99583717401448336963462877 37343894025543126361298579)
    ·
      refine ⟨56015841038314689541947869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37343894025543126361298579 56015841038314689541947869)
      ·
        refine ⟨21005940389368008578230451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56015841038314689541947869 21005940389368008578230451)
        ·
          refine ⟨31508910584052012867345677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005940389368008578230451 31508910584052012867345677)
          ·
            refine ⟨11815841469019504825254629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31508910584052012867345677 11815841469019504825254629)
            ·
              refine ⟨2215470275441157154735243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11815841469019504825254629 2215470275441157154735243)
              ·
                refine ⟨3323205413161735732102865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215470275441157154735243 3323205413161735732102865)
                ·
                  refine ⟨2492404059871301799077149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323205413161735732102865 2492404059871301799077149)
                  ·
                    refine ⟨934651522451738174653931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492404059871301799077149 934651522451738174653931)
                    ·
                      rfl

theorem cell22_2730341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_2730341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730341 prefixEnd_2730341 := by exact prefixLift 2730341
  have htrace : WordTrace (prefixWord ++ tailWord_2730341) baseStart_2730341 baseEnd_2730341 := by
    simpa [prefixWord, tailWord_2730341, baseEnd_2730341] using wordTrace_append hprefix tailTrace_2730341
  have hstable : (prefixWord ++ tailWord_2730341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730341).length < 2 ^ (prefixWord ++ tailWord_2730341).sum := by decide
  have hdescent : baseEnd_2730341 < baseStart_2730341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730433 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 7]
def baseStart_2730433 : Nat := 118140960795 + 2730433 * 2 ^ 59
def prefixEnd_2730433 : Nat := 4983230072969 + 3 ^ 40 * 2730433 * 2
def baseEnd_2730433 : Nat := 311561005310626867117883

theorem tailTrace_2730433 : CollatzResearch.WordTrace tailWord_2730433 prefixEnd_2730433 311561005310626867117883 := by
  unfold tailWord_2730433
  simp only [CollatzResearch.WordTrace]
  refine ⟨99587072917115036675811953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66391381944743357783874635 99587072917115036675811953)
  ·
    refine ⟨74690304687836277506858965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99587072917115036675811953 74690304687836277506858965)
    ·
      refine ⟨1750554016121162754067007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74690304687836277506858965 1750554016121162754067007)
      ·
        refine ⟨2625831024181744131100511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750554016121162754067007 2625831024181744131100511)
        ·
          refine ⟨3938746536272616196650767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625831024181744131100511 3938746536272616196650767)
          ·
            refine ⟨5908119804408924294976151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938746536272616196650767 5908119804408924294976151)
            ·
              refine ⟨8862179706613386442464227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908119804408924294976151 8862179706613386442464227)
              ·
                refine ⟨13293269559920079663696341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862179706613386442464227 13293269559920079663696341)
                ·
                  refine ⟨311561005310626867117883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13293269559920079663696341 311561005310626867117883)
                  ·
                    rfl

theorem cell22_2730433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_2730433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730433 prefixEnd_2730433 := by exact prefixLift 2730433
  have htrace : WordTrace (prefixWord ++ tailWord_2730433) baseStart_2730433 baseEnd_2730433 := by
    simpa [prefixWord, tailWord_2730433, baseEnd_2730433] using wordTrace_append hprefix tailTrace_2730433
  have hstable : (prefixWord ++ tailWord_2730433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730433).length < 2 ^ (prefixWord ++ tailWord_2730433).sum := by decide
  have hdescent : baseEnd_2730433 < baseStart_2730433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730457 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2730457 : Nat := 118140960795 + 2730457 * 2 ^ 59
def prefixEnd_2730457 : Nat := 4983230072969 + 3 ^ 40 * 2730457 * 2
def baseEnd_2730457 : Nat := 934691231622352538753575

theorem tailTrace_2730457 : CollatzResearch.WordTrace tailWord_2730457 prefixEnd_2730457 934691231622352538753575 := by
  unfold tailWord_2730457
  simp only [CollatzResearch.WordTrace]
  refine ⟨99587948269028088774685625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66391965512685392516457083 99587948269028088774685625)
  ·
    refine ⟨74690961201771066581014219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99587948269028088774685625 74690961201771066581014219)
    ·
      refine ⟨112036441802656599871521329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74690961201771066581014219 112036441802656599871521329)
      ·
        refine ⟨84027331351992449903640997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112036441802656599871521329 84027331351992449903640997)
        ·
          refine ⟨15755124628498584356932687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84027331351992449903640997 15755124628498584356932687)
          ·
            refine ⟨23632686942747876535399031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15755124628498584356932687 23632686942747876535399031)
            ·
              refine ⟨35449030414121814803098547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23632686942747876535399031 35449030414121814803098547)
              ·
                refine ⟨53173545621182722204647821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35449030414121814803098547 53173545621182722204647821)
                ·
                  refine ⟨19940079607943520826742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53173545621182722204647821 19940079607943520826742933)
                  ·
                    refine ⟨934691231622352538753575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19940079607943520826742933 934691231622352538753575)
                    ·
                      rfl

theorem cell22_2730457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2730457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730457 prefixEnd_2730457 := by exact prefixLift 2730457
  have htrace : WordTrace (prefixWord ++ tailWord_2730457) baseStart_2730457 baseEnd_2730457 := by
    simpa [prefixWord, tailWord_2730457, baseEnd_2730457] using wordTrace_append hprefix tailTrace_2730457
  have hstable : (prefixWord ++ tailWord_2730457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730457).length < 2 ^ (prefixWord ++ tailWord_2730457).sum := by decide
  have hdescent : baseEnd_2730457 < baseStart_2730457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730474 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2730474 : Nat := 118140960795 + 2730474 * 2 ^ 59
def prefixEnd_2730474 : Nat := 4983230072969 + 3 ^ 40 * 2730474 * 2
def baseEnd_2730474 : Nat := 934697051069770161078523

theorem tailTrace_2730474 : CollatzResearch.WordTrace tailWord_2730474 prefixEnd_2730474 934697051069770161078523 := by
  unfold tailWord_2730474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897142077491625169513619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66392378873311000452036317 24897142077491625169513619)
  ·
    refine ⟨37345713116237437754270429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24897142077491625169513619 37345713116237437754270429)
    ·
      refine ⟨14004642418589039157851411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37345713116237437754270429 14004642418589039157851411)
      ·
        refine ⟨21006963627883558736777117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004642418589039157851411 21006963627883558736777117)
        ·
          refine ⟨7877611360456334526291419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21006963627883558736777117 7877611360456334526291419)
          ·
            refine ⟨11816417040684501789437129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7877611360456334526291419 11816417040684501789437129)
            ·
              refine ⟨8862312780513376342077847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11816417040684501789437129 8862312780513376342077847)
              ·
                refine ⟨13293469170770064513116771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862312780513376342077847 13293469170770064513116771)
                ·
                  refine ⟨19940203756155096769675157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13293469170770064513116771 19940203756155096769675157)
                  ·
                    refine ⟨934697051069770161078523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19940203756155096769675157 934697051069770161078523)
                    ·
                      rfl

theorem cell22_2730474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2730474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730474 prefixEnd_2730474 := by exact prefixLift 2730474
  have htrace : WordTrace (prefixWord ++ tailWord_2730474) baseStart_2730474 baseEnd_2730474 := by
    simpa [prefixWord, tailWord_2730474, baseEnd_2730474] using wordTrace_append hprefix tailTrace_2730474
  have hstable : (prefixWord ++ tailWord_2730474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730474).length < 2 ^ (prefixWord ++ tailWord_2730474).sum := by decide
  have hdescent : baseEnd_2730474 < baseStart_2730474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730478 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_2730478 : Nat := 118140960795 + 2730478 * 2 ^ 59
def prefixEnd_2730478 : Nat := 4983230072969 + 3 ^ 40 * 2730478 * 2
def baseEnd_2730478 : Nat := 311566140117171827992837

theorem tailTrace_2730478 : CollatzResearch.WordTrace tailWord_2730478 prefixEnd_2730478 311566140117171827992837 := by
  unfold tailWord_2730478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448589275244001170150011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66392476134634672907466725 12448589275244001170150011)
  ·
    refine ⟨18672883912866001755225017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12448589275244001170150011 18672883912866001755225017)
    ·
      refine ⟨14004662934649501316418763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18672883912866001755225017 14004662934649501316418763)
      ·
        refine ⟨21006994401974251974628145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004662934649501316418763 21006994401974251974628145)
        ·
          refine ⟨15755245801480688980971109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21006994401974251974628145 15755245801480688980971109)
          ·
            refine ⟨2954108587777629183932083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15755245801480688980971109 2954108587777629183932083)
            ·
              refine ⟨4431162881666443775898125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954108587777629183932083 4431162881666443775898125)
              ·
                refine ⟨1661686080624916415961797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4431162881666443775898125 1661686080624916415961797)
                ·
                  refine ⟨311566140117171827992837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661686080624916415961797 311566140117171827992837)
                  ·
                    rfl

theorem cell22_2730478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_2730478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730478 prefixEnd_2730478 := by exact prefixLift 2730478
  have htrace : WordTrace (prefixWord ++ tailWord_2730478) baseStart_2730478 baseEnd_2730478 := by
    simpa [prefixWord, tailWord_2730478, baseEnd_2730478] using wordTrace_append hprefix tailTrace_2730478
  have hstable : (prefixWord ++ tailWord_2730478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730478).length < 2 ^ (prefixWord ++ tailWord_2730478).sum := by decide
  have hdescent : baseEnd_2730478 < baseStart_2730478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730510 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_2730510 : Nat := 118140960795 + 2730510 * 2 ^ 59
def prefixEnd_2730510 : Nat := 4983230072969 + 3 ^ 40 * 2730510 * 2
def baseEnd_2730510 : Nat := 934709374605478067178413

theorem tailTrace_2730510 : CollatzResearch.WordTrace tailWord_2730510 prefixEnd_2730510 934709374605478067178413 := by
  unfold tailWord_2730510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448735167229509853295623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66393254225224052550909989 12448735167229509853295623)
  ·
    refine ⟨18673102750844264779943435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12448735167229509853295623 18673102750844264779943435)
    ·
      refine ⟨28009654126266397169915153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18673102750844264779943435 28009654126266397169915153)
      ·
        refine ⟨21007240594699797877436365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28009654126266397169915153 21007240594699797877436365)
        ·
          refine ⟨7877715223012424204038637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21007240594699797877436365 7877715223012424204038637)
          ·
            refine ⟨2954143208629659076514489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7877715223012424204038637 2954143208629659076514489)
            ·
              refine ⟨2215607406472244307385867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954143208629659076514489 2215607406472244307385867)
              ·
                refine ⟨3323411109708366461078801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215607406472244307385867 3323411109708366461078801)
                ·
                  refine ⟨2492558332281274845809101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323411109708366461078801 2492558332281274845809101)
                  ·
                    refine ⟨934709374605478067178413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492558332281274845809101 934709374605478067178413)
                    ·
                      rfl

theorem cell22_2730510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_2730510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730510 prefixEnd_2730510 := by exact prefixLift 2730510
  have htrace : WordTrace (prefixWord ++ tailWord_2730510) baseStart_2730510 baseEnd_2730510 := by
    simpa [prefixWord, tailWord_2730510, baseEnd_2730510] using wordTrace_append hprefix tailTrace_2730510
  have hstable : (prefixWord ++ tailWord_2730510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730510).length < 2 ^ (prefixWord ++ tailWord_2730510).sum := by decide
  have hdescent : baseEnd_2730510 < baseStart_2730510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730549 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2730549 : Nat := 118140960795 + 2730549 * 2 ^ 59
def prefixEnd_2730549 : Nat := 4983230072969 + 3 ^ 40 * 2730549 * 2
def baseEnd_2730549 : Nat := 934722725102494965453293

theorem tailTrace_2730549 : CollatzResearch.WordTrace tailWord_2730549 prefixEnd_2730549 934722725102494965453293 := by
  unfold tailWord_2730549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99591303784694788487034701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66394202523129858991356467 99591303784694788487034701)
  ·
    refine ⟨37346738919260545682638013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99591303784694788487034701 37346738919260545682638013)
    ·
      refine ⟨14005027094722704630989255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37346738919260545682638013 14005027094722704630989255)
      ·
        refine ⟨21007540642084056946483883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14005027094722704630989255 21007540642084056946483883)
        ·
          refine ⟨31511310963126085419725825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21007540642084056946483883 31511310963126085419725825)
          ·
            refine ⟨23633483222344564064794369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31511310963126085419725825 23633483222344564064794369)
            ·
              refine ⟨17725112416758423048595777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23633483222344564064794369 17725112416758423048595777)
              ·
                refine ⟨13293834312568817286446833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17725112416758423048595777 13293834312568817286446833)
                ·
                  refine ⟨9970375734426612964835125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13293834312568817286446833 9970375734426612964835125)
                  ·
                    refine ⟨934722725102494965453293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9970375734426612964835125 934722725102494965453293)
                    ·
                      rfl

theorem cell22_2730549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2730549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730549 prefixEnd_2730549 := by exact prefixLift 2730549
  have htrace : WordTrace (prefixWord ++ tailWord_2730549) baseStart_2730549 baseEnd_2730549 := by
    simpa [prefixWord, tailWord_2730549, baseEnd_2730549] using wordTrace_append hprefix tailTrace_2730549
  have hstable : (prefixWord ++ tailWord_2730549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730549).length < 2 ^ (prefixWord ++ tailWord_2730549).sum := by decide
  have hdescent : baseEnd_2730549 < baseStart_2730549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730611 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 2, 3]
def baseStart_2730611 : Nat := 118140960795 + 2730611 * 2 ^ 59
def prefixEnd_2730611 : Nat := 4983230072969 + 3 ^ 40 * 2730611 * 2
def baseEnd_2730611 : Nat := 934743948969547470403103

theorem tailTrace_2730611 : CollatzResearch.WordTrace tailWord_2730611 prefixEnd_2730611 934743948969547470403103 := by
  unfold tailWord_2730611
  simp only [CollatzResearch.WordTrace]
  refine ⟨99593565110470173075791687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66395710073646782050527791 99593565110470173075791687)
  ·
    refine ⟨149390347665705259613687531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99593565110470173075791687 149390347665705259613687531)
    ·
      refine ⟨224085521498557889420531297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149390347665705259613687531 224085521498557889420531297)
      ·
        refine ⟨168064141123918417065398473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224085521498557889420531297 168064141123918417065398473)
        ·
          refine ⟨126048105842938812799048855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168064141123918417065398473 126048105842938812799048855)
          ·
            refine ⟨189072158764408219198573283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126048105842938812799048855 189072158764408219198573283)
            ·
              refine ⟨283608238146612328797859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189072158764408219198573283 283608238146612328797859925)
              ·
                refine ⟨3323534040780613228099921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 283608238146612328797859925 3323534040780613228099921)
                ·
                  refine ⟨2492650530585459921074941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323534040780613228099921 2492650530585459921074941)
                  ·
                    refine ⟨934743948969547470403103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492650530585459921074941 934743948969547470403103)
                    ·
                      rfl

theorem cell22_2730611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].length) (baseStart_2730611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730611 prefixEnd_2730611 := by exact prefixLift 2730611
  have htrace : WordTrace (prefixWord ++ tailWord_2730611) baseStart_2730611 baseEnd_2730611 := by
    simpa [prefixWord, tailWord_2730611, baseEnd_2730611] using wordTrace_append hprefix tailTrace_2730611
  have hstable : (prefixWord ++ tailWord_2730611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730611).length < 2 ^ (prefixWord ++ tailWord_2730611).sum := by decide
  have hdescent : baseEnd_2730611 < baseStart_2730611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730613 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 6]
def baseStart_2730613 : Nat := 118140960795 + 2730613 * 2 ^ 59
def prefixEnd_2730613 : Nat := 4983230072969 + 3 ^ 40 * 2730613 * 2
def baseEnd_2730613 : Nat := 311581544536806710617699

theorem tailTrace_2730613 : CollatzResearch.WordTrace tailWord_2730613 prefixEnd_2730613 311581544536806710617699 := by
  unfold tailWord_2730613
  simp only [CollatzResearch.WordTrace]
  refine ⟨99593638056462927417364493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66395758704308618278242995 99593638056462927417364493)
  ·
    refine ⟨37347614271173597781511685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99593638056462927417364493 37347614271173597781511685)
    ·
      refine ⟨7002677675845049584033441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37347614271173597781511685 7002677675845049584033441)
      ·
        refine ⟨5252008256883787188025081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7002677675845049584033441 5252008256883787188025081)
        ·
          refine ⟨3939006192662840391018811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252008256883787188025081 3939006192662840391018811)
          ·
            refine ⟨5908509288994260586528217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939006192662840391018811 5908509288994260586528217)
            ·
              refine ⟨4431381966745695439896163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5908509288994260586528217 4431381966745695439896163)
              ·
                refine ⟨6647072950118543159844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431381966745695439896163 6647072950118543159844245)
                ·
                  refine ⟨311581544536806710617699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6647072950118543159844245 311581544536806710617699)
                  ·
                    rfl

theorem cell22_2730613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_2730613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730613 prefixEnd_2730613 := by exact prefixLift 2730613
  have htrace : WordTrace (prefixWord ++ tailWord_2730613) baseStart_2730613 baseEnd_2730613 := by
    simpa [prefixWord, tailWord_2730613, baseEnd_2730613] using wordTrace_append hprefix tailTrace_2730613
  have hstable : (prefixWord ++ tailWord_2730613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730613).length < 2 ^ (prefixWord ++ tailWord_2730613).sum := by decide
  have hdescent : baseEnd_2730613 < baseStart_2730613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730628 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2730628 : Nat := 118140960795 + 2730628 * 2 ^ 59
def prefixEnd_2730628 : Nat := 4983230072969 + 3 ^ 40 * 2730628 * 2
def baseEnd_2730628 : Nat := 934749768416965092728051

theorem tailTrace_2730628 : CollatzResearch.WordTrace tailWord_2730628 prefixEnd_2730628 934749768416965092728051 := by
  unfold tailWord_2730628
  simp only [CollatzResearch.WordTrace]
  refine ⟨49797092575704292489580269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66396123434272389986107025 49797092575704292489580269)
  ·
    refine ⟨18673909715889109683592601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49797092575704292489580269 18673909715889109683592601)
    ·
      refine ⟨14005432286916832262694451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18673909715889109683592601 14005432286916832262694451)
      ·
        refine ⟨21008148430375248394041677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14005432286916832262694451 21008148430375248394041677)
        ·
          refine ⟨7878055661390718147765629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21008148430375248394041677 7878055661390718147765629)
          ·
            refine ⟨2954270873021519305412111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7878055661390718147765629 2954270873021519305412111)
            ·
              refine ⟨4431406309532278958118167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954270873021519305412111 4431406309532278958118167)
              ·
                refine ⟨6647109464298418437177251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431406309532278958118167 6647109464298418437177251)
                ·
                  refine ⟨9970664196447627655765877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647109464298418437177251 9970664196447627655765877)
                  ·
                    refine ⟨934749768416965092728051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9970664196447627655765877 934749768416965092728051)
                    ·
                      rfl

theorem cell22_2730628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2730628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730628 prefixEnd_2730628 := by exact prefixLift 2730628
  have htrace : WordTrace (prefixWord ++ tailWord_2730628) baseStart_2730628 baseEnd_2730628 := by
    simpa [prefixWord, tailWord_2730628, baseEnd_2730628] using wordTrace_append hprefix tailTrace_2730628
  have hstable : (prefixWord ++ tailWord_2730628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730628).length < 2 ^ (prefixWord ++ tailWord_2730628).sum := by decide
  have hdescent : baseEnd_2730628 < baseStart_2730628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730746 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_2730746 : Nat := 118140960795 + 2730746 * 2 ^ 59
def prefixEnd_2730746 : Nat := 4983230072969 + 3 ^ 40 * 2730746 * 2
def baseEnd_2730746 : Nat := 934790162228452118277689

theorem tailTrace_2730746 : CollatzResearch.WordTrace tailWord_2730746 prefixEnd_2730746 934790162228452118277689 := by
  unfold tailWord_2730746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24899622241245272782989023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66398992643320727421304061 24899622241245272782989023)
  ·
    refine ⟨37349433361867909174483535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24899622241245272782989023 37349433361867909174483535)
    ·
      refine ⟨56024150042801863761725303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37349433361867909174483535 56024150042801863761725303)
      ·
        refine ⟨84036225064202795642587955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56024150042801863761725303 84036225064202795642587955)
        ·
          refine ⟨126054337596304193463881933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84036225064202795642587955 126054337596304193463881933)
          ·
            refine ⟨47270376598614072548955725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126054337596304193463881933 47270376598614072548955725)
            ·
              refine ⟨17726391224480277205858397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47270376598614072548955725 17726391224480277205858397)
              ·
                refine ⟨6647396709180103952196899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17726391224480277205858397 6647396709180103952196899)
                ·
                  refine ⟨9971095063770155928295349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647396709180103952196899 9971095063770155928295349)
                  ·
                    refine ⟨934790162228452118277689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971095063770155928295349 934790162228452118277689)
                    ·
                      rfl

theorem cell22_2730746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_2730746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730746 prefixEnd_2730746 := by exact prefixLift 2730746
  have htrace : WordTrace (prefixWord ++ tailWord_2730746) baseStart_2730746 baseEnd_2730746 := by
    simpa [prefixWord, tailWord_2730746, baseEnd_2730746] using wordTrace_append hprefix tailTrace_2730746
  have hstable : (prefixWord ++ tailWord_2730746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730746).length < 2 ^ (prefixWord ++ tailWord_2730746).sum := by decide
  have hdescent : baseEnd_2730746 < baseStart_2730746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730780 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2730780 : Nat := 118140960795 + 2730780 * 2 ^ 59
def prefixEnd_2730780 : Nat := 4983230072969 + 3 ^ 40 * 2730780 * 2
def baseEnd_2730780 : Nat := 934801801123287362927585

theorem tailTrace_2730780 : CollatzResearch.WordTrace tailWord_2730780 prefixEnd_2730780 934801801123287362927585 := by
  unfold tailWord_2730780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49799864523428957469346897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66399819364571943292462529 49799864523428957469346897)
  ·
    refine ⟨37349898392571718102010173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49799864523428957469346897 37349898392571718102010173)
    ·
      refine ⟨14006211897214394288253815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37349898392571718102010173 14006211897214394288253815)
      ·
        refine ⟨21009317845821591432380723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14006211897214394288253815 21009317845821591432380723)
        ·
          refine ⟨31513976768732387148571085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21009317845821591432380723 31513976768732387148571085)
          ·
            refine ⟨11817741288274645180714157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31513976768732387148571085 11817741288274645180714157)
            ·
              refine ⟨4431652983102991942767809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11817741288274645180714157 4431652983102991942767809)
              ·
                refine ⟨3323739737327243957075857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4431652983102991942767809 3323739737327243957075857)
                ·
                  refine ⟨2492804802995432967806893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323739737327243957075857 2492804802995432967806893)
                  ·
                    refine ⟨934801801123287362927585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492804802995432967806893 934801801123287362927585)
                    ·
                      rfl

theorem cell22_2730780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2730780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730780 prefixEnd_2730780 := by exact prefixLift 2730780
  have htrace : WordTrace (prefixWord ++ tailWord_2730780) baseStart_2730780 baseEnd_2730780 := by
    simpa [prefixWord, tailWord_2730780, baseEnd_2730780] using wordTrace_append hprefix tailTrace_2730780
  have hstable : (prefixWord ++ tailWord_2730780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730780).length < 2 ^ (prefixWord ++ tailWord_2730780).sum := by decide
  have hdescent : baseEnd_2730780 < baseStart_2730780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730808 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_2730808 : Nat := 118140960795 + 2730808 * 2 ^ 59
def prefixEnd_2730808 : Nat := 4983230072969 + 3 ^ 40 * 2730808 * 2
def baseEnd_2730808 : Nat := 934811386095504623227499

theorem tailTrace_2730808 : CollatzResearch.WordTrace tailWord_2730808 prefixEnd_2730808 934811386095504623227499 := by
  unfold tailWord_2730808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49800375145378237860356539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66400500193837650480475385 49800375145378237860356539)
  ·
    refine ⟨74700562718067356790534809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49800375145378237860356539 74700562718067356790534809)
    ·
      refine ⟨56025422038550517592901107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74700562718067356790534809 56025422038550517592901107)
      ·
        refine ⟨84038133057825776389351661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56025422038550517592901107 84038133057825776389351661)
        ·
          refine ⟨31514299896684666146006873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84038133057825776389351661 31514299896684666146006873)
          ·
            refine ⟨23635724922513499609505155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31514299896684666146006873 23635724922513499609505155)
            ·
              refine ⟨35453587383770249414257733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23635724922513499609505155 35453587383770249414257733)
              ·
                refine ⟨6647547634456921765173325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35453587383770249414257733 6647547634456921765173325)
                ·
                  refine ⟨2492830362921345661939997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6647547634456921765173325 2492830362921345661939997)
                  ·
                    refine ⟨934811386095504623227499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492830362921345661939997 934811386095504623227499)
                    ·
                      rfl

theorem cell22_2730808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_2730808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730808 prefixEnd_2730808 := by exact prefixLift 2730808
  have htrace : WordTrace (prefixWord ++ tailWord_2730808) baseStart_2730808 baseEnd_2730808 := by
    simpa [prefixWord, tailWord_2730808, baseEnd_2730808] using wordTrace_append hprefix tailTrace_2730808
  have hstable : (prefixWord ++ tailWord_2730808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730808).length < 2 ^ (prefixWord ++ tailWord_2730808).sum := by decide
  have hdescent : baseEnd_2730808 < baseStart_2730808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730810 : List Nat := [3, 1, 1, 1, 6, 2, 2, 6]
def baseStart_2730810 : Nat := 118140960795 + 2730810 * 2 ^ 59
def prefixEnd_2730810 : Nat := 4983230072969 + 3 ^ 40 * 2730810 * 2
def baseEnd_2730810 : Nat := 103868007859597476075277

theorem tailTrace_2730810 : CollatzResearch.WordTrace tailWord_2730810 prefixEnd_2730810 103868007859597476075277 := by
  unfold tailWord_2730810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24900205809187307515571471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66400548824499486708190589 24900205809187307515571471)
  ·
    refine ⟨37350308713780961273357207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24900205809187307515571471 37350308713780961273357207)
    ·
      refine ⟨56025463070671441910035811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37350308713780961273357207 56025463070671441910035811)
      ·
        refine ⟨84038194606007162865053717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56025463070671441910035811 84038194606007162865053717)
        ·
          refine ⟨3939290372156585759299393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84038194606007162865053717 3939290372156585759299393)
          ·
            refine ⟨2954467779117439319474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939290372156585759299393 2954467779117439319474545)
            ·
              refine ⟨2215850834338079489605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954467779117439319474545 2215850834338079489605909)
              ·
                refine ⟨103868007859597476075277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2215850834338079489605909 103868007859597476075277)
                ·
                  rfl

theorem cell22_2730810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_2730810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730810 prefixEnd_2730810 := by exact prefixLift 2730810
  have htrace : WordTrace (prefixWord ++ tailWord_2730810) baseStart_2730810 baseEnd_2730810 := by
    simpa [prefixWord, tailWord_2730810, baseEnd_2730810] using wordTrace_append hprefix tailTrace_2730810
  have hstable : (prefixWord ++ tailWord_2730810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730810).length < 2 ^ (prefixWord ++ tailWord_2730810).sum := by decide
  have hdescent : baseEnd_2730810 < baseStart_2730810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730855 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 5]
def baseStart_2730855 : Nat := 118140960795 + 2730855 * 2 ^ 59
def prefixEnd_2730855 : Nat := 4983230072969 + 3 ^ 40 * 2730855 * 2
def baseEnd_2730855 : Nat := 311609158385337389100785

theorem tailTrace_2730855 : CollatzResearch.WordTrace tailWord_2730855 prefixEnd_2730855 311609158385337389100785 := by
  unfold tailWord_2730855
  simp only [CollatzResearch.WordTrace]
  refine ⟨99602464521586202747674019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66401643014390801831782679 99602464521586202747674019)
  ·
    refine ⟨149403696782379304121511029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99602464521586202747674019 149403696782379304121511029)
    ·
      refine ⟨14006596573348059761391659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149403696782379304121511029 14006596573348059761391659)
      ·
        refine ⟨21009894860022089642087489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14006596573348059761391659 21009894860022089642087489)
        ·
          refine ⟨15757421145016567231565617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21009894860022089642087489 15757421145016567231565617)
          ·
            refine ⟨11818065858762425423674213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15757421145016567231565617 11818065858762425423674213)
            ·
              refine ⟨2215887348517954766938915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11818065858762425423674213 2215887348517954766938915)
              ·
                refine ⟨3323831022776932150408373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215887348517954766938915 3323831022776932150408373)
                ·
                  refine ⟨311609158385337389100785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3323831022776932150408373 311609158385337389100785)
                  ·
                    rfl

theorem cell22_2730855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 5].length) (baseStart_2730855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730855 prefixEnd_2730855 := by exact prefixLift 2730855
  have htrace : WordTrace (prefixWord ++ tailWord_2730855) baseStart_2730855 baseEnd_2730855 := by
    simpa [prefixWord, tailWord_2730855, baseEnd_2730855] using wordTrace_append hprefix tailTrace_2730855
  have hstable : (prefixWord ++ tailWord_2730855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730855).length < 2 ^ (prefixWord ++ tailWord_2730855).sum := by decide
  have hdescent : baseEnd_2730855 < baseStart_2730855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730915 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 2, 3]
def baseStart_2730915 : Nat := 118140960795 + 2730915 * 2 ^ 59
def prefixEnd_2730915 : Nat := 4983230072969 + 3 ^ 40 * 2730915 * 2
def baseEnd_2730915 : Nat := 934848014382192010802171

theorem tailTrace_2730915 : CollatzResearch.WordTrace tailWord_2730915 prefixEnd_2730915 934848014382192010802171 := by
  unfold tailWord_2730915
  simp only [CollatzResearch.WordTrace]
  refine ⟨99604652901368832994858199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66403101934245888663238799 99604652901368832994858199)
  ·
    refine ⟨149406979352053249492287299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99604652901368832994858199 149406979352053249492287299)
    ·
      refine ⟨224110469028079874238430949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149406979352053249492287299 224110469028079874238430949)
      ·
        refine ⟨42020712942764976419705803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224110469028079874238430949 42020712942764976419705803)
        ·
          refine ⟨63031069414147464629558705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42020712942764976419705803 63031069414147464629558705)
          ·
            refine ⟨47273302060610598472169029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63031069414147464629558705 47273302060610598472169029)
            ·
              refine ⟨8863744136364487213531693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47273302060610598472169029 8863744136364487213531693)
              ·
                refine ⟨3323904051136682705074385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8863744136364487213531693 3323904051136682705074385)
                ·
                  refine ⟨2492928038352512028805789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323904051136682705074385 2492928038352512028805789)
                  ·
                    refine ⟨934848014382192010802171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492928038352512028805789 934848014382192010802171)
                    ·
                      rfl

theorem cell22_2730915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 3].length) (baseStart_2730915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730915 prefixEnd_2730915 := by exact prefixLift 2730915
  have htrace : WordTrace (prefixWord ++ tailWord_2730915) baseStart_2730915 baseEnd_2730915 := by
    simpa [prefixWord, tailWord_2730915, baseEnd_2730915] using wordTrace_append hprefix tailTrace_2730915
  have hstable : (prefixWord ++ tailWord_2730915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730915).length < 2 ^ (prefixWord ++ tailWord_2730915).sum := by decide
  have hdescent : baseEnd_2730915 < baseStart_2730915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730932 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2730932 : Nat := 118140960795 + 2730932 * 2 ^ 59
def prefixEnd_2730932 : Nat := 4983230072969 + 3 ^ 40 * 2730932 * 2
def baseEnd_2730932 : Nat := 934853833829609633127119

theorem tailTrace_2730932 : CollatzResearch.WordTrace tailWord_2730932 prefixEnd_2730932 934853833829609633127119 := by
  unfold tailWord_2730932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49802636471153622449113525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66403515294871496598818033 49802636471153622449113525)
  ·
    refine ⟨4668997169170652104604393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49802636471153622449113525 4668997169170652104604393)
    ·
      refine ⟨3501747876877989078453295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4668997169170652104604393 3501747876877989078453295)
      ·
        refine ⟨5252621815316983617679943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501747876877989078453295 5252621815316983617679943)
        ·
          refine ⟨7878932722975475426519915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252621815316983617679943 7878932722975475426519915)
          ·
            refine ⟨11818399084463213139779873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7878932722975475426519915 11818399084463213139779873)
            ·
              refine ⟨8863799313347409854834905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818399084463213139779873 8863799313347409854834905)
              ·
                refine ⟨6647849485010557391126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8863799313347409854834905 6647849485010557391126179)
                ·
                  refine ⟨9971774227515836086689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647849485010557391126179 9971774227515836086689269)
                  ·
                    refine ⟨934853833829609633127119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971774227515836086689269 934853833829609633127119)
                    ·
                      rfl

theorem cell22_2730932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2730932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730932 prefixEnd_2730932 := by exact prefixLift 2730932
  have htrace : WordTrace (prefixWord ++ tailWord_2730932) baseStart_2730932 baseEnd_2730932 := by
    simpa [prefixWord, tailWord_2730932, baseEnd_2730932] using wordTrace_append hprefix tailTrace_2730932
  have hstable : (prefixWord ++ tailWord_2730932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730932).length < 2 ^ (prefixWord ++ tailWord_2730932).sum := by decide
  have hdescent : baseEnd_2730932 < baseStart_2730932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730966 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2730966 : Nat := 118140960795 + 2730966 * 2 ^ 59
def prefixEnd_2730966 : Nat := 4983230072969 + 3 ^ 40 * 2730966 * 2
def baseEnd_2730966 : Nat := 934865472724444877777015

theorem tailTrace_2730966 : CollatzResearch.WordTrace tailWord_2730966 prefixEnd_2730966 934865472724444877777015 := by
  unfold tailWord_2730966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225407064011504294060297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66404342016122712469976501 6225407064011504294060297)
  ·
    refine ⟨4669055298008628220545223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6225407064011504294060297 4669055298008628220545223)
    ·
      refine ⟨7003582947012942330817835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669055298008628220545223 7003582947012942330817835)
      ·
        refine ⟨10505374420519413496226753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003582947012942330817835 10505374420519413496226753)
        ·
          refine ⟨7879030815389560122170065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10505374420519413496226753 7879030815389560122170065)
          ·
            refine ⟨5909273111542170091627549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7879030815389560122170065 5909273111542170091627549)
            ·
              refine ⟨2215977416828313784360331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5909273111542170091627549 2215977416828313784360331)
              ·
                refine ⟨3323966125242470676540497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215977416828313784360331 3323966125242470676540497)
                ·
                  refine ⟨2492974593931853007405373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323966125242470676540497 2492974593931853007405373)
                  ·
                    refine ⟨934865472724444877777015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492974593931853007405373 934865472724444877777015)
                    ·
                      rfl

theorem cell22_2730966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2730966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730966 prefixEnd_2730966 := by exact prefixLift 2730966
  have htrace : WordTrace (prefixWord ++ tailWord_2730966) baseStart_2730966 baseEnd_2730966 := by
    simpa [prefixWord, tailWord_2730966, baseEnd_2730966] using wordTrace_append hprefix tailTrace_2730966
  have hstable : (prefixWord ++ tailWord_2730966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730966).length < 2 ^ (prefixWord ++ tailWord_2730966).sum := by decide
  have hdescent : baseEnd_2730966 < baseStart_2730966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2730996 : List Nat := [2, 6, 2, 1, 1, 2, 8]
def baseStart_2730996 : Nat := 118140960795 + 2730996 * 2 ^ 59
def prefixEnd_2730996 : Nat := 4983230072969 + 3 ^ 40 * 2730996 * 2
def baseEnd_2730996 : Nat := 34625027493982770352849

theorem tailTrace_2730996 : CollatzResearch.WordTrace tailWord_2730996 prefixEnd_2730996 34625027493982770352849 := by
  unfold tailWord_2730996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49803803607037691914278421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66405071476050255885704561 49803803607037691914278421)
  ·
    refine ⟨2334553294079891808481801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49803803607037691914278421 2334553294079891808481801)
    ·
      refine ⟨1750914970559918856361351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334553294079891808481801 1750914970559918856361351)
      ·
        refine ⟨2626372455839878284542027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750914970559918856361351 2626372455839878284542027)
        ·
          refine ⟨3939558683759817426813041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626372455839878284542027 3939558683759817426813041)
          ·
            refine ⟨2954669012819863070109781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939558683759817426813041 2954669012819863070109781)
            ·
              refine ⟨34625027493982770352849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2954669012819863070109781 34625027493982770352849)
              ·
                rfl

theorem cell22_2730996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 8].length) (baseStart_2730996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2730996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2730996 prefixEnd_2730996 := by exact prefixLift 2730996
  have htrace : WordTrace (prefixWord ++ tailWord_2730996) baseStart_2730996 baseEnd_2730996 := by
    simpa [prefixWord, tailWord_2730996, baseEnd_2730996] using wordTrace_append hprefix tailTrace_2730996
  have hstable : (prefixWord ++ tailWord_2730996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2730996).length < 2 ^ (prefixWord ++ tailWord_2730996).sum := by decide
  have hdescent : baseEnd_2730996 < baseStart_2730996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2730996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731003 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_2731003 : Nat := 118140960795 + 2731003 * 2 ^ 59
def prefixEnd_2731003 : Nat := 4983230072969 + 3 ^ 40 * 2731003 * 2
def baseEnd_2731003 : Nat := 934878138580589114601901

theorem tailTrace_2731003 : CollatzResearch.WordTrace tailWord_2731003 prefixEnd_2731003 934878138580589114601901 := by
  unfold tailWord_2731003
  simp only [CollatzResearch.WordTrace]
  refine ⟨99607862525050024024061663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66405241683366682682707775 99607862525050024024061663)
  ·
    refine ⟨149411793787575036036092495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99607862525050024024061663 149411793787575036036092495)
    ·
      refine ⟨224117690681362554054138743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149411793787575036036092495 224117690681362554054138743)
      ·
        refine ⟨336176536022043831081208115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224117690681362554054138743 336176536022043831081208115)
        ·
          refine ⟨504264804033065746621812173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336176536022043831081208115 504264804033065746621812173)
          ·
            refine ⟨189099301512399654983179565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504264804033065746621812173 189099301512399654983179565)
            ·
              refine ⟨70912238067149870618692337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189099301512399654983179565 70912238067149870618692337)
              ·
                refine ⟨53184178550362402964019253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70912238067149870618692337 53184178550362402964019253)
                ·
                  refine ⟨4986016739096475277876805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53184178550362402964019253 4986016739096475277876805)
                  ·
                    refine ⟨934878138580589114601901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986016739096475277876805 934878138580589114601901)
                    ·
                      rfl

theorem cell22_2731003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_2731003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731003 prefixEnd_2731003 := by exact prefixLift 2731003
  have htrace : WordTrace (prefixWord ++ tailWord_2731003) baseStart_2731003 baseEnd_2731003 := by
    simpa [prefixWord, tailWord_2731003, baseEnd_2731003] using wordTrace_append hprefix tailTrace_2731003
  have hstable : (prefixWord ++ tailWord_2731003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731003).length < 2 ^ (prefixWord ++ tailWord_2731003).sum := by decide
  have hdescent : baseEnd_2731003 < baseStart_2731003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731037 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2731037 : Nat := 118140960795 + 2731037 * 2 ^ 59
def prefixEnd_2731037 : Nat := 4983230072969 + 3 ^ 40 * 2731037 * 2
def baseEnd_2731037 : Nat := 934889777475424359251797

theorem tailTrace_2731037 : CollatzResearch.WordTrace tailWord_2731037 prefixEnd_2731037 934889777475424359251797 := by
  unfold tailWord_2731037
  simp only [CollatzResearch.WordTrace]
  refine ⟨99609102606926847830799365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66406068404617898553866243 99609102606926847830799365)
  ·
    refine ⟨18676706738798783968274881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99609102606926847830799365 18676706738798783968274881)
    ·
      refine ⟨14007530054099087976206161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18676706738798783968274881 14007530054099087976206161)
      ·
        refine ⟨10505647540574315982154621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14007530054099087976206161 10505647540574315982154621)
        ·
          refine ⟨3939617827715368493307983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10505647540574315982154621 3939617827715368493307983)
          ·
            refine ⟨5909426741573052739961975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939617827715368493307983 5909426741573052739961975)
            ·
              refine ⟨8864140112359579109942963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909426741573052739961975 8864140112359579109942963)
              ·
                refine ⟨13296210168539368664914445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8864140112359579109942963 13296210168539368664914445)
                ·
                  refine ⟨4986078813202263249342917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13296210168539368664914445 4986078813202263249342917)
                  ·
                    refine ⟨934889777475424359251797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986078813202263249342917 934889777475424359251797)
                    ·
                      rfl

theorem cell22_2731037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2731037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731037 prefixEnd_2731037 := by exact prefixLift 2731037
  have htrace : WordTrace (prefixWord ++ tailWord_2731037) baseStart_2731037 baseEnd_2731037 := by
    simpa [prefixWord, tailWord_2731037, baseEnd_2731037] using wordTrace_append hprefix tailTrace_2731037
  have hstable : (prefixWord ++ tailWord_2731037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731037).length < 2 ^ (prefixWord ++ tailWord_2731037).sum := by decide
  have hdescent : baseEnd_2731037 < baseStart_2731037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731054 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2731054 : Nat := 118140960795 + 2731054 * 2 ^ 59
def prefixEnd_2731054 : Nat := 4983230072969 + 3 ^ 40 * 2731054 * 2
def baseEnd_2731054 : Nat := 934895596922841981576745

theorem tailTrace_2731054 : CollatzResearch.WordTrace tailWord_2731054 prefixEnd_2731054 934895596922841981576745 := by
  unfold tailWord_2731054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451215330983157466771027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66406481765243506489445477 12451215330983157466771027)
  ·
    refine ⟨18676822996474736200156541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12451215330983157466771027 18676822996474736200156541)
    ·
      refine ⟨7003808623678026075058703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18676822996474736200156541 7003808623678026075058703)
      ·
        refine ⟨10505712935517039112588055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003808623678026075058703 10505712935517039112588055)
        ·
          refine ⟨15758569403275558668882083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505712935517039112588055 15758569403275558668882083)
          ·
            refine ⟨23637854104913338003323125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758569403275558668882083 23637854104913338003323125)
            ·
              refine ⟨2216048822335625437811543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23637854104913338003323125 2216048822335625437811543)
              ·
                refine ⟨3324073233503438156717315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216048822335625437811543 3324073233503438156717315)
                ·
                  refine ⟨4986109850255157235075973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324073233503438156717315 4986109850255157235075973)
                  ·
                    refine ⟨934895596922841981576745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986109850255157235075973 934895596922841981576745)
                    ·
                      rfl

theorem cell22_2731054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2731054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731054 prefixEnd_2731054 := by exact prefixLift 2731054
  have htrace : WordTrace (prefixWord ++ tailWord_2731054) baseStart_2731054 baseEnd_2731054 := by
    simpa [prefixWord, tailWord_2731054, baseEnd_2731054] using wordTrace_append hprefix tailTrace_2731054
  have hstable : (prefixWord ++ tailWord_2731054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731054).length < 2 ^ (prefixWord ++ tailWord_2731054).sum := by decide
  have hdescent : baseEnd_2731054 < baseStart_2731054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731069 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 4]
def baseStart_2731069 : Nat := 118140960795 + 2731069 * 2 ^ 59
def prefixEnd_2731069 : Nat := 4983230072969 + 3 ^ 40 * 2731069 * 2
def baseEnd_2731069 : Nat := 311633577243128980817233

theorem tailTrace_2731069 : CollatzResearch.WordTrace tailWord_2731069 prefixEnd_2731069 311633577243128980817233 := by
  unfold tailWord_2731069
  simp only [CollatzResearch.WordTrace]
  refine ⟨99610269742810917295964261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66406846495207278197309507 99610269742810917295964261)
  ·
    refine ⟨18676925576777046992993299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99610269742810917295964261 18676925576777046992993299)
    ·
      refine ⟨28015388365165570489489949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18676925576777046992993299 28015388365165570489489949)
      ·
        refine ⟨10505770636937088933558731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28015388365165570489489949 10505770636937088933558731)
        ·
          refine ⟨15758655955405633400338097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505770636937088933558731 15758655955405633400338097)
          ·
            refine ⟨11818991966554225050253573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15758655955405633400338097 11818991966554225050253573)
            ·
              refine ⟨2216060993728917196922545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11818991966554225050253573 2216060993728917196922545)
              ·
                refine ⟨1662045745296687897691909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216060993728917196922545 1662045745296687897691909)
                ·
                  refine ⟨311633577243128980817233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662045745296687897691909 311633577243128980817233)
                  ·
                    rfl

theorem cell22_2731069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_2731069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731069 prefixEnd_2731069 := by exact prefixLift 2731069
  have htrace : WordTrace (prefixWord ++ tailWord_2731069) baseStart_2731069 baseEnd_2731069 := by
    simpa [prefixWord, tailWord_2731069, baseEnd_2731069] using wordTrace_append hprefix tailTrace_2731069
  have hstable : (prefixWord ++ tailWord_2731069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731069).length < 2 ^ (prefixWord ++ tailWord_2731069).sum := by decide
  have hdescent : baseEnd_2731069 < baseStart_2731069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731129 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_2731129 : Nat := 118140960795 + 2731129 * 2 ^ 59
def prefixEnd_2731129 : Nat := 4983230072969 + 3 ^ 40 * 2731129 * 2
def baseEnd_2731129 : Nat := 934921270955566785951515

theorem tailTrace_2731129 : CollatzResearch.WordTrace tailWord_2731129 prefixEnd_2731129 934921270955566785951515 := by
  unfold tailWord_2731129
  simp only [CollatzResearch.WordTrace]
  refine ⟨99612458122593547543148441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66408305415062365028765627 99612458122593547543148441)
  ·
    refine ⟨74709343591945160657361331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99612458122593547543148441 74709343591945160657361331)
    ·
      refine ⟨112064015387917740986041997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74709343591945160657361331 112064015387917740986041997)
      ·
        refine ⟨42024005770469152869765749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112064015387917740986041997 42024005770469152869765749)
        ·
          refine ⟨3939750540981483081540539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42024005770469152869765749 3939750540981483081540539)
          ·
            refine ⟨5909625811472224622310809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939750540981483081540539 5909625811472224622310809)
            ·
              refine ⟨4432219358604168466733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909625811472224622310809 4432219358604168466733107)
              ·
                refine ⟨6648329037906252700099661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432219358604168466733107 6648329037906252700099661)
                ·
                  refine ⟨2493123389214844762537373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6648329037906252700099661 2493123389214844762537373)
                  ·
                    refine ⟨934921270955566785951515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493123389214844762537373 934921270955566785951515)
                    ·
                      rfl

theorem cell22_2731129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_2731129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731129 prefixEnd_2731129 := by exact prefixLift 2731129
  have htrace : WordTrace (prefixWord ++ tailWord_2731129) baseStart_2731129 baseEnd_2731129 := by
    simpa [prefixWord, tailWord_2731129, baseEnd_2731129] using wordTrace_append hprefix tailTrace_2731129
  have hstable : (prefixWord ++ tailWord_2731129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731129).length < 2 ^ (prefixWord ++ tailWord_2731129).sum := by decide
  have hdescent : baseEnd_2731129 < baseStart_2731129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731155 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_2731155 : Nat := 118140960795 + 2731155 * 2 ^ 59
def prefixEnd_2731155 : Nat := 4983230072969 + 3 ^ 40 * 2731155 * 2
def baseEnd_2731155 : Nat := 934930171286911384801435

theorem tailTrace_2731155 : CollatzResearch.WordTrace tailWord_2731155 prefixEnd_2731155 934930171286911384801435 := by
  unfold tailWord_2731155
  simp only [CollatzResearch.WordTrace]
  refine ⟨99613406420499353983594919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66408937613666235989063279 99613406420499353983594919)
  ·
    refine ⟨149420109630749030975392379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99613406420499353983594919 149420109630749030975392379)
    ·
      refine ⟨224130164446123546463088569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149420109630749030975392379 224130164446123546463088569)
      ·
        refine ⟨168097623334592659847316427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224130164446123546463088569 168097623334592659847316427)
        ·
          refine ⟨252146435001888989770974641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168097623334592659847316427 252146435001888989770974641)
          ·
            refine ⟨189109826251416742328230981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252146435001888989770974641 189109826251416742328230981)
            ·
              refine ⟨35458092422140639186543309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189109826251416742328230981 35458092422140639186543309)
              ·
                refine ⟨13296784658302739694953741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35458092422140639186543309 13296784658302739694953741)
                ·
                  refine ⟨4986294246863527385607653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13296784658302739694953741 4986294246863527385607653)
                  ·
                    refine ⟨934930171286911384801435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986294246863527385607653 934930171286911384801435)
                    ·
                      rfl

theorem cell22_2731155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_2731155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731155 prefixEnd_2731155 := by exact prefixLift 2731155
  have htrace : WordTrace (prefixWord ++ tailWord_2731155) baseStart_2731155 baseEnd_2731155 := by
    simpa [prefixWord, tailWord_2731155, baseEnd_2731155] using wordTrace_append hprefix tailTrace_2731155
  have hstable : (prefixWord ++ tailWord_2731155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731155).length < 2 ^ (prefixWord ++ tailWord_2731155).sum := by decide
  have hdescent : baseEnd_2731155 < baseStart_2731155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731187 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 4]
def baseStart_2731187 : Nat := 118140960795 + 2731187 * 2 ^ 59
def prefixEnd_2731187 : Nat := 4983230072969 + 3 ^ 40 * 2731187 * 2
def baseEnd_2731187 : Nat := 311647041846957989333779

theorem tailTrace_2731187 : CollatzResearch.WordTrace tailWord_2731187 prefixEnd_2731187 311647041846957989333779 := by
  unfold tailWord_2731187
  simp only [CollatzResearch.WordTrace]
  refine ⟨99614573556383423448759815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66409715704255615632506543 99614573556383423448759815)
  ·
    refine ⟨149421860334575135173139723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99614573556383423448759815 149421860334575135173139723)
    ·
      refine ⟨224132790501862702759709585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149421860334575135173139723 224132790501862702759709585)
      ·
        refine ⟨168099592876397027069782189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224132790501862702759709585 168099592876397027069782189)
        ·
          refine ⟨63037347328648885151168321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168099592876397027069782189 63037347328648885151168321)
          ·
            refine ⟨47278010496486663863376241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63037347328648885151168321 47278010496486663863376241)
            ·
              refine ⟨35458507872364997897532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47278010496486663863376241 35458507872364997897532181)
              ·
                refine ⟨1662117556517109276446821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35458507872364997897532181 1662117556517109276446821)
                ·
                  refine ⟨311647041846957989333779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662117556517109276446821 311647041846957989333779)
                  ·
                    rfl

theorem cell22_2731187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 4].length) (baseStart_2731187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731187 prefixEnd_2731187 := by exact prefixLift 2731187
  have htrace : WordTrace (prefixWord ++ tailWord_2731187) baseStart_2731187 baseEnd_2731187 := by
    simpa [prefixWord, tailWord_2731187, baseEnd_2731187] using wordTrace_append hprefix tailTrace_2731187
  have hstable : (prefixWord ++ tailWord_2731187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731187).length < 2 ^ (prefixWord ++ tailWord_2731187).sum := by decide
  have hdescent : baseEnd_2731187 < baseStart_2731187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731266 : List Nat := [3, 4, 1, 1, 3, 1, 3, 6]
def baseStart_2731266 : Nat := 118140960795 + 2731266 * 2 ^ 59
def prefixEnd_2731266 : Nat := 4983230072969 + 3 ^ 40 * 2731266 * 2
def baseEnd_2731266 : Nat := 103885352095038232808455

theorem tailTrace_2731266 : CollatzResearch.WordTrace tailWord_2731266 prefixEnd_2731266 103885352095038232808455 := by
  unfold tailWord_2731266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904363730774304985221413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66411636615398146627257101 24904363730774304985221413)
  ·
    refine ⟨4669568199520182184729015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24904363730774304985221413 4669568199520182184729015)
    ·
      refine ⟨7004352299280273277093523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669568199520182184729015 7004352299280273277093523)
      ·
        refine ⟨10506528448920409915640285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004352299280273277093523 10506528448920409915640285)
        ·
          refine ⟨3939948168345153718365107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10506528448920409915640285 3939948168345153718365107)
          ·
            refine ⟨5909922252517730577547661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939948168345153718365107 5909922252517730577547661)
            ·
              refine ⟨2216220844694148966580373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5909922252517730577547661 2216220844694148966580373)
              ·
                refine ⟨103885352095038232808455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2216220844694148966580373 103885352095038232808455)
                ·
                  rfl

theorem cell22_2731266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_2731266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731266 prefixEnd_2731266 := by exact prefixLift 2731266
  have htrace : WordTrace (prefixWord ++ tailWord_2731266) baseStart_2731266 baseEnd_2731266 := by
    simpa [prefixWord, tailWord_2731266, baseEnd_2731266] using wordTrace_append hprefix tailTrace_2731266
  have hstable : (prefixWord ++ tailWord_2731266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731266).length < 2 ^ (prefixWord ++ tailWord_2731266).sum := by decide
  have hdescent : baseEnd_2731266 < baseStart_2731266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731281 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2731281 : Nat := 118140960795 + 2731281 * 2 ^ 59
def prefixEnd_2731281 : Nat := 4983230072969 + 3 ^ 40 * 2731281 * 2
def baseEnd_2731281 : Nat := 934973303661889056151049

theorem tailTrace_2731281 : CollatzResearch.WordTrace tailWord_2731281 prefixEnd_2731281 934973303661889056151049 := by
  unfold tailWord_2731281
  simp only [CollatzResearch.WordTrace]
  refine ⟨99618002018042877502681697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66412001345361918335121131 99618002018042877502681697)
  ·
    refine ⟨74713501513532158127011273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99618002018042877502681697 74713501513532158127011273)
    ·
      refine ⟨56035126135149118595258455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74713501513532158127011273 56035126135149118595258455)
      ·
        refine ⟨84052689202723677892887683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56035126135149118595258455 84052689202723677892887683)
        ·
          refine ⟨126079033804085516839331525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84052689202723677892887683 126079033804085516839331525)
          ·
            refine ⟨23639818838266034407374661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126079033804085516839331525 23639818838266034407374661)
            ·
              refine ⟨4432466032174881451382749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23639818838266034407374661 4432466032174881451382749)
              ·
                refine ⟨1662174762065580544268531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4432466032174881451382749 1662174762065580544268531)
                ·
                  refine ⟨2493262143098370816402797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662174762065580544268531 2493262143098370816402797)
                  ·
                    refine ⟨934973303661889056151049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493262143098370816402797 934973303661889056151049)
                    ·
                      rfl

theorem cell22_2731281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2731281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731281 prefixEnd_2731281 := by exact prefixLift 2731281
  have htrace : WordTrace (prefixWord ++ tailWord_2731281) baseStart_2731281 baseEnd_2731281 := by
    simpa [prefixWord, tailWord_2731281, baseEnd_2731281] using wordTrace_append hprefix tailTrace_2731281
  have hstable : (prefixWord ++ tailWord_2731281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731281).length < 2 ^ (prefixWord ++ tailWord_2731281).sum := by decide
  have hdescent : baseEnd_2731281 < baseStart_2731281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731292 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2731292 : Nat := 118140960795 + 2731292 * 2 ^ 59
def prefixEnd_2731292 : Nat := 4983230072969 + 3 ^ 40 * 2731292 * 2
def baseEnd_2731292 : Nat := 934977069186688694126015

theorem tailTrace_2731292 : CollatzResearch.WordTrace tailWord_2731292 prefixEnd_2731292 934977069186688694126015 := by
  unfold tailWord_2731292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809201610501513190666065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66412268814002017587554753 49809201610501513190666065)
  ·
    refine ⟨37356901207876134892999549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49809201610501513190666065 37356901207876134892999549)
    ·
      refine ⟨14008837952953550584874831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37356901207876134892999549 14008837952953550584874831)
      ·
        refine ⟨21013256929430325877312247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14008837952953550584874831 21013256929430325877312247)
        ·
          refine ⟨31519885394145488815968371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013256929430325877312247 31519885394145488815968371)
          ·
            refine ⟨47279828091218233223952557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31519885394145488815968371 47279828091218233223952557)
            ·
              refine ⟨17729935534206837458982209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47279828091218233223952557 17729935534206837458982209)
              ·
                refine ⟨13297451650655128094236657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17729935534206837458982209 13297451650655128094236657)
                ·
                  refine ⟨9973088737991346070677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13297451650655128094236657 9973088737991346070677493)
                  ·
                    refine ⟨934977069186688694126015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9973088737991346070677493 934977069186688694126015)
                    ·
                      rfl

theorem cell22_2731292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2731292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731292 prefixEnd_2731292 := by exact prefixLift 2731292
  have htrace : WordTrace (prefixWord ++ tailWord_2731292) baseStart_2731292 baseEnd_2731292 := by
    simpa [prefixWord, tailWord_2731292, baseEnd_2731292] using wordTrace_append hprefix tailTrace_2731292
  have hstable : (prefixWord ++ tailWord_2731292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731292).length < 2 ^ (prefixWord ++ tailWord_2731292).sum := by decide
  have hdescent : baseEnd_2731292 < baseStart_2731292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731322 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_2731322 : Nat := 118140960795 + 2731322 * 2 ^ 59
def prefixEnd_2731322 : Nat := 4983230072969 + 3 ^ 40 * 2731322 * 2
def baseEnd_2731322 : Nat := 311662446266592871958641

theorem tailTrace_2731322 : CollatzResearch.WordTrace tailWord_2731322 prefixEnd_2731322 311662446266592871958641 := by
  unfold tailWord_2731322
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904874352723585376231055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66412998273929561003282813 24904874352723585376231055)
  ·
    refine ⟨37357311529085378064346583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24904874352723585376231055 37357311529085378064346583)
    ·
      refine ⟨56035967293628067096519875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37357311529085378064346583 56035967293628067096519875)
      ·
        refine ⟨84053950940442100644779813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56035967293628067096519875 84053950940442100644779813)
        ·
          refine ⟨15760115801332893870896215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84053950940442100644779813 15760115801332893870896215)
          ·
            refine ⟨23640173701999340806344323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15760115801332893870896215 23640173701999340806344323)
            ·
              refine ⟨35460260552999011209516485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23640173701999340806344323 35460260552999011209516485)
              ·
                refine ⟨6648798853687314601784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35460260552999011209516485 6648798853687314601784341)
                ·
                  refine ⟨311662446266592871958641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6648798853687314601784341 311662446266592871958641)
                  ·
                    rfl

theorem cell22_2731322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_2731322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731322 prefixEnd_2731322 := by exact prefixLift 2731322
  have htrace : WordTrace (prefixWord ++ tailWord_2731322) baseStart_2731322 baseEnd_2731322 := by
    simpa [prefixWord, tailWord_2731322, baseEnd_2731322] using wordTrace_append hprefix tailTrace_2731322
  have hstable : (prefixWord ++ tailWord_2731322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731322).length < 2 ^ (prefixWord ++ tailWord_2731322).sum := by decide
  have hdescent : baseEnd_2731322 < baseStart_2731322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731324 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_2731324 : Nat := 118140960795 + 2731324 * 2 ^ 59
def prefixEnd_2731324 : Nat := 4983230072969 + 3 ^ 40 * 2731324 * 2
def baseEnd_2731324 : Nat := 934988023440651277325917

theorem tailTrace_2731324 : CollatzResearch.WordTrace tailWord_2731324 prefixEnd_2731324 934988023440651277325917 := by
  unfold tailWord_2731324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809785178443547923248513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66413046904591397230998017 49809785178443547923248513)
  ·
    refine ⟨37357338883832660942436385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49809785178443547923248513 37357338883832660942436385)
    ·
      refine ⟨28018004162874495706827289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37357338883832660942436385 28018004162874495706827289)
      ·
        refine ⟨21013503122155871780120467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28018004162874495706827289 21013503122155871780120467)
        ·
          refine ⟨31520254683233807670180701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013503122155871780120467 31520254683233807670180701)
          ·
            refine ⟨11820095506212677876317763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31520254683233807670180701 11820095506212677876317763)
            ·
              refine ⟨17730143259319016814476645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11820095506212677876317763 17730143259319016814476645)
              ·
                refine ⟨3324401861122315652714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17730143259319016814476645 3324401861122315652714371)
                ·
                  refine ⟨4986602791683473479071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324401861122315652714371 4986602791683473479071557)
                  ·
                    refine ⟨934988023440651277325917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986602791683473479071557 934988023440651277325917)
                    ·
                      rfl

theorem cell22_2731324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_2731324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731324 prefixEnd_2731324 := by exact prefixLift 2731324
  have htrace : WordTrace (prefixWord ++ tailWord_2731324) baseStart_2731324 baseEnd_2731324 := by
    simpa [prefixWord, tailWord_2731324, baseEnd_2731324] using wordTrace_append hprefix tailTrace_2731324
  have hstable : (prefixWord ++ tailWord_2731324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731324).length < 2 ^ (prefixWord ++ tailWord_2731324).sum := by decide
  have hdescent : baseEnd_2731324 < baseStart_2731324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731337 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_2731337 : Nat := 118140960795 + 2731337 * 2 ^ 59
def prefixEnd_2731337 : Nat := 4983230072969 + 3 ^ 40 * 2731337 * 2
def baseEnd_2731337 : Nat := 934992473606323576750877

theorem tailTrace_2731337 : CollatzResearch.WordTrace tailWord_2731337 prefixEnd_2731337 934992473606323576750877 := by
  unfold tailWord_2731337
  simp only [CollatzResearch.WordTrace]
  refine ⟨99620044505839999066720265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66413363003893332711146843 99620044505839999066720265)
  ·
    refine ⟨74715033379379999300040199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99620044505839999066720265 74715033379379999300040199)
    ·
      refine ⟨112072550069069998950060299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74715033379379999300040199 112072550069069998950060299)
      ·
        refine ⟨168108825103604998425090449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112072550069069998950060299 168108825103604998425090449)
        ·
          refine ⟨126081618827703748818817837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168108825103604998425090449 126081618827703748818817837)
          ·
            refine ⟨47280607060388905807056689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126081618827703748818817837 47280607060388905807056689)
            ·
              refine ⟨35460455295291679355292517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47280607060388905807056689 35460455295291679355292517)
              ·
                refine ⟨6648835367867189879117347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35460455295291679355292517 6648835367867189879117347)
                ·
                  refine ⟨9973253051800784818676021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648835367867189879117347 9973253051800784818676021)
                  ·
                    refine ⟨934992473606323576750877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9973253051800784818676021 934992473606323576750877)
                    ·
                      rfl

theorem cell22_2731337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_2731337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731337 prefixEnd_2731337 := by exact prefixLift 2731337
  have htrace : WordTrace (prefixWord ++ tailWord_2731337) baseStart_2731337 baseEnd_2731337 := by
    simpa [prefixWord, tailWord_2731337, baseEnd_2731337] using wordTrace_append hprefix tailTrace_2731337
  have hstable : (prefixWord ++ tailWord_2731337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731337).length < 2 ^ (prefixWord ++ tailWord_2731337).sum := by decide
  have hdescent : baseEnd_2731337 < baseStart_2731337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731354 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_2731354 : Nat := 118140960795 + 2731354 * 2 ^ 59
def prefixEnd_2731354 : Nat := 4983230072969 + 3 ^ 40 * 2731354 * 2
def baseEnd_2731354 : Nat := 934998293053741199075825

theorem tailTrace_2731354 : CollatzResearch.WordTrace tailWord_2731354 prefixEnd_2731354 934998293053741199075825 := by
  unfold tailWord_2731354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905166136694602742522279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66413776364518940646726077 24905166136694602742522279)
  ·
    refine ⟨37357749205041904113783419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24905166136694602742522279 37357749205041904113783419)
    ·
      refine ⟨56036623807562856170675129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37357749205041904113783419 56036623807562856170675129)
      ·
        refine ⟨42027467855672142128006347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56036623807562856170675129 42027467855672142128006347)
        ·
          refine ⟨63041201783508213192009521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42027467855672142128006347 63041201783508213192009521)
          ·
            refine ⟨47280901337631159894007141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63041201783508213192009521 47280901337631159894007141)
            ·
              refine ⟨8865169000805842480126339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47280901337631159894007141 8865169000805842480126339)
              ·
                refine ⟨13297753501208763720189509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865169000805842480126339 13297753501208763720189509)
                ·
                  refine ⟨2493328781476643197535533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13297753501208763720189509 2493328781476643197535533)
                  ·
                    refine ⟨934998293053741199075825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493328781476643197535533 934998293053741199075825)
                    ·
                      rfl

theorem cell22_2731354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_2731354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731354 prefixEnd_2731354 := by exact prefixLift 2731354
  have htrace : WordTrace (prefixWord ++ tailWord_2731354) baseStart_2731354 baseEnd_2731354 := by
    simpa [prefixWord, tailWord_2731354, baseEnd_2731354] using wordTrace_append hprefix tailTrace_2731354
  have hstable : (prefixWord ++ tailWord_2731354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731354).length < 2 ^ (prefixWord ++ tailWord_2731354).sum := by decide
  have hdescent : baseEnd_2731354 < baseStart_2731354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731493 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2731493 : Nat := 118140960795 + 2731493 * 2 ^ 59
def prefixEnd_2731493 : Nat := 4983230072969 + 3 ^ 40 * 2731493 * 2
def baseEnd_2731493 : Nat := 935045875594391169850399

theorem tailTrace_2731493 : CollatzResearch.WordTrace tailWord_2731493 prefixEnd_2731493 935045875594391169850399 := by
  unfold tailWord_2731493
  simp only [CollatzResearch.WordTrace]
  refine ⟨99625734293274837709399133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66417156195516558472932755 99625734293274837709399133)
  ·
    refine ⟨37359650359978064141024675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99625734293274837709399133 37359650359978064141024675)
    ·
      refine ⟨56039475539967096211537013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37359650359978064141024675 56039475539967096211537013)
      ·
        refine ⟨5253700831871915269831595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56039475539967096211537013 5253700831871915269831595)
        ·
          refine ⟨7880551247807872904747393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253700831871915269831595 7880551247807872904747393)
          ·
            refine ⟨5910413435855904678560545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880551247807872904747393 5910413435855904678560545)
            ·
              refine ⟨4432810076891928508920409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910413435855904678560545 4432810076891928508920409)
              ·
                refine ⟨3324607557668946381690307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432810076891928508920409 3324607557668946381690307)
                ·
                  refine ⟨4986911336503419572535461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324607557668946381690307 4986911336503419572535461)
                  ·
                    refine ⟨935045875594391169850399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986911336503419572535461 935045875594391169850399)
                    ·
                      rfl

theorem cell22_2731493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2731493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731493 prefixEnd_2731493 := by exact prefixLift 2731493
  have htrace : WordTrace (prefixWord ++ tailWord_2731493) baseStart_2731493 baseEnd_2731493 := by
    simpa [prefixWord, tailWord_2731493, baseEnd_2731493] using wordTrace_append hprefix tailTrace_2731493
  have hstable : (prefixWord ++ tailWord_2731493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731493).length < 2 ^ (prefixWord ++ tailWord_2731493).sum := by decide
  have hdescent : baseEnd_2731493 < baseStart_2731493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731504 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_2731504 : Nat := 118140960795 + 2731504 * 2 ^ 59
def prefixEnd_2731504 : Nat := 4983230072969 + 3 ^ 40 * 2731504 * 2
def baseEnd_2731504 : Nat := 935049641119190807825365

theorem tailTrace_2731504 : CollatzResearch.WordTrace tailWord_2731504 prefixEnd_2731504 935049641119190807825365 := by
  unfold tailWord_2731504
  simp only [CollatzResearch.WordTrace]
  refine ⟨49813067748117493294024783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66417423664156657725366377 49813067748117493294024783)
  ·
    refine ⟨74719601622176239941037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49813067748117493294024783 74719601622176239941037175)
    ·
      refine ⟨112079402433264359911555763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74719601622176239941037175 112079402433264359911555763)
      ·
        refine ⟨168119103649896539867333645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112079402433264359911555763 168119103649896539867333645)
        ·
          refine ⟨63044663868711202450250117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168119103649896539867333645 63044663868711202450250117)
          ·
            refine ⟨11820874475383350459421897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63044663868711202450250117 11820874475383350459421897)
            ·
              refine ⟨8865655856537512844566423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11820874475383350459421897 8865655856537512844566423)
              ·
                refine ⟨13298483784806269266849635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865655856537512844566423 13298483784806269266849635)
                ·
                  refine ⟨19947725677209403900274453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13298483784806269266849635 19947725677209403900274453)
                  ·
                    refine ⟨935049641119190807825365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19947725677209403900274453 935049641119190807825365)
                    ·
                      rfl

theorem cell22_2731504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_2731504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731504 prefixEnd_2731504 := by exact prefixLift 2731504
  have htrace : WordTrace (prefixWord ++ tailWord_2731504) baseStart_2731504 baseEnd_2731504 := by
    simpa [prefixWord, tailWord_2731504, baseEnd_2731504] using wordTrace_append hprefix tailTrace_2731504
  have hstable : (prefixWord ++ tailWord_2731504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731504).length < 2 ^ (prefixWord ++ tailWord_2731504).sum := by decide
  have hdescent : baseEnd_2731504 < baseStart_2731504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731551 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 3, 3]
def baseStart_2731551 : Nat := 118140960795 + 2731551 * 2 ^ 59
def prefixEnd_2731551 : Nat := 4983230072969 + 3 ^ 40 * 2731551 * 2
def baseEnd_2731551 : Nat := 935065730179698351900221

theorem tailTrace_2731551 : CollatzResearch.WordTrace tailWord_2731551 prefixEnd_2731551 935065730179698351900221 := by
  unfold tailWord_2731551
  simp only [CollatzResearch.WordTrace]
  refine ⟨99627849727064713615010507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66418566484709809076673671 99627849727064713615010507)
  ·
    refine ⟨149441774590597070422515761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99627849727064713615010507 149441774590597070422515761)
    ·
      refine ⟨112081330942947802816886821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149441774590597070422515761 112081330942947802816886821)
      ·
        refine ⟨21015249551802713028166279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112081330942947802816886821 21015249551802713028166279)
        ·
          refine ⟨31522874327704069542249419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21015249551802713028166279 31522874327704069542249419)
          ·
            refine ⟨47284311491556104313374129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31522874327704069542249419 47284311491556104313374129)
            ·
              refine ⟨35463233618667078235030597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47284311491556104313374129 35463233618667078235030597)
              ·
                refine ⟨6649356303500077169068237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35463233618667078235030597 6649356303500077169068237)
                ·
                  refine ⟨2493508613812528938400589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6649356303500077169068237 2493508613812528938400589)
                  ·
                    refine ⟨935065730179698351900221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493508613812528938400589 935065730179698351900221)
                    ·
                      rfl

theorem cell22_2731551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_2731551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731551 prefixEnd_2731551 := by exact prefixLift 2731551
  have htrace : WordTrace (prefixWord ++ tailWord_2731551) baseStart_2731551 baseEnd_2731551 := by
    simpa [prefixWord, tailWord_2731551, baseEnd_2731551] using wordTrace_append hprefix tailTrace_2731551
  have hstable : (prefixWord ++ tailWord_2731551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731551).length < 2 ^ (prefixWord ++ tailWord_2731551).sum := by decide
  have hdescent : baseEnd_2731551 < baseStart_2731551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731568 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_2731568 : Nat := 118140960795 + 2731568 * 2 ^ 59
def prefixEnd_2731568 : Nat := 4983230072969 + 3 ^ 40 * 2731568 * 2
def baseEnd_2731568 : Nat := 935071549627115974225169

theorem tailTrace_2731568 : CollatzResearch.WordTrace tailWord_2731568 prefixEnd_2731568 935071549627115974225169 := by
  unfold tailWord_2731568
  simp only [CollatzResearch.WordTrace]
  refine ⟨49814234884001562759189679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66418979845335417012252905 49814234884001562759189679)
  ·
    refine ⟨74721352326002344138784519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49814234884001562759189679 74721352326002344138784519)
    ·
      refine ⟨112082028489003516208176779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74721352326002344138784519 112082028489003516208176779)
      ·
        refine ⟨168123042733505274312265169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112082028489003516208176779 168123042733505274312265169)
        ·
          refine ⟨126092282050128955734198877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168123042733505274312265169 126092282050128955734198877)
          ·
            refine ⟨47284605768798358400324579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126092282050128955734198877 47284605768798358400324579)
            ·
              refine ⟨70926908653197537600486869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47284605768798358400324579 70926908653197537600486869)
              ·
                refine ⟨1662349421559317287511411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70926908653197537600486869 1662349421559317287511411)
                ·
                  refine ⟨2493524132338975931267117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662349421559317287511411 2493524132338975931267117)
                  ·
                    refine ⟨935071549627115974225169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493524132338975931267117 935071549627115974225169)
                    ·
                      rfl

theorem cell22_2731568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_2731568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731568 prefixEnd_2731568 := by exact prefixLift 2731568
  have htrace : WordTrace (prefixWord ++ tailWord_2731568) baseStart_2731568 baseEnd_2731568 := by
    simpa [prefixWord, tailWord_2731568, baseEnd_2731568] using wordTrace_append hprefix tailTrace_2731568
  have hstable : (prefixWord ++ tailWord_2731568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731568).length < 2 ^ (prefixWord ++ tailWord_2731568).sum := by decide
  have hdescent : baseEnd_2731568 < baseStart_2731568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731585 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2731585 : Nat := 118140960795 + 2731585 * 2 ^ 59
def prefixEnd_2731585 : Nat := 4983230072969 + 3 ^ 40 * 2731585 * 2
def baseEnd_2731585 : Nat := 935077369074533596550117

theorem tailTrace_2731585 : CollatzResearch.WordTrace tailWord_2731585 prefixEnd_2731585 935077369074533596550117 := by
  unfold tailWord_2731585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99629089808941537421748209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66419393205961024947832139 99629089808941537421748209)
  ·
    refine ⟨74721817356706153066311157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99629089808941537421748209 74721817356706153066311157)
    ·
      refine ⟨7005170377191201849966671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74721817356706153066311157 7005170377191201849966671)
      ·
        refine ⟨10507755565786802774950007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005170377191201849966671 10507755565786802774950007)
        ·
          refine ⟨15761633348680204162425011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10507755565786802774950007 15761633348680204162425011)
          ·
            refine ⟨23642450023020306243637517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15761633348680204162425011 23642450023020306243637517)
            ·
              refine ⟨8865918758632614841364069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23642450023020306243637517 8865918758632614841364069)
              ·
                refine ⟨1662359767243615282755763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8865918758632614841364069 1662359767243615282755763)
                ·
                  refine ⟨2493539650865422924133645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662359767243615282755763 2493539650865422924133645)
                  ·
                    refine ⟨935077369074533596550117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493539650865422924133645 935077369074533596550117)
                    ·
                      rfl

theorem cell22_2731585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2731585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731585 prefixEnd_2731585 := by exact prefixLift 2731585
  have htrace : WordTrace (prefixWord ++ tailWord_2731585) baseStart_2731585 baseEnd_2731585 := by
    simpa [prefixWord, tailWord_2731585, baseEnd_2731585] using wordTrace_append hprefix tailTrace_2731585
  have hstable : (prefixWord ++ tailWord_2731585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731585).length < 2 ^ (prefixWord ++ tailWord_2731585).sum := by decide
  have hdescent : baseEnd_2731585 < baseStart_2731585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731596 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_2731596 : Nat := 118140960795 + 2731596 * 2 ^ 59
def prefixEnd_2731596 : Nat := 4983230072969 + 3 ^ 40 * 2731596 * 2
def baseEnd_2731596 : Nat := 935081134599333234525083

theorem tailTrace_2731596 : CollatzResearch.WordTrace tailWord_2731596 prefixEnd_2731596 935081134599333234525083 := by
  unfold tailWord_2731596
  simp only [CollatzResearch.WordTrace]
  refine ⟨49814745505950843150199321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66419660674601124200265761 49814745505950843150199321)
  ·
    refine ⟨37361059129463132362649491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49814745505950843150199321 37361059129463132362649491)
    ·
      refine ⟨56041588694194698543974237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37361059129463132362649491 56041588694194698543974237)
      ·
        refine ⟨21015595760323011953990339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56041588694194698543974237 21015595760323011953990339)
        ·
          refine ⟨31523393640484517930985509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21015595760323011953990339 31523393640484517930985509)
          ·
            refine ⟨5910636307590847112059783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31523393640484517930985509 5910636307590847112059783)
            ·
              refine ⟨8865954461386270668089675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910636307590847112059783 8865954461386270668089675)
              ·
                refine ⟨13298931692079406002134513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865954461386270668089675 13298931692079406002134513)
                ·
                  refine ⟨9974198769059554501600885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13298931692079406002134513 9974198769059554501600885)
                  ·
                    refine ⟨935081134599333234525083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9974198769059554501600885 935081134599333234525083)
                    ·
                      rfl

theorem cell22_2731596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_2731596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731596 prefixEnd_2731596 := by exact prefixLift 2731596
  have htrace : WordTrace (prefixWord ++ tailWord_2731596) baseStart_2731596 baseEnd_2731596 := by
    simpa [prefixWord, tailWord_2731596, baseEnd_2731596] using wordTrace_append hprefix tailTrace_2731596
  have hstable : (prefixWord ++ tailWord_2731596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731596).length < 2 ^ (prefixWord ++ tailWord_2731596).sum := by decide
  have hdescent : baseEnd_2731596 < baseStart_2731596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731658 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_2731658 : Nat := 118140960795 + 2731658 * 2 ^ 59
def prefixEnd_2731658 : Nat := 4983230072969 + 3 ^ 40 * 2731658 * 2
def baseEnd_2731658 : Nat := 935102358466385739474893

theorem tailTrace_2731658 : CollatzResearch.WordTrace tailWord_2731658 prefixEnd_2731658 935102358466385739474893 := by
  unfold tailWord_2731658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24907938084419267722288907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66421168225118047259437085 24907938084419267722288907)
  ·
    refine ⟨37361907126628901583433361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24907938084419267722288907 37361907126628901583433361)
    ·
      refine ⟨28021430344971676187575021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37361907126628901583433361 28021430344971676187575021)
      ·
        refine ⟨10508036379364378570340633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28021430344971676187575021 10508036379364378570340633)
        ·
          refine ⟨7881027284523283927755475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10508036379364378570340633 7881027284523283927755475)
          ·
            refine ⟨11821540926784925891633213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7881027284523283927755475 11821540926784925891633213)
            ·
              refine ⟨4433077847544347209362455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11821540926784925891633213 4433077847544347209362455)
              ·
                refine ⟨6649616771316520814043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433077847544347209362455 6649616771316520814043683)
                ·
                  refine ⟨9974425156974781221065525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6649616771316520814043683 9974425156974781221065525)
                  ·
                    refine ⟨935102358466385739474893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9974425156974781221065525 935102358466385739474893)
                    ·
                      rfl

theorem cell22_2731658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_2731658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731658 prefixEnd_2731658 := by exact prefixLift 2731658
  have htrace : WordTrace (prefixWord ++ tailWord_2731658) baseStart_2731658 baseEnd_2731658 := by
    simpa [prefixWord, tailWord_2731658, baseEnd_2731658] using wordTrace_append hprefix tailTrace_2731658
  have hstable : (prefixWord ++ tailWord_2731658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731658).length < 2 ^ (prefixWord ++ tailWord_2731658).sum := by decide
  have hdescent : baseEnd_2731658 < baseStart_2731658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731671 : List Nat := [1, 1, 3, 3, 2, 3, 1, 8]
def baseStart_2731671 : Nat := 118140960795 + 2731671 * 2 ^ 59
def prefixEnd_2731671 : Nat := 4983230072969 + 3 ^ 40 * 2731671 * 2
def baseEnd_2731671 : Nat := 103900756514673115433317

theorem tailTrace_2731671 : CollatzResearch.WordTrace tailWord_2731671 prefixEnd_2731671 103900756514673115433317 := by
  unfold tailWord_2731671
  simp only [CollatzResearch.WordTrace]
  refine ⟨99632226486629974109378867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66421484324419982739585911 99632226486629974109378867)
  ·
    refine ⟨149448339729944961164068301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99632226486629974109378867 149448339729944961164068301)
    ·
      refine ⟨56043127398729360436525613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149448339729944961164068301 56043127398729360436525613)
      ·
        refine ⟨21016172774523510163697105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56043127398729360436525613 21016172774523510163697105)
        ·
          refine ⟨15762129580892632622772829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21016172774523510163697105 15762129580892632622772829)
          ·
            refine ⟨5910798592834737233539811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15762129580892632622772829 5910798592834737233539811)
            ·
              refine ⟨8866197889252105850309717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910798592834737233539811 8866197889252105850309717)
              ·
                refine ⟨103900756514673115433317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8866197889252105850309717 103900756514673115433317)
                ·
                  rfl

theorem cell22_2731671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 8].length) (baseStart_2731671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731671 prefixEnd_2731671 := by exact prefixLift 2731671
  have htrace : WordTrace (prefixWord ++ tailWord_2731671) baseStart_2731671 baseEnd_2731671 := by
    simpa [prefixWord, tailWord_2731671, baseEnd_2731671] using wordTrace_append hprefix tailTrace_2731671
  have hstable : (prefixWord ++ tailWord_2731671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731671).length < 2 ^ (prefixWord ++ tailWord_2731671).sum := by decide
  have hdescent : baseEnd_2731671 < baseStart_2731671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731694 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_2731694 : Nat := 118140960795 + 2731694 * 2 ^ 59
def prefixEnd_2731694 : Nat := 4983230072969 + 3 ^ 40 * 2731694 * 2
def baseEnd_2731694 : Nat := 311704894000697881858261

theorem tailTrace_2731694 : CollatzResearch.WordTrace tailWord_2731694 prefixEnd_2731694 311704894000697881858261 := by
  unfold tailWord_2731694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454133170693331129683267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66422043577031099358310757 12454133170693331129683267)
  ·
    refine ⟨18681199756039996694524901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12454133170693331129683267 18681199756039996694524901)
    ·
      refine ⟨3502724954257499380223419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18681199756039996694524901 3502724954257499380223419)
      ·
        refine ⟨5254087431386249070335129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502724954257499380223419 5254087431386249070335129)
        ·
          refine ⟨3940565573539686802751347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5254087431386249070335129 3940565573539686802751347)
          ·
            refine ⟨5910848360309530204127021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940565573539686802751347 5910848360309530204127021)
            ·
              refine ⟨2216568135116073826547633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5910848360309530204127021 2216568135116073826547633)
              ·
                refine ⟨1662426101337055369910725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216568135116073826547633 1662426101337055369910725)
                ·
                  refine ⟨311704894000697881858261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662426101337055369910725 311704894000697881858261)
                  ·
                    rfl

theorem cell22_2731694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_2731694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731694 prefixEnd_2731694 := by exact prefixLift 2731694
  have htrace : WordTrace (prefixWord ++ tailWord_2731694) baseStart_2731694 baseEnd_2731694 := by
    simpa [prefixWord, tailWord_2731694, baseEnd_2731694] using wordTrace_append hprefix tailTrace_2731694
  have hstable : (prefixWord ++ tailWord_2731694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731694).length < 2 ^ (prefixWord ++ tailWord_2731694).sum := by decide
  have hdescent : baseEnd_2731694 < baseStart_2731694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731776 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_2731776 : Nat := 118140960795 + 2731776 * 2 ^ 59
def prefixEnd_2731776 : Nat := 4983230072969 + 3 ^ 40 * 2731776 * 2
def baseEnd_2731776 : Nat := 935142752277872765024531

theorem tailTrace_2731776 : CollatzResearch.WordTrace tailWord_2731776 prefixEnd_2731776 935142752277872765024531 := by
  unfold tailWord_2731776
  simp only [CollatzResearch.WordTrace]
  refine ⟨49818028075624788520975591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66424037434166384694634121 49818028075624788520975591)
  ·
    refine ⟨74727042113437182781463387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49818028075624788520975591 74727042113437182781463387)
    ·
      refine ⟨112090563170155774172195081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74727042113437182781463387 112090563170155774172195081)
      ·
        refine ⟨84067922377616830629146311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112090563170155774172195081 84067922377616830629146311)
        ·
          refine ⟨126101883566425245943719467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84067922377616830629146311 126101883566425245943719467)
          ·
            refine ⟨189152825349637868915579201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126101883566425245943719467 189152825349637868915579201)
            ·
              refine ⟨141864619012228401686684401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189152825349637868915579201 141864619012228401686684401)
              ·
                refine ⟨106398464259171301265013301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141864619012228401686684401 106398464259171301265013301)
                ·
                  refine ⟨9974856024297309493594997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106398464259171301265013301 9974856024297309493594997)
                  ·
                    refine ⟨935142752277872765024531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9974856024297309493594997 935142752277872765024531)
                    ·
                      rfl

theorem cell22_2731776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_2731776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731776 prefixEnd_2731776 := by exact prefixLift 2731776
  have htrace : WordTrace (prefixWord ++ tailWord_2731776) baseStart_2731776 baseEnd_2731776 := by
    simpa [prefixWord, tailWord_2731776, baseEnd_2731776] using wordTrace_append hprefix tailTrace_2731776
  have hstable : (prefixWord ++ tailWord_2731776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731776).length < 2 ^ (prefixWord ++ tailWord_2731776).sum := by decide
  have hdescent : baseEnd_2731776 < baseStart_2731776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731793 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_2731793 : Nat := 118140960795 + 2731793 * 2 ^ 59
def prefixEnd_2731793 : Nat := 4983230072969 + 3 ^ 40 * 2731793 * 2
def baseEnd_2731793 : Nat := 935148571725290387349479

theorem tailTrace_2731793 : CollatzResearch.WordTrace tailWord_2731793 prefixEnd_2731793 935148571725290387349479 := by
  unfold tailWord_2731793
  simp only [CollatzResearch.WordTrace]
  refine ⟨99636676192187988945320033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66424450794791992630213355 99636676192187988945320033)
  ·
    refine ⟨74727507144140991708990025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99636676192187988945320033 74727507144140991708990025)
    ·
      refine ⟨56045630358105743781742519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74727507144140991708990025 56045630358105743781742519)
      ·
        refine ⟨84068445537158615672613779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56045630358105743781742519 84068445537158615672613779)
        ·
          refine ⟨126102668305737923508920669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84068445537158615672613779 126102668305737923508920669)
          ·
            refine ⟨47288500614651721315845251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126102668305737923508920669 47288500614651721315845251)
            ·
              refine ⟨70932750921977581973767877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47288500614651721315845251 70932750921977581973767877)
              ·
                refine ⟨13299890797870796620081477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70932750921977581973767877 13299890797870796620081477)
                ·
                  refine ⟨2493729524600774366265277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13299890797870796620081477 2493729524600774366265277)
                  ·
                    refine ⟨935148571725290387349479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493729524600774366265277 935148571725290387349479)
                    ·
                      rfl

theorem cell22_2731793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_2731793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731793 prefixEnd_2731793 := by exact prefixLift 2731793
  have htrace : WordTrace (prefixWord ++ tailWord_2731793) baseStart_2731793 baseEnd_2731793 := by
    simpa [prefixWord, tailWord_2731793, baseEnd_2731793] using wordTrace_append hprefix tailTrace_2731793
  have hstable : (prefixWord ++ tailWord_2731793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731793).length < 2 ^ (prefixWord ++ tailWord_2731793).sum := by decide
  have hdescent : baseEnd_2731793 < baseStart_2731793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731797 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_2731797 : Nat := 118140960795 + 2731797 * 2 ^ 59
def prefixEnd_2731797 : Nat := 4983230072969 + 3 ^ 40 * 2731797 * 2
def baseEnd_2731797 : Nat := 935149941007035710249467

theorem tailTrace_2731797 : CollatzResearch.WordTrace tailWord_2731797 prefixEnd_2731797 935149941007035710249467 := by
  unfold tailWord_2731797
  simp only [CollatzResearch.WordTrace]
  refine ⟨99636822084173497628465645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66424548056115665085643763 99636822084173497628465645)
  ·
    refine ⟨37363808281565061610674617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99636822084173497628465645 37363808281565061610674617)
    ·
      refine ⟨28022856211173796208005963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37363808281565061610674617 28022856211173796208005963)
      ·
        refine ⟨42034284316760694312008945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28022856211173796208005963 42034284316760694312008945)
        ·
          refine ⟨31525713237570520734006709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42034284316760694312008945 31525713237570520734006709)
          ·
            refine ⟨2955535616022236318813129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31525713237570520734006709 2955535616022236318813129)
            ·
              refine ⟨2216651712016677239109847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955535616022236318813129 2216651712016677239109847)
              ·
                refine ⟨3324977568025015858664771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216651712016677239109847 3324977568025015858664771)
                ·
                  refine ⟨4987466352037523787997157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324977568025015858664771 4987466352037523787997157)
                  ·
                    refine ⟨935149941007035710249467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4987466352037523787997157 935149941007035710249467)
                    ·
                      rfl

theorem cell22_2731797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_2731797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731797 prefixEnd_2731797 := by exact prefixLift 2731797
  have htrace : WordTrace (prefixWord ++ tailWord_2731797) baseStart_2731797 baseEnd_2731797 := by
    simpa [prefixWord, tailWord_2731797, baseEnd_2731797] using wordTrace_append hprefix tailTrace_2731797
  have hstable : (prefixWord ++ tailWord_2731797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731797).length < 2 ^ (prefixWord ++ tailWord_2731797).sum := by decide
  have hdescent : baseEnd_2731797 < baseStart_2731797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731808 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_2731808 : Nat := 118140960795 + 2731808 * 2 ^ 59
def prefixEnd_2731808 : Nat := 4983230072969 + 3 ^ 40 * 2731808 * 2
def baseEnd_2731808 : Nat := 935153706531835348224433

theorem tailTrace_2731808 : CollatzResearch.WordTrace tailWord_2731808 prefixEnd_2731808 935153706531835348224433 := by
  unfold tailWord_2731808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49818611643566823253558039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66424815524755764338077385 49818611643566823253558039)
  ·
    refine ⟨74727917465350234880337059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49818611643566823253558039 74727917465350234880337059)
    ·
      refine ⟨112091876198025352320505589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74727917465350234880337059 112091876198025352320505589)
      ·
        refine ⟨10508613393564876780047399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112091876198025352320505589 10508613393564876780047399)
        ·
          refine ⟨15762920090347315170071099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10508613393564876780047399 15762920090347315170071099)
          ·
            refine ⟨23644380135520972755106649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15762920090347315170071099 23644380135520972755106649)
            ·
              refine ⟨17733285101640729566329987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23644380135520972755106649 17733285101640729566329987)
              ·
                refine ⟨26599927652461094349494981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17733285101640729566329987 26599927652461094349494981)
                ·
                  refine ⟨4987486434836455190530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26599927652461094349494981 4987486434836455190530309)
                  ·
                    refine ⟨935153706531835348224433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4987486434836455190530309 935153706531835348224433)
                    ·
                      rfl

theorem cell22_2731808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_2731808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731808 prefixEnd_2731808 := by exact prefixLift 2731808
  have htrace : WordTrace (prefixWord ++ tailWord_2731808) baseStart_2731808 baseEnd_2731808 := by
    simpa [prefixWord, tailWord_2731808, baseEnd_2731808] using wordTrace_append hprefix tailTrace_2731808
  have hstable : (prefixWord ++ tailWord_2731808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731808).length < 2 ^ (prefixWord ++ tailWord_2731808).sum := by decide
  have hdescent : baseEnd_2731808 < baseStart_2731808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731810 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2731810 : Nat := 118140960795 + 2731810 * 2 ^ 59
def prefixEnd_2731810 : Nat := 4983230072969 + 3 ^ 40 * 2731810 * 2
def baseEnd_2731810 : Nat := 935154391172708009674427

theorem tailTrace_2731810 : CollatzResearch.WordTrace tailWord_2731810 prefixEnd_2731810 935154391172708009674427 := by
  unfold tailWord_2731810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24909324058281600212172221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66424864155417600565792589 24909324058281600212172221)
  ·
    refine ⟨9340996521855600079564583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24909324058281600212172221 9340996521855600079564583)
    ·
      refine ⟨14011494782783400119346875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9340996521855600079564583 14011494782783400119346875)
      ·
        refine ⟨21017242174175100179020313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14011494782783400119346875 21017242174175100179020313)
        ·
          refine ⟨15762931630631325134265235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21017242174175100179020313 15762931630631325134265235)
          ·
            refine ⟨23644397445946987701397853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15762931630631325134265235 23644397445946987701397853)
            ·
              refine ⟨8866649042230120388024195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23644397445946987701397853 8866649042230120388024195)
              ·
                refine ⟨13299973563345180582036293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8866649042230120388024195 13299973563345180582036293)
                ·
                  refine ⟨2493745043127221359131805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13299973563345180582036293 2493745043127221359131805)
                  ·
                    refine ⟨935154391172708009674427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493745043127221359131805 935154391172708009674427)
                    ·
                      rfl

theorem cell22_2731810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2731810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731810 prefixEnd_2731810 := by exact prefixLift 2731810
  have htrace : WordTrace (prefixWord ++ tailWord_2731810) baseStart_2731810 baseEnd_2731810 := by
    simpa [prefixWord, tailWord_2731810, baseEnd_2731810] using wordTrace_append hprefix tailTrace_2731810
  have hstable : (prefixWord ++ tailWord_2731810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731810).length < 2 ^ (prefixWord ++ tailWord_2731810).sum := by decide
  have hdescent : baseEnd_2731810 < baseStart_2731810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731827 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 5]
def baseStart_2731827 : Nat := 118140960795 + 2731827 * 2 ^ 59
def prefixEnd_2731827 : Nat := 4983230072969 + 3 ^ 40 * 2731827 * 2
def baseEnd_2731827 : Nat := 935160210620125631999375

theorem tailTrace_2731827 : CollatzResearch.WordTrace tailWord_2731827 prefixEnd_2731827 935160210620125631999375 := by
  unfold tailWord_2731827
  simp only [CollatzResearch.WordTrace]
  refine ⟨99637916274064812752057735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66425277516043208501371823 99637916274064812752057735)
  ·
    refine ⟨149456874411097219128086603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99637916274064812752057735 149456874411097219128086603)
    ·
      refine ⟨224185311616645828692129905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149456874411097219128086603 224185311616645828692129905)
      ·
        refine ⟨168138983712484371519097429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224185311616645828692129905 168138983712484371519097429)
        ·
          refine ⟨1970378715380676228739423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 168138983712484371519097429 1970378715380676228739423)
          ·
            refine ⟨2955568073071014343109135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970378715380676228739423 2955568073071014343109135)
            ·
              refine ⟨4433352109606521514663703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955568073071014343109135 4433352109606521514663703)
              ·
                refine ⟨6650028164409782271995555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433352109606521514663703 6650028164409782271995555)
                ·
                  refine ⟨9975042246614673407993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650028164409782271995555 9975042246614673407993333)
                  ·
                    refine ⟨935160210620125631999375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9975042246614673407993333 935160210620125631999375)
                    ·
                      rfl

theorem cell22_2731827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 5].length) (baseStart_2731827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731827 prefixEnd_2731827 := by exact prefixLift 2731827
  have htrace : WordTrace (prefixWord ++ tailWord_2731827) baseStart_2731827 baseEnd_2731827 := by
    simpa [prefixWord, tailWord_2731827, baseEnd_2731827] using wordTrace_append hprefix tailTrace_2731827
  have hstable : (prefixWord ++ tailWord_2731827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731827).length < 2 ^ (prefixWord ++ tailWord_2731827).sum := by decide
  have hdescent : baseEnd_2731827 < baseStart_2731827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731846 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2731846 : Nat := 118140960795 + 2731846 * 2 ^ 59
def prefixEnd_2731846 : Nat := 4983230072969 + 3 ^ 40 * 2731846 * 2
def baseEnd_2731846 : Nat := 311722238236138638591439

theorem tailTrace_2731846 : CollatzResearch.WordTrace tailWord_2731846 prefixEnd_2731846 311722238236138638591439 := by
  unfold tailWord_2731846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113706539406124343656231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66425739507330652664666261 3113706539406124343656231)
  ·
    refine ⟨4670559809109186515484347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113706539406124343656231 4670559809109186515484347)
    ·
      refine ⟨7005839713663779773226521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670559809109186515484347 7005839713663779773226521)
      ·
        refine ⟨5254379785247834829919891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7005839713663779773226521 5254379785247834829919891)
        ·
          refine ⟨7881569677871752244879837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254379785247834829919891 7881569677871752244879837)
          ·
            refine ⟨2955588629201907091829939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7881569677871752244879837 2955588629201907091829939)
            ·
              refine ⟨4433382943802860637744909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955588629201907091829939 4433382943802860637744909)
              ·
                refine ⟨1662518603926072739154341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433382943802860637744909 1662518603926072739154341)
                ·
                  refine ⟨311722238236138638591439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662518603926072739154341 311722238236138638591439)
                  ·
                    rfl

theorem cell22_2731846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2731846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731846 prefixEnd_2731846 := by exact prefixLift 2731846
  have htrace : WordTrace (prefixWord ++ tailWord_2731846) baseStart_2731846 baseEnd_2731846 := by
    simpa [prefixWord, tailWord_2731846, baseEnd_2731846] using wordTrace_append hprefix tailTrace_2731846
  have hstable : (prefixWord ++ tailWord_2731846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731846).length < 2 ^ (prefixWord ++ tailWord_2731846).sum := by decide
  have hdescent : baseEnd_2731846 < baseStart_2731846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731872 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_2731872 : Nat := 118140960795 + 2731872 * 2 ^ 59
def prefixEnd_2731872 : Nat := 4983230072969 + 3 ^ 40 * 2731872 * 2
def baseEnd_2731872 : Nat := 935175615039760514624237

theorem tailTrace_2731872 : CollatzResearch.WordTrace tailWord_2731872 prefixEnd_2731872 935175615039760514624237 := by
  unfold tailWord_2731872
  simp only [CollatzResearch.WordTrace]
  refine ⟨49819778779450892718722935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66426371705934523624963913 49819778779450892718722935)
  ·
    refine ⟨74729668169176339078084403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49819778779450892718722935 74729668169176339078084403)
    ·
      refine ⟨112094502253764508617126605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74729668169176339078084403 112094502253764508617126605)
      ·
        refine ⟨42035438345161690731422477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112094502253764508617126605 42035438345161690731422477)
        ·
          refine ⟨15763289379435634024283429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42035438345161690731422477 15763289379435634024283429)
          ·
            refine ⟨2955616758644181379553143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15763289379435634024283429 2955616758644181379553143)
            ·
              refine ⟨4433425137966272069329715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955616758644181379553143 4433425137966272069329715)
              ·
                refine ⟨6650137706949408103994573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433425137966272069329715 6650137706949408103994573)
                ·
                  refine ⟨2493801640106028038997965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6650137706949408103994573 2493801640106028038997965)
                  ·
                    refine ⟨935175615039760514624237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493801640106028038997965 935175615039760514624237)
                    ·
                      rfl

theorem cell22_2731872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_2731872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731872 prefixEnd_2731872 := by exact prefixLift 2731872
  have htrace : WordTrace (prefixWord ++ tailWord_2731872) baseStart_2731872 baseEnd_2731872 := by
    simpa [prefixWord, tailWord_2731872, baseEnd_2731872] using wordTrace_append hprefix tailTrace_2731872
  have hstable : (prefixWord ++ tailWord_2731872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731872).length < 2 ^ (prefixWord ++ tailWord_2731872).sum := by decide
  have hdescent : baseEnd_2731872 < baseStart_2731872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2731934 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2731934 : Nat := 118140960795 + 2731934 * 2 ^ 59
def prefixEnd_2731934 : Nat := 4983230072969 + 3 ^ 40 * 2731934 * 2
def baseEnd_2731934 : Nat := 935196838906813019574047

theorem tailTrace_2731934 : CollatzResearch.WordTrace tailWord_2731934 prefixEnd_2731934 935196838906813019574047 := by
  unfold tailWord_2731934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455227360584646253275357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66427879256451446684135237 12455227360584646253275357)
  ·
    refine ⟨4670710260219242344978259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12455227360584646253275357 4670710260219242344978259)
    ·
      refine ⟨7006065390328863517467389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670710260219242344978259 7006065390328863517467389)
      ·
        refine ⟨2627274521373323819050271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7006065390328863517467389 2627274521373323819050271)
        ·
          refine ⟨3940911782059985728575407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627274521373323819050271 3940911782059985728575407)
          ·
            refine ⟨5911367673089978592863111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940911782059985728575407 5911367673089978592863111)
            ·
              refine ⟨8867051509634967889294667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911367673089978592863111 8867051509634967889294667)
              ·
                refine ⟨13300577264452451833942001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8867051509634967889294667 13300577264452451833942001)
                ·
                  refine ⟨9975432948339338875456501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13300577264452451833942001 9975432948339338875456501)
                  ·
                    refine ⟨935196838906813019574047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9975432948339338875456501 935196838906813019574047)
                    ·
                      rfl

theorem cell22_2731934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2731934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2731934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2731934 prefixEnd_2731934 := by exact prefixLift 2731934
  have htrace : WordTrace (prefixWord ++ tailWord_2731934) baseStart_2731934 baseEnd_2731934 := by
    simpa [prefixWord, tailWord_2731934, baseEnd_2731934] using wordTrace_append hprefix tailTrace_2731934
  have hstable : (prefixWord ++ tailWord_2731934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2731934).length < 2 ^ (prefixWord ++ tailWord_2731934).sum := by decide
  have hdescent : baseEnd_2731934 < baseStart_2731934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2731934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732024 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_2732024 : Nat := 118140960795 + 2732024 * 2 ^ 59
def prefixEnd_2732024 : Nat := 4983230072969 + 3 ^ 40 * 2732024 * 2
def baseEnd_2732024 : Nat := 935227647746082784823771

theorem tailTrace_2732024 : CollatzResearch.WordTrace tailWord_2732024 prefixEnd_2732024 935227647746082784823771 := by
  unfold tailWord_2732024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49822550727175557698489563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66430067636234076931319417 49822550727175557698489563)
  ·
    refine ⟨74733826090763336547734345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49822550727175557698489563 74733826090763336547734345)
    ·
      refine ⟨56050369568072502410800759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74733826090763336547734345 56050369568072502410800759)
      ·
        refine ⟨84075554352108753616201139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56050369568072502410800759 84075554352108753616201139)
        ·
          refine ⟨126113331528163130424301709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84075554352108753616201139 126113331528163130424301709)
          ·
            refine ⟨47292499323061173909113141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126113331528163130424301709 47292499323061173909113141)
            ·
              refine ⟨4433671811536985053979357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47292499323061173909113141 4433671811536985053979357)
              ·
                refine ⟨1662626929326369395242259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433671811536985053979357 1662626929326369395242259)
                ·
                  refine ⟨2493940393989554092863389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662626929326369395242259 2493940393989554092863389)
                  ·
                    refine ⟨935227647746082784823771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493940393989554092863389 935227647746082784823771)
                    ·
                      rfl

theorem cell22_2732024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_2732024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732024 prefixEnd_2732024 := by exact prefixLift 2732024
  have htrace : WordTrace (prefixWord ++ tailWord_2732024) baseStart_2732024 baseEnd_2732024 := by
    simpa [prefixWord, tailWord_2732024, baseEnd_2732024] using wordTrace_append hprefix tailTrace_2732024
  have hstable : (prefixWord ++ tailWord_2732024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732024).length < 2 ^ (prefixWord ++ tailWord_2732024).sum := by decide
  have hdescent : baseEnd_2732024 < baseStart_2732024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732080 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_2732080 : Nat := 118140960795 + 2732080 * 2 ^ 59
def prefixEnd_2732080 : Nat := 4983230072969 + 3 ^ 40 * 2732080 * 2
def baseEnd_2732080 : Nat := 935246817690517305423599

theorem tailTrace_2732080 : CollatzResearch.WordTrace tailWord_2732080 prefixEnd_2732080 935246817690517305423599 := by
  unfold tailWord_2732080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49823571971074118480508847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66431429294765491307345129 49823571971074118480508847)
  ·
    refine ⟨74735357956611177720763271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49823571971074118480508847 74735357956611177720763271)
    ·
      refine ⟨112103036934916766581144907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74735357956611177720763271 112103036934916766581144907)
      ·
        refine ⟨168154555402375149871717361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112103036934916766581144907 168154555402375149871717361)
        ·
          refine ⟨126115916551781362403788021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168154555402375149871717361 126115916551781362403788021)
          ·
            refine ⟨11823367176729502725355127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126115916551781362403788021 11823367176729502725355127)
            ·
              refine ⟨17735050765094254088032691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11823367176729502725355127 17735050765094254088032691)
              ·
                refine ⟨26602576147641381132049037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17735050765094254088032691 26602576147641381132049037)
                ·
                  refine ⟨9975966055365517924518389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26602576147641381132049037 9975966055365517924518389)
                  ·
                    refine ⟨935246817690517305423599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9975966055365517924518389 935246817690517305423599)
                    ·
                      rfl

theorem cell22_2732080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_2732080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732080 prefixEnd_2732080 := by exact prefixLift 2732080
  have htrace : WordTrace (prefixWord ++ tailWord_2732080) baseStart_2732080 baseEnd_2732080 := by
    simpa [prefixWord, tailWord_2732080, baseEnd_2732080] using wordTrace_append hprefix tailTrace_2732080
  have hstable : (prefixWord ++ tailWord_2732080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732080).length < 2 ^ (prefixWord ++ tailWord_2732080).sum := by decide
  have hdescent : baseEnd_2732080 < baseStart_2732080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732114 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2732114 : Nat := 118140960795 + 2732114 * 2 ^ 59
def prefixEnd_2732114 : Nat := 4983230072969 + 3 ^ 40 * 2732114 * 2
def baseEnd_2732114 : Nat := 935258456585352550073495

theorem tailTrace_2732114 : CollatzResearch.WordTrace tailWord_2732114 prefixEnd_2732114 935258456585352550073495 := by
  unfold tailWord_2732114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912096006006265191938849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66432256016016707178503597 24912096006006265191938849)
  ·
    refine ⟨18684072004504698893954137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24912096006006265191938849 18684072004504698893954137)
    ·
      refine ⟨14013054003378524170465603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18684072004504698893954137 14013054003378524170465603)
      ·
        refine ⟨21019581005067786255698405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013054003378524170465603 21019581005067786255698405)
        ·
          refine ⟨3941171438450209922943451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21019581005067786255698405 3941171438450209922943451)
          ·
            refine ⟨5911757157675314884415177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941171438450209922943451 5911757157675314884415177)
            ·
              refine ⟨4433817868256486163311383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911757157675314884415177 4433817868256486163311383)
              ·
                refine ⟨6650726802384729244967075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433817868256486163311383 6650726802384729244967075)
                ·
                  refine ⟨9976090203577093867450613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650726802384729244967075 9976090203577093867450613)
                  ·
                    refine ⟨935258456585352550073495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9976090203577093867450613 935258456585352550073495)
                    ·
                      rfl

theorem cell22_2732114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2732114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732114 prefixEnd_2732114 := by exact prefixLift 2732114
  have htrace : WordTrace (prefixWord ++ tailWord_2732114) baseStart_2732114 baseEnd_2732114 := by
    simpa [prefixWord, tailWord_2732114, baseEnd_2732114] using wordTrace_append hprefix tailTrace_2732114
  have hstable : (prefixWord ++ tailWord_2732114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732114).length < 2 ^ (prefixWord ++ tailWord_2732114).sum := by decide
  have hdescent : baseEnd_2732114 < baseStart_2732114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732185 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2732185 : Nat := 118140960795 + 2732185 * 2 ^ 59
def prefixEnd_2732185 : Nat := 4983230072969 + 3 ^ 40 * 2732185 * 2
def baseEnd_2732185 : Nat := 935282761336332031548277

theorem tailTrace_2732185 : CollatzResearch.WordTrace tailWord_2732185 prefixEnd_2732185 935282761336332031548277 := by
  unfold tailWord_2732185
  simp only [CollatzResearch.WordTrace]
  refine ⟨99650973606767839893590009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66433982404511893262393339 99650973606767839893590009)
  ·
    refine ⟨74738230205075879920192507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99650973606767839893590009 74738230205075879920192507)
    ·
      refine ⟨112107345307613819880288761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74738230205075879920192507 112107345307613819880288761)
      ·
        refine ⟨84080508980710364910216571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112107345307613819880288761 84080508980710364910216571)
        ·
          refine ⟨126120763471065547365324857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84080508980710364910216571 126120763471065547365324857)
          ·
            refine ⟨94590572603299160523993643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126120763471065547365324857 94590572603299160523993643)
            ·
              refine ⟨141885858904948740785990465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94590572603299160523993643 141885858904948740785990465)
              ·
                refine ⟨106414394178711555589492849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141885858904948740785990465 106414394178711555589492849)
                ·
                  refine ⟨79810795634033666692119637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106414394178711555589492849 79810795634033666692119637)
                  ·
                    refine ⟨935282761336332031548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79810795634033666692119637 935282761336332031548277)
                    ·
                      rfl

theorem cell22_2732185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2732185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732185 prefixEnd_2732185 := by exact prefixLift 2732185
  have htrace : WordTrace (prefixWord ++ tailWord_2732185) baseStart_2732185 baseEnd_2732185 := by
    simpa [prefixWord, tailWord_2732185, baseEnd_2732185] using wordTrace_append hprefix tailTrace_2732185
  have hstable : (prefixWord ++ tailWord_2732185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732185).length < 2 ^ (prefixWord ++ tailWord_2732185).sum := by decide
  have hdescent : baseEnd_2732185 < baseStart_2732185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732193 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2732193 : Nat := 118140960795 + 2732193 * 2 ^ 59
def prefixEnd_2732193 : Nat := 4983230072969 + 3 ^ 40 * 2732193 * 2
def baseEnd_2732193 : Nat := 935285499899822677348253

theorem tailTrace_2732193 : CollatzResearch.WordTrace tailWord_2732193 prefixEnd_2732193 935285499899822677348253 := by
  unfold tailWord_2732193
  simp only [CollatzResearch.WordTrace]
  refine ⟨99651265390738857259881233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66434176927159238173254155 99651265390738857259881233)
  ·
    refine ⟨74738449043054142944910925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99651265390738857259881233 74738449043054142944910925)
    ·
      refine ⟨28026918391145303604341597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74738449043054142944910925 28026918391145303604341597)
      ·
        refine ⟨10510094396679488851628099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28026918391145303604341597 10510094396679488851628099)
        ·
          refine ⟨15765141595019233277442149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510094396679488851628099 15765141595019233277442149)
          ·
            refine ⟨2955964049066106239520403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15765141595019233277442149 2955964049066106239520403)
            ·
              refine ⟨4433946073599159359280605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955964049066106239520403 4433946073599159359280605)
              ·
                refine ⟨1662729777599684759730227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433946073599159359280605 1662729777599684759730227)
                ·
                  refine ⟨2494094666399527139595341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662729777599684759730227 2494094666399527139595341)
                  ·
                    refine ⟨935285499899822677348253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494094666399527139595341 935285499899822677348253)
                    ·
                      rfl

theorem cell22_2732193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2732193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732193 prefixEnd_2732193 := by exact prefixLift 2732193
  have htrace : WordTrace (prefixWord ++ tailWord_2732193) baseStart_2732193 baseEnd_2732193 := by
    simpa [prefixWord, tailWord_2732193, baseEnd_2732193] using wordTrace_append hprefix tailTrace_2732193
  have hstable : (prefixWord ++ tailWord_2732193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732193).length < 2 ^ (prefixWord ++ tailWord_2732193).sum := by decide
  have hdescent : baseEnd_2732193 < baseStart_2732193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732232 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2732232 : Nat := 118140960795 + 2732232 * 2 ^ 59
def prefixEnd_2732232 : Nat := 4983230072969 + 3 ^ 40 * 2732232 * 2
def baseEnd_2732232 : Nat := 935298850396839575623133

theorem tailTrace_2732232 : CollatzResearch.WordTrace tailWord_2732232 prefixEnd_2732232 935298850396839575623133 := by
  unfold tailWord_2732232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826343918798783460275475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66435125225065044613700633 49826343918798783460275475)
  ·
    refine ⟨74739515878198175190413213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49826343918798783460275475 74739515878198175190413213)
    ·
      refine ⟨28027318454324315696404955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74739515878198175190413213 28027318454324315696404955)
      ·
        refine ⟨42040977681486473544607433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28027318454324315696404955 42040977681486473544607433)
        ·
          refine ⟨31530733261114855158455575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42040977681486473544607433 31530733261114855158455575)
          ·
            refine ⟨47296099891672282737683363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31530733261114855158455575 47296099891672282737683363)
            ·
              refine ⟨70944149837508424106525045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47296099891672282737683363 70944149837508424106525045)
              ·
                refine ⟨6651014047266414759986723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70944149837508424106525045 6651014047266414759986723)
                ·
                  refine ⟨9976521070899622139980085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6651014047266414759986723 9976521070899622139980085)
                  ·
                    refine ⟨935298850396839575623133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9976521070899622139980085 935298850396839575623133)
                    ·
                      rfl

theorem cell22_2732232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2732232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732232 prefixEnd_2732232 := by exact prefixLift 2732232
  have htrace : WordTrace (prefixWord ++ tailWord_2732232) baseStart_2732232 baseEnd_2732232 := by
    simpa [prefixWord, tailWord_2732232, baseEnd_2732232] using wordTrace_append hprefix tailTrace_2732232
  have hstable : (prefixWord ++ tailWord_2732232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732232).length < 2 ^ (prefixWord ++ tailWord_2732232).sum := by decide
  have hdescent : baseEnd_2732232 < baseStart_2732232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732236 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_2732236 : Nat := 118140960795 + 2732236 * 2 ^ 59
def prefixEnd_2732236 : Nat := 4983230072969 + 3 ^ 40 * 2732236 * 2
def baseEnd_2732236 : Nat := 935300219678584898523121

theorem tailTrace_2732236 : CollatzResearch.WordTrace tailWord_2732236 prefixEnd_2732236 935300219678584898523121 := by
  unfold tailWord_2732236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826416864791537801848281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66435222486388717069131041 49826416864791537801848281)
  ·
    refine ⟨37369812648593653351386211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49826416864791537801848281 37369812648593653351386211)
    ·
      refine ⟨56054718972890480027079317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37369812648593653351386211 56054718972890480027079317)
      ·
        refine ⟨2627564951854241251269343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56054718972890480027079317 2627564951854241251269343)
        ·
          refine ⟨3941347427781361876904015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627564951854241251269343 3941347427781361876904015)
          ·
            refine ⟨5912021141672042815356023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941347427781361876904015 5912021141672042815356023)
            ·
              refine ⟨8868031712508064223034035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912021141672042815356023 8868031712508064223034035)
              ·
                refine ⟨13302047568762096334551053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868031712508064223034035 13302047568762096334551053)
                ·
                  refine ⟨4988267838285786125456645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13302047568762096334551053 4988267838285786125456645)
                  ·
                    refine ⟨935300219678584898523121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988267838285786125456645 935300219678584898523121)
                    ·
                      rfl

theorem cell22_2732236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_2732236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732236 prefixEnd_2732236 := by exact prefixLift 2732236
  have htrace : WordTrace (prefixWord ++ tailWord_2732236) baseStart_2732236 baseEnd_2732236 := by
    simpa [prefixWord, tailWord_2732236, baseEnd_2732236] using wordTrace_append hprefix tailTrace_2732236
  have hstable : (prefixWord ++ tailWord_2732236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732236).length < 2 ^ (prefixWord ++ tailWord_2732236).sum := by decide
  have hdescent : baseEnd_2732236 < baseStart_2732236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732253 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2732253 : Nat := 118140960795 + 2732253 * 2 ^ 59
def prefixEnd_2732253 : Nat := 4983230072969 + 3 ^ 40 * 2732253 * 2
def baseEnd_2732253 : Nat := 935306039126002520848069

theorem tailTrace_2732253 : CollatzResearch.WordTrace tailWord_2732253 prefixEnd_2732253 935306039126002520848069 := by
  unfold tailWord_2732253
  simp only [CollatzResearch.WordTrace]
  refine ⟨99653453770521487507065413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66435635847014325004710275 99653453770521487507065413)
  ·
    refine ⟨18685022581972778907574765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99653453770521487507065413 18685022581972778907574765)
    ·
      refine ⟨7006883468239792090340537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18685022581972778907574765 7006883468239792090340537)
      ·
        refine ⟨5255162601179844067755403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7006883468239792090340537 5255162601179844067755403)
        ·
          refine ⟨7882743901769766101633105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5255162601179844067755403 7882743901769766101633105)
          ·
            refine ⟨5912057926327324576224829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7882743901769766101633105 5912057926327324576224829)
            ·
              refine ⟨2217021722372746716084311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5912057926327324576224829 2217021722372746716084311)
              ·
                refine ⟨3325532583559120074126467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217021722372746716084311 3325532583559120074126467)
                ·
                  refine ⟨4988298875338680111189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325532583559120074126467 4988298875338680111189701)
                  ·
                    refine ⟨935306039126002520848069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988298875338680111189701 935306039126002520848069)
                    ·
                      rfl

theorem cell22_2732253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2732253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732253 prefixEnd_2732253 := by exact prefixLift 2732253
  have htrace : WordTrace (prefixWord ++ tailWord_2732253) baseStart_2732253 baseEnd_2732253 := by
    simpa [prefixWord, tailWord_2732253, baseEnd_2732253] using wordTrace_append hprefix tailTrace_2732253
  have hstable : (prefixWord ++ tailWord_2732253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732253).length < 2 ^ (prefixWord ++ tailWord_2732253).sum := by decide
  have hdescent : baseEnd_2732253 < baseStart_2732253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732264 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2732264 : Nat := 118140960795 + 2732264 * 2 ^ 59
def prefixEnd_2732264 : Nat := 4983230072969 + 3 ^ 40 * 2732264 * 2
def baseEnd_2732264 : Nat := 935309804650802158823035

theorem tailTrace_2732264 : CollatzResearch.WordTrace tailWord_2732264 prefixEnd_2732264 935309804650802158823035 := by
  unfold tailWord_2732264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826927486740818192857923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66435903315654424257143897 49826927486740818192857923)
  ·
    refine ⟨74740391230111227289286885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49826927486740818192857923 74740391230111227289286885)
    ·
      refine ⟨14013823355645855116741291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74740391230111227289286885 14013823355645855116741291)
      ·
        refine ⟨21020735033468782675111937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013823355645855116741291 21020735033468782675111937)
        ·
          refine ⟨15765551275101587006333953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21020735033468782675111937 15765551275101587006333953)
          ·
            refine ⟨11824163456326190254750465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15765551275101587006333953 11824163456326190254750465)
            ·
              refine ⟨8868122592244642691062849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11824163456326190254750465 8868122592244642691062849)
              ·
                refine ⟨6651091944183482018297137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8868122592244642691062849 6651091944183482018297137)
                ·
                  refine ⟨4988318958137611513722853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6651091944183482018297137 4988318958137611513722853)
                  ·
                    refine ⟨935309804650802158823035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988318958137611513722853 935309804650802158823035)
                    ·
                      rfl

theorem cell22_2732264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2732264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732264 prefixEnd_2732264 := by exact prefixLift 2732264
  have htrace : WordTrace (prefixWord ++ tailWord_2732264) baseStart_2732264 baseEnd_2732264 := by
    simpa [prefixWord, tailWord_2732264, baseEnd_2732264] using wordTrace_append hprefix tailTrace_2732264
  have hstable : (prefixWord ++ tailWord_2732264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732264).length < 2 ^ (prefixWord ++ tailWord_2732264).sum := by decide
  have hdescent : baseEnd_2732264 < baseStart_2732264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732266 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2732266 : Nat := 118140960795 + 2732266 * 2 ^ 59
def prefixEnd_2732266 : Nat := 4983230072969 + 3 ^ 40 * 2732266 * 2
def baseEnd_2732266 : Nat := 935310489291674820273029

theorem tailTrace_2732266 : CollatzResearch.WordTrace tailWord_2732266 prefixEnd_2732266 935310489291674820273029 := by
  unfold tailWord_2732266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913481979868597681822163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66435951946316260484859101 24913481979868597681822163)
  ·
    refine ⟨37370222969802896522733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24913481979868597681822163 37370222969802896522733245)
    ·
      refine ⟨14013833613676086196024967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37370222969802896522733245 14013833613676086196024967)
      ·
        refine ⟨21020750420514129294037451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013833613676086196024967 21020750420514129294037451)
        ·
          refine ⟨31531125630771193941056177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21020750420514129294037451 31531125630771193941056177)
          ·
            refine ⟨23648344223078395455792133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31531125630771193941056177 23648344223078395455792133)
            ·
              refine ⟨4434064541827199147961025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23648344223078395455792133 4434064541827199147961025)
              ·
                refine ⟨3325548406370399360970769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434064541827199147961025 3325548406370399360970769)
                ·
                  refine ⟨2494161304777799520728077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3325548406370399360970769 2494161304777799520728077)
                  ·
                    refine ⟨935310489291674820273029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494161304777799520728077 935310489291674820273029)
                    ·
                      rfl

theorem cell22_2732266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2732266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732266 prefixEnd_2732266 := by exact prefixLift 2732266
  have htrace : WordTrace (prefixWord ++ tailWord_2732266) baseStart_2732266 baseEnd_2732266 := by
    simpa [prefixWord, tailWord_2732266, baseEnd_2732266] using wordTrace_append hprefix tailTrace_2732266
  have hstable : (prefixWord ++ tailWord_2732266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732266).length < 2 ^ (prefixWord ++ tailWord_2732266).sum := by decide
  have hdescent : baseEnd_2732266 < baseStart_2732266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732324 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2732324 : Nat := 118140960795 + 2732324 * 2 ^ 59
def prefixEnd_2732324 : Nat := 4983230072969 + 3 ^ 40 * 2732324 * 2
def baseEnd_2732324 : Nat := 311776781292327334107617

theorem tailTrace_2732324 : CollatzResearch.WordTrace tailWord_2732324 prefixEnd_2732324 311776781292327334107617 := by
  unfold tailWord_2732324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828021676632133316450013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66437362235509511088600017 49828021676632133316450013)
  ·
    refine ⟨18685508128737049993668755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49828021676632133316450013 18685508128737049993668755)
    ·
      refine ⟨28028262193105574990503133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18685508128737049993668755 28028262193105574990503133)
      ·
        refine ⟨10510598322414590621438675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28028262193105574990503133 10510598322414590621438675)
        ·
          refine ⟨15765897483621885932158013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510598322414590621438675 15765897483621885932158013)
          ·
            refine ⟨5912211556358207224559255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15765897483621885932158013 5912211556358207224559255)
            ·
              refine ⟨8868317334537310836838883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912211556358207224559255 8868317334537310836838883)
              ·
                refine ⟨13302476001805966255258325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868317334537310836838883 13302476001805966255258325)
                ·
                  refine ⟨311776781292327334107617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13302476001805966255258325 311776781292327334107617)
                  ·
                    rfl

theorem cell22_2732324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2732324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732324 prefixEnd_2732324 := by exact prefixLift 2732324
  have htrace : WordTrace (prefixWord ++ tailWord_2732324) baseStart_2732324 baseEnd_2732324 := by
    simpa [prefixWord, tailWord_2732324, baseEnd_2732324] using wordTrace_append hprefix tailTrace_2732324
  have hstable : (prefixWord ++ tailWord_2732324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732324).length < 2 ^ (prefixWord ++ tailWord_2732324).sum := by decide
  have hdescent : baseEnd_2732324 < baseStart_2732324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732328 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2732328 : Nat := 118140960795 + 2732328 * 2 ^ 59
def prefixEnd_2732328 : Nat := 4983230072969 + 3 ^ 40 * 2732328 * 2
def baseEnd_2732328 : Nat := 935331713158727325222839

theorem tailTrace_2732328 : CollatzResearch.WordTrace tailWord_2732328 prefixEnd_2732328 935331713158727325222839 := by
  unfold tailWord_2732328
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828094622624887658022819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66437459496833183544030425 49828094622624887658022819)
  ·
    refine ⟨74742141933937331487034229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49828094622624887658022819 74742141933937331487034229)
    ·
      refine ⟨7007075806306624826909459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74742141933937331487034229 7007075806306624826909459)
      ·
        refine ⟨10510613709459937240364189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007075806306624826909459 10510613709459937240364189)
        ·
          refine ⟨3941480141047476465136571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10510613709459937240364189 3941480141047476465136571)
          ·
            refine ⟨5912220211571214697704857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941480141047476465136571 5912220211571214697704857)
            ·
              refine ⟨4434165158678411023278643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912220211571214697704857 4434165158678411023278643)
              ·
                refine ⟨6651247738017616534917965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434165158678411023278643 6651247738017616534917965)
                ·
                  refine ⟨2494217901756606200594237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6651247738017616534917965 2494217901756606200594237)
                  ·
                    refine ⟨935331713158727325222839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494217901756606200594237 935331713158727325222839)
                    ·
                      rfl

theorem cell22_2732328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2732328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732328 prefixEnd_2732328 := by exact prefixLift 2732328
  have htrace : WordTrace (prefixWord ++ tailWord_2732328) baseStart_2732328 baseEnd_2732328 := by
    simpa [prefixWord, tailWord_2732328, baseEnd_2732328] using wordTrace_append hprefix tailTrace_2732328
  have hstable : (prefixWord ++ tailWord_2732328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732328).length < 2 ^ (prefixWord ++ tailWord_2732328).sum := by decide
  have hdescent : baseEnd_2732328 < baseStart_2732328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732341 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 5]
def baseStart_2732341 : Nat := 118140960795 + 2732341 * 2 ^ 59
def prefixEnd_2732341 : Nat := 4983230072969 + 3 ^ 40 * 2732341 * 2
def baseEnd_2732341 : Nat := 311778721108133208215933

theorem tailTrace_2732341 : CollatzResearch.WordTrace tailWord_2732341 prefixEnd_2732341 311778721108133208215933 := by
  unfold tailWord_2732341
  simp only [CollatzResearch.WordTrace]
  refine ⟨99656663394202678536268877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66437775596135119024179251 99656663394202678536268877)
  ·
    refine ⟨37371248772826004451100829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99656663394202678536268877 37371248772826004451100829)
    ·
      refine ⟨14014218289809751669162811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37371248772826004451100829 14014218289809751669162811)
      ·
        refine ⟨21021327434714627503744217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14014218289809751669162811 21021327434714627503744217)
        ·
          refine ⟨15765995576035970627808163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21021327434714627503744217 15765995576035970627808163)
          ·
            refine ⟨23648993364053955941712245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15765995576035970627808163 23648993364053955941712245)
            ·
              refine ⟨2217093127880058369535523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23648993364053955941712245 2217093127880058369535523)
              ·
                refine ⟨3325639691820087554303285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217093127880058369535523 3325639691820087554303285)
                ·
                  refine ⟨311778721108133208215933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325639691820087554303285 311778721108133208215933)
                  ·
                    rfl

theorem cell22_2732341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_2732341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732341 prefixEnd_2732341 := by exact prefixLift 2732341
  have htrace : WordTrace (prefixWord ++ tailWord_2732341) baseStart_2732341 baseEnd_2732341 := by
    simpa [prefixWord, tailWord_2732341, baseEnd_2732341] using wordTrace_append hprefix tailTrace_2732341
  have hstable : (prefixWord ++ tailWord_2732341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732341).length < 2 ^ (prefixWord ++ tailWord_2732341).sum := by decide
  have hdescent : baseEnd_2732341 < baseStart_2732341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732352 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_2732352 : Nat := 118140960795 + 2732352 * 2 ^ 59
def prefixEnd_2732352 : Nat := 4983230072969 + 3 ^ 40 * 2732352 * 2
def baseEnd_2732352 : Nat := 311779976283066420874255

theorem tailTrace_2732352 : CollatzResearch.WordTrace tailWord_2732352 prefixEnd_2732352 311779976283066420874255 := by
  unfold tailWord_2732352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828532298581413707459655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66438043064775218276612873 49828532298581413707459655)
  ·
    refine ⟨74742798447872120561189483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49828532298581413707459655 74742798447872120561189483)
    ·
      refine ⟨112114197671808180841784225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74742798447872120561189483 112114197671808180841784225)
      ·
        refine ⟨84085648253856135631338169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112114197671808180841784225 84085648253856135631338169)
        ·
          refine ⟨63064236190392101723503627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84085648253856135631338169 63064236190392101723503627)
          ·
            refine ⟨94596354285588152585255441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63064236190392101723503627 94596354285588152585255441)
            ·
              refine ⟨70947265714191114438941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94596354285588152585255441 70947265714191114438941581)
              ·
                refine ⟨26605224642821667914603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70947265714191114438941581 26605224642821667914603093)
                ·
                  refine ⟨311779976283066420874255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26605224642821667914603093 311779976283066420874255)
                  ·
                    rfl

theorem cell22_2732352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_2732352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732352 prefixEnd_2732352 := by exact prefixLift 2732352
  have htrace : WordTrace (prefixWord ++ tailWord_2732352) baseStart_2732352 baseEnd_2732352 := by
    simpa [prefixWord, tailWord_2732352, baseEnd_2732352] using wordTrace_append hprefix tailTrace_2732352
  have hstable : (prefixWord ++ tailWord_2732352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732352).length < 2 ^ (prefixWord ++ tailWord_2732352).sum := by decide
  have hdescent : baseEnd_2732352 < baseStart_2732352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732386 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2732386 : Nat := 118140960795 + 2732386 * 2 ^ 59
def prefixEnd_2732386 : Nat := 4983230072969 + 3 ^ 40 * 2732386 * 2
def baseEnd_2732386 : Nat := 311783855914678169090887

theorem tailTrace_2732386 : CollatzResearch.WordTrace tailWord_2732386 prefixEnd_2732386 311783855914678169090887 := by
  unfold tailWord_2732386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24914576169759912805414253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66438869786026434147771341 24914576169759912805414253)
  ·
    refine ⟨9342966063659967302030345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24914576169759912805414253 9342966063659967302030345)
    ·
      refine ⟨7007224547744975476522759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9342966063659967302030345 7007224547744975476522759)
      ·
        refine ⟨10510836821617463214784139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007224547744975476522759 10510836821617463214784139)
        ·
          refine ⟨15766255232426194822176209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510836821617463214784139 15766255232426194822176209)
          ·
            refine ⟨11824691424319646116632157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15766255232426194822176209 11824691424319646116632157)
            ·
              refine ⟨4434259284119867293737059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11824691424319646116632157 4434259284119867293737059)
              ·
                refine ⟨6651388926179800940605589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434259284119867293737059 6651388926179800940605589)
                ·
                  refine ⟨311783855914678169090887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6651388926179800940605589 311783855914678169090887)
                  ·
                    rfl

theorem cell22_2732386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2732386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732386 prefixEnd_2732386 := by exact prefixLift 2732386
  have htrace : WordTrace (prefixWord ++ tailWord_2732386) baseStart_2732386 baseEnd_2732386 := by
    simpa [prefixWord, tailWord_2732386, baseEnd_2732386] using wordTrace_append hprefix tailTrace_2732386
  have hstable : (prefixWord ++ tailWord_2732386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732386).length < 2 ^ (prefixWord ++ tailWord_2732386).sum := by decide
  have hdescent : baseEnd_2732386 < baseStart_2732386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732536 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_2732536 : Nat := 118140960795 + 2732536 * 2 ^ 59
def prefixEnd_2732536 : Nat := 4983230072969 + 3 ^ 40 * 2732536 * 2
def baseEnd_2732536 : Nat := 935402915809484116022201

theorem tailTrace_2732536 : CollatzResearch.WordTrace tailWord_2732536 prefixEnd_2732536 935402915809484116022201 := by
  unfold tailWord_2732536
  simp only [CollatzResearch.WordTrace]
  refine ⟨49831887814248113419808731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66442517085664151226411641 49831887814248113419808731)
  ·
    refine ⟨74747831721372170129713097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49831887814248113419808731 74747831721372170129713097)
    ·
      refine ⟨56060873791029127597284823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74747831721372170129713097 56060873791029127597284823)
      ·
        refine ⟨84091310686543691395927235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56060873791029127597284823 84091310686543691395927235)
        ·
          refine ⟨126136966029815537093890853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84091310686543691395927235 126136966029815537093890853)
          ·
            refine ⟨23650681130590413205104535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126136966029815537093890853 23650681130590413205104535)
            ·
              refine ⟨35476021695885619807656803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23650681130590413205104535 35476021695885619807656803)
              ·
                refine ⟨53214032543828429711485205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35476021695885619807656803 53214032543828429711485205)
                ·
                  refine ⟨2494407775491957642725869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53214032543828429711485205 2494407775491957642725869)
                  ·
                    refine ⟨935402915809484116022201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494407775491957642725869 935402915809484116022201)
                    ·
                      rfl

theorem cell22_2732536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_2732536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732536 prefixEnd_2732536 := by exact prefixLift 2732536
  have htrace : WordTrace (prefixWord ++ tailWord_2732536) baseStart_2732536 baseEnd_2732536 := by
    simpa [prefixWord, tailWord_2732536, baseEnd_2732536] using wordTrace_append hprefix tailTrace_2732536
  have hstable : (prefixWord ++ tailWord_2732536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732536).length < 2 ^ (prefixWord ++ tailWord_2732536).sum := by decide
  have hdescent : baseEnd_2732536 < baseStart_2732536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732549 : List Nat := [1, 3, 1, 1, 2, 2, 12]
def baseStart_2732549 : Nat := 118140960795 + 2732549 * 2 ^ 59
def prefixEnd_2732549 : Nat := 4983230072969 + 3 ^ 40 * 2732549 * 2
def baseEnd_2732549 : Nat := 34644717258339126498043

theorem tailTrace_2732549 : CollatzResearch.WordTrace tailWord_2732549 prefixEnd_2732549 34644717258339126498043 := by
  unfold tailWord_2732549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99664249777449130059840701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66442833184966086706560467 99664249777449130059840701)
  ·
    refine ⟨37374093666543423772440263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99664249777449130059840701 37374093666543423772440263)
    ·
      refine ⟨56061140499815135658660395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37374093666543423772440263 56061140499815135658660395)
      ·
        refine ⟨84091710749722703487990593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56061140499815135658660395 84091710749722703487990593)
        ·
          refine ⟨63068783062292027615992945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84091710749722703487990593 63068783062292027615992945)
          ·
            refine ⟨47301587296719020711994709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63068783062292027615992945 47301587296719020711994709)
            ·
              refine ⟨34644717258339126498043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47301587296719020711994709 34644717258339126498043)
              ·
                rfl

theorem cell22_2732549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 12].length) (baseStart_2732549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732549 prefixEnd_2732549 := by exact prefixLift 2732549
  have htrace : WordTrace (prefixWord ++ tailWord_2732549) baseStart_2732549 baseEnd_2732549 := by
    simpa [prefixWord, tailWord_2732549, baseEnd_2732549] using wordTrace_append hprefix tailTrace_2732549
  have hstable : (prefixWord ++ tailWord_2732549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732549).length < 2 ^ (prefixWord ++ tailWord_2732549).sum := by decide
  have hdescent : baseEnd_2732549 < baseStart_2732549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732555 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 4]
def baseStart_2732555 : Nat := 118140960795 + 2732555 * 2 ^ 59
def prefixEnd_2732555 : Nat := 4983230072969 + 3 ^ 40 * 2732555 * 2
def baseEnd_2732555 : Nat := 311803139965924799932381

theorem tailTrace_2732555 : CollatzResearch.WordTrace tailWord_2732555 prefixEnd_2732555 311803139965924799932381 := by
  unfold tailWord_2732555
  simp only [CollatzResearch.WordTrace]
  refine ⟨99664468615427393084559119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66442979076951595389706079 99664468615427393084559119)
  ·
    refine ⟨149496702923141089626838679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99664468615427393084559119 149496702923141089626838679)
    ·
      refine ⟨224245054384711634440258019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149496702923141089626838679 224245054384711634440258019)
      ·
        refine ⟨336367581577067451660387029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224245054384711634440258019 336367581577067451660387029)
        ·
          refine ⟨7883615193212518398290321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 336367581577067451660387029 7883615193212518398290321)
          ·
            refine ⟨5912711394909388798717741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7883615193212518398290321 5912711394909388798717741)
            ·
              refine ⟨2217266773091020799519153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5912711394909388798717741 2217266773091020799519153)
              ·
                refine ⟨1662950079818265599639365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217266773091020799519153 1662950079818265599639365)
                ·
                  refine ⟨311803139965924799932381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662950079818265599639365 311803139965924799932381)
                  ·
                    rfl

theorem cell22_2732555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 4].length) (baseStart_2732555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732555 prefixEnd_2732555 := by exact prefixLift 2732555
  have htrace : WordTrace (prefixWord ++ tailWord_2732555) baseStart_2732555 baseEnd_2732555 := by
    simpa [prefixWord, tailWord_2732555, baseEnd_2732555] using wordTrace_append hprefix tailTrace_2732555
  have hstable : (prefixWord ++ tailWord_2732555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732555).length < 2 ^ (prefixWord ++ tailWord_2732555).sum := by decide
  have hdescent : baseEnd_2732555 < baseStart_2732555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732570 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_2732570 : Nat := 118140960795 + 2732570 * 2 ^ 59
def prefixEnd_2732570 : Nat := 4983230072969 + 3 ^ 40 * 2732570 * 2
def baseEnd_2732570 : Nat := 935414554704319360672097

theorem tailTrace_2732570 : CollatzResearch.WordTrace tailWord_2732570 prefixEnd_2732570 935414554704319360672097 := by
  unfold tailWord_2732570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24916253927593262661588791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66443343806915367097570109 24916253927593262661588791)
  ·
    refine ⟨37374380891389893992383187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24916253927593262661588791 37374380891389893992383187)
    ·
      refine ⟨56061571337084840988574781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37374380891389893992383187 56061571337084840988574781)
      ·
        refine ⟨21023089251406815370715543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56061571337084840988574781 21023089251406815370715543)
        ·
          refine ⟨31534633877110223056073315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21023089251406815370715543 31534633877110223056073315)
          ·
            refine ⟨47301950815665334584109973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31534633877110223056073315 47301950815665334584109973)
            ·
              refine ⟨2217278944484312558630155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47301950815665334584109973 2217278944484312558630155)
              ·
                refine ⟨3325918416726468837945233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217278944484312558630155 3325918416726468837945233)
                ·
                  refine ⟨2494438812544851628458925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3325918416726468837945233 2494438812544851628458925)
                  ·
                    refine ⟨935414554704319360672097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494438812544851628458925 935414554704319360672097)
                    ·
                      rfl

theorem cell22_2732570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_2732570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732570 prefixEnd_2732570 := by exact prefixLift 2732570
  have htrace : WordTrace (prefixWord ++ tailWord_2732570) baseStart_2732570 baseEnd_2732570 := by
    simpa [prefixWord, tailWord_2732570, baseEnd_2732570] using wordTrace_append hprefix tailTrace_2732570
  have hstable : (prefixWord ++ tailWord_2732570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732570).length < 2 ^ (prefixWord ++ tailWord_2732570).sum := by decide
  have hdescent : baseEnd_2732570 < baseStart_2732570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732606 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2732606 : Nat := 118140960795 + 2732606 * 2 ^ 59
def prefixEnd_2732606 : Nat := 4983230072969 + 3 ^ 40 * 2732606 * 2
def baseEnd_2732606 : Nat := 311808959413342422257329

theorem tailTrace_2732606 : CollatzResearch.WordTrace tailWord_2732606 prefixEnd_2732606 311808959413342422257329 := by
  unfold tailWord_2732606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458291092280328599333209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66444219158828419196443781 12458291092280328599333209)
  ·
    refine ⟨9343718319210246449499907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12458291092280328599333209 9343718319210246449499907)
    ·
      refine ⟨14015577478815369674249861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343718319210246449499907 14015577478815369674249861)
      ·
        refine ⟨2627920777277881813921849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14015577478815369674249861 2627920777277881813921849)
        ·
          refine ⟨1970940582958411360441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627920777277881813921849 1970940582958411360441387)
          ·
            refine ⟨2956410874437617040662081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970940582958411360441387 2956410874437617040662081)
            ·
              refine ⟨2217308155828212780496561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956410874437617040662081 2217308155828212780496561)
              ·
                refine ⟨1662981116871159585372421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217308155828212780496561 1662981116871159585372421)
                ·
                  refine ⟨311808959413342422257329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662981116871159585372421 311808959413342422257329)
                  ·
                    rfl

theorem cell22_2732606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2732606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732606 prefixEnd_2732606 := by exact prefixLift 2732606
  have htrace : WordTrace (prefixWord ++ tailWord_2732606) baseStart_2732606 baseEnd_2732606 := by
    simpa [prefixWord, tailWord_2732606, baseEnd_2732606] using wordTrace_append hprefix tailTrace_2732606
  have hstable : (prefixWord ++ tailWord_2732606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732606).length < 2 ^ (prefixWord ++ tailWord_2732606).sum := by decide
  have hdescent : baseEnd_2732606 < baseStart_2732606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732628 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2732628 : Nat := 118140960795 + 2732628 * 2 ^ 59
def prefixEnd_2732628 : Nat := 4983230072969 + 3 ^ 40 * 2732628 * 2
def baseEnd_2732628 : Nat := 311811469763208847573973

theorem tailTrace_2732628 : CollatzResearch.WordTrace tailWord_2732628 prefixEnd_2732628 311811469763208847573973 := by
  unfold tailWord_2732628
  simp only [CollatzResearch.WordTrace]
  refine ⟨49833565572081463275983269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66444754096108617701311025 49833565572081463275983269)
  ·
    refine ⟨9343793544765274364246863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49833565572081463275983269 9343793544765274364246863)
    ·
      refine ⟨14015690317147911546370295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343793544765274364246863 14015690317147911546370295)
      ·
        refine ⟨21023535475721867319555443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015690317147911546370295 21023535475721867319555443)
        ·
          refine ⟨31535303213582800979333165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21023535475721867319555443 31535303213582800979333165)
          ·
            refine ⟨11825738705093550367249937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31535303213582800979333165 11825738705093550367249937)
            ·
              refine ⟨8869304028820162775437453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11825738705093550367249937 8869304028820162775437453)
              ·
                refine ⟨3325989010807561040789045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8869304028820162775437453 3325989010807561040789045)
                ·
                  refine ⟨311811469763208847573973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325989010807561040789045 311811469763208847573973)
                  ·
                    rfl

theorem cell22_2732628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2732628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732628 prefixEnd_2732628 := by exact prefixLift 2732628
  have htrace : WordTrace (prefixWord ++ tailWord_2732628) baseStart_2732628 baseEnd_2732628 := by
    simpa [prefixWord, tailWord_2732628, baseEnd_2732628] using wordTrace_append hprefix tailTrace_2732628
  have hstable : (prefixWord ++ tailWord_2732628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732628).length < 2 ^ (prefixWord ++ tailWord_2732628).sum := by decide
  have hdescent : baseEnd_2732628 < baseStart_2732628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732662 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2732662 : Nat := 118140960795 + 2732662 * 2 ^ 59
def prefixEnd_2732662 : Nat := 4983230072969 + 3 ^ 40 * 2732662 * 2
def baseEnd_2732662 : Nat := 311815349394820595790605

theorem tailTrace_2732662 : CollatzResearch.WordTrace tailWord_2732662 prefixEnd_2732662 311815349394820595790605 := by
  unfold tailWord_2732662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229273201627484397419015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66445580817359833572469493 6229273201627484397419015)
  ·
    refine ⟨9343909802441226596128523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229273201627484397419015 9343909802441226596128523)
    ·
      refine ⟨14015864703661839894192785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343909802441226596128523 14015864703661839894192785)
      ·
        refine ⟨10511898527746379920644589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14015864703661839894192785 10511898527746379920644589)
        ·
          refine ⟨3941961947904892470241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10511898527746379920644589 3941961947904892470241721)
          ·
            refine ⟨2956471460928669352681291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3941961947904892470241721 2956471460928669352681291)
            ·
              refine ⟨4434707191393004029021937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956471460928669352681291 4434707191393004029021937)
              ·
                refine ⟨3326030393544753021766453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434707191393004029021937 3326030393544753021766453)
                ·
                  refine ⟨311815349394820595790605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326030393544753021766453 311815349394820595790605)
                  ·
                    rfl

theorem cell22_2732662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2732662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732662 prefixEnd_2732662 := by exact prefixLift 2732662
  have htrace : WordTrace (prefixWord ++ tailWord_2732662) baseStart_2732662 baseEnd_2732662 := by
    simpa [prefixWord, tailWord_2732662, baseEnd_2732662] using wordTrace_append hprefix tailTrace_2732662
  have hstable : (prefixWord ++ tailWord_2732662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732662).length < 2 ^ (prefixWord ++ tailWord_2732662).sum := by decide
  have hdescent : baseEnd_2732662 < baseStart_2732662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732673 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 6]
def baseStart_2732673 : Nat := 118140960795 + 2732673 * 2 ^ 59
def prefixEnd_2732673 : Nat := 4983230072969 + 3 ^ 40 * 2732673 * 2
def baseEnd_2732673 : Nat := 311816604569753808448927

theorem tailTrace_2732673 : CollatzResearch.WordTrace tailWord_2732673 prefixEnd_2732673 311816604569753808448927 := by
  unfold tailWord_2732673
  simp only [CollatzResearch.WordTrace]
  refine ⟨99668772428999899237354673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66445848285999932824903115 99668772428999899237354673)
  ·
    refine ⟨74751579321749924428016005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99668772428999899237354673 74751579321749924428016005)
    ·
      refine ⟨14015921122828110830253001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74751579321749924428016005 14015921122828110830253001)
      ·
        refine ⟨10511940842121083122689751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14015921122828110830253001 10511940842121083122689751)
        ·
          refine ⟨15767911263181624684034627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10511940842121083122689751 15767911263181624684034627)
          ·
            refine ⟨23651866894772437026051941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15767911263181624684034627 23651866894772437026051941)
            ·
              refine ⟨4434725042769831942384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23651866894772437026051941 4434725042769831942384739)
              ·
                refine ⟨6652087564154747913577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434725042769831942384739 6652087564154747913577109)
                ·
                  refine ⟨311816604569753808448927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6652087564154747913577109 311816604569753808448927)
                  ·
                    rfl

theorem cell22_2732673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_2732673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732673 prefixEnd_2732673 := by exact prefixLift 2732673
  have htrace : WordTrace (prefixWord ++ tailWord_2732673) baseStart_2732673 baseEnd_2732673 := by
    simpa [prefixWord, tailWord_2732673, baseEnd_2732673] using wordTrace_append hprefix tailTrace_2732673
  have hstable : (prefixWord ++ tailWord_2732673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732673).length < 2 ^ (prefixWord ++ tailWord_2732673).sum := by decide
  have hdescent : baseEnd_2732673 < baseStart_2732673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732692 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2732692 : Nat := 118140960795 + 2732692 * 2 ^ 59
def prefixEnd_2732692 : Nat := 4983230072969 + 3 ^ 40 * 2732692 * 2
def baseEnd_2732692 : Nat := 935456317797551709121723

theorem tailTrace_2732692 : CollatzResearch.WordTrace tailWord_2732692 prefixEnd_2732692 935456317797551709121723 := by
  unfold tailWord_2732692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49834732707965532741148165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66446310277287376988197553 49834732707965532741148165)
  ·
    refine ⟨9344012382743537388965281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49834732707965532741148165 9344012382743537388965281)
    ·
      refine ⟨7008009287057653041723961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9344012382743537388965281 7008009287057653041723961)
      ·
        refine ⟨5256006965293239781292971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7008009287057653041723961 5256006965293239781292971)
        ·
          refine ⟨7884010447939859671939457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256006965293239781292971 7884010447939859671939457)
          ·
            refine ⟨5913007835954894753954593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884010447939859671939457 5913007835954894753954593)
            ·
              refine ⟨4434755876966171065465945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5913007835954894753954593 4434755876966171065465945)
              ·
                refine ⟨3326066907724628299099459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434755876966171065465945 3326066907724628299099459)
                ·
                  refine ⟨4989100361586942448649189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326066907724628299099459 4989100361586942448649189)
                  ·
                    refine ⟨935456317797551709121723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989100361586942448649189 935456317797551709121723)
                    ·
                      rfl

theorem cell22_2732692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2732692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732692 prefixEnd_2732692 := by exact prefixLift 2732692
  have htrace : WordTrace (prefixWord ++ tailWord_2732692) baseStart_2732692 baseEnd_2732692 := by
    simpa [prefixWord, tailWord_2732692, baseEnd_2732692] using wordTrace_append hprefix tailTrace_2732692
  have hstable : (prefixWord ++ tailWord_2732692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732692).length < 2 ^ (prefixWord ++ tailWord_2732692).sum := by decide
  have hdescent : baseEnd_2732692 < baseStart_2732692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732778 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2732778 : Nat := 118140960795 + 2732778 * 2 ^ 59
def prefixEnd_2732778 : Nat := 4983230072969 + 3 ^ 40 * 2732778 * 2
def baseEnd_2732778 : Nat := 935485757355076151471459

theorem tailTrace_2732778 : CollatzResearch.WordTrace tailWord_2732778 prefixEnd_2732778 935485757355076151471459 := by
  unfold tailWord_2732778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918150523404875542481747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66448401395746334779951325 24918150523404875542481747)
  ·
    refine ⟨37377225785107313313722621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24918150523404875542481747 37377225785107313313722621)
    ·
      refine ⟨14016459669415242492645983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37377225785107313313722621 14016459669415242492645983)
      ·
        refine ⟨21024689504122863738968975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14016459669415242492645983 21024689504122863738968975)
        ·
          refine ⟨31537034256184295608453463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21024689504122863738968975 31537034256184295608453463)
          ·
            refine ⟨47305551384276443412680195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31537034256184295608453463 47305551384276443412680195)
            ·
              refine ⟨70958327076414665119020293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47305551384276443412680195 70958327076414665119020293)
              ·
                refine ⟨13304686326827749709816305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70958327076414665119020293 13304686326827749709816305)
                ·
                  refine ⟨9978514745120812282362229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13304686326827749709816305 9978514745120812282362229)
                  ·
                    refine ⟨935485757355076151471459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9978514745120812282362229 935485757355076151471459)
                    ·
                      rfl

theorem cell22_2732778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2732778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732778 prefixEnd_2732778 := by exact prefixLift 2732778
  have htrace : WordTrace (prefixWord ++ tailWord_2732778) baseStart_2732778 baseEnd_2732778 := by
    simpa [prefixWord, tailWord_2732778, baseEnd_2732778] using wordTrace_append hprefix tailTrace_2732778
  have hstable : (prefixWord ++ tailWord_2732778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732778).length < 2 ^ (prefixWord ++ tailWord_2732778).sum := by decide
  have hdescent : baseEnd_2732778 < baseStart_2732778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732808 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_2732808 : Nat := 118140960795 + 2732808 * 2 ^ 59
def prefixEnd_2732808 : Nat := 4983230072969 + 3 ^ 40 * 2732808 * 2
def baseEnd_2732808 : Nat := 311832008989388691073789

theorem tailTrace_2732808 : CollatzResearch.WordTrace tailWord_2732808 prefixEnd_2732808 311832008989388691073789 := by
  unfold tailWord_2732808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49836848141755408646759539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66449130855673878195679385 49836848141755408646759539)
  ·
    refine ⟨74755272212633112970139309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49836848141755408646759539 74755272212633112970139309)
    ·
      refine ⟨28033227079737417363802241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74755272212633112970139309 28033227079737417363802241)
      ·
        refine ⟨21024920309803063022851681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28033227079737417363802241 21024920309803063022851681)
        ·
          refine ⟨15768690232352297267138761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21024920309803063022851681 15768690232352297267138761)
          ·
            refine ⟨11826517674264222950354071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15768690232352297267138761 11826517674264222950354071)
            ·
              refine ⟨17739776511396334425531107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11826517674264222950354071 17739776511396334425531107)
              ·
                refine ⟨26609664767094501638296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17739776511396334425531107 26609664767094501638296661)
                ·
                  refine ⟨311832008989388691073789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26609664767094501638296661 311832008989388691073789)
                  ·
                    rfl

theorem cell22_2732808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_2732808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732808 prefixEnd_2732808 := by exact prefixLift 2732808
  have htrace : WordTrace (prefixWord ++ tailWord_2732808) baseStart_2732808 baseEnd_2732808 := by
    simpa [prefixWord, tailWord_2732808, baseEnd_2732808] using wordTrace_append hprefix tailTrace_2732808
  have hstable : (prefixWord ++ tailWord_2732808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732808).length < 2 ^ (prefixWord ++ tailWord_2732808).sum := by decide
  have hdescent : baseEnd_2732808 < baseStart_2732808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732810 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_2732810 : Nat := 118140960795 + 2732810 * 2 ^ 59
def prefixEnd_2732810 : Nat := 4983230072969 + 3 ^ 40 * 2732810 * 2
def baseEnd_2732810 : Nat := 935496711609038734671361

theorem tailTrace_2732810 : CollatzResearch.WordTrace tailWord_2732810 prefixEnd_2732810 935496711609038734671361 := by
  unfold tailWord_2732810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918442307375892908772971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66449179486335714423394589 24918442307375892908772971)
  ·
    refine ⟨37377663461063839363159457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24918442307375892908772971 37377663461063839363159457)
    ·
      refine ⟨28033247595797879522369593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37377663461063839363159457 28033247595797879522369593)
      ·
        refine ⟨21024935696848409641777195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28033247595797879522369593 21024935696848409641777195)
        ·
          refine ⟨31537403545272614462665793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21024935696848409641777195 31537403545272614462665793)
          ·
            refine ⟨23653052658954460846999345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31537403545272614462665793 23653052658954460846999345)
            ·
              refine ⟨17739789494215845635249509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23653052658954460846999345 17739789494215845635249509)
              ·
                refine ⟨3326210530165471056609283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17739789494215845635249509 3326210530165471056609283)
                ·
                  refine ⟨4989315795248206584913925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326210530165471056609283 4989315795248206584913925)
                  ·
                    refine ⟨935496711609038734671361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989315795248206584913925 935496711609038734671361)
                    ·
                      rfl

theorem cell22_2732810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_2732810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732810 prefixEnd_2732810 := by exact prefixLift 2732810
  have htrace : WordTrace (prefixWord ++ tailWord_2732810) baseStart_2732810 baseEnd_2732810 := by
    simpa [prefixWord, tailWord_2732810, baseEnd_2732810] using wordTrace_append hprefix tailTrace_2732810
  have hstable : (prefixWord ++ tailWord_2732810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732810).length < 2 ^ (prefixWord ++ tailWord_2732810).sum := by decide
  have hdescent : baseEnd_2732810 < baseStart_2732810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732962 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2732962 : Nat := 118140960795 + 2732962 * 2 ^ 59
def prefixEnd_2732962 : Nat := 4983230072969 + 3 ^ 40 * 2732962 * 2
def baseEnd_2732962 : Nat := 935548744315361004870895

theorem tailTrace_2732962 : CollatzResearch.WordTrace tailWord_2732962 prefixEnd_2732962 935548744315361004870895 := by
  unfold tailWord_2732962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919828281238225398656285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66452875416635267729750093 24919828281238225398656285)
  ·
    refine ⟨9344935605464334524496107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24919828281238225398656285 9344935605464334524496107)
    ·
      refine ⟨14017403408196501786744161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344935605464334524496107 14017403408196501786744161)
      ·
        refine ⟨10513052556147376340058121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14017403408196501786744161 10513052556147376340058121)
        ·
          refine ⟨7884789417110532255043591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10513052556147376340058121 7884789417110532255043591)
          ·
            refine ⟨11827184125665798382565387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7884789417110532255043591 11827184125665798382565387)
            ·
              refine ⟨17740776188498697573848081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11827184125665798382565387 17740776188498697573848081)
              ·
                refine ⟨13305582141374023180386061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17740776188498697573848081 13305582141374023180386061)
                ·
                  refine ⟨4989593303015258692644773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13305582141374023180386061 4989593303015258692644773)
                  ·
                    refine ⟨935548744315361004870895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989593303015258692644773 935548744315361004870895)
                    ·
                      rfl

theorem cell22_2732962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2732962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732962 prefixEnd_2732962 := by exact prefixLift 2732962
  have htrace : WordTrace (prefixWord ++ tailWord_2732962) baseStart_2732962 baseEnd_2732962 := by
    simpa [prefixWord, tailWord_2732962, baseEnd_2732962] using wordTrace_append hprefix tailTrace_2732962
  have hstable : (prefixWord ++ tailWord_2732962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732962).length < 2 ^ (prefixWord ++ tailWord_2732962).sum := by decide
  have hdescent : baseEnd_2732962 < baseStart_2732962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732977 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 6]
def baseStart_2732977 : Nat := 118140960795 + 2732977 * 2 ^ 59
def prefixEnd_2732977 : Nat := 4983230072969 + 3 ^ 40 * 2732977 * 2
def baseEnd_2732977 : Nat := 311851293040635321915283

theorem tailTrace_2732977 : CollatzResearch.WordTrace tailWord_2732977 prefixEnd_2732977 311851293040635321915283 := by
  unfold tailWord_2732977
  simp only [CollatzResearch.WordTrace]
  refine ⟨99679860219898559156421185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66453240146599039437614123 99679860219898559156421185)
  ·
    refine ⟨74759895164923919367315889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99679860219898559156421185 74759895164923919367315889)
    ·
      refine ⟨56069921373692939525486917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74759895164923919367315889 56069921373692939525486917)
      ·
        refine ⟨10513110257567426161028797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56069921373692939525486917 10513110257567426161028797)
        ·
          refine ⟨3942416346587784810385799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10513110257567426161028797 3942416346587784810385799)
          ·
            refine ⟨5913624519881677215578699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942416346587784810385799 5913624519881677215578699)
            ·
              refine ⟨8870436779822515823368049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913624519881677215578699 8870436779822515823368049)
              ·
                refine ⟨6652827584866886867526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8870436779822515823368049 6652827584866886867526037)
                ·
                  refine ⟨311851293040635321915283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6652827584866886867526037 311851293040635321915283)
                  ·
                    rfl

theorem cell22_2732977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_2732977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732977 prefixEnd_2732977 := by exact prefixLift 2732977
  have htrace : WordTrace (prefixWord ++ tailWord_2732977) baseStart_2732977 baseEnd_2732977 := by
    simpa [prefixWord, tailWord_2732977, baseEnd_2732977] using wordTrace_append hprefix tailTrace_2732977
  have hstable : (prefixWord ++ tailWord_2732977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732977).length < 2 ^ (prefixWord ++ tailWord_2732977).sum := by decide
  have hdescent : baseEnd_2732977 < baseStart_2732977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2732996 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2732996 : Nat := 118140960795 + 2732996 * 2 ^ 59
def prefixEnd_2732996 : Nat := 4983230072969 + 3 ^ 40 * 2732996 * 2
def baseEnd_2732996 : Nat := 935560383210196249520791

theorem tailTrace_2732996 : CollatzResearch.WordTrace tailWord_2732996 prefixEnd_2732996 935560383210196249520791 := by
  unfold tailWord_2732996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49840276603414862700681421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66453702137886483600908561 49840276603414862700681421)
  ·
    refine ⟨18690103726280573512755533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49840276603414862700681421 18690103726280573512755533)
    ·
      refine ⟨7008788897355215067283325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18690103726280573512755533 7008788897355215067283325)
      ·
        refine ⟨2628295836508205650231247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7008788897355215067283325 2628295836508205650231247)
        ·
          refine ⟨3942443754762308475346871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628295836508205650231247 3942443754762308475346871)
          ·
            refine ⟨5913665632143462713020307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942443754762308475346871 5913665632143462713020307)
            ·
              refine ⟨8870498448215194069530461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913665632143462713020307 8870498448215194069530461)
              ·
                refine ⟨3326436918080697776073923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8870498448215194069530461 3326436918080697776073923)
                ·
                  refine ⟨4989655377121046664110885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326436918080697776073923 4989655377121046664110885)
                  ·
                    refine ⟨935560383210196249520791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989655377121046664110885 935560383210196249520791)
                    ·
                      rfl

theorem cell22_2732996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2732996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2732996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2732996 prefixEnd_2732996 := by exact prefixLift 2732996
  have htrace : WordTrace (prefixWord ++ tailWord_2732996) baseStart_2732996 baseEnd_2732996 := by
    simpa [prefixWord, tailWord_2732996, baseEnd_2732996] using wordTrace_append hprefix tailTrace_2732996
  have hstable : (prefixWord ++ tailWord_2732996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2732996).length < 2 ^ (prefixWord ++ tailWord_2732996).sum := by decide
  have hdescent : baseEnd_2732996 < baseStart_2732996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2732996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733026 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2733026 : Nat := 118140960795 + 2733026 * 2 ^ 59
def prefixEnd_2733026 : Nat := 4983230072969 + 3 ^ 40 * 2733026 * 2
def baseEnd_2733026 : Nat := 935570652823286171270699

theorem tailTrace_2733026 : CollatzResearch.WordTrace tailWord_2733026 prefixEnd_2733026 935570652823286171270699 := by
  unfold tailWord_2733026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24920411849180260131238733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66454431597814027016636621 24920411849180260131238733)
  ·
    refine ⟨9345154443442597549214525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24920411849180260131238733 9345154443442597549214525)
    ·
      refine ⟨3504432916290974080955447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9345154443442597549214525 3504432916290974080955447)
      ·
        refine ⟨5256649374436461121433171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504432916290974080955447 5256649374436461121433171)
        ·
          refine ⟨7884974061654691682149757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256649374436461121433171 7884974061654691682149757)
          ·
            refine ⟨2956865273120509380806159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7884974061654691682149757 2956865273120509380806159)
            ·
              refine ⟨4435297909680764071209239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956865273120509380806159 4435297909680764071209239)
              ·
                refine ⟨6652946864521146106813859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435297909680764071209239 6652946864521146106813859)
                ·
                  refine ⟨9979420296781719160220789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6652946864521146106813859 9979420296781719160220789)
                  ·
                    refine ⟨935570652823286171270699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9979420296781719160220789 935570652823286171270699)
                    ·
                      rfl

theorem cell22_2733026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2733026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733026 prefixEnd_2733026 := by exact prefixLift 2733026
  have htrace : WordTrace (prefixWord ++ tailWord_2733026) baseStart_2733026 baseEnd_2733026 := by
    simpa [prefixWord, tailWord_2733026, baseEnd_2733026] using wordTrace_append hprefix tailTrace_2733026
  have hstable : (prefixWord ++ tailWord_2733026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733026).length < 2 ^ (prefixWord ++ tailWord_2733026).sum := by decide
  have hdescent : baseEnd_2733026 < baseStart_2733026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733045 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 4]
def baseStart_2733045 : Nat := 118140960795 + 2733045 * 2 ^ 59
def prefixEnd_2733045 : Nat := 4983230072969 + 3 ^ 40 * 2733045 * 2
def baseEnd_2733045 : Nat := 311859052303858818348547

theorem tailTrace_2733045 : CollatzResearch.WordTrace tailWord_2733045 prefixEnd_2733045 311859052303858818348547 := by
  unfold tailWord_2733045
  simp only [CollatzResearch.WordTrace]
  refine ⟨99682340383652206769896589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66454893589101471179931059 99682340383652206769896589)
  ·
    refine ⟨37380877643869577538711221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99682340383652206769896589 37380877643869577538711221)
    ·
      refine ⟨3504457279112772894254177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37380877643869577538711221 3504457279112772894254177)
      ·
        refine ⟨2628342959334579670690633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3504457279112772894254177 2628342959334579670690633)
        ·
          refine ⟨1971257219500934753017975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2628342959334579670690633 1971257219500934753017975)
          ·
            refine ⟨2956885829251402129526963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971257219500934753017975 2956885829251402129526963)
            ·
              refine ⟨4435328743877103194290445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956885829251402129526963 4435328743877103194290445)
              ·
                refine ⟨1663248278953913697858917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4435328743877103194290445 1663248278953913697858917)
                ·
                  refine ⟨311859052303858818348547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663248278953913697858917 311859052303858818348547)
                  ·
                    rfl

theorem cell22_2733045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_2733045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733045 prefixEnd_2733045 := by exact prefixLift 2733045
  have htrace : WordTrace (prefixWord ++ tailWord_2733045) baseStart_2733045 baseEnd_2733045 := by
    simpa [prefixWord, tailWord_2733045, baseEnd_2733045] using wordTrace_append hprefix tailTrace_2733045
  have hstable : (prefixWord ++ tailWord_2733045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733045).length < 2 ^ (prefixWord ++ tailWord_2733045).sum := by decide
  have hdescent : baseEnd_2733045 < baseStart_2733045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733065 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_2733065 : Nat := 118140960795 + 2733065 * 2 ^ 59
def prefixEnd_2733065 : Nat := 4983230072969 + 3 ^ 40 * 2733065 * 2
def baseEnd_2733065 : Nat := 935584003320303069545579

theorem tailTrace_2733065 : CollatzResearch.WordTrace tailWord_2733065 prefixEnd_2733065 935584003320303069545579 := by
  unfold tailWord_2733065
  simp only [CollatzResearch.WordTrace]
  refine ⟨99683069843579750185624649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66455379895719833457083099 99683069843579750185624649)
  ·
    refine ⟨74762302382684812639218487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99683069843579750185624649 74762302382684812639218487)
    ·
      refine ⟨112143453574027218958827731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74762302382684812639218487 112143453574027218958827731)
      ·
        refine ⟨168215180361040828438241597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112143453574027218958827731 168215180361040828438241597)
        ·
          refine ⟨63080692635390310664340599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168215180361040828438241597 63080692635390310664340599)
          ·
            refine ⟨94621038953085465996510899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63080692635390310664340599 94621038953085465996510899)
            ·
              refine ⟨141931558429628198994766349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94621038953085465996510899 141931558429628198994766349)
              ·
                refine ⟨53224334411110574623037381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141931558429628198994766349 53224334411110574623037381)
                ·
                  refine ⟨9979562702083232741819509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53224334411110574623037381 9979562702083232741819509)
                  ·
                    refine ⟨935584003320303069545579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9979562702083232741819509 935584003320303069545579)
                    ·
                      rfl

theorem cell22_2733065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_2733065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733065 prefixEnd_2733065 := by exact prefixLift 2733065
  have htrace : WordTrace (prefixWord ++ tailWord_2733065) baseStart_2733065 baseEnd_2733065 := by
    simpa [prefixWord, tailWord_2733065, baseEnd_2733065] using wordTrace_append hprefix tailTrace_2733065
  have hstable : (prefixWord ++ tailWord_2733065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733065).length < 2 ^ (prefixWord ++ tailWord_2733065).sum := by decide
  have hdescent : baseEnd_2733065 < baseStart_2733065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733084 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_2733084 : Nat := 118140960795 + 2733084 * 2 ^ 59
def prefixEnd_2733084 : Nat := 4983230072969 + 3 ^ 40 * 2733084 * 2
def baseEnd_2733084 : Nat := 311863502469531117773507

theorem tailTrace_2733084 : CollatzResearch.WordTrace tailWord_2733084 prefixEnd_2733084 311863502469531117773507 := by
  unfold tailWord_2733084
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841881415255458215283153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66455841887007277620377537 49841881415255458215283153)
  ·
    refine ⟨37381411061441593661462365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49841881415255458215283153 37381411061441593661462365)
    ·
      refine ⟨14018029148040597623048387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37381411061441593661462365 14018029148040597623048387)
      ·
        refine ⟨21027043722060896434572581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018029148040597623048387 21027043722060896434572581)
        ·
          refine ⟨3942570697886418081482359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21027043722060896434572581 3942570697886418081482359)
          ·
            refine ⟨5913856046829627122223539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942570697886418081482359 5913856046829627122223539)
            ·
              refine ⟨8870784070244440683335309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913856046829627122223539 8870784070244440683335309)
              ·
                refine ⟨3326544026341665256250741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8870784070244440683335309 3326544026341665256250741)
                ·
                  refine ⟨311863502469531117773507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326544026341665256250741 311863502469531117773507)
                  ·
                    rfl

theorem cell22_2733084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_2733084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733084 prefixEnd_2733084 := by exact prefixLift 2733084
  have htrace : WordTrace (prefixWord ++ tailWord_2733084) baseStart_2733084 baseEnd_2733084 := by
    simpa [prefixWord, tailWord_2733084, baseEnd_2733084] using wordTrace_append hprefix tailTrace_2733084
  have hstable : (prefixWord ++ tailWord_2733084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733084).length < 2 ^ (prefixWord ++ tailWord_2733084).sum := by decide
  have hdescent : baseEnd_2733084 < baseStart_2733084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733144 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_2733144 : Nat := 118140960795 + 2733144 * 2 ^ 59
def prefixEnd_2733144 : Nat := 4983230072969 + 3 ^ 40 * 2733144 * 2
def baseEnd_2733144 : Nat := 935611046634773196820337

theorem tailTrace_2733144 : CollatzResearch.WordTrace tailWord_2733144 prefixEnd_2733144 935611046634773196820337 := by
  unfold tailWord_2733144
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842975605146773338875243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66457300806862364451833657 49842975605146773338875243)
  ·
    refine ⟨74764463407720160008312865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49842975605146773338875243 74764463407720160008312865)
    ·
      refine ⟨56073347555790120006234649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74764463407720160008312865 56073347555790120006234649)
      ·
        refine ⟨42055010666842590004675987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56073347555790120006234649 42055010666842590004675987)
        ·
          refine ⟨63082516000263885007013981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42055010666842590004675987 63082516000263885007013981)
          ·
            refine ⟨23655943500098956877630243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63082516000263885007013981 23655943500098956877630243)
            ·
              refine ⟨35483915250148435316445365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23655943500098956877630243 35483915250148435316445365)
              ·
                refine ⟨3326617054701415810916753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35483915250148435316445365 3326617054701415810916753)
                ·
                  refine ⟨2494962791026061858187565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3326617054701415810916753 2494962791026061858187565)
                  ·
                    refine ⟨935611046634773196820337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494962791026061858187565 935611046634773196820337)
                    ·
                      rfl

theorem cell22_2733144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_2733144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733144 prefixEnd_2733144 := by exact prefixLift 2733144
  have htrace : WordTrace (prefixWord ++ tailWord_2733144) baseStart_2733144 baseEnd_2733144 := by
    simpa [prefixWord, tailWord_2733144, baseEnd_2733144] using wordTrace_append hprefix tailTrace_2733144
  have hstable : (prefixWord ++ tailWord_2733144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733144).length < 2 ^ (prefixWord ++ tailWord_2733144).sum := by decide
  have hdescent : baseEnd_2733144 < baseStart_2733144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733159 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2733159 : Nat := 118140960795 + 2733159 * 2 ^ 59
def prefixEnd_2733159 : Nat := 4983230072969 + 3 ^ 40 * 2733159 * 2
def baseEnd_2733159 : Nat := 935616181441318157695291

theorem tailTrace_2733159 : CollatzResearch.WordTrace tailWord_2733159 prefixEnd_2733159 935616181441318157695291 := by
  unfold tailWord_2733159
  simp only [CollatzResearch.WordTrace]
  refine ⟨99686498305239204239546531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66457665536826136159697687 99686498305239204239546531)
  ·
    refine ⟨149529747457858806359319797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99686498305239204239546531 149529747457858806359319797)
    ·
      refine ⟨14018413824174263096186231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149529747457858806359319797 14018413824174263096186231)
      ·
        refine ⟨21027620736261394644279347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018413824174263096186231 21027620736261394644279347)
        ·
          refine ⟨31541431104392091966419021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21027620736261394644279347 31541431104392091966419021)
          ·
            refine ⟨11828036664147034487407133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31541431104392091966419021 11828036664147034487407133)
            ·
              refine ⟨4435513749055137932777675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11828036664147034487407133 4435513749055137932777675)
              ·
                refine ⟨6653270623582706899166513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435513749055137932777675 6653270623582706899166513)
                ·
                  refine ⟨4989952967687030174374885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653270623582706899166513 4989952967687030174374885)
                  ·
                    refine ⟨935616181441318157695291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4989952967687030174374885 935616181441318157695291)
                    ·
                      rfl

theorem cell22_2733159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2733159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733159 prefixEnd_2733159 := by exact prefixLift 2733159
  have htrace : WordTrace (prefixWord ++ tailWord_2733159) baseStart_2733159 baseEnd_2733159 := by
    simpa [prefixWord, tailWord_2733159, baseEnd_2733159] using wordTrace_append hprefix tailTrace_2733159
  have hstable : (prefixWord ++ tailWord_2733159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733159).length < 2 ^ (prefixWord ++ tailWord_2733159).sum := by decide
  have hdescent : baseEnd_2733159 < baseStart_2733159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733279 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 6, 3]
def baseStart_2733279 : Nat := 118140960795 + 2733279 * 2 ^ 59
def prefixEnd_2733279 : Nat := 4983230072969 + 3 ^ 40 * 2733279 * 2
def baseEnd_2733279 : Nat := 935657259893677844694923

theorem tailTrace_2733279 : CollatzResearch.WordTrace tailWord_2733279 prefixEnd_2733279 935657259893677844694923 := by
  unfold tailWord_2733279
  simp only [CollatzResearch.WordTrace]
  refine ⟨99690875064804464733914891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66460583376536309822609927 99690875064804464733914891)
  ·
    refine ⟨149536312597206697100872337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99690875064804464733914891 149536312597206697100872337)
    ·
      refine ⟨112152234447905022825654253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149536312597206697100872337 112152234447905022825654253)
      ·
        refine ⟨42057087917964383559620345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112152234447905022825654253 42057087917964383559620345)
        ·
          refine ⟨31542815938473287669715259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42057087917964383559620345 31542815938473287669715259)
          ·
            refine ⟨47314223907709931504572889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31542815938473287669715259 47314223907709931504572889)
            ·
              refine ⟨35485667930782448628429667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47314223907709931504572889 35485667930782448628429667)
              ·
                refine ⟨53228501896173672942644501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35485667930782448628429667 53228501896173672942644501)
                ·
                  refine ⟨2495086026383140919186461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53228501896173672942644501 2495086026383140919186461)
                  ·
                    refine ⟨935657259893677844694923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495086026383140919186461 935657259893677844694923)
                    ·
                      rfl

theorem cell22_2733279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_2733279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733279 prefixEnd_2733279 := by exact prefixLift 2733279
  have htrace : WordTrace (prefixWord ++ tailWord_2733279) baseStart_2733279 baseEnd_2733279 := by
    simpa [prefixWord, tailWord_2733279, baseEnd_2733279] using wordTrace_append hprefix tailTrace_2733279
  have hstable : (prefixWord ++ tailWord_2733279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733279).length < 2 ^ (prefixWord ++ tailWord_2733279).sum := by decide
  have hdescent : baseEnd_2733279 < baseStart_2733279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733292 : List Nat := [2, 2, 1, 1, 2, 14]
def baseStart_2733292 : Nat := 118140960795 + 2733292 * 2 ^ 59
def prefixEnd_2733292 : Nat := 4983230072969 + 3 ^ 40 * 2733292 * 2
def baseEnd_2733292 : Nat := 11551379136535186964443

theorem tailTrace_2733292 : CollatzResearch.WordTrace tailWord_2733292 prefixEnd_2733292 11551379136535186964443 := by
  unfold tailWord_2733292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49845674606878683977069065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66460899475838245302758753 49845674606878683977069065)
  ·
    refine ⟨37384255955159012982801799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49845674606878683977069065 37384255955159012982801799)
    ·
      refine ⟨56076383932738519474202699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37384255955159012982801799 56076383932738519474202699)
      ·
        refine ⟨84114575899107779211304049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56076383932738519474202699 84114575899107779211304049)
        ·
          refine ⟨63085931924330834408478037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84114575899107779211304049 63085931924330834408478037)
          ·
            refine ⟨11551379136535186964443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 63085931924330834408478037 11551379136535186964443)
            ·
              rfl

theorem cell22_2733292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 14].length) (baseStart_2733292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733292 prefixEnd_2733292 := by exact prefixLift 2733292
  have htrace : WordTrace (prefixWord ++ tailWord_2733292) baseStart_2733292 baseEnd_2733292 := by
    simpa [prefixWord, tailWord_2733292, baseEnd_2733292] using wordTrace_append hprefix tailTrace_2733292
  have hstable : (prefixWord ++ tailWord_2733292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733292).length < 2 ^ (prefixWord ++ tailWord_2733292).sum := by decide
  have hdescent : baseEnd_2733292 < baseStart_2733292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733298 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_2733298 : Nat := 118140960795 + 2733298 * 2 ^ 59
def prefixEnd_2733298 : Nat := 4983230072969 + 3 ^ 40 * 2733298 * 2
def baseEnd_2733298 : Nat := 311887921327322709489955

theorem tailTrace_2733298 : CollatzResearch.WordTrace tailWord_2733298 prefixEnd_2733298 311887921327322709489955 := by
  unfold tailWord_2733298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24922892012933907744714137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66461045367823753985904365 24922892012933907744714137)
  ·
    refine ⟨18692169009700430808535603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24922892012933907744714137 18692169009700430808535603)
    ·
      refine ⟨28038253514550646212803405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18692169009700430808535603 28038253514550646212803405)
      ·
        refine ⟨10514345067956492329801277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28038253514550646212803405 10514345067956492329801277)
        ·
          refine ⟨3942879400483684623675479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10514345067956492329801277 3942879400483684623675479)
          ·
            refine ⟨5914319100725526935513219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942879400483684623675479 5914319100725526935513219)
            ·
              refine ⟨8871478651088290403269829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914319100725526935513219 8871478651088290403269829)
              ·
                refine ⟨1663402247079054450613093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8871478651088290403269829 1663402247079054450613093)
                ·
                  refine ⟨311887921327322709489955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663402247079054450613093 311887921327322709489955)
                  ·
                    rfl

theorem cell22_2733298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_2733298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733298 prefixEnd_2733298 := by exact prefixLift 2733298
  have htrace : WordTrace (prefixWord ++ tailWord_2733298) baseStart_2733298 baseEnd_2733298 := by
    simpa [prefixWord, tailWord_2733298, baseEnd_2733298] using wordTrace_append hprefix tailTrace_2733298
  have hstable : (prefixWord ++ tailWord_2733298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733298).length < 2 ^ (prefixWord ++ tailWord_2733298).sum := by decide
  have hdescent : baseEnd_2733298 < baseStart_2733298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733326 : List Nat := [4, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2733326 : Nat := 118140960795 + 2733326 * 2 ^ 59
def prefixEnd_2733326 : Nat := 4983230072969 + 3 ^ 40 * 2733326 * 2
def baseEnd_2733326 : Nat := 103963705439353932085531

theorem tailTrace_2733326 : CollatzResearch.WordTrace tailWord_2733326 prefixEnd_2733326 103963705439353932085531 := by
  unfold tailWord_2733326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12461573661954273970109479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66461726197089461173917221 12461573661954273970109479)
  ·
    refine ⟨18692360492931410955164219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12461573661954273970109479 18692360492931410955164219)
    ·
      refine ⟨28038540739397116432746329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18692360492931410955164219 28038540739397116432746329)
      ·
        refine ⟨21028905554547837324559747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28038540739397116432746329 21028905554547837324559747)
        ·
          refine ⟨31543358331821755986839621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21028905554547837324559747 31543358331821755986839621)
          ·
            refine ⟨5914379687216579247532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31543358331821755986839621 5914379687216579247532429)
            ·
              refine ⟨2217892382706217217824661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5914379687216579247532429 2217892382706217217824661)
              ·
                refine ⟨103963705439353932085531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2217892382706217217824661 103963705439353932085531)
                ·
                  rfl

theorem cell22_2733326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2733326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733326 prefixEnd_2733326 := by exact prefixLift 2733326
  have htrace : WordTrace (prefixWord ++ tailWord_2733326) baseStart_2733326 baseEnd_2733326 := by
    simpa [prefixWord, tailWord_2733326, baseEnd_2733326] using wordTrace_append hprefix tailTrace_2733326
  have hstable : (prefixWord ++ tailWord_2733326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733326).length < 2 ^ (prefixWord ++ tailWord_2733326).sum := by decide
  have hdescent : baseEnd_2733326 < baseStart_2733326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733401 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_2733401 : Nat := 118140960795 + 2733401 * 2 ^ 59
def prefixEnd_2733401 : Nat := 4983230072969 + 3 ^ 40 * 2733401 * 2
def baseEnd_2733401 : Nat := 935699022986910193144549

theorem tailTrace_2733401 : CollatzResearch.WordTrace tailWord_2733401 prefixEnd_2733401 935699022986910193144549 := by
  unfold tailWord_2733401
  simp only [CollatzResearch.WordTrace]
  refine ⟨99695324770362479569856057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66463549846908319713237371 99695324770362479569856057)
  ·
    refine ⟨74771493577771859677392043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99695324770362479569856057 74771493577771859677392043)
    ·
      refine ⟨112157240366657789516088065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74771493577771859677392043 112157240366657789516088065)
      ·
        refine ⟨84117930274993342137066049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112157240366657789516088065 84117930274993342137066049)
        ·
          refine ⟨63088447706245006602799537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84117930274993342137066049 63088447706245006602799537)
          ·
            refine ⟨47316335779683754952099653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63088447706245006602799537 47316335779683754952099653)
            ·
              refine ⟨8871812958690704053518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47316335779683754952099653 8871812958690704053518685)
              ·
                refine ⟨3326929859509014020069507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8871812958690704053518685 3326929859509014020069507)
                ·
                  refine ⟨4990394789263521030104261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326929859509014020069507 4990394789263521030104261)
                  ·
                    refine ⟨935699022986910193144549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4990394789263521030104261 935699022986910193144549)
                    ·
                      rfl

theorem cell22_2733401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_2733401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733401 prefixEnd_2733401 := by exact prefixLift 2733401
  have htrace : WordTrace (prefixWord ++ tailWord_2733401) baseStart_2733401 baseEnd_2733401 := by
    simpa [prefixWord, tailWord_2733401, baseEnd_2733401] using wordTrace_append hprefix tailTrace_2733401
  have hstable : (prefixWord ++ tailWord_2733401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733401).length < 2 ^ (prefixWord ++ tailWord_2733401).sum := by decide
  have hdescent : baseEnd_2733401 < baseStart_2733401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733422 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_2733422 : Nat := 118140960795 + 2733422 * 2 ^ 59
def prefixEnd_2733422 : Nat := 4983230072969 + 3 ^ 40 * 2733422 * 2
def baseEnd_2733422 : Nat := 311902070572024379456495

theorem tailTrace_2733422 : CollatzResearch.WordTrace tailWord_2733422 prefixEnd_2733422 311902070572024379456495 := by
  unfold tailWord_2733422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462011337910800019546315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66464060468857600104247013 12462011337910800019546315)
  ·
    refine ⟨18693017006866200029319473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12462011337910800019546315 18693017006866200029319473)
    ·
      refine ⟨14019762755149650021989605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18693017006866200029319473 14019762755149650021989605)
      ·
        refine ⟨2628705516590559379123051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14019762755149650021989605 2628705516590559379123051)
        ·
          refine ⟨3943058274885839068684577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628705516590559379123051 3943058274885839068684577)
          ·
            refine ⟨2957293706164379301513433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3943058274885839068684577 2957293706164379301513433)
            ·
              refine ⟨2217970279623284476135075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957293706164379301513433 2217970279623284476135075)
              ·
                refine ⟨3326955419434926714202613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217970279623284476135075 3326955419434926714202613)
                ·
                  refine ⟨311902070572024379456495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3326955419434926714202613 311902070572024379456495)
                  ·
                    rfl

theorem cell22_2733422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_2733422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733422 prefixEnd_2733422 := by exact prefixLift 2733422
  have htrace : WordTrace (prefixWord ++ tailWord_2733422) baseStart_2733422 baseEnd_2733422 := by
    simpa [prefixWord, tailWord_2733422, baseEnd_2733422] using wordTrace_append hprefix tailTrace_2733422
  have hstable : (prefixWord ++ tailWord_2733422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733422).length < 2 ^ (prefixWord ++ tailWord_2733422).sum := by decide
  have hdescent : baseEnd_2733422 < baseStart_2733422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733493 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2733493 : Nat := 118140960795 + 2733493 * 2 ^ 59
def prefixEnd_2733493 : Nat := 4983230072969 + 3 ^ 40 * 2733493 * 2
def baseEnd_2733493 : Nat := 935730516467052619844267

theorem tailTrace_2733493 : CollatzResearch.WordTrace tailWord_2733493 prefixEnd_2733493 935730516467052619844267 := by
  unfold tailWord_2733493
  simp only [CollatzResearch.WordTrace]
  refine ⟨99698680286029179282205133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66465786857352786188136755 99698680286029179282205133)
  ·
    refine ⟨37387005107260942230826925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99698680286029179282205133 37387005107260942230826925)
    ·
      refine ⟨14020126915222853336560097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37387005107260942230826925 14020126915222853336560097)
      ·
        refine ⟨10515095186417140002420073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14020126915222853336560097 10515095186417140002420073)
        ·
          refine ⟨7886321389812855001815055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515095186417140002420073 7886321389812855001815055)
          ·
            refine ⟨11829482084719282502722583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7886321389812855001815055 11829482084719282502722583)
            ·
              refine ⟨17744223127078923754083875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829482084719282502722583 17744223127078923754083875)
              ·
                refine ⟨26616334690618385631125813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17744223127078923754083875 26616334690618385631125813)
                ·
                  refine ⟨2495281377245473652918045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26616334690618385631125813 2495281377245473652918045)
                  ·
                    refine ⟨935730516467052619844267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495281377245473652918045 935730516467052619844267)
                    ·
                      rfl

theorem cell22_2733493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2733493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733493 prefixEnd_2733493 := by exact prefixLift 2733493
  have htrace : WordTrace (prefixWord ++ tailWord_2733493) baseStart_2733493 baseEnd_2733493 := by
    simpa [prefixWord, tailWord_2733493, baseEnd_2733493] using wordTrace_append hprefix tailTrace_2733493
  have hstable : (prefixWord ++ tailWord_2733493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733493).length < 2 ^ (prefixWord ++ tailWord_2733493).sum := by decide
  have hdescent : baseEnd_2733493 < baseStart_2733493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733536 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_2733536 : Nat := 118140960795 + 2733536 * 2 ^ 59
def prefixEnd_2733536 : Nat := 4983230072969 + 3 ^ 40 * 2733536 * 2
def baseEnd_2733536 : Nat := 935745236245814841019135

theorem tailTrace_2733536 : CollatzResearch.WordTrace tailWord_2733536 prefixEnd_2733536 935745236245814841019135 := by
  unfold tailWord_2733536
  simp only [CollatzResearch.WordTrace]
  refine ⟨49850124312436698813010231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66466832416582265084013641 49850124312436698813010231)
  ·
    refine ⟨74775186468655048219515347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49850124312436698813010231 74775186468655048219515347)
    ·
      refine ⟨112162779702982572329273021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74775186468655048219515347 112162779702982572329273021)
      ·
        refine ⟨42061042388618464623477383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112162779702982572329273021 42061042388618464623477383)
        ·
          refine ⟨63091563582927696935216075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42061042388618464623477383 63091563582927696935216075)
          ·
            refine ⟨94637345374391545402824113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63091563582927696935216075 94637345374391545402824113)
            ·
              refine ⟨70978009030793659052118085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94637345374391545402824113 70978009030793659052118085)
              ·
                refine ⟨13308376693273811072272141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70978009030793659052118085 13308376693273811072272141)
                ·
                  refine ⟨4990641259977679152102053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13308376693273811072272141 4990641259977679152102053)
                  ·
                    refine ⟨935745236245814841019135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4990641259977679152102053 935745236245814841019135)
                    ·
                      rfl

theorem cell22_2733536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_2733536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733536 prefixEnd_2733536 := by exact prefixLift 2733536
  have htrace : WordTrace (prefixWord ++ tailWord_2733536) baseStart_2733536 baseEnd_2733536 := by
    simpa [prefixWord, tailWord_2733536, baseEnd_2733536] using wordTrace_append hprefix tailTrace_2733536
  have hstable : (prefixWord ++ tailWord_2733536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733536).length < 2 ^ (prefixWord ++ tailWord_2733536).sum := by decide
  have hdescent : baseEnd_2733536 < baseStart_2733536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733551 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 6]
def baseStart_2733551 : Nat := 118140960795 + 2733551 * 2 ^ 59
def prefixEnd_2733551 : Nat := 4983230072969 + 3 ^ 40 * 2733551 * 2
def baseEnd_2733551 : Nat := 311916790350786600631363

theorem tailTrace_2733551 : CollatzResearch.WordTrace tailWord_2733551 prefixEnd_2733551 311916790350786600631363 := by
  unfold tailWord_2733551
  simp only [CollatzResearch.WordTrace]
  refine ⟨99700795719819055187816507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66467197146546036791877671 99700795719819055187816507)
  ·
    refine ⟨149551193579728582781724761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99700795719819055187816507 149551193579728582781724761)
    ·
      refine ⟨112163395184796437086293571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149551193579728582781724761 112163395184796437086293571)
      ·
        refine ⟨168245092777194655629440357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112163395184796437086293571 168245092777194655629440357)
        ·
          refine ⟨31545954895723997930520067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168245092777194655629440357 31545954895723997930520067)
          ·
            refine ⟨47318932343585996895780101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31545954895723997930520067 47318932343585996895780101)
            ·
              refine ⟨8872299814422374417958769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47318932343585996895780101 8872299814422374417958769)
              ·
                refine ⟨6654224860816780813469077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8872299814422374417958769 6654224860816780813469077)
                ·
                  refine ⟨311916790350786600631363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6654224860816780813469077 311916790350786600631363)
                  ·
                    rfl

theorem cell22_2733551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_2733551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733551 prefixEnd_2733551 := by exact prefixLift 2733551
  have htrace : WordTrace (prefixWord ++ tailWord_2733551) baseStart_2733551 baseEnd_2733551 := by
    simpa [prefixWord, tailWord_2733551, baseEnd_2733551] using wordTrace_append hprefix tailTrace_2733551
  have hstable : (prefixWord ++ tailWord_2733551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733551).length < 2 ^ (prefixWord ++ tailWord_2733551).sum := by decide
  have hdescent : baseEnd_2733551 < baseStart_2733551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733553 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2733553 : Nat := 118140960795 + 2733553 * 2 ^ 59
def prefixEnd_2733553 : Nat := 4983230072969 + 3 ^ 40 * 2733553 * 2
def baseEnd_2733553 : Nat := 935751055693232463344083

theorem tailTrace_2733553 : CollatzResearch.WordTrace tailWord_2733553 prefixEnd_2733553 935751055693232463344083 := by
  unfold tailWord_2733553
  simp only [CollatzResearch.WordTrace]
  refine ⟨99700868665811809529389313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66467245777207873019592875 99700868665811809529389313)
  ·
    refine ⟨74775651499358857147041985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99700868665811809529389313 74775651499358857147041985)
    ·
      refine ⟨56081738624519142860281489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74775651499358857147041985 56081738624519142860281489)
      ·
        refine ⟨42061303968389357145211117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56081738624519142860281489 42061303968389357145211117)
        ·
          refine ⟨15772988988146008929454169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42061303968389357145211117 15772988988146008929454169)
          ·
            refine ⟨11829741741109506697090627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772988988146008929454169 11829741741109506697090627)
            ·
              refine ⟨17744612611664260045635941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829741741109506697090627 17744612611664260045635941)
              ·
                refine ⟨3327114864687048758556739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17744612611664260045635941 3327114864687048758556739)
                ·
                  refine ⟨4990672297030573137835109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327114864687048758556739 4990672297030573137835109)
                  ·
                    refine ⟨935751055693232463344083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4990672297030573137835109 935751055693232463344083)
                    ·
                      rfl

theorem cell22_2733553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2733553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733553 prefixEnd_2733553 := by exact prefixLift 2733553
  have htrace : WordTrace (prefixWord ++ tailWord_2733553) baseStart_2733553 baseEnd_2733553 := by
    simpa [prefixWord, tailWord_2733553, baseEnd_2733553] using wordTrace_append hprefix tailTrace_2733553
  have hstable : (prefixWord ++ tailWord_2733553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733553).length < 2 ^ (prefixWord ++ tailWord_2733553).sum := by decide
  have hdescent : baseEnd_2733553 < baseStart_2733553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733585 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 4]
def baseStart_2733585 : Nat := 118140960795 + 2733585 * 2 ^ 59
def prefixEnd_2733585 : Nat := 4983230072969 + 3 ^ 40 * 2733585 * 2
def baseEnd_2733585 : Nat := 311920669982398348847995

theorem tailTrace_2733585 : CollatzResearch.WordTrace tailWord_2733585 prefixEnd_2733585 311920669982398348847995 := by
  unfold tailWord_2733585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99702035801695878994554209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66468023867797252663036139 99702035801695878994554209)
  ·
    refine ⟨74776526851271909245915657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99702035801695878994554209 74776526851271909245915657)
    ·
      refine ⟨56082395138453931934436743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74776526851271909245915657 56082395138453931934436743)
      ·
        refine ⟨84123592707680897901655115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56082395138453931934436743 84123592707680897901655115)
        ·
          refine ⟨126185389061521346852482673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84123592707680897901655115 126185389061521346852482673)
          ·
            refine ⟨94639041796141010139362005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126185389061521346852482673 94639041796141010139362005)
            ·
              refine ⟨2218102542097054925141297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94639041796141010139362005 2218102542097054925141297)
              ·
                refine ⟨1663576906572791193855973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218102542097054925141297 1663576906572791193855973)
                ·
                  refine ⟨311920669982398348847995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663576906572791193855973 311920669982398348847995)
                  ·
                    rfl

theorem cell22_2733585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_2733585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733585 prefixEnd_2733585 := by exact prefixLift 2733585
  have htrace : WordTrace (prefixWord ++ tailWord_2733585) baseStart_2733585 baseEnd_2733585 := by
    simpa [prefixWord, tailWord_2733585, baseEnd_2733585] using wordTrace_append hprefix tailTrace_2733585
  have hstable : (prefixWord ++ tailWord_2733585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733585).length < 2 ^ (prefixWord ++ tailWord_2733585).sum := by decide
  have hdescent : baseEnd_2733585 < baseStart_2733585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733641 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 7]
def baseStart_2733641 : Nat := 118140960795 + 2733641 * 2 ^ 59
def prefixEnd_2733641 : Nat := 4983230072969 + 3 ^ 40 * 2733641 * 2
def baseEnd_2733641 : Nat := 311927059963876522381271

theorem tailTrace_2733641 : CollatzResearch.WordTrace tailWord_2733641 prefixEnd_2733641 311927059963876522381271 := by
  unfold tailWord_2733641
  simp only [CollatzResearch.WordTrace]
  refine ⟨99704078289493000558592777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66469385526328667039061851 99704078289493000558592777)
  ·
    refine ⟨74778058717119750418944583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99704078289493000558592777 74778058717119750418944583)
    ·
      refine ⟨112167088075679625628416875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74778058717119750418944583 112167088075679625628416875)
      ·
        refine ⟨168250632113519438442625313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112167088075679625628416875 168250632113519438442625313)
        ·
          refine ⟨126187974085139578831968985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168250632113519438442625313 126187974085139578831968985)
          ·
            refine ⟨94640980563854684123976739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126187974085139578831968985 94640980563854684123976739)
            ·
              refine ⟨141961470845782026185965109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94640980563854684123976739 141961470845782026185965109)
              ·
                refine ⟨13308887891792064954934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141961470845782026185965109 13308887891792064954934229)
                ·
                  refine ⟨311927059963876522381271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13308887891792064954934229 311927059963876522381271)
                  ·
                    rfl

theorem cell22_2733641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_2733641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733641 prefixEnd_2733641 := by exact prefixLift 2733641
  have htrace : WordTrace (prefixWord ++ tailWord_2733641) baseStart_2733641 baseEnd_2733641 := by
    simpa [prefixWord, tailWord_2733641, baseEnd_2733641] using wordTrace_append hprefix tailTrace_2733641
  have hstable : (prefixWord ++ tailWord_2733641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733641).length < 2 ^ (prefixWord ++ tailWord_2733641).sum := by decide
  have hdescent : baseEnd_2733641 < baseStart_2733641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733703 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 6]
def baseStart_2733703 : Nat := 118140960795 + 2733703 * 2 ^ 59
def prefixEnd_2733703 : Nat := 4983230072969 + 3 ^ 40 * 2733703 * 2
def baseEnd_2733703 : Nat := 311934134586227357364541

theorem tailTrace_2733703 : CollatzResearch.WordTrace tailWord_2733703 prefixEnd_2733703 311934134586227357364541 := by
  unfold tailWord_2733703
  simp only [CollatzResearch.WordTrace]
  refine ⟨99706339615268385147349763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66470893076845590098233175 99706339615268385147349763)
  ·
    refine ⟨149559509422902577721024645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99706339615268385147349763 149559509422902577721024645)
    ·
      refine ⟨28042408016794233322692121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149559509422902577721024645 28042408016794233322692121)
      ·
        refine ⟨21031806012595674992019091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28042408016794233322692121 21031806012595674992019091)
        ·
          refine ⟨31547709018893512488028637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21031806012595674992019091 31547709018893512488028637)
          ·
            refine ⟨11830390882085067183010739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31547709018893512488028637 11830390882085067183010739)
            ·
              refine ⟨17745586323127600774516109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830390882085067183010739 17745586323127600774516109)
              ·
                refine ⟨6654594871172850290443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17745586323127600774516109 6654594871172850290443541)
                ·
                  refine ⟨311934134586227357364541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6654594871172850290443541 311934134586227357364541)
                  ·
                    rfl

theorem cell22_2733703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_2733703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733703 prefixEnd_2733703 := by exact prefixLift 2733703
  have htrace : WordTrace (prefixWord ++ tailWord_2733703) baseStart_2733703 baseEnd_2733703 := by
    simpa [prefixWord, tailWord_2733703, baseEnd_2733703] using wordTrace_append hprefix tailTrace_2733703
  have hstable : (prefixWord ++ tailWord_2733703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733703).length < 2 ^ (prefixWord ++ tailWord_2733703).sum := by decide
  have hdescent : baseEnd_2733703 < baseStart_2733703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733733 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2733733 : Nat := 118140960795 + 2733733 * 2 ^ 59
def prefixEnd_2733733 : Nat := 4983230072969 + 3 ^ 40 * 2733733 * 2
def baseEnd_2733733 : Nat := 935812673371771993843531

theorem tailTrace_2733733 : CollatzResearch.WordTrace tailWord_2733733 prefixEnd_2733733 935812673371771993843531 := by
  unfold tailWord_2733733
  simp only [CollatzResearch.WordTrace]
  refine ⟨99707433805159700270941853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66471622536773133513961235 99707433805159700270941853)
  ·
    refine ⟨37390287676934887601603195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99707433805159700270941853 37390287676934887601603195)
    ·
      refine ⟨56085431515402331402404793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37390287676934887601603195 56085431515402331402404793)
      ·
        refine ⟨42064073636551748551803595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56085431515402331402404793 42064073636551748551803595)
        ·
          refine ⟨63096110454827622827705393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42064073636551748551803595 63096110454827622827705393)
          ·
            refine ⟨47322082841120717120779045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63096110454827622827705393 47322082841120717120779045)
            ·
              refine ⟨8872890532710134460146071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47322082841120717120779045 8872890532710134460146071)
              ·
                refine ⟨13309335799065201690219107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872890532710134460146071 13309335799065201690219107)
                ·
                  refine ⟨19964003698597802535328661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309335799065201690219107 19964003698597802535328661)
                  ·
                    refine ⟨935812673371771993843531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19964003698597802535328661 935812673371771993843531)
                    ·
                      rfl

theorem cell22_2733733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2733733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733733 prefixEnd_2733733 := by exact prefixLift 2733733
  have htrace : WordTrace (prefixWord ++ tailWord_2733733) baseStart_2733733 baseEnd_2733733 := by
    simpa [prefixWord, tailWord_2733733, baseEnd_2733733] using wordTrace_append hprefix tailTrace_2733733
  have hstable : (prefixWord ++ tailWord_2733733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733733).length < 2 ^ (prefixWord ++ tailWord_2733733).sum := by decide
  have hdescent : baseEnd_2733733 < baseStart_2733733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733857 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2733857 : Nat := 118140960795 + 2733857 * 2 ^ 59
def prefixEnd_2733857 : Nat := 4983230072969 + 3 ^ 40 * 2733857 * 2
def baseEnd_2733857 : Nat := 935855121105877003743151

theorem tailTrace_2733857 : CollatzResearch.WordTrace tailWord_2733857 prefixEnd_2733857 935855121105877003743151 := by
  unfold tailWord_2733857
  simp only [CollatzResearch.WordTrace]
  refine ⟨99711956456710469448455825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66474637637806979632303883 99711956456710469448455825)
  ·
    refine ⟨74783967342532852086341869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99711956456710469448455825 74783967342532852086341869)
    ·
      refine ⟨28043987753449819532378201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74783967342532852086341869 28043987753449819532378201)
      ·
        refine ⟨21032990815087364649283651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28043987753449819532378201 21032990815087364649283651)
        ·
          refine ⟨31549486222631046973925477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21032990815087364649283651 31549486222631046973925477)
          ·
            refine ⟨5915528666743321307611027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31549486222631046973925477 5915528666743321307611027)
            ·
              refine ⟨8873293000114981961416541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915528666743321307611027 8873293000114981961416541)
              ·
                refine ⟨3327484875043118235531203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8873293000114981961416541 3327484875043118235531203)
                ·
                  refine ⟨4991227312564677353296805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327484875043118235531203 4991227312564677353296805)
                  ·
                    refine ⟨935855121105877003743151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991227312564677353296805 935855121105877003743151)
                    ·
                      rfl

theorem cell22_2733857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2733857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2733857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2733857 prefixEnd_2733857 := by exact prefixLift 2733857
  have htrace : WordTrace (prefixWord ++ tailWord_2733857) baseStart_2733857 baseEnd_2733857 := by
    simpa [prefixWord, tailWord_2733857, baseEnd_2733857] using wordTrace_append hprefix tailTrace_2733857
  have hstable : (prefixWord ++ tailWord_2733857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733857).length < 2 ^ (prefixWord ++ tailWord_2733857).sum := by decide
  have hdescent : baseEnd_2733857 < baseStart_2733857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734024 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_2734024 : Nat := 118140960795 + 2734024 * 2 ^ 59
def prefixEnd_2734024 : Nat := 4983230072969 + 3 ^ 40 * 2734024 * 2
def baseEnd_2734024 : Nat := 311970762872914744939213

theorem tailTrace_2734024 : CollatzResearch.WordTrace tailWord_2734024 prefixEnd_2734024 311970762872914744939213 := by
  unfold tailWord_2734024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49859023723552728484892563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66478698298070304646523417 49859023723552728484892563)
  ·
    refine ⟨74788535585329092727338845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49859023723552728484892563 74788535585329092727338845)
    ·
      refine ⟨28045700844498409772752067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74788535585329092727338845 28045700844498409772752067)
      ·
        refine ⟨42068551266747614659128101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28045700844498409772752067 42068551266747614659128101)
        ·
          refine ⟨7887853362515177748586519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42068551266747614659128101 7887853362515177748586519)
          ·
            refine ⟨11831780043772766622879779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887853362515177748586519 11831780043772766622879779)
            ·
              refine ⟨17747670065659149934319669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11831780043772766622879779 17747670065659149934319669)
              ·
                refine ⟨1663844068655545306342469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17747670065659149934319669 1663844068655545306342469)
                ·
                  refine ⟨311970762872914744939213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663844068655545306342469 311970762872914744939213)
                  ·
                    rfl

theorem cell22_2734024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_2734024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734024 prefixEnd_2734024 := by exact prefixLift 2734024
  have htrace : WordTrace (prefixWord ++ tailWord_2734024) baseStart_2734024 baseEnd_2734024 := by
    simpa [prefixWord, tailWord_2734024, baseEnd_2734024] using wordTrace_append hprefix tailTrace_2734024
  have hstable : (prefixWord ++ tailWord_2734024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734024).length < 2 ^ (prefixWord ++ tailWord_2734024).sum := by decide
  have hdescent : baseEnd_2734024 < baseStart_2734024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734114 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2734114 : Nat := 118140960795 + 2734114 * 2 ^ 59
def prefixEnd_2734114 : Nat := 4983230072969 + 3 ^ 40 * 2734114 * 2
def baseEnd_2734114 : Nat := 311981032486004666689121

theorem tailTrace_2734114 : CollatzResearch.WordTrace tailWord_2734114 prefixEnd_2734114 311981032486004666689121 := by
  unfold tailWord_2734114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24930332504194850585140349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66480886677852934893707597 24930332504194850585140349)
  ·
    refine ⟨9348874689073068969427631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24930332504194850585140349 9348874689073068969427631)
    ·
      refine ⟨14023312033609603454141447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9348874689073068969427631 14023312033609603454141447)
      ·
        refine ⟨21034968050414405181212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023312033609603454141447 21034968050414405181212171)
        ·
          refine ⟨31552452075621607771818257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21034968050414405181212171 31552452075621607771818257)
          ·
            refine ⟨23664339056716205828863693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31552452075621607771818257 23664339056716205828863693)
            ·
              refine ⟨8874127146268577185823885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23664339056716205828863693 8874127146268577185823885)
              ·
                refine ⟨3327797679850716444683957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8874127146268577185823885 3327797679850716444683957)
                ·
                  refine ⟨311981032486004666689121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3327797679850716444683957 311981032486004666689121)
                  ·
                    rfl

theorem cell22_2734114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2734114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734114 prefixEnd_2734114 := by exact prefixLift 2734114
  have htrace : WordTrace (prefixWord ++ tailWord_2734114) baseStart_2734114 baseEnd_2734114 := by
    simpa [prefixWord, tailWord_2734114, baseEnd_2734114] using wordTrace_append hprefix tailTrace_2734114
  have hstable : (prefixWord ++ tailWord_2734114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734114).length < 2 ^ (prefixWord ++ tailWord_2734114).sum := by decide
  have hdescent : baseEnd_2734114 < baseStart_2734114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734159 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 4]
def baseStart_2734159 : Nat := 118140960795 + 2734159 * 2 ^ 59
def prefixEnd_2734159 : Nat := 4983230072969 + 3 ^ 40 * 2734159 * 2
def baseEnd_2734159 : Nat := 311986167292549627564075

theorem tailTrace_2734159 : CollatzResearch.WordTrace tailWord_2734159 prefixEnd_2734159 311986167292549627564075 := by
  unfold tailWord_2734159
  simp only [CollatzResearch.WordTrace]
  refine ⟨99722971301616375025949531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66481980867744250017299687 99722971301616375025949531)
  ·
    refine ⟨149584456952424562538924297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99722971301616375025949531 149584456952424562538924297)
    ·
      refine ⟨112188342714318421904193223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149584456952424562538924297 112188342714318421904193223)
      ·
        refine ⟨168282514071477632856289835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112188342714318421904193223 168282514071477632856289835)
        ·
          refine ⟨252423771107216449284434753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168282514071477632856289835 252423771107216449284434753)
          ·
            refine ⟨189317828330412336963326065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252423771107216449284434753 189317828330412336963326065)
            ·
              refine ⟨141988371247809252722494549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189317828330412336963326065 141988371247809252722494549)
              ·
                refine ⟨1663926225560264680341733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 141988371247809252722494549 1663926225560264680341733)
                ·
                  refine ⟨311986167292549627564075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663926225560264680341733 311986167292549627564075)
                  ·
                    rfl

theorem cell22_2734159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 4].length) (baseStart_2734159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734159 prefixEnd_2734159 := by exact prefixLift 2734159
  have htrace : WordTrace (prefixWord ++ tailWord_2734159) baseStart_2734159 baseEnd_2734159 := by
    simpa [prefixWord, tailWord_2734159, baseEnd_2734159] using wordTrace_append hprefix tailTrace_2734159
  have hstable : (prefixWord ++ tailWord_2734159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734159).length < 2 ^ (prefixWord ++ tailWord_2734159).sum := by decide
  have hdescent : baseEnd_2734159 < baseStart_2734159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734189 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2734189 : Nat := 118140960795 + 2734189 * 2 ^ 59
def prefixEnd_2734189 : Nat := 4983230072969 + 3 ^ 40 * 2734189 * 2
def baseEnd_2734189 : Nat := 935968771490738804442133

theorem tailTrace_2734189 : CollatzResearch.WordTrace tailWord_2734189 prefixEnd_2734189 935968771490738804442133 := by
  unfold tailWord_2734189
  simp only [CollatzResearch.WordTrace]
  refine ⟨99724065491507690149541621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66482710327671793433027747 99724065491507690149541621)
  ·
    refine ⟨9349131139828845951519527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99724065491507690149541621 9349131139828845951519527)
    ·
      refine ⟨14023696709743268927279291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349131139828845951519527 14023696709743268927279291)
      ·
        refine ⟨21035545064614903390918937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023696709743268927279291 21035545064614903390918937)
        ·
          refine ⟨15776658798461177543189203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21035545064614903390918937 15776658798461177543189203)
          ·
            refine ⟨23664988197691766314783805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15776658798461177543189203 23664988197691766314783805)
            ·
              refine ⟨8874370574134412368043927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23664988197691766314783805 8874370574134412368043927)
              ·
                refine ⟨13311555861201618552065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8874370574134412368043927 13311555861201618552065891)
                ·
                  refine ⟨19967333791802427828098837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13311555861201618552065891 19967333791802427828098837)
                  ·
                    refine ⟨935968771490738804442133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19967333791802427828098837 935968771490738804442133)
                    ·
                      rfl

theorem cell22_2734189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2734189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734189 prefixEnd_2734189 := by exact prefixLift 2734189
  have htrace : WordTrace (prefixWord ++ tailWord_2734189) baseStart_2734189 baseEnd_2734189 := by
    simpa [prefixWord, tailWord_2734189, baseEnd_2734189] using wordTrace_append hprefix tailTrace_2734189
  have hstable : (prefixWord ++ tailWord_2734189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734189).length < 2 ^ (prefixWord ++ tailWord_2734189).sum := by decide
  have hdescent : baseEnd_2734189 < baseStart_2734189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734202 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_2734202 : Nat := 118140960795 + 2734202 * 2 ^ 59
def prefixEnd_2734202 : Nat := 4983230072969 + 3 ^ 40 * 2734202 * 2
def baseEnd_2734202 : Nat := 935973221656411103867093

theorem tailTrace_2734202 : CollatzResearch.WordTrace tailWord_2734202 prefixEnd_2734202 935973221656411103867093 := by
  unfold tailWord_2734202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24931134910115148342441215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66483026426973728913176573 24931134910115148342441215)
  ·
    refine ⟨37396702365172722513661823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24931134910115148342441215 37396702365172722513661823)
    ·
      refine ⟨56095053547759083770492735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37396702365172722513661823 56095053547759083770492735)
      ·
        refine ⟨84142580321638625655739103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56095053547759083770492735 84142580321638625655739103)
        ·
          refine ⟨126213870482457938483608655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84142580321638625655739103 126213870482457938483608655)
          ·
            refine ⟨189320805723686907725412983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126213870482457938483608655 189320805723686907725412983)
            ·
              refine ⟨283981208585530361588119475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189320805723686907725412983 283981208585530361588119475)
              ·
                refine ⟨425971812878295542382179213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283981208585530361588119475 425971812878295542382179213)
                ·
                  refine ⟨159739429829360828393317205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425971812878295542382179213 159739429829360828393317205)
                  ·
                    refine ⟨935973221656411103867093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159739429829360828393317205 935973221656411103867093)
                    ·
                      rfl

theorem cell22_2734202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_2734202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734202 prefixEnd_2734202 := by exact prefixLift 2734202
  have htrace : WordTrace (prefixWord ++ tailWord_2734202) baseStart_2734202 baseEnd_2734202 := by
    simpa [prefixWord, tailWord_2734202, baseEnd_2734202] using wordTrace_append hprefix tailTrace_2734202
  have hstable : (prefixWord ++ tailWord_2734202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734202).length < 2 ^ (prefixWord ++ tailWord_2734202).sum := by decide
  have hdescent : baseEnd_2734202 < baseStart_2734202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734236 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2734236 : Nat := 118140960795 + 2734236 * 2 ^ 59
def prefixEnd_2734236 : Nat := 4983230072969 + 3 ^ 40 * 2734236 * 2
def baseEnd_2734236 : Nat := 935984860551246348516989

theorem tailTrace_2734236 : CollatzResearch.WordTrace tailWord_2734236 prefixEnd_2734236 935984860551246348516989 := by
  unfold tailWord_2734236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862889861168708588251281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66483853148224944784335041 49862889861168708588251281)
  ·
    refine ⟨37397167395876531441188461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49862889861168708588251281 37397167395876531441188461)
    ·
      refine ⟨14023937773453699290445673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37397167395876531441188461 14023937773453699290445673)
      ·
        refine ⟨10517953330090274467834255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14023937773453699290445673 10517953330090274467834255)
        ·
          refine ⟨15776929995135411701751383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10517953330090274467834255 15776929995135411701751383)
          ·
            refine ⟨23665394992703117552627075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15776929995135411701751383 23665394992703117552627075)
            ·
              refine ⟨35498092489054676328940613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23665394992703117552627075 35498092489054676328940613)
              ·
                refine ⟨6655892341697751811676365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35498092489054676328940613 6655892341697751811676365)
                ·
                  refine ⟨2495959628136656929378637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6655892341697751811676365 2495959628136656929378637)
                  ·
                    refine ⟨935984860551246348516989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495959628136656929378637 935984860551246348516989)
                    ·
                      rfl

theorem cell22_2734236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2734236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734236 prefixEnd_2734236 := by exact prefixLift 2734236
  have htrace : WordTrace (prefixWord ++ tailWord_2734236) baseStart_2734236 baseEnd_2734236 := by
    simpa [prefixWord, tailWord_2734236, baseEnd_2734236] using wordTrace_append hprefix tailTrace_2734236
  have hstable : (prefixWord ++ tailWord_2734236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734236).length < 2 ^ (prefixWord ++ tailWord_2734236).sum := by decide
  have hdescent : baseEnd_2734236 < baseStart_2734236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734270 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2734270 : Nat := 118140960795 + 2734270 * 2 ^ 59
def prefixEnd_2734270 : Nat := 4983230072969 + 3 ^ 40 * 2734270 * 2
def baseEnd_2734270 : Nat := 935996499446081593166885

theorem tailTrace_2734270 : CollatzResearch.WordTrace tailWord_2734270 prefixEnd_2734270 935996499446081593166885 := by
  unfold tailWord_2734270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465877475526780122905033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66484679869476160655493509 12465877475526780122905033)
  ·
    refine ⟨9349408106645085092178775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12465877475526780122905033 9349408106645085092178775)
    ·
      refine ⟨14024112159967627638268163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349408106645085092178775 14024112159967627638268163)
      ·
        refine ⟨21036168239951441457402245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14024112159967627638268163 21036168239951441457402245)
        ·
          refine ⟨3944281544990895273262921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21036168239951441457402245 3944281544990895273262921)
          ·
            refine ⟨2958211158743171454947191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3944281544990895273262921 2958211158743171454947191)
            ·
              refine ⟨4437316738114757182420787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958211158743171454947191 4437316738114757182420787)
              ·
                refine ⟨6655975107172135773631181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437316738114757182420787 6655975107172135773631181)
                ·
                  refine ⟨2495990665189550915111693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6655975107172135773631181 2495990665189550915111693)
                  ·
                    refine ⟨935996499446081593166885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495990665189550915111693 935996499446081593166885)
                    ·
                      rfl

theorem cell22_2734270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2734270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734270 prefixEnd_2734270 := by exact prefixLift 2734270
  have htrace : WordTrace (prefixWord ++ tailWord_2734270) baseStart_2734270 baseEnd_2734270 := by
    simpa [prefixWord, tailWord_2734270, baseEnd_2734270] using wordTrace_append hprefix tailTrace_2734270
  have hstable : (prefixWord ++ tailWord_2734270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734270).length < 2 ^ (prefixWord ++ tailWord_2734270).sum := by decide
  have hdescent : baseEnd_2734270 < baseStart_2734270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734296 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2734296 : Nat := 118140960795 + 2734296 * 2 ^ 59
def prefixEnd_2734296 : Nat := 4983230072969 + 3 ^ 40 * 2734296 * 2
def baseEnd_2734296 : Nat := 936005399777426192016805

theorem tailTrace_2734296 : CollatzResearch.WordTrace tailWord_2734296 prefixEnd_2734296 936005399777426192016805 := by
  unfold tailWord_2734296
  simp only [CollatzResearch.WordTrace]
  refine ⟨49863984051060023711843371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66485312068080031615791161 49863984051060023711843371)
  ·
    refine ⟨74795976076590035567765057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49863984051060023711843371 74795976076590035567765057)
    ·
      refine ⟨56096982057442526675823793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74795976076590035567765057 56096982057442526675823793)
      ·
        refine ⟨42072736543081895006867845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56096982057442526675823793 42072736543081895006867845)
        ·
          refine ⟨7888638101827855313787721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42072736543081895006867845 7888638101827855313787721)
          ·
            refine ⟨5916478576370891485340791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7888638101827855313787721 5916478576370891485340791)
            ·
              refine ⟨8874717864556337228011187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916478576370891485340791 8874717864556337228011187)
              ·
                refine ⟨13312076796834505842016781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8874717864556337228011187 13312076796834505842016781)
                ·
                  refine ⟨4992028798812939690756293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13312076796834505842016781 4992028798812939690756293)
                  ·
                    refine ⟨936005399777426192016805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4992028798812939690756293 936005399777426192016805)
                    ·
                      rfl

theorem cell22_2734296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2734296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734296 prefixEnd_2734296 := by exact prefixLift 2734296
  have htrace : WordTrace (prefixWord ++ tailWord_2734296) baseStart_2734296 baseEnd_2734296 := by
    simpa [prefixWord, tailWord_2734296, baseEnd_2734296] using wordTrace_append hprefix tailTrace_2734296
  have hstable : (prefixWord ++ tailWord_2734296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734296).length < 2 ^ (prefixWord ++ tailWord_2734296).sum := by decide
  have hdescent : baseEnd_2734296 < baseStart_2734296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734371 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 5, 3]
def baseStart_2734371 : Nat := 118140960795 + 2734371 * 2 ^ 59
def prefixEnd_2734371 : Nat := 4983230072969 + 3 ^ 40 * 2734371 * 2
def baseEnd_2734371 : Nat := 936031073810150996391575

theorem tailTrace_2734371 : CollatzResearch.WordTrace tailWord_2734371 prefixEnd_2734371 936031073810150996391575 := by
  unfold tailWord_2734371
  simp only [CollatzResearch.WordTrace]
  refine ⟨99730703576848335232666967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66487135717898890155111311 99730703576848335232666967)
  ·
    refine ⟨149596055365272502849000451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99730703576848335232666967 149596055365272502849000451)
    ·
      refine ⟨224394083047908754273500677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149596055365272502849000451 224394083047908754273500677)
      ·
        refine ⟨42073890571482891426281377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224394083047908754273500677 42073890571482891426281377)
        ·
          refine ⟨31555417928612168569711033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42073890571482891426281377 31555417928612168569711033)
          ·
            refine ⟨23666563446459126427283275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31555417928612168569711033 23666563446459126427283275)
            ·
              refine ⟨35499845169688689640924913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23666563446459126427283275 35499845169688689640924913)
              ·
                refine ⟨26624883877266517230693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35499845169688689640924913 26624883877266517230693685)
                ·
                  refine ⟨2496082863493735990377533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26624883877266517230693685 2496082863493735990377533)
                  ·
                    refine ⟨936031073810150996391575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496082863493735990377533 936031073810150996391575)
                    ·
                      rfl

theorem cell22_2734371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].length) (baseStart_2734371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734371 prefixEnd_2734371 := by exact prefixLift 2734371
  have htrace : WordTrace (prefixWord ++ tailWord_2734371) baseStart_2734371 baseEnd_2734371 := by
    simpa [prefixWord, tailWord_2734371, baseEnd_2734371] using wordTrace_append hprefix tailTrace_2734371
  have hstable : (prefixWord ++ tailWord_2734371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734371).length < 2 ^ (prefixWord ++ tailWord_2734371).sum := by decide
  have hdescent : baseEnd_2734371 < baseStart_2734371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734465 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2734465 : Nat := 118140960795 + 2734465 * 2 ^ 59
def prefixEnd_2734465 : Nat := 4983230072969 + 3 ^ 40 * 2734465 * 2
def baseEnd_2734465 : Nat := 936063251931166084541287

theorem tailTrace_2734465 : CollatzResearch.WordTrace tailWord_2734465 prefixEnd_2734465 936063251931166084541287 := by
  unfold tailWord_2734465
  simp only [CollatzResearch.WordTrace]
  refine ⟨99734132038507789286588849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66489421359005192857725899 99734132038507789286588849)
  ·
    refine ⟨74800599028880841964941637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99734132038507789286588849 74800599028880841964941637)
    ·
      refine ⟨14025112317915157868426557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74800599028880841964941637 14025112317915157868426557)
      ·
        refine ⟨5259417119218184200659959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14025112317915157868426557 5259417119218184200659959)
        ·
          refine ⟨7889125678827276300989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259417119218184200659959 7889125678827276300989939)
          ·
            refine ⟨11833688518240914451484909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889125678827276300989939 11833688518240914451484909)
            ·
              refine ⟨4437633194340342919306841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11833688518240914451484909 4437633194340342919306841)
              ·
                refine ⟨3328224895755257189480131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437633194340342919306841 3328224895755257189480131)
                ·
                  refine ⟨4992337343632885784220197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328224895755257189480131 4992337343632885784220197)
                  ·
                    refine ⟨936063251931166084541287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4992337343632885784220197 936063251931166084541287)
                    ·
                      rfl

theorem cell22_2734465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2734465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734465 prefixEnd_2734465 := by exact prefixLift 2734465
  have htrace : WordTrace (prefixWord ++ tailWord_2734465) baseStart_2734465 baseEnd_2734465 := by
    simpa [prefixWord, tailWord_2734465, baseEnd_2734465] using wordTrace_append hprefix tailTrace_2734465
  have hstable : (prefixWord ++ tailWord_2734465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734465).length < 2 ^ (prefixWord ++ tailWord_2734465).sum := by decide
  have hdescent : baseEnd_2734465 < baseStart_2734465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734478 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2734478 : Nat := 118140960795 + 2734478 * 2 ^ 59
def prefixEnd_2734478 : Nat := 4983230072969 + 3 ^ 40 * 2734478 * 2
def baseEnd_2734478 : Nat := 936067702096838383966247

theorem tailTrace_2734478 : CollatzResearch.WordTrace tailWord_2734478 prefixEnd_2734478 936067702096838383966247 := by
  unfold tailWord_2734478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466825773432586563351511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66489737458307128337874725 12466825773432586563351511)
  ·
    refine ⟨18700238660148879845027267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12466825773432586563351511 18700238660148879845027267)
    ·
      refine ⟨28050357990223319767540901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18700238660148879845027267 28050357990223319767540901)
      ·
        refine ⟨5259442123166872456413919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28050357990223319767540901 5259442123166872456413919)
        ·
          refine ⟨7889163184750308684620879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259442123166872456413919 7889163184750308684620879)
          ·
            refine ⟨11833744777125463026931319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889163184750308684620879 11833744777125463026931319)
            ·
              refine ⟨17750617165688194540396979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833744777125463026931319 17750617165688194540396979)
              ·
                refine ⟨26625925748532291810595469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17750617165688194540396979 26625925748532291810595469)
                ·
                  refine ⟨9984722155699609428973301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26625925748532291810595469 9984722155699609428973301)
                  ·
                    refine ⟨936067702096838383966247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9984722155699609428973301 936067702096838383966247)
                    ·
                      rfl

theorem cell22_2734478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2734478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734478 prefixEnd_2734478 := by exact prefixLift 2734478
  have htrace : WordTrace (prefixWord ++ tailWord_2734478) baseStart_2734478 baseEnd_2734478 := by
    simpa [prefixWord, tailWord_2734478, baseEnd_2734478] using wordTrace_append hprefix tailTrace_2734478
  have hstable : (prefixWord ++ tailWord_2734478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734478).length < 2 ^ (prefixWord ++ tailWord_2734478).sum := by decide
  have hdescent : baseEnd_2734478 < baseStart_2734478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734495 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 2, 3]
def baseStart_2734495 : Nat := 118140960795 + 2734495 * 2 ^ 59
def prefixEnd_2734495 : Nat := 4983230072969 + 3 ^ 40 * 2734495 * 2
def baseEnd_2734495 : Nat := 936073521544256006291195

theorem tailTrace_2734495 : CollatzResearch.WordTrace tailWord_2734495 prefixEnd_2734495 936073521544256006291195 := by
  unfold tailWord_2734495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99735226228399104410180939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66490150818932736273453959 99735226228399104410180939)
  ·
    refine ⟨149602839342598656615271409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99735226228399104410180939 149602839342598656615271409)
    ·
      refine ⟨112202129506948992461453557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149602839342598656615271409 112202129506948992461453557)
      ·
        refine ⟨10518949641276468043261271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112202129506948992461453557 10518949641276468043261271)
        ·
          refine ⟨15778424461914702064891907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10518949641276468043261271 15778424461914702064891907)
          ·
            refine ⟨23667636692872053097337861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15778424461914702064891907 23667636692872053097337861)
            ·
              refine ⟨4437681879913509955750849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23667636692872053097337861 4437681879913509955750849)
              ·
                refine ⟨3328261409935132466813137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437681879913509955750849 3328261409935132466813137)
                ·
                  refine ⟨2496196057451349350109853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328261409935132466813137 2496196057451349350109853)
                  ·
                    refine ⟨936073521544256006291195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496196057451349350109853 936073521544256006291195)
                    ·
                      rfl

theorem cell22_2734495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_2734495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734495 prefixEnd_2734495 := by exact prefixLift 2734495
  have htrace : WordTrace (prefixWord ++ tailWord_2734495) baseStart_2734495 baseEnd_2734495 := by
    simpa [prefixWord, tailWord_2734495, baseEnd_2734495] using wordTrace_append hprefix tailTrace_2734495
  have hstable : (prefixWord ++ tailWord_2734495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734495).length < 2 ^ (prefixWord ++ tailWord_2734495).sum := by decide
  have hdescent : baseEnd_2734495 < baseStart_2734495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734497 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 4]
def baseStart_2734497 : Nat := 118140960795 + 2734497 * 2 ^ 59
def prefixEnd_2734497 : Nat := 4983230072969 + 3 ^ 40 * 2734497 * 2
def baseEnd_2734497 : Nat := 312024735395042889247063

theorem tailTrace_2734497 : CollatzResearch.WordTrace tailWord_2734497 prefixEnd_2734497 312024735395042889247063 := by
  unfold tailWord_2734497
  simp only [CollatzResearch.WordTrace]
  refine ⟨99735299174391858751753745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66490199449594572501169163 99735299174391858751753745)
  ·
    refine ⟨74801474380793894063815309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99735299174391858751753745 74801474380793894063815309)
    ·
      refine ⟨28050552892797710273930741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74801474380793894063815309 28050552892797710273930741)
      ·
        refine ⟨2629739333699785338181007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28050552892797710273930741 2629739333699785338181007)
        ·
          refine ⟨3944609000549678007271511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629739333699785338181007 3944609000549678007271511)
          ·
            refine ⟨5916913500824517010907267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944609000549678007271511 5916913500824517010907267)
            ·
              refine ⟨8875370251236775516360901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916913500824517010907267 8875370251236775516360901)
              ·
                refine ⟨1664131922106895409317669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8875370251236775516360901 1664131922106895409317669)
                ·
                  refine ⟨312024735395042889247063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664131922106895409317669 312024735395042889247063)
                  ·
                    rfl

theorem cell22_2734497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_2734497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734497 prefixEnd_2734497 := by exact prefixLift 2734497
  have htrace : WordTrace (prefixWord ++ tailWord_2734497) baseStart_2734497 baseEnd_2734497 := by
    simpa [prefixWord, tailWord_2734497, baseEnd_2734497] using wordTrace_append hprefix tailTrace_2734497
  have hstable : (prefixWord ++ tailWord_2734497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734497).length < 2 ^ (prefixWord ++ tailWord_2734497).sum := by decide
  have hdescent : baseEnd_2734497 < baseStart_2734497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734546 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2734546 : Nat := 118140960795 + 2734546 * 2 ^ 59
def prefixEnd_2734546 : Nat := 4983230072969 + 3 ^ 40 * 2734546 * 2
def baseEnd_2734546 : Nat := 936090979886508873266039

theorem tailTrace_2734546 : CollatzResearch.WordTrace tailWord_2734546 prefixEnd_2734546 936090979886508873266039 := by
  unfold tailWord_2734546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934271587803585030071873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66491390900809560080191661 24934271587803585030071873)
  ·
    refine ⟨18700703690852688772553905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24934271587803585030071873 18700703690852688772553905)
    ·
      refine ⟨14025527768139516579415429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18700703690852688772553905 14025527768139516579415429)
      ·
        refine ⟨2629786456526159358640393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14025527768139516579415429 2629786456526159358640393)
        ·
          refine ⟨1972339842394619518980295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629786456526159358640393 1972339842394619518980295)
          ·
            refine ⟨2958509763591929278470443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972339842394619518980295 2958509763591929278470443)
            ·
              refine ⟨4437764645387893917705665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958509763591929278470443 4437764645387893917705665)
              ·
                refine ⟨3328323484040920438279249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437764645387893917705665 3328323484040920438279249)
                ·
                  refine ⟨2496242613030690328709437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328323484040920438279249 2496242613030690328709437)
                  ·
                    refine ⟨936090979886508873266039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496242613030690328709437 936090979886508873266039)
                    ·
                      rfl

theorem cell22_2734546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2734546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734546 prefixEnd_2734546 := by exact prefixLift 2734546
  have htrace : WordTrace (prefixWord ++ tailWord_2734546) baseStart_2734546 baseEnd_2734546 := by
    simpa [prefixWord, tailWord_2734546, baseEnd_2734546] using wordTrace_append hprefix tailTrace_2734546
  have hstable : (prefixWord ++ tailWord_2734546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734546).length < 2 ^ (prefixWord ++ tailWord_2734546).sum := by decide
  have hdescent : baseEnd_2734546 < baseStart_2734546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734557 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2734557 : Nat := 118140960795 + 2734557 * 2 ^ 59
def prefixEnd_2734557 : Nat := 4983230072969 + 3 ^ 40 * 2734557 * 2
def baseEnd_2734557 : Nat := 936094745411308511241005

theorem tailTrace_2734557 : CollatzResearch.WordTrace tailWord_2734557 prefixEnd_2734557 936094745411308511241005 := by
  unfold tailWord_2734557
  simp only [CollatzResearch.WordTrace]
  refine ⟨99737487554174488998937925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66491658369449659332625283 99737487554174488998937925)
  ·
    refine ⟨18700778916407716687300861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99737487554174488998937925 18700778916407716687300861)
    ·
      refine ⟨7012792093652893757737823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18700778916407716687300861 7012792093652893757737823)
      ·
        refine ⟨10519188140479340636606735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012792093652893757737823 10519188140479340636606735)
        ·
          refine ⟨15778782210719010954910103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10519188140479340636606735 15778782210719010954910103)
          ·
            refine ⟨23668173316078516432365155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15778782210719010954910103 23668173316078516432365155)
            ·
              refine ⟨35502259974117774648547733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23668173316078516432365155 35502259974117774648547733)
              ·
                refine ⟨1664168436286770686650675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35502259974117774648547733 1664168436286770686650675)
                ·
                  refine ⟨2496252654430156029976013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664168436286770686650675 2496252654430156029976013)
                  ·
                    refine ⟨936094745411308511241005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496252654430156029976013 936094745411308511241005)
                    ·
                      rfl

theorem cell22_2734557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2734557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734557 prefixEnd_2734557 := by exact prefixLift 2734557
  have htrace : WordTrace (prefixWord ++ tailWord_2734557) baseStart_2734557 baseEnd_2734557 := by
    simpa [prefixWord, tailWord_2734557, baseEnd_2734557] using wordTrace_append hprefix tailTrace_2734557
  have hstable : (prefixWord ++ tailWord_2734557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734557).length < 2 ^ (prefixWord ++ tailWord_2734557).sum := by decide
  have hdescent : baseEnd_2734557 < baseStart_2734557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734568 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2734568 : Nat := 118140960795 + 2734568 * 2 ^ 59
def prefixEnd_2734568 : Nat := 4983230072969 + 3 ^ 40 * 2734568 * 2
def baseEnd_2734568 : Nat := 936098510936108149215971

theorem tailTrace_2734568 : CollatzResearch.WordTrace tailWord_2734568 prefixEnd_2734568 936098510936108149215971 := by
  unfold tailWord_2734568
  simp only [CollatzResearch.WordTrace]
  refine ⟨49868944378567318938794179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66491925838089758585058905 49868944378567318938794179)
  ·
    refine ⟨74803416567850978408191269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49868944378567318938794179 74803416567850978408191269)
    ·
      refine ⟨14025640606472058451535863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74803416567850978408191269 14025640606472058451535863)
      ·
        refine ⟨21038460909708087677303795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14025640606472058451535863 21038460909708087677303795)
        ·
          refine ⟨31557691364562131515955693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21038460909708087677303795 31557691364562131515955693)
          ·
            refine ⟨11834134261710799318483385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31557691364562131515955693 11834134261710799318483385)
            ·
              refine ⟨8875600696283099488862539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11834134261710799318483385 8875600696283099488862539)
              ·
                refine ⟨13313401044424649233293809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8875600696283099488862539 13313401044424649233293809)
                ·
                  refine ⟨9985050783318486924970357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13313401044424649233293809 9985050783318486924970357)
                  ·
                    refine ⟨936098510936108149215971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9985050783318486924970357 936098510936108149215971)
                    ·
                      rfl

theorem cell22_2734568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2734568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734568 prefixEnd_2734568 := by exact prefixLift 2734568
  have htrace : WordTrace (prefixWord ++ tailWord_2734568) baseStart_2734568 baseEnd_2734568 := by
    simpa [prefixWord, tailWord_2734568, baseEnd_2734568] using wordTrace_append hprefix tailTrace_2734568
  have hstable : (prefixWord ++ tailWord_2734568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734568).length < 2 ^ (prefixWord ++ tailWord_2734568).sum := by decide
  have hdescent : baseEnd_2734568 < baseStart_2734568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734645 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2734645 : Nat := 118140960795 + 2734645 * 2 ^ 59
def prefixEnd_2734645 : Nat := 4983230072969 + 3 ^ 40 * 2734645 * 2
def baseEnd_2734645 : Nat := 936124869609705615040735

theorem tailTrace_2734645 : CollatzResearch.WordTrace tailWord_2734645 prefixEnd_2734645 936124869609705615040735 := by
  unfold tailWord_2734645
  simp only [CollatzResearch.WordTrace]
  refine ⟨99740697177855680028141389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66493798118570453352094259 99740697177855680028141389)
  ·
    refine ⟨37402761441695880010553021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99740697177855680028141389 37402761441695880010553021)
    ·
      refine ⟨14026035540635955003957383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37402761441695880010553021 14026035540635955003957383)
      ·
        refine ⟨21039053310953932505936075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026035540635955003957383 21039053310953932505936075)
        ·
          refine ⟨31558579966430898758904113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21039053310953932505936075 31558579966430898758904113)
          ·
            refine ⟨23668934974823174069178085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31558579966430898758904113 23668934974823174069178085)
            ·
              refine ⟨4437925307779345137970891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23668934974823174069178085 4437925307779345137970891)
              ·
                refine ⟨6656887961669017706956337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437925307779345137970891 6656887961669017706956337)
                ·
                  refine ⟨4992665971251763280217253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656887961669017706956337 4992665971251763280217253)
                  ·
                    refine ⟨936124869609705615040735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4992665971251763280217253 936124869609705615040735)
                    ·
                      rfl

theorem cell22_2734645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2734645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734645 prefixEnd_2734645 := by exact prefixLift 2734645
  have htrace : WordTrace (prefixWord ++ tailWord_2734645) baseStart_2734645 baseEnd_2734645 := by
    simpa [prefixWord, tailWord_2734645, baseEnd_2734645] using wordTrace_append hprefix tailTrace_2734645
  have hstable : (prefixWord ++ tailWord_2734645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734645).length < 2 ^ (prefixWord ++ tailWord_2734645).sum := by decide
  have hdescent : baseEnd_2734645 < baseStart_2734645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734673 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2734673 : Nat := 118140960795 + 2734673 * 2 ^ 59
def prefixEnd_2734673 : Nat := 4983230072969 + 3 ^ 40 * 2734673 * 2
def baseEnd_2734673 : Nat := 936134454581922875340649

theorem tailTrace_2734673 : CollatzResearch.WordTrace tailWord_2734673 prefixEnd_2734673 936134454581922875340649 := by
  unfold tailWord_2734673
  simp only [CollatzResearch.WordTrace]
  refine ⟨99741718421754240810160673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66494478947836160540107115 99741718421754240810160673)
  ·
    refine ⟨74806288816315680607620505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99741718421754240810160673 74806288816315680607620505)
    ·
      refine ⟨56104716612236760455715379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74806288816315680607620505 56104716612236760455715379)
      ·
        refine ⟨84157074918355140683573069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56104716612236760455715379 84157074918355140683573069)
        ·
          refine ⟨31558903094383177756339901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84157074918355140683573069 31558903094383177756339901)
          ·
            refine ⟨11834588660393691658627463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31558903094383177756339901 11834588660393691658627463)
            ·
              refine ⟨17751882990590537487941195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11834588660393691658627463 17751882990590537487941195)
              ·
                refine ⟨26627824485885806231911793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17751882990590537487941195 26627824485885806231911793)
                ·
                  refine ⟨19970868364414354673933845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26627824485885806231911793 19970868364414354673933845)
                  ·
                    refine ⟨936134454581922875340649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19970868364414354673933845 936134454581922875340649)
                    ·
                      rfl

theorem cell22_2734673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2734673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734673 prefixEnd_2734673 := by exact prefixLift 2734673
  have htrace : WordTrace (prefixWord ++ tailWord_2734673) baseStart_2734673 baseEnd_2734673 := by
    simpa [prefixWord, tailWord_2734673, baseEnd_2734673] using wordTrace_append hprefix tailTrace_2734673
  have hstable : (prefixWord ++ tailWord_2734673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734673).length < 2 ^ (prefixWord ++ tailWord_2734673).sum := by decide
  have hdescent : baseEnd_2734673 < baseStart_2734673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734767 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 4]
def baseStart_2734767 : Nat := 118140960795 + 2734767 * 2 ^ 59
def prefixEnd_2734767 : Nat := 4983230072969 + 3 ^ 40 * 2734767 * 2
def baseEnd_2734767 : Nat := 312055544234312654496787

theorem tailTrace_2734767 : CollatzResearch.WordTrace tailWord_2734767 prefixEnd_2734767 312055544234312654496787 := by
  unfold tailWord_2734767
  simp only [CollatzResearch.WordTrace]
  refine ⟨99745146883413694864082555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66496764588942463242721703 99745146883413694864082555)
  ·
    refine ⟨149617720325120542296123833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99745146883413694864082555 149617720325120542296123833)
    ·
      refine ⟨112213290243840406722092875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149617720325120542296123833 112213290243840406722092875)
      ·
        refine ⟨168319935365760610083139313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112213290243840406722092875 168319935365760610083139313)
        ·
          refine ⟨126239951524320457562354485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168319935365760610083139313 126239951524320457562354485)
          ·
            refine ⟨11834995455405042896470733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126239951524320457562354485 11834995455405042896470733)
            ·
              refine ⟨4438123295776891086176525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11834995455405042896470733 4438123295776891086176525)
              ·
                refine ⟨1664296235916334157316197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4438123295776891086176525 1664296235916334157316197)
                ·
                  refine ⟨312055544234312654496787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664296235916334157316197 312055544234312654496787)
                  ·
                    rfl

theorem cell22_2734767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 4].length) (baseStart_2734767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734767 prefixEnd_2734767 := by exact prefixLift 2734767
  have htrace : WordTrace (prefixWord ++ tailWord_2734767) baseStart_2734767 baseEnd_2734767 := by
    simpa [prefixWord, tailWord_2734767, baseEnd_2734767] using wordTrace_append hprefix tailTrace_2734767
  have hstable : (prefixWord ++ tailWord_2734767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734767).length < 2 ^ (prefixWord ++ tailWord_2734767).sum := by decide
  have hdescent : baseEnd_2734767 < baseStart_2734767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734782 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2734782 : Nat := 118140960795 + 2734782 * 2 ^ 59
def prefixEnd_2734782 : Nat := 4983230072969 + 3 ^ 40 * 2734782 * 2
def baseEnd_2734782 : Nat := 936171767509482924365315

theorem tailTrace_2734782 : CollatzResearch.WordTrace tailWord_2734782 prefixEnd_2734782 936171767509482924365315 := by
  unfold tailWord_2734782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468211747294919053234825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66497129318906234950585733 12468211747294919053234825)
  ·
    refine ⟨9351158810471189289926119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12468211747294919053234825 9351158810471189289926119)
    ·
      refine ⟨14026738215706783934889179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351158810471189289926119 14026738215706783934889179)
      ·
        refine ⟨21040107323560175902333769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026738215706783934889179 21040107323560175902333769)
        ·
          refine ⟨15780080492670131926750327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21040107323560175902333769 15780080492670131926750327)
          ·
            refine ⟨23670120739005197890125491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15780080492670131926750327 23670120739005197890125491)
            ·
              refine ⟨35505181108507796835188237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23670120739005197890125491 35505181108507796835188237)
              ·
                refine ⟨13314442915690423813195589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35505181108507796835188237 13314442915690423813195589)
                ·
                  refine ⟨2496458046691954464974173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13314442915690423813195589 2496458046691954464974173)
                  ·
                    refine ⟨936171767509482924365315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496458046691954464974173 936171767509482924365315)
                    ·
                      rfl

theorem cell22_2734782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2734782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734782 prefixEnd_2734782 := by exact prefixLift 2734782
  have htrace : WordTrace (prefixWord ++ tailWord_2734782) baseStart_2734782 baseEnd_2734782 := by
    simpa [prefixWord, tailWord_2734782, baseEnd_2734782] using wordTrace_append hprefix tailTrace_2734782
  have hstable : (prefixWord ++ tailWord_2734782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734782).length < 2 ^ (prefixWord ++ tailWord_2734782).sum := by decide
  have hdescent : baseEnd_2734782 < baseStart_2734782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734784 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_2734784 : Nat := 118140960795 + 2734784 * 2 ^ 59
def prefixEnd_2734784 : Nat := 4983230072969 + 3 ^ 40 * 2734784 * 2
def baseEnd_2734784 : Nat := 312057484050118528605103

theorem tailTrace_2734784 : CollatzResearch.WordTrace tailWord_2734784 prefixEnd_2734784 312057484050118528605103 := by
  unfold tailWord_2734784
  simp only [CollatzResearch.WordTrace]
  refine ⟨49872883462176053383725703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66497177949568071178300937 49872883462176053383725703)
  ·
    refine ⟨74809325193264080075588555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49872883462176053383725703 74809325193264080075588555)
    ·
      refine ⟨112213987789896120113382833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74809325193264080075588555 112213987789896120113382833)
      ·
        refine ⟨84160490842422090085037125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112213987789896120113382833 84160490842422090085037125)
        ·
          refine ⟨15780092032954141890944461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84160490842422090085037125 15780092032954141890944461)
          ·
            refine ⟨5917534512357803209104173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15780092032954141890944461 5917534512357803209104173)
            ·
              refine ⟨2219075442134176203414065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5917534512357803209104173 2219075442134176203414065)
              ·
                refine ⟨1664306581600632152560549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219075442134176203414065 1664306581600632152560549)
                ·
                  refine ⟨312057484050118528605103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664306581600632152560549 312057484050118528605103)
                  ·
                    rfl

theorem cell22_2734784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_2734784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734784 prefixEnd_2734784 := by exact prefixLift 2734784
  have htrace : WordTrace (prefixWord ++ tailWord_2734784) baseStart_2734784 baseEnd_2734784 := by
    simpa [prefixWord, tailWord_2734784, baseEnd_2734784] using wordTrace_append hprefix tailTrace_2734784
  have hstable : (prefixWord ++ tailWord_2734784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734784).length < 2 ^ (prefixWord ++ tailWord_2734784).sum := by decide
  have hdescent : baseEnd_2734784 < baseStart_2734784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734790 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2734790 : Nat := 118140960795 + 2734790 * 2 ^ 59
def prefixEnd_2734790 : Nat := 4983230072969 + 3 ^ 40 * 2734790 * 2
def baseEnd_2734790 : Nat := 312058168690991190055097

theorem tailTrace_2734790 : CollatzResearch.WordTrace tailWord_2734790 prefixEnd_2734790 312058168690991190055097 := by
  unfold tailWord_2734790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117062055072824056005307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66497323841553579861446549 3117062055072824056005307)
  ·
    refine ⟨4675593082609236084007961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117062055072824056005307 4675593082609236084007961)
    ·
      refine ⟨3506694811956927063005971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4675593082609236084007961 3506694811956927063005971)
      ·
        refine ⟨5260042217935390594508957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506694811956927063005971 5260042217935390594508957)
        ·
          refine ⟨1972515831725771472940859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5260042217935390594508957 1972515831725771472940859)
          ·
            refine ⟨2958773747588657209411289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972515831725771472940859 2958773747588657209411289)
            ·
              refine ⟨2219080310691492907058467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958773747588657209411289 2219080310691492907058467)
              ·
                refine ⟨3328620466037239360587701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219080310691492907058467 3328620466037239360587701)
                ·
                  refine ⟨312058168690991190055097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3328620466037239360587701 312058168690991190055097)
                  ·
                    rfl

theorem cell22_2734790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2734790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734790 prefixEnd_2734790 := by exact prefixLift 2734790
  have htrace : WordTrace (prefixWord ++ tailWord_2734790) baseStart_2734790 baseEnd_2734790 := by
    simpa [prefixWord, tailWord_2734790, baseEnd_2734790] using wordTrace_append hprefix tailTrace_2734790
  have hstable : (prefixWord ++ tailWord_2734790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734790).length < 2 ^ (prefixWord ++ tailWord_2734790).sum := by decide
  have hdescent : baseEnd_2734790 < baseStart_2734790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734812 : List Nat := [2, 2, 5, 1, 1, 1, 2, 8]
def baseStart_2734812 : Nat := 118140960795 + 2734812 * 2 ^ 59
def prefixEnd_2734812 : Nat := 4983230072969 + 3 ^ 40 * 2734812 * 2
def baseEnd_2734812 : Nat := 104020226346952538457247

theorem tailTrace_2734812 : CollatzResearch.WordTrace tailWord_2734812 prefixEnd_2734812 104020226346952538457247 := by
  unfold tailWord_2734812
  simp only [CollatzResearch.WordTrace]
  refine ⟨49873394084125333774735345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66497858778833778366313793 49873394084125333774735345)
  ·
    refine ⟨37405045563094000331051509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49873394084125333774735345 37405045563094000331051509)
    ·
      refine ⟨3506723021540062531036079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37405045563094000331051509 3506723021540062531036079)
      ·
        refine ⟨5260084532310093796554119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506723021540062531036079 5260084532310093796554119)
        ·
          refine ⟨7890126798465140694831179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260084532310093796554119 7890126798465140694831179)
          ·
            refine ⟨11835190197697711042246769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890126798465140694831179 11835190197697711042246769)
            ·
              refine ⟨8876392648273283281685077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11835190197697711042246769 8876392648273283281685077)
              ·
                refine ⟨104020226346952538457247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8876392648273283281685077 104020226346952538457247)
                ·
                  rfl

theorem cell22_2734812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_2734812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734812 prefixEnd_2734812 := by exact prefixLift 2734812
  have htrace : WordTrace (prefixWord ++ tailWord_2734812) baseStart_2734812 baseEnd_2734812 := by
    simpa [prefixWord, tailWord_2734812, baseEnd_2734812] using wordTrace_append hprefix tailTrace_2734812
  have hstable : (prefixWord ++ tailWord_2734812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734812).length < 2 ^ (prefixWord ++ tailWord_2734812).sum := by decide
  have hdescent : baseEnd_2734812 < baseStart_2734812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734885 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 8]
def baseStart_2734885 : Nat := 118140960795 + 2734885 * 2 ^ 59
def prefixEnd_2734885 : Nat := 4983230072969 + 3 ^ 40 * 2734885 * 2
def baseEnd_2734885 : Nat := 312069008838141663013333

theorem tailTrace_2734885 : CollatzResearch.WordTrace tailWord_2734885 prefixEnd_2734885 312069008838141663013333 := by
  unfold tailWord_2734885
  simp only [CollatzResearch.WordTrace]
  refine ⟨99749450696986201016878109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66499633797990800677918739 99749450696986201016878109)
  ·
    refine ⟨37406044011369825381329291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99749450696986201016878109 37406044011369825381329291)
    ·
      refine ⟨56109066017054738071993937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37406044011369825381329291 56109066017054738071993937)
      ·
        refine ⟨42081799512791053553995453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56109066017054738071993937 42081799512791053553995453)
        ·
          refine ⟨15780674817296645082748295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42081799512791053553995453 15780674817296645082748295)
          ·
            refine ⟨23671012225944967624122443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15780674817296645082748295 23671012225944967624122443)
            ·
              refine ⟨35506518338917451436183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23671012225944967624122443 35506518338917451436183665)
              ·
                refine ⟨26629888754188088577137749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35506518338917451436183665 26629888754188088577137749)
                ·
                  refine ⟨312069008838141663013333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26629888754188088577137749 312069008838141663013333)
                  ·
                    rfl

theorem cell22_2734885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_2734885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734885 prefixEnd_2734885 := by exact prefixLift 2734885
  have htrace : WordTrace (prefixWord ++ tailWord_2734885) baseStart_2734885 baseEnd_2734885 := by
    simpa [prefixWord, tailWord_2734885, baseEnd_2734885] using wordTrace_append hprefix tailTrace_2734885
  have hstable : (prefixWord ++ tailWord_2734885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734885).length < 2 ^ (prefixWord ++ tailWord_2734885).sum := by decide
  have hdescent : baseEnd_2734885 < baseStart_2734885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734915 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_2734915 : Nat := 118140960795 + 2734915 * 2 ^ 59
def prefixEnd_2734915 : Nat := 4983230072969 + 3 ^ 40 * 2734915 * 2
def baseEnd_2734915 : Nat := 936217296127514910789907

theorem tailTrace_2734915 : CollatzResearch.WordTrace tailWord_2734915 prefixEnd_2734915 936217296127514910789907 := by
  unfold tailWord_2734915
  simp only [CollatzResearch.WordTrace]
  refine ⟨99750544886877516140470199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66500363257918344093646799 99750544886877516140470199)
  ·
    refine ⟨149625817330316274210705299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99750544886877516140470199 149625817330316274210705299)
    ·
      refine ⟨224438725995474411316057949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149625817330316274210705299 224438725995474411316057949)
      ·
        refine ⟨84164522248302904243521731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224438725995474411316057949 84164522248302904243521731)
        ·
          refine ⟨126246783372454356365282597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84164522248302904243521731 126246783372454356365282597)
          ·
            refine ⟨23671271882335191818490487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126246783372454356365282597 23671271882335191818490487)
            ·
              refine ⟨35506907823502787727735731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23671271882335191818490487 35506907823502787727735731)
              ·
                refine ⟨53260361735254181591603597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35506907823502787727735731 53260361735254181591603597)
                ·
                  refine ⟨19972635650720318096851349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53260361735254181591603597 19972635650720318096851349)
                  ·
                    refine ⟨936217296127514910789907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19972635650720318096851349 936217296127514910789907)
                    ·
                      rfl

theorem cell22_2734915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_2734915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734915 prefixEnd_2734915 := by exact prefixLift 2734915
  have htrace : WordTrace (prefixWord ++ tailWord_2734915) baseStart_2734915 baseEnd_2734915 := by
    simpa [prefixWord, tailWord_2734915, baseEnd_2734915] using wordTrace_append hprefix tailTrace_2734915
  have hstable : (prefixWord ++ tailWord_2734915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734915).length < 2 ^ (prefixWord ++ tailWord_2734915).sum := by decide
  have hdescent : baseEnd_2734915 < baseStart_2734915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734947 : List Nat := [1, 1, 1, 5, 3, 3, 8]
def baseStart_2734947 : Nat := 118140960795 + 2734947 * 2 ^ 59
def prefixEnd_2734947 : Nat := 4983230072969 + 3 ^ 40 * 2734947 * 2
def baseEnd_2734947 : Nat := 34675120384499166444067

theorem tailTrace_2734947 : CollatzResearch.WordTrace tailWord_2734947 prefixEnd_2734947 34675120384499166444067 := by
  unfold tailWord_2734947
  simp only [CollatzResearch.WordTrace]
  refine ⟨99751712022761585605635095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66501141348507723737090063 99751712022761585605635095)
  ·
    refine ⟨149627568034142378408452643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99751712022761585605635095 149627568034142378408452643)
    ·
      refine ⟨224441352051213567612678965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149627568034142378408452643 224441352051213567612678965)
      ·
        refine ⟨21041376754801271963688653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224441352051213567612678965 21041376754801271963688653)
        ·
          refine ⟨7890516283050476986383245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21041376754801271963688653 7890516283050476986383245)
          ·
            refine ⟨2958943606143928869893717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7890516283050476986383245 2958943606143928869893717)
            ·
              refine ⟨34675120384499166444067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2958943606143928869893717 34675120384499166444067)
              ·
                rfl

theorem cell22_2734947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 8].length) (baseStart_2734947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2734947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2734947 prefixEnd_2734947 := by exact prefixLift 2734947
  have htrace : WordTrace (prefixWord ++ tailWord_2734947) baseStart_2734947 baseEnd_2734947 := by
    simpa [prefixWord, tailWord_2734947, baseEnd_2734947] using wordTrace_append hprefix tailTrace_2734947
  have hstable : (prefixWord ++ tailWord_2734947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734947).length < 2 ^ (prefixWord ++ tailWord_2734947).sum := by decide
  have hdescent : baseEnd_2734947 < baseStart_2734947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735009 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 5]
def baseStart_2735009 : Nat := 118140960795 + 2735009 * 2 ^ 59
def prefixEnd_2735009 : Nat := 4983230072969 + 3 ^ 40 * 2735009 * 2
def baseEnd_2735009 : Nat := 312083158082843332979873

theorem tailTrace_2735009 : CollatzResearch.WordTrace tailWord_2735009 prefixEnd_2735009 312083158082843332979873 := by
  unfold tailWord_2735009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99753973348536970194392081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66502648899024646796261387 99753973348536970194392081)
  ·
    refine ⟨74815480011402727645794061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99753973348536970194392081 74815480011402727645794061)
    ·
      refine ⟨28055805004276022867172773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74815480011402727645794061 28055805004276022867172773)
      ·
        refine ⟨5260463438301754287594895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28055805004276022867172773 5260463438301754287594895)
        ·
          refine ⟨7890695157452631431392343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260463438301754287594895 7890695157452631431392343)
          ·
            refine ⟨11836042736178947147088515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890695157452631431392343 11836042736178947147088515)
            ·
              refine ⟨17754064104268420720632773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836042736178947147088515 17754064104268420720632773)
              ·
                refine ⟨3328887019550328885118645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17754064104268420720632773 3328887019550328885118645)
                ·
                  refine ⟨312083158082843332979873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3328887019550328885118645 312083158082843332979873)
                  ·
                    rfl

theorem cell22_2735009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_2735009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735009 prefixEnd_2735009 := by exact prefixLift 2735009
  have htrace : WordTrace (prefixWord ++ tailWord_2735009) baseStart_2735009 baseEnd_2735009 := by
    simpa [prefixWord, tailWord_2735009, baseEnd_2735009] using wordTrace_append hprefix tailTrace_2735009
  have hstable : (prefixWord ++ tailWord_2735009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735009).length < 2 ^ (prefixWord ++ tailWord_2735009).sum := by decide
  have hdescent : baseEnd_2735009 < baseStart_2735009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735097 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2735097 : Nat := 118140960795 + 2735097 * 2 ^ 59
def prefixEnd_2735097 : Nat := 4983230072969 + 3 ^ 40 * 2735097 * 2
def baseEnd_2735097 : Nat := 936279598446927102739349

theorem tailTrace_2735097 : CollatzResearch.WordTrace tailWord_2735097 prefixEnd_2735097 936279598446927102739349 := by
  unfold tailWord_2735097
  simp only [CollatzResearch.WordTrace]
  refine ⟨99757182972218161223595545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66504788648145440815730363 99757182972218161223595545)
  ·
    refine ⟨74817887229163620917696659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99757182972218161223595545 74817887229163620917696659)
    ·
      refine ⟨112226830843745431376544989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74817887229163620917696659 112226830843745431376544989)
      ·
        refine ⟨42085061566404536766204371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112226830843745431376544989 42085061566404536766204371)
        ·
          refine ⟨63127592349606805149306557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42085061566404536766204371 63127592349606805149306557)
          ·
            refine ⟨23672847131102551930989959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63127592349606805149306557 23672847131102551930989959)
            ·
              refine ⟨35509270696653827896484939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23672847131102551930989959 35509270696653827896484939)
              ·
                refine ⟨53263906044980741844727409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35509270696653827896484939 53263906044980741844727409)
                ·
                  refine ⟨39947929533735556383545557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53263906044980741844727409 39947929533735556383545557)
                  ·
                    refine ⟨936279598446927102739349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39947929533735556383545557 936279598446927102739349)
                    ·
                      rfl

theorem cell22_2735097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2735097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735097 prefixEnd_2735097 := by exact prefixLift 2735097
  have htrace : WordTrace (prefixWord ++ tailWord_2735097) baseStart_2735097 baseEnd_2735097 := by
    simpa [prefixWord, tailWord_2735097, baseEnd_2735097] using wordTrace_append hprefix tailTrace_2735097
  have hstable : (prefixWord ++ tailWord_2735097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735097).length < 2 ^ (prefixWord ++ tailWord_2735097).sum := by decide
  have hdescent : baseEnd_2735097 < baseStart_2735097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735122 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2735122 : Nat := 118140960795 + 2735122 * 2 ^ 59
def prefixEnd_2735122 : Nat := 4983230072969 + 3 ^ 40 * 2735122 * 2
def baseEnd_2735122 : Nat := 312096052152611790288091

theorem tailTrace_2735122 : CollatzResearch.WordTrace tailWord_2735122 prefixEnd_2735122 312096052152611790288091 := by
  unfold tailWord_2735122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939523699281897623313905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66505396531418393662170413 24939523699281897623313905)
  ·
    refine ⟨18704642774461423217485429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24939523699281897623313905 18704642774461423217485429)
    ·
      refine ⟨1753560260105758426639259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18704642774461423217485429 1753560260105758426639259)
      ·
        refine ⟨2630340390158637639958889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753560260105758426639259 2630340390158637639958889)
        ·
          refine ⟨1972755292618978229969167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630340390158637639958889 1972755292618978229969167)
          ·
            refine ⟨2959132938928467344953751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972755292618978229969167 2959132938928467344953751)
            ·
              refine ⟨4438699408392701017430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959132938928467344953751 4438699408392701017430627)
              ·
                refine ⟨6658049112589051526145941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438699408392701017430627 6658049112589051526145941)
                ·
                  refine ⟨312096052152611790288091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6658049112589051526145941 312096052152611790288091)
                  ·
                    rfl

theorem cell22_2735122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2735122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735122 prefixEnd_2735122 := by exact prefixLift 2735122
  have htrace : WordTrace (prefixWord ++ tailWord_2735122) baseStart_2735122 baseEnd_2735122 := by
    simpa [prefixWord, tailWord_2735122, baseEnd_2735122] using wordTrace_append hprefix tailTrace_2735122
  have hstable : (prefixWord ++ tailWord_2735122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735122).length < 2 ^ (prefixWord ++ tailWord_2735122).sum := by decide
  have hdescent : baseEnd_2735122 < baseStart_2735122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735189 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 6]
def baseStart_2735189 : Nat := 118140960795 + 2735189 * 2 ^ 59
def prefixEnd_2735189 : Nat := 4983230072969 + 3 ^ 40 * 2735189 * 2
def baseEnd_2735189 : Nat := 312103697309023176479689

theorem tailTrace_2735189 : CollatzResearch.WordTrace tailWord_2735189 prefixEnd_2735189 312103697309023176479689 := by
  unfold tailWord_2735189
  simp only [CollatzResearch.WordTrace]
  refine ⟨99760538487884860935944621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66507025658589907290629747 99760538487884860935944621)
  ·
    refine ⟨37410201932956822850979233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99760538487884860935944621 37410201932956822850979233)
    ·
      refine ⟨28057651449717617138234425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37410201932956822850979233 28057651449717617138234425)
      ·
        refine ⟨21043238587288212853675819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28057651449717617138234425 21043238587288212853675819)
        ·
          refine ⟨31564857880932319280513729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21043238587288212853675819 31564857880932319280513729)
          ·
            refine ⟨23673643410699239460385297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31564857880932319280513729 23673643410699239460385297)
            ·
              refine ⟨17755232558024429595288973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23673643410699239460385297 17755232558024429595288973)
              ·
                refine ⟨6658212209259161098233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17755232558024429595288973 6658212209259161098233365)
                ·
                  refine ⟨312103697309023176479689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6658212209259161098233365 312103697309023176479689)
                  ·
                    rfl

theorem cell22_2735189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_2735189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735189 prefixEnd_2735189 := by exact prefixLift 2735189
  have htrace : WordTrace (prefixWord ++ tailWord_2735189) baseStart_2735189 baseEnd_2735189 := by
    simpa [prefixWord, tailWord_2735189, baseEnd_2735189] using wordTrace_append hprefix tailTrace_2735189
  have hstable : (prefixWord ++ tailWord_2735189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735189).length < 2 ^ (prefixWord ++ tailWord_2735189).sum := by decide
  have hdescent : baseEnd_2735189 < baseStart_2735189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735225 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_2735225 : Nat := 118140960795 + 2735225 * 2 ^ 59
def prefixEnd_2735225 : Nat := 4983230072969 + 3 ^ 40 * 2735225 * 2
def baseEnd_2735225 : Nat := 936323415462777435538957

theorem tailTrace_2735225 : CollatzResearch.WordTrace tailWord_2735225 prefixEnd_2735225 936323415462777435538957 := by
  unfold tailWord_2735225
  simp only [CollatzResearch.WordTrace]
  refine ⟨99761851515754439084255129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66507901010502959389503419 99761851515754439084255129)
  ·
    refine ⟨74821388636815829313191347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99761851515754439084255129 74821388636815829313191347)
    ·
      refine ⟨112232082955223743969787021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74821388636815829313191347 112232082955223743969787021)
      ·
        refine ⟨42087031108208903988670133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112232082955223743969787021 42087031108208903988670133)
        ·
          refine ⟨3945659166394584748937825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42087031108208903988670133 3945659166394584748937825)
          ·
            refine ⟨2959244374795938561703369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945659166394584748937825 2959244374795938561703369)
            ·
              refine ⟨2219433281096953921277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959244374795938561703369 2219433281096953921277527)
              ·
                refine ⟨3329149921645430881916291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219433281096953921277527 3329149921645430881916291)
                ·
                  refine ⟨4993724882468146322874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329149921645430881916291 4993724882468146322874437)
                  ·
                    refine ⟨936323415462777435538957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4993724882468146322874437 936323415462777435538957)
                    ·
                      rfl

theorem cell22_2735225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_2735225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735225 prefixEnd_2735225 := by exact prefixLift 2735225
  have htrace : WordTrace (prefixWord ++ tailWord_2735225) baseStart_2735225 baseEnd_2735225 := by
    simpa [prefixWord, tailWord_2735225, baseEnd_2735225] using wordTrace_append hprefix tailTrace_2735225
  have hstable : (prefixWord ++ tailWord_2735225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735225).length < 2 ^ (prefixWord ++ tailWord_2735225).sum := by decide
  have hdescent : baseEnd_2735225 < baseStart_2735225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735255 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 2, 3]
def baseStart_2735255 : Nat := 118140960795 + 2735255 * 2 ^ 59
def prefixEnd_2735255 : Nat := 4983230072969 + 3 ^ 40 * 2735255 * 2
def baseEnd_2735255 : Nat := 936333685075867357288865

theorem tailTrace_2735255 : CollatzResearch.WordTrace tailWord_2735255 prefixEnd_2735255 936333685075867357288865 := by
  unfold tailWord_2735255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99762945705645754207847219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66508630470430502805231479 99762945705645754207847219)
  ·
    refine ⟨149644418558468631311770829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99762945705645754207847219 149644418558468631311770829)
    ·
      refine ⟨56116656959425736741914061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149644418558468631311770829 56116656959425736741914061)
      ·
        refine ⟨21043746359784651278217773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56116656959425736741914061 21043746359784651278217773)
        ·
          refine ⟨7891404884919244229331665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21043746359784651278217773 7891404884919244229331665)
          ·
            refine ⟨5918553663689433171998749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891404884919244229331665 5918553663689433171998749)
            ·
              refine ⟨2219457623883537439499531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5918553663689433171998749 2219457623883537439499531)
              ·
                refine ⟨3329186435825306159249297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219457623883537439499531 3329186435825306159249297)
                ·
                  refine ⟨2496889826868979619436973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329186435825306159249297 2496889826868979619436973)
                  ·
                    refine ⟨936333685075867357288865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496889826868979619436973 936333685075867357288865)
                    ·
                      rfl

theorem cell22_2735255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_2735255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735255 prefixEnd_2735255 := by exact prefixLift 2735255
  have htrace : WordTrace (prefixWord ++ tailWord_2735255) baseStart_2735255 baseEnd_2735255 := by
    simpa [prefixWord, tailWord_2735255, baseEnd_2735255] using wordTrace_append hprefix tailTrace_2735255
  have hstable : (prefixWord ++ tailWord_2735255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735255).length < 2 ^ (prefixWord ++ tailWord_2735255).sum := by decide
  have hdescent : baseEnd_2735255 < baseStart_2735255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735268 : List Nat := [2, 3, 1, 2, 3, 3, 2, 6]
def baseStart_2735268 : Nat := 118140960795 + 2735268 * 2 ^ 59
def prefixEnd_2735268 : Nat := 4983230072969 + 3 ^ 40 * 2735268 * 2
def baseEnd_2735268 : Nat := 104037570582393295190425

theorem tailTrace_2735268 : CollatzResearch.WordTrace tailWord_2735268 prefixEnd_2735268 104037570582393295190425 := by
  unfold tailWord_2735268
  simp only [CollatzResearch.WordTrace]
  refine ⟨49881709927299328714035229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66508946569732438285380305 49881709927299328714035229)
  ·
    refine ⟨18705641222737248267763211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49881709927299328714035229 18705641222737248267763211)
    ·
      refine ⟨28058461834105872401644817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18705641222737248267763211 28058461834105872401644817)
      ·
        refine ⟨21043846375579404301233613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28058461834105872401644817 21043846375579404301233613)
        ·
          refine ⟨7891442390842276612962605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21043846375579404301233613 7891442390842276612962605)
          ·
            refine ⟨2959290896565853729860977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7891442390842276612962605 2959290896565853729860977)
            ·
              refine ⟨2219468172424390297395733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959290896565853729860977 2219468172424390297395733)
              ·
                refine ⟨104037570582393295190425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2219468172424390297395733 104037570582393295190425)
                ·
                  rfl

theorem cell22_2735268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_2735268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735268 prefixEnd_2735268 := by exact prefixLift 2735268
  have htrace : WordTrace (prefixWord ++ tailWord_2735268) baseStart_2735268 baseEnd_2735268 := by
    simpa [prefixWord, tailWord_2735268, baseEnd_2735268] using wordTrace_append hprefix tailTrace_2735268
  have hstable : (prefixWord ++ tailWord_2735268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735268).length < 2 ^ (prefixWord ++ tailWord_2735268).sum := by decide
  have hdescent : baseEnd_2735268 < baseStart_2735268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735279 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 7]
def baseStart_2735279 : Nat := 118140960795 + 2735279 * 2 ^ 59
def prefixEnd_2735279 : Nat := 4983230072969 + 3 ^ 40 * 2735279 * 2
def baseEnd_2735279 : Nat := 312113966922113098229597

theorem tailTrace_2735279 : CollatzResearch.WordTrace tailWord_2735279 prefixEnd_2735279 312113966922113098229597 := by
  unfold tailWord_2735279
  simp only [CollatzResearch.WordTrace]
  refine ⟨99763821057558806306720891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66509214038372537537813927 99763821057558806306720891)
  ·
    refine ⟨149645731586338209460081337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99763821057558806306720891 149645731586338209460081337)
    ·
      refine ⟨112234298689753657095061003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149645731586338209460081337 112234298689753657095061003)
      ·
        refine ⟨168351448034630485642591505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112234298689753657095061003 168351448034630485642591505)
        ·
          refine ⟨126263586025972864231943629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168351448034630485642591505 126263586025972864231943629)
          ·
            refine ⟨47348844759739824086978861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126263586025972864231943629 47348844759739824086978861)
            ·
              refine ⟨17755816784902434032617073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47348844759739824086978861 17755816784902434032617073)
              ·
                refine ⟨13316862588676825524462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17755816784902434032617073 13316862588676825524462805)
                ·
                  refine ⟨312113966922113098229597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13316862588676825524462805 312113966922113098229597)
                  ·
                    rfl

theorem cell22_2735279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_2735279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735279 prefixEnd_2735279 := by exact prefixLift 2735279
  have htrace : WordTrace (prefixWord ++ tailWord_2735279) baseStart_2735279 baseEnd_2735279 := by
    simpa [prefixWord, tailWord_2735279, baseEnd_2735279] using wordTrace_append hprefix tailTrace_2735279
  have hstable : (prefixWord ++ tailWord_2735279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735279).length < 2 ^ (prefixWord ++ tailWord_2735279).sum := by decide
  have hdescent : baseEnd_2735279 < baseStart_2735279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735302 : List Nat := [6, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2735302 : Nat := 118140960795 + 2735302 * 2 ^ 59
def prefixEnd_2735302 : Nat := 4983230072969 + 3 ^ 40 * 2735302 * 2
def baseEnd_2735302 : Nat := 104038863792930544595969

theorem tailTrace_2735302 : CollatzResearch.WordTrace tailWord_2735302 prefixEnd_2735302 104038863792930544595969 := by
  unfold tailWord_2735302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117645623014858788587755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66509773290983654156538773 3117645623014858788587755)
  ·
    refine ⟨4676468434522288182881633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117645623014858788587755 4676468434522288182881633)
    ·
      refine ⟨3507351325891716137161225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676468434522288182881633 3507351325891716137161225)
      ·
        refine ⟨2630513494418787102870919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507351325891716137161225 2630513494418787102870919)
        ·
          refine ⟨3945770241628180654306379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630513494418787102870919 3945770241628180654306379)
          ·
            refine ⟨5918655362442270981459569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945770241628180654306379 5918655362442270981459569)
            ·
              refine ⟨4438991521831703236094677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918655362442270981459569 4438991521831703236094677)
              ·
                refine ⟨104038863792930544595969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4438991521831703236094677 104038863792930544595969)
                ·
                  rfl

theorem cell22_2735302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2735302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735302 prefixEnd_2735302 := by exact prefixLift 2735302
  have htrace : WordTrace (prefixWord ++ tailWord_2735302) baseStart_2735302 baseEnd_2735302 := by
    simpa [prefixWord, tailWord_2735302, baseEnd_2735302] using wordTrace_append hprefix tailTrace_2735302
  have hstable : (prefixWord ++ tailWord_2735302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735302).length < 2 ^ (prefixWord ++ tailWord_2735302).sum := by decide
  have hdescent : baseEnd_2735302 < baseStart_2735302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735388 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2735388 : Nat := 118140960795 + 2735388 * 2 ^ 59
def prefixEnd_2735388 : Nat := 4983230072969 + 3 ^ 40 * 2735388 * 2
def baseEnd_2735388 : Nat := 936379213693899343713457

theorem tailTrace_2735388 : CollatzResearch.WordTrace tailWord_2735388 prefixEnd_2735388 936379213693899343713457 := by
  unfold tailWord_2735388
  simp only [CollatzResearch.WordTrace]
  refine ⟨49883898307081958961219409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66511864409442611948292545 49883898307081958961219409)
  ·
    refine ⟨37412923730311469220914557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49883898307081958961219409 37412923730311469220914557)
    ·
      refine ⟨14029846398866800957842959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37412923730311469220914557 14029846398866800957842959)
      ·
        refine ⟨21044769598300201436764439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029846398866800957842959 21044769598300201436764439)
        ·
          refine ⟨31567154397450302155146659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21044769598300201436764439 31567154397450302155146659)
          ·
            refine ⟨47350731596175453232719989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31567154397450302155146659 47350731596175453232719989)
            ·
              refine ⟨4439131087141448740567499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47350731596175453232719989 4439131087141448740567499)
              ·
                refine ⟨6658696630712173110851249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439131087141448740567499 6658696630712173110851249)
                ·
                  refine ⟨4994022473034129833138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658696630712173110851249 4994022473034129833138437)
                  ·
                    refine ⟨936379213693899343713457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994022473034129833138437 936379213693899343713457)
                    ·
                      rfl

theorem cell22_2735388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2735388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735388 prefixEnd_2735388 := by exact prefixLift 2735388
  have htrace : WordTrace (prefixWord ++ tailWord_2735388) baseStart_2735388 baseEnd_2735388 := by
    simpa [prefixWord, tailWord_2735388, baseEnd_2735388] using wordTrace_append hprefix tailTrace_2735388
  have hstable : (prefixWord ++ tailWord_2735388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735388).length < 2 ^ (prefixWord ++ tailWord_2735388).sum := by decide
  have hdescent : baseEnd_2735388 < baseStart_2735388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735394 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2735394 : Nat := 118140960795 + 2735394 * 2 ^ 59
def prefixEnd_2735394 : Nat := 4983230072969 + 3 ^ 40 * 2735394 * 2
def baseEnd_2735394 : Nat := 936381267616517328063439

theorem tailTrace_2735394 : CollatzResearch.WordTrace tailWord_2735394 prefixEnd_2735394 936381267616517328063439 := by
  unfold tailWord_2735394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942003863035545236789309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66512010301428120631438157 24942003863035545236789309)
  ·
    refine ⟨9353251448638329463795991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24942003863035545236789309 9353251448638329463795991)
    ·
      refine ⟨14029877172957494195693987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353251448638329463795991 14029877172957494195693987)
      ·
        refine ⟨21044815759436241293540981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029877172957494195693987 21044815759436241293540981)
        ·
          refine ⟨1972951477447147621269467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21044815759436241293540981 1972951477447147621269467)
          ·
            refine ⟨2959427216170721431904201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972951477447147621269467 2959427216170721431904201)
            ·
              refine ⟨2219570412128041073928151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959427216170721431904201 2219570412128041073928151)
              ·
                refine ⟨3329355618192061610892227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219570412128041073928151 3329355618192061610892227)
                ·
                  refine ⟨4994033427288092416338341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329355618192061610892227 4994033427288092416338341)
                  ·
                    refine ⟨936381267616517328063439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994033427288092416338341 936381267616517328063439)
                    ·
                      rfl

theorem cell22_2735394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2735394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735394 prefixEnd_2735394 := by exact prefixLift 2735394
  have htrace : WordTrace (prefixWord ++ tailWord_2735394) baseStart_2735394 baseEnd_2735394 := by
    simpa [prefixWord, tailWord_2735394, baseEnd_2735394] using wordTrace_append hprefix tailTrace_2735394
  have hstable : (prefixWord ++ tailWord_2735394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735394).length < 2 ^ (prefixWord ++ tailWord_2735394).sum := by decide
  have hdescent : baseEnd_2735394 < baseStart_2735394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735469 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2735469 : Nat := 118140960795 + 2735469 * 2 ^ 59
def prefixEnd_2735469 : Nat := 4983230072969 + 3 ^ 40 * 2735469 * 2
def baseEnd_2735469 : Nat := 936406941649242132438209

theorem tailTrace_2735469 : CollatzResearch.WordTrace tailWord_2735469 prefixEnd_2735469 936406941649242132438209 := by
  unfold tailWord_2735469
  simp only [CollatzResearch.WordTrace]
  refine ⟨99770750926870468756137461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66513833951246979170758307 99770750926870468756137461)
  ·
    refine ⟨9353507899394106445887887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99770750926870468756137461 9353507899394106445887887)
    ·
      refine ⟨14030261849091159668831831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353507899394106445887887 14030261849091159668831831)
      ·
        refine ⟨21045392773636739503247747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030261849091159668831831 21045392773636739503247747)
        ·
          refine ⟨31568089160455109254871621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21045392773636739503247747 31568089160455109254871621)
          ·
            refine ⟨5919016717585332985288429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31568089160455109254871621 5919016717585332985288429)
            ·
              refine ⟨2219631269094499869483161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5919016717585332985288429 2219631269094499869483161)
              ·
                refine ⟨1664723451820874902112371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219631269094499869483161 1664723451820874902112371)
                ·
                  refine ⟨2497085177731312353168557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664723451820874902112371 2497085177731312353168557)
                  ·
                    refine ⟨936406941649242132438209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497085177731312353168557 936406941649242132438209)
                    ·
                      rfl

theorem cell22_2735469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2735469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735469 prefixEnd_2735469 := by exact prefixLift 2735469
  have htrace : WordTrace (prefixWord ++ tailWord_2735469) baseStart_2735469 baseEnd_2735469 := by
    simpa [prefixWord, tailWord_2735469, baseEnd_2735469] using wordTrace_append hprefix tailTrace_2735469
  have hstable : (prefixWord ++ tailWord_2735469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735469).length < 2 ^ (prefixWord ++ tailWord_2735469).sum := by decide
  have hdescent : baseEnd_2735469 < baseStart_2735469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735495 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2735495 : Nat := 118140960795 + 2735495 * 2 ^ 59
def prefixEnd_2735495 : Nat := 4983230072969 + 3 ^ 40 * 2735495 * 2
def baseEnd_2735495 : Nat := 936415841980586731288129

theorem tailTrace_2735495 : CollatzResearch.WordTrace tailWord_2735495 prefixEnd_2735495 936415841980586731288129 := by
  unfold tailWord_2735495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99771699224776275196583939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66514466149850850131055959 99771699224776275196583939)
  ·
    refine ⟨149657548837164412794875909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99771699224776275196583939 149657548837164412794875909)
    ·
      refine ⟨28060790406968327399039233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149657548837164412794875909 28060790406968327399039233)
      ·
        refine ⟨21045592805226245549279425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28060790406968327399039233 21045592805226245549279425)
        ·
          refine ⟨15784194603919684161959569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21045592805226245549279425 15784194603919684161959569)
          ·
            refine ⟨11838145952939763121469677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15784194603919684161959569 11838145952939763121469677)
            ·
              refine ⟨4439304732352411170551129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11838145952939763121469677 4439304732352411170551129)
              ·
                refine ⟨3329478549264308377913347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439304732352411170551129 3329478549264308377913347)
                ·
                  refine ⟨4994217823896462566870021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329478549264308377913347 4994217823896462566870021)
                  ·
                    refine ⟨936415841980586731288129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994217823896462566870021 936415841980586731288129)
                    ·
                      rfl

theorem cell22_2735495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2735495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735495 prefixEnd_2735495 := by exact prefixLift 2735495
  have htrace : WordTrace (prefixWord ++ tailWord_2735495) baseStart_2735495 baseEnd_2735495 := by
    simpa [prefixWord, tailWord_2735495, baseEnd_2735495] using wordTrace_append hprefix tailTrace_2735495
  have hstable : (prefixWord ++ tailWord_2735495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735495).length < 2 ^ (prefixWord ++ tailWord_2735495).sum := by decide
  have hdescent : baseEnd_2735495 < baseStart_2735495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735521 : List Nat := [1, 2, 3, 16]
def baseStart_2735521 : Nat := 118140960795 + 2735521 * 2 ^ 59
def prefixEnd_2735521 : Nat := 4983230072969 + 3 ^ 40 * 2735521 * 2
def baseEnd_2735521 : Nat := 1284533254200180151081

theorem tailTrace_2735521 : CollatzResearch.WordTrace tailWord_2735521 prefixEnd_2735521 1284533254200180151081 := by
  unfold tailWord_2735521
  simp only [CollatzResearch.WordTrace]
  refine ⟨99772647522682081637030417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66515098348454721091353611 99772647522682081637030417)
  ·
    refine ⟨74829485642011561227772813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99772647522682081637030417 74829485642011561227772813)
    ·
      refine ⟨28061057115754335460414805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74829485642011561227772813 28061057115754335460414805)
      ·
        refine ⟨1284533254200180151081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 28061057115754335460414805 1284533254200180151081)
        ·
          rfl

theorem cell22_2735521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 16].length) (baseStart_2735521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735521 prefixEnd_2735521 := by exact prefixLift 2735521
  have htrace : WordTrace (prefixWord ++ tailWord_2735521) baseStart_2735521 baseEnd_2735521 := by
    simpa [prefixWord, tailWord_2735521, baseEnd_2735521] using wordTrace_append hprefix tailTrace_2735521
  have hstable : (prefixWord ++ tailWord_2735521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735521).length < 2 ^ (prefixWord ++ tailWord_2735521).sum := by decide
  have hdescent : baseEnd_2735521 < baseStart_2735521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735523 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_2735523 : Nat := 118140960795 + 2735523 * 2 ^ 59
def prefixEnd_2735523 : Nat := 4983230072969 + 3 ^ 40 * 2735523 * 2
def baseEnd_2735523 : Nat := 936425426952803991588043

theorem tailTrace_2735523 : CollatzResearch.WordTrace tailWord_2735523 prefixEnd_2735523 936425426952803991588043 := by
  unfold tailWord_2735523
  simp only [CollatzResearch.WordTrace]
  refine ⟨99772720468674835978603223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66515146979116557319068815 99772720468674835978603223)
  ·
    refine ⟨149659080703012253967904835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99772720468674835978603223 149659080703012253967904835)
    ·
      refine ⟨224488621054518380951857253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149659080703012253967904835 224488621054518380951857253)
      ·
        refine ⟨42091616447722196428473235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224488621054518380951857253 42091616447722196428473235)
        ·
          refine ⟨63137424671583294642709853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42091616447722196428473235 63137424671583294642709853)
          ·
            refine ⟨23676534251843735491016195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63137424671583294642709853 23676534251843735491016195)
            ·
              refine ⟨35514801377765603236524293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23676534251843735491016195 35514801377765603236524293)
              ·
                refine ⟨6659025258331050606848305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35514801377765603236524293 6659025258331050606848305)
                ·
                  refine ⟨4994268943748287955136229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659025258331050606848305 4994268943748287955136229)
                  ·
                    refine ⟨936425426952803991588043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994268943748287955136229 936425426952803991588043)
                    ·
                      rfl

theorem cell22_2735523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_2735523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735523 prefixEnd_2735523 := by exact prefixLift 2735523
  have htrace : WordTrace (prefixWord ++ tailWord_2735523) baseStart_2735523 baseEnd_2735523 := by
    simpa [prefixWord, tailWord_2735523, baseEnd_2735523] using wordTrace_append hprefix tailTrace_2735523
  have hstable : (prefixWord ++ tailWord_2735523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735523).length < 2 ^ (prefixWord ++ tailWord_2735523).sum := by decide
  have hdescent : baseEnd_2735523 < baseStart_2735523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735583 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 7]
def baseStart_2735583 : Nat := 118140960795 + 2735583 * 2 ^ 59
def prefixEnd_2735583 : Nat := 4983230072969 + 3 ^ 40 * 2735583 * 2
def baseEnd_2735583 : Nat := 312148655392994611695953

theorem tailTrace_2735583 : CollatzResearch.WordTrace tailWord_2735583 prefixEnd_2735583 312148655392994611695953 := by
  unfold tailWord_2735583
  simp only [CollatzResearch.WordTrace]
  refine ⟨99774908848457466225787403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66516605898971644150524935 99774908848457466225787403)
  ·
    refine ⟨149662363272686199338681105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99774908848457466225787403 149662363272686199338681105)
    ·
      refine ⟨112246772454514649504010829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149662363272686199338681105 112246772454514649504010829)
      ·
        refine ⟨42092539670442993564004061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112246772454514649504010829 42092539670442993564004061)
        ·
          refine ⟨15784702376416122586501523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42092539670442993564004061 15784702376416122586501523)
          ·
            refine ⟨23677053564624183879752285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15784702376416122586501523 23677053564624183879752285)
            ·
              refine ⟨8878895086734068954907107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23677053564624183879752285 8878895086734068954907107)
              ·
                refine ⟨13318342630101103432360661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878895086734068954907107 13318342630101103432360661)
                ·
                  refine ⟨312148655392994611695953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13318342630101103432360661 312148655392994611695953)
                  ·
                    rfl

theorem cell22_2735583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_2735583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735583 prefixEnd_2735583 := by exact prefixLift 2735583
  have htrace : WordTrace (prefixWord ++ tailWord_2735583) baseStart_2735583 baseEnd_2735583 := by
    simpa [prefixWord, tailWord_2735583, baseEnd_2735583] using wordTrace_append hprefix tailTrace_2735583
  have hstable : (prefixWord ++ tailWord_2735583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735583).length < 2 ^ (prefixWord ++ tailWord_2735583).sum := by decide
  have hdescent : baseEnd_2735583 < baseStart_2735583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735587 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 3, 3]
def baseStart_2735587 : Nat := 118140960795 + 2735587 * 2 ^ 59
def prefixEnd_2735587 : Nat := 4983230072969 + 3 ^ 40 * 2735587 * 2
def baseEnd_2735587 : Nat := 936447335460729157987847

theorem tailTrace_2735587 : CollatzResearch.WordTrace tailWord_2735587 prefixEnd_2735587 936447335460729157987847 := by
  unfold tailWord_2735587
  simp only [CollatzResearch.WordTrace]
  refine ⟨99775054740442974908933015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66516703160295316605955343 99775054740442974908933015)
  ·
    refine ⟨149662582110664462363399523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99775054740442974908933015 149662582110664462363399523)
    ·
      refine ⟨224493873165996693545099285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149662582110664462363399523 224493873165996693545099285)
      ·
        refine ⟨10523150304656095009926529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224493873165996693545099285 10523150304656095009926529)
        ·
          refine ⟨7892362728492071257444897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10523150304656095009926529 7892362728492071257444897)
          ·
            refine ⟨5919272046369053443083673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892362728492071257444897 5919272046369053443083673)
            ·
              refine ⟨4439454034776790082312755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919272046369053443083673 4439454034776790082312755)
              ·
                refine ⟨6659181052165185123469133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439454034776790082312755 6659181052165185123469133)
                ·
                  refine ⟨2497192894561944421300925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6659181052165185123469133 2497192894561944421300925)
                  ·
                    refine ⟨936447335460729157987847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497192894561944421300925 936447335460729157987847)
                    ·
                      rfl

theorem cell22_2735587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].length) (baseStart_2735587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735587 prefixEnd_2735587 := by exact prefixLift 2735587
  have htrace : WordTrace (prefixWord ++ tailWord_2735587) baseStart_2735587 baseEnd_2735587 := by
    simpa [prefixWord, tailWord_2735587, baseEnd_2735587] using wordTrace_append hprefix tailTrace_2735587
  have hstable : (prefixWord ++ tailWord_2735587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735587).length < 2 ^ (prefixWord ++ tailWord_2735587).sum := by decide
  have hdescent : baseEnd_2735587 < baseStart_2735587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735677 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2735677 : Nat := 118140960795 + 2735677 * 2 ^ 59
def prefixEnd_2735677 : Nat := 4983230072969 + 3 ^ 40 * 2735677 * 2
def baseEnd_2735677 : Nat := 936478144299998923237571

theorem tailTrace_2735677 : CollatzResearch.WordTrace tailWord_2735677 prefixEnd_2735677 936478144299998923237571 := by
  unfold tailWord_2735677
  simp only [CollatzResearch.WordTrace]
  refine ⟨99778337310116920279709285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66518891540077946853139523 99778337310116920279709285)
  ·
    refine ⟨18708438245646922552445491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99778337310116920279709285 18708438245646922552445491)
    ·
      refine ⟨28062657368470383828668237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18708438245646922552445491 28062657368470383828668237)
      ·
        refine ⟨10523496513176393935750589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28062657368470383828668237 10523496513176393935750589)
        ·
          refine ⟨3946311192441147725906471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10523496513176393935750589 3946311192441147725906471)
          ·
            refine ⟨5919466788661721588859707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946311192441147725906471 5919466788661721588859707)
            ·
              refine ⟨8879200182992582383289561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919466788661721588859707 8879200182992582383289561)
              ·
                refine ⟨6659400137244436787467171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879200182992582383289561 6659400137244436787467171)
                ·
                  refine ⟨9989100205866655181200757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6659400137244436787467171 9989100205866655181200757)
                  ·
                    refine ⟨936478144299998923237571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9989100205866655181200757 936478144299998923237571)
                    ·
                      rfl

theorem cell22_2735677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2735677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735677 prefixEnd_2735677 := by exact prefixLift 2735677
  have htrace : WordTrace (prefixWord ++ tailWord_2735677) baseStart_2735677 baseEnd_2735677 := by
    simpa [prefixWord, tailWord_2735677, baseEnd_2735677] using wordTrace_append hprefix tailTrace_2735677
  have hstable : (prefixWord ++ tailWord_2735677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735677).length < 2 ^ (prefixWord ++ tailWord_2735677).sum := by decide
  have hdescent : baseEnd_2735677 < baseStart_2735677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735705 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_2735705 : Nat := 118140960795 + 2735705 * 2 ^ 59
def prefixEnd_2735705 : Nat := 4983230072969 + 3 ^ 40 * 2735705 * 2
def baseEnd_2735705 : Nat := 936487729272216183537485

theorem tailTrace_2735705 : CollatzResearch.WordTrace tailWord_2735705 prefixEnd_2735705 936487729272216183537485 := by
  unfold tailWord_2735705
  simp only [CollatzResearch.WordTrace]
  refine ⟨99779358554015481061728569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66519572369343654041152379 99779358554015481061728569)
  ·
    refine ⟨74834518915511610796296427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99779358554015481061728569 74834518915511610796296427)
    ·
      refine ⟨112251778373267416194444641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74834518915511610796296427 112251778373267416194444641)
      ·
        refine ⟨84188833779950562145833481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112251778373267416194444641 84188833779950562145833481)
        ·
          refine ⟨63141625334962921609375111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84188833779950562145833481 63141625334962921609375111)
          ·
            refine ⟨94712438002444382414062667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63141625334962921609375111 94712438002444382414062667)
            ·
              refine ⟨142068657003666573621094001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94712438002444382414062667 142068657003666573621094001)
              ·
                refine ⟨106551492752749930215820501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142068657003666573621094001 106551492752749930215820501)
                ·
                  refine ⟨2497300611392576489433293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106551492752749930215820501 2497300611392576489433293)
                  ·
                    refine ⟨936487729272216183537485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497300611392576489433293 936487729272216183537485)
                    ·
                      rfl

theorem cell22_2735705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_2735705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735705 prefixEnd_2735705 := by exact prefixLift 2735705
  have htrace : WordTrace (prefixWord ++ tailWord_2735705) baseStart_2735705 baseEnd_2735705 := by
    simpa [prefixWord, tailWord_2735705, baseEnd_2735705] using wordTrace_append hprefix tailTrace_2735705
  have hstable : (prefixWord ++ tailWord_2735705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735705).length < 2 ^ (prefixWord ++ tailWord_2735705).sum := by decide
  have hdescent : baseEnd_2735705 < baseStart_2735705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735722 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2735722 : Nat := 118140960795 + 2735722 * 2 ^ 59
def prefixEnd_2735722 : Nat := 4983230072969 + 3 ^ 40 * 2735722 * 2
def baseEnd_2735722 : Nat := 936493548719633805862433

theorem tailTrace_2735722 : CollatzResearch.WordTrace tailWord_2735722 prefixEnd_2735722 936493548719633805862433 := by
  unfold tailWord_2735722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24944994648738473241274355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66519985729969261976731613 24944994648738473241274355)
  ·
    refine ⟨37417491973107709861911533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24944994648738473241274355 37417491973107709861911533)
    ·
      refine ⟨14031559489915391198216825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37417491973107709861911533 14031559489915391198216825)
      ·
        refine ⟨10523669617436543398662619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14031559489915391198216825 10523669617436543398662619)
        ·
          refine ⟨15785504426154815097993929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10523669617436543398662619 15785504426154815097993929)
          ·
            refine ⟨11839128319616111323495447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15785504426154815097993929 11839128319616111323495447)
            ·
              refine ⟨17758692479424166985243171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11839128319616111323495447 17758692479424166985243171)
              ·
                refine ⟨26638038719136250477864757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17758692479424166985243171 26638038719136250477864757)
                ·
                  refine ⟨2497316129919023482299821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26638038719136250477864757 2497316129919023482299821)
                  ·
                    refine ⟨936493548719633805862433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497316129919023482299821 936493548719633805862433)
                    ·
                      rfl

theorem cell22_2735722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2735722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735722 prefixEnd_2735722 := by exact prefixLift 2735722
  have htrace : WordTrace (prefixWord ++ tailWord_2735722) baseStart_2735722 baseEnd_2735722 := by
    simpa [prefixWord, tailWord_2735722, baseEnd_2735722] using wordTrace_append hprefix tailTrace_2735722
  have hstable : (prefixWord ++ tailWord_2735722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735722).length < 2 ^ (prefixWord ++ tailWord_2735722).sum := by decide
  have hdescent : baseEnd_2735722 < baseStart_2735722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735726 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2735726 : Nat := 118140960795 + 2735726 * 2 ^ 59
def prefixEnd_2735726 : Nat := 4983230072969 + 3 ^ 40 * 2735726 * 2
def baseEnd_2735726 : Nat := 936494918001379128762421

theorem tailTrace_2735726 : CollatzResearch.WordTrace tailWord_2735726 prefixEnd_2735726 936494918001379128762421 := by
  unfold tailWord_2735726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472515560867425206030379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66520082991292934432162021 12472515560867425206030379)
  ·
    refine ⟨18708773341301137809045569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472515560867425206030379 18708773341301137809045569)
    ·
      refine ⟨14031580005975853356784177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18708773341301137809045569 14031580005975853356784177)
      ·
        refine ⟨10523685004481890017588133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14031580005975853356784177 10523685004481890017588133)
        ·
          refine ⟨1973190938340354378297775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10523685004481890017588133 1973190938340354378297775)
          ·
            refine ⟨2959786407510531567446663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973190938340354378297775 2959786407510531567446663)
            ·
              refine ⟨4439679611265797351169995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959786407510531567446663 4439679611265797351169995)
              ·
                refine ⟨6659519416898696026754993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439679611265797351169995 6659519416898696026754993)
                ·
                  refine ⟨4994639562674022020066245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659519416898696026754993 4994639562674022020066245)
                  ·
                    refine ⟨936494918001379128762421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994639562674022020066245 936494918001379128762421)
                    ·
                      rfl

theorem cell22_2735726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2735726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735726 prefixEnd_2735726 := by exact prefixLift 2735726
  have htrace : WordTrace (prefixWord ++ tailWord_2735726) baseStart_2735726 baseEnd_2735726 := by
    simpa [prefixWord, tailWord_2735726, baseEnd_2735726] using wordTrace_append hprefix tailTrace_2735726
  have hstable : (prefixWord ++ tailWord_2735726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735726).length < 2 ^ (prefixWord ++ tailWord_2735726).sum := by decide
  have hdescent : baseEnd_2735726 < baseStart_2735726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735739 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 1, 3]
def baseStart_2735739 : Nat := 118140960795 + 2735739 * 2 ^ 59
def prefixEnd_2735739 : Nat := 4983230072969 + 3 ^ 40 * 2735739 * 2
def baseEnd_2735739 : Nat := 936499368167051428187381

theorem tailTrace_2735739 : CollatzResearch.WordTrace tailWord_2735739 prefixEnd_2735739 936499368167051428187381 := by
  unfold tailWord_2735739
  simp only [CollatzResearch.WordTrace]
  refine ⟨99780598635892304868466271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66520399090594869912310847 99780598635892304868466271)
  ·
    refine ⟨149670897953838457302699407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99780598635892304868466271 149670897953838457302699407)
    ·
      refine ⟨224506346930757685954049111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149670897953838457302699407 224506346930757685954049111)
      ·
        refine ⟨336759520396136528931073667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224506346930757685954049111 336759520396136528931073667)
        ·
          refine ⟨505139280594204793396610501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336759520396136528931073667 505139280594204793396610501)
          ·
            refine ⟨94713615111413398761864469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 505139280594204793396610501 94713615111413398761864469)
            ·
              refine ⟨4439700708347503066962397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94713615111413398761864469 4439700708347503066962397)
              ·
                refine ⟨1664887765630313650110899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439700708347503066962397 1664887765630313650110899)
                ·
                  refine ⟨2497331648445470475166349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664887765630313650110899 2497331648445470475166349)
                  ·
                    refine ⟨936499368167051428187381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497331648445470475166349 936499368167051428187381)
                    ·
                      rfl

theorem cell22_2735739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 3].length) (baseStart_2735739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735739 prefixEnd_2735739 := by exact prefixLift 2735739
  have htrace : WordTrace (prefixWord ++ tailWord_2735739) baseStart_2735739 baseEnd_2735739 := by
    simpa [prefixWord, tailWord_2735739, baseEnd_2735739] using wordTrace_append hprefix tailTrace_2735739
  have hstable : (prefixWord ++ tailWord_2735739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735739).length < 2 ^ (prefixWord ++ tailWord_2735739).sum := by decide
  have hdescent : baseEnd_2735739 < baseStart_2735739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735765 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2735765 : Nat := 118140960795 + 2735765 * 2 ^ 59
def prefixEnd_2735765 : Nat := 4983230072969 + 3 ^ 40 * 2735765 * 2
def baseEnd_2735765 : Nat := 936508268498396027037301

theorem tailTrace_2735765 : CollatzResearch.WordTrace tailWord_2735765 prefixEnd_2735765 936508268498396027037301 := by
  unfold tailWord_2735765
  simp only [CollatzResearch.WordTrace]
  refine ⟨99781546933798111308912749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66521031289198740872608499 99781546933798111308912749)
  ·
    refine ⟨37418080100174291740842281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99781546933798111308912749 37418080100174291740842281)
    ·
      refine ⟨28063560075130718805631711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37418080100174291740842281 28063560075130718805631711)
      ·
        refine ⟨42095340112696078208447567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28063560075130718805631711 42095340112696078208447567)
        ·
          refine ⟨63143010169044117312671351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42095340112696078208447567 63143010169044117312671351)
          ·
            refine ⟨94714515253566175969007027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63143010169044117312671351 94714515253566175969007027)
            ·
              refine ⟨142071772880349263953510541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94714515253566175969007027 142071772880349263953510541)
              ·
                refine ⟨53276914830130973982566453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142071772880349263953510541 53276914830130973982566453)
                ·
                  refine ⟨4994710765324778810865605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53276914830130973982566453 4994710765324778810865605)
                  ·
                    refine ⟨936508268498396027037301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4994710765324778810865605 936508268498396027037301)
                    ·
                      rfl

theorem cell22_2735765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2735765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735765 prefixEnd_2735765 := by exact prefixLift 2735765
  have htrace : WordTrace (prefixWord ++ tailWord_2735765) baseStart_2735765 baseEnd_2735765 := by
    simpa [prefixWord, tailWord_2735765, baseEnd_2735765] using wordTrace_append hprefix tailTrace_2735765
  have hstable : (prefixWord ++ tailWord_2735765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735765).length < 2 ^ (prefixWord ++ tailWord_2735765).sum := by decide
  have hdescent : baseEnd_2735765 < baseStart_2735765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735790 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2735790 : Nat := 118140960795 + 2735790 * 2 ^ 59
def prefixEnd_2735790 : Nat := 4983230072969 + 3 ^ 40 * 2735790 * 2
def baseEnd_2735790 : Nat := 936516826509304295162225

theorem tailTrace_2735790 : CollatzResearch.WordTrace tailWord_2735790 prefixEnd_2735790 936516826509304295162225 := by
  unfold tailWord_2735790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472807344838442572321603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66521639172471693719048549 12472807344838442572321603)
  ·
    refine ⟨18709211017257663858482405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472807344838442572321603 18709211017257663858482405)
    ·
      refine ⟨3507977065735811973465451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18709211017257663858482405 3507977065735811973465451)
      ·
        refine ⟨5261965598603717960198177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507977065735811973465451 5261965598603717960198177)
        ·
          refine ⟨3946474198952788470148633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261965598603717960198177 3946474198952788470148633)
          ·
            refine ⟨2959855649214591352611475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3946474198952788470148633 2959855649214591352611475)
            ·
              refine ⟨4439783473821887028917213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959855649214591352611475 4439783473821887028917213)
              ·
                refine ⟨1664918802683207635843955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439783473821887028917213 1664918802683207635843955)
                ·
                  refine ⟨2497378204024811453765933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664918802683207635843955 2497378204024811453765933)
                  ·
                    refine ⟨936516826509304295162225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497378204024811453765933 936516826509304295162225)
                    ·
                      rfl

theorem cell22_2735790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2735790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735790 prefixEnd_2735790 := by exact prefixLift 2735790
  have htrace : WordTrace (prefixWord ++ tailWord_2735790) baseStart_2735790 baseEnd_2735790 := by
    simpa [prefixWord, tailWord_2735790, baseEnd_2735790] using wordTrace_append hprefix tailTrace_2735790
  have hstable : (prefixWord ++ tailWord_2735790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735790).length < 2 ^ (prefixWord ++ tailWord_2735790).sum := by decide
  have hdescent : baseEnd_2735790 < baseStart_2735790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735795 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_2735795 : Nat := 118140960795 + 2735795 * 2 ^ 59
def prefixEnd_2735795 : Nat := 4983230072969 + 3 ^ 40 * 2735795 * 2
def baseEnd_2735795 : Nat := 936518538111485948787209

theorem tailTrace_2735795 : CollatzResearch.WordTrace tailWord_2735795 prefixEnd_2735795 936518538111485948787209 := by
  unfold tailWord_2735795
  simp only [CollatzResearch.WordTrace]
  refine ⟨99782641123689426432504839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66521760749126284288336559 99782641123689426432504839)
  ·
    refine ⟨149673961685534139648757259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99782641123689426432504839 149673961685534139648757259)
    ·
      refine ⟨224510942528301209473135889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149673961685534139648757259 224510942528301209473135889)
      ·
        refine ⟨168383206896225907104851917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224510942528301209473135889 168383206896225907104851917)
        ·
          refine ⟨63143702586084715164319469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168383206896225907104851917 63143702586084715164319469)
          ·
            refine ⟨23678888469781768186619801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63143702586084715164319469 23678888469781768186619801)
            ·
              refine ⟨17759166352336326139964851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23678888469781768186619801 17759166352336326139964851)
              ·
                refine ⟨26638749528504489209947277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759166352336326139964851 26638749528504489209947277)
                ·
                  refine ⟨9989531073189183453730229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26638749528504489209947277 9989531073189183453730229)
                  ·
                    refine ⟨936518538111485948787209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9989531073189183453730229 936518538111485948787209)
                    ·
                      rfl

theorem cell22_2735795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_2735795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735795 prefixEnd_2735795 := by exact prefixLift 2735795
  have htrace : WordTrace (prefixWord ++ tailWord_2735795) baseStart_2735795 baseEnd_2735795 := by
    simpa [prefixWord, tailWord_2735795, baseEnd_2735795] using wordTrace_append hprefix tailTrace_2735795
  have hstable : (prefixWord ++ tailWord_2735795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735795).length < 2 ^ (prefixWord ++ tailWord_2735795).sum := by decide
  have hdescent : baseEnd_2735795 < baseStart_2735795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735825 : List Nat := [1, 2, 2, 1, 2, 4, 1, 9]
def baseStart_2735825 : Nat := 118140960795 + 2735825 * 2 ^ 59
def prefixEnd_2735825 : Nat := 4983230072969 + 3 ^ 40 * 2735825 * 2
def baseEnd_2735825 : Nat := 104058756413841763393013

theorem tailTrace_2735825 : CollatzResearch.WordTrace tailWord_2735825 prefixEnd_2735825 104058756413841763393013 := by
  unfold tailWord_2735825
  simp only [CollatzResearch.WordTrace]
  refine ⟨99783735313580741556096929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66522490209053827704064619 99783735313580741556096929)
  ·
    refine ⟨74837801485185556167072697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99783735313580741556096929 74837801485185556167072697)
    ·
      refine ⟨56128351113889167125304523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74837801485185556167072697 56128351113889167125304523)
      ·
        refine ⟨84192526670833750687956785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56128351113889167125304523 84192526670833750687956785)
        ·
          refine ⟨63144395003125313015967589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84192526670833750687956785 63144395003125313015967589)
          ·
            refine ⟨11839574063085996190493923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63144395003125313015967589 11839574063085996190493923)
            ·
              refine ⟨17759361094628994285740885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11839574063085996190493923 17759361094628994285740885)
              ·
                refine ⟨104058756413841763393013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17759361094628994285740885 104058756413841763393013)
                ·
                  rfl

theorem cell22_2735825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 9].length) (baseStart_2735825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735825 prefixEnd_2735825 := by exact prefixLift 2735825
  have htrace : WordTrace (prefixWord ++ tailWord_2735825) baseStart_2735825 baseEnd_2735825 := by
    simpa [prefixWord, tailWord_2735825, baseEnd_2735825] using wordTrace_append hprefix tailTrace_2735825
  have hstable : (prefixWord ++ tailWord_2735825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735825).length < 2 ^ (prefixWord ++ tailWord_2735825).sum := by decide
  have hdescent : baseEnd_2735825 < baseStart_2735825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735840 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_2735840 : Nat := 118140960795 + 2735840 * 2 ^ 59
def prefixEnd_2735840 : Nat := 4983230072969 + 3 ^ 40 * 2735840 * 2
def baseEnd_2735840 : Nat := 936533942531120831412071

theorem tailTrace_2735840 : CollatzResearch.WordTrace tailWord_2735840 prefixEnd_2735840 936533942531120831412071 := by
  unfold tailWord_2735840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49892141204263199558946487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66522854939017599411928649 49892141204263199558946487)
  ·
    refine ⟨74838211806394799338419731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49892141204263199558946487 74838211806394799338419731)
    ·
      refine ⟨112257317709592199007629597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74838211806394799338419731 112257317709592199007629597)
      ·
        refine ⟨42096494141097074627861099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112257317709592199007629597 42096494141097074627861099)
        ·
          refine ⟨63144741211645611941791649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42096494141097074627861099 63144741211645611941791649)
          ·
            refine ⟨47358555908734208956343737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63144741211645611941791649 47358555908734208956343737)
            ·
              refine ⟨35518916931550656717257803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47358555908734208956343737 35518916931550656717257803)
              ·
                refine ⟨53278375397325985075886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35518916931550656717257803 53278375397325985075886705)
                ·
                  refine ⟨39958781547994488806915029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53278375397325985075886705 39958781547994488806915029)
                  ·
                    refine ⟨936533942531120831412071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39958781547994488806915029 936533942531120831412071)
                    ·
                      rfl

theorem cell22_2735840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_2735840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735840 prefixEnd_2735840 := by exact prefixLift 2735840
  have htrace : WordTrace (prefixWord ++ tailWord_2735840) baseStart_2735840 baseEnd_2735840 := by
    simpa [prefixWord, tailWord_2735840, baseEnd_2735840] using wordTrace_append hprefix tailTrace_2735840
  have hstable : (prefixWord ++ tailWord_2735840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735840).length < 2 ^ (prefixWord ++ tailWord_2735840).sum := by decide
  have hdescent : baseEnd_2735840 < baseStart_2735840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735908 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_2735908 : Nat := 118140960795 + 2735908 * 2 ^ 59
def prefixEnd_2735908 : Nat := 4983230072969 + 3 ^ 40 * 2735908 * 2
def baseEnd_2735908 : Nat := 936557220320791320711863

theorem tailTrace_2735908 : CollatzResearch.WordTrace tailWord_2735908 prefixEnd_2735908 936557220320791320711863 := by
  unfold tailWord_2735908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893381286140023365684189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66524508381520031154245585 49893381286140023365684189)
  ·
    refine ⟨18710017982302508762131571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49893381286140023365684189 18710017982302508762131571)
    ·
      refine ⟨28065026973453763143197357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18710017982302508762131571 28065026973453763143197357)
      ·
        refine ⟨10524385115045161178699009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28065026973453763143197357 10524385115045161178699009)
        ·
          refine ⟨7893288836283870884024257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10524385115045161178699009 7893288836283870884024257)
          ·
            refine ⟨5919966627212903163018193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7893288836283870884024257 5919966627212903163018193)
            ·
              refine ⟨4439974970409677372263645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919966627212903163018193 4439974970409677372263645)
              ·
                refine ⟨1664990613903629014598867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439974970409677372263645 1664990613903629014598867)
                ·
                  refine ⟨2497485920855443521898301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664990613903629014598867 2497485920855443521898301)
                  ·
                    refine ⟨936557220320791320711863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497485920855443521898301 936557220320791320711863)
                    ·
                      rfl

theorem cell22_2735908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_2735908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735908 prefixEnd_2735908 := by exact prefixLift 2735908
  have htrace : WordTrace (prefixWord ++ tailWord_2735908) baseStart_2735908 baseEnd_2735908 := by
    simpa [prefixWord, tailWord_2735908, baseEnd_2735908] using wordTrace_append hprefix tailTrace_2735908
  have hstable : (prefixWord ++ tailWord_2735908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735908).length < 2 ^ (prefixWord ++ tailWord_2735908).sum := by decide
  have hdescent : baseEnd_2735908 < baseStart_2735908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735932 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_2735932 : Nat := 118140960795 + 2735932 * 2 ^ 59
def prefixEnd_2735932 : Nat := 4983230072969 + 3 ^ 40 * 2735932 * 2
def baseEnd_2735932 : Nat := 312188478670421086037263

theorem tailTrace_2735932 : CollatzResearch.WordTrace tailWord_2735932 prefixEnd_2735932 312188478670421086037263 := by
  unfold tailWord_2735932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893818962096549415121025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66525091949462065886828033 49893818962096549415121025)
  ·
    refine ⟨37420364221572412061340769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49893818962096549415121025 37420364221572412061340769)
    ·
      refine ⟨28065273166179309046005577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37420364221572412061340769 28065273166179309046005577)
      ·
        refine ⟨21048954874634481784504183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28065273166179309046005577 21048954874634481784504183)
        ·
          refine ⟨31573432311951722676756275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21048954874634481784504183 31573432311951722676756275)
          ·
            refine ⟨47360148467927584015134413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31573432311951722676756275 47360148467927584015134413)
            ·
              refine ⟨17760055675472844005675405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47360148467927584015134413 17760055675472844005675405)
              ·
                refine ⟨6660020878302316502128277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17760055675472844005675405 6660020878302316502128277)
                ·
                  refine ⟨312188478670421086037263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6660020878302316502128277 312188478670421086037263)
                  ·
                    rfl

theorem cell22_2735932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_2735932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735932 prefixEnd_2735932 := by exact prefixLift 2735932
  have htrace : WordTrace (prefixWord ++ tailWord_2735932) baseStart_2735932 baseEnd_2735932 := by
    simpa [prefixWord, tailWord_2735932, baseEnd_2735932] using wordTrace_append hprefix tailTrace_2735932
  have hstable : (prefixWord ++ tailWord_2735932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735932).length < 2 ^ (prefixWord ++ tailWord_2735932).sum := by decide
  have hdescent : baseEnd_2735932 < baseStart_2735932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735962 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2735962 : Nat := 118140960795 + 2735962 * 2 ^ 59
def prefixEnd_2735962 : Nat := 4983230072969 + 3 ^ 40 * 2735962 * 2
def baseEnd_2735962 : Nat := 936575705624353179861697

theorem tailTrace_2735962 : CollatzResearch.WordTrace tailWord_2735962 prefixEnd_2735962 936575705624353179861697 := by
  unfold tailWord_2735962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24947183028521103488458535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66525821409389609302556093 24947183028521103488458535)
  ·
    refine ⟨37420774542781655232687803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24947183028521103488458535 37420774542781655232687803)
    ·
      refine ⟨56131161814172482849031705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37420774542781655232687803 56131161814172482849031705)
      ·
        refine ⟨42098371360629362136773779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56131161814172482849031705 42098371360629362136773779)
        ·
          refine ⟨63147557040944043205160669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42098371360629362136773779 63147557040944043205160669)
          ·
            refine ⟨23680333890354016201935251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63147557040944043205160669 23680333890354016201935251)
            ·
              refine ⟨35520500835531024302902877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23680333890354016201935251 35520500835531024302902877)
              ·
                refine ⟨13320187813324134113588579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35520500835531024302902877 13320187813324134113588579)
                ·
                  refine ⟨19980281719986201170382869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13320187813324134113588579 19980281719986201170382869)
                  ·
                    refine ⟨936575705624353179861697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19980281719986201170382869 936575705624353179861697)
                    ·
                      rfl

theorem cell22_2735962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2735962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2735962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2735962 prefixEnd_2735962 := by exact prefixLift 2735962
  have htrace : WordTrace (prefixWord ++ tailWord_2735962) baseStart_2735962 baseEnd_2735962 := by
    simpa [prefixWord, tailWord_2735962, baseEnd_2735962] using wordTrace_append hprefix tailTrace_2735962
  have hstable : (prefixWord ++ tailWord_2735962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735962).length < 2 ^ (prefixWord ++ tailWord_2735962).sum := by decide
  have hdescent : baseEnd_2735962 < baseStart_2735962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736009 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_2736009 : Nat := 118140960795 + 2736009 * 2 ^ 59
def prefixEnd_2736009 : Nat := 4983230072969 + 3 ^ 40 * 2736009 * 2
def baseEnd_2736009 : Nat := 936591794684860723936553

theorem tailTrace_2736009 : CollatzResearch.WordTrace tailWord_2736009 prefixEnd_2736009 936591794684860723936553 := by
  unfold tailWord_2736009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99790446344914140980795081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66526964229942760653863387 99790446344914140980795081)
  ·
    refine ⟨74842834758685605735596311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99790446344914140980795081 74842834758685605735596311)
    ·
      refine ⟨112264252138028408603394467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74842834758685605735596311 112264252138028408603394467)
      ·
        refine ⟨168396378207042612905091701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112264252138028408603394467 168396378207042612905091701)
        ·
          refine ⟨15787160456910244959852347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168396378207042612905091701 15787160456910244959852347)
          ·
            refine ⟨23680740685365367439778521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15787160456910244959852347 23680740685365367439778521)
            ·
              refine ⟨17760555514024025579833891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23680740685365367439778521 17760555514024025579833891)
              ·
                refine ⟨26640833271036038369750837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17760555514024025579833891 26640833271036038369750837)
                ·
                  refine ⟨2497578119159628597164141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26640833271036038369750837 2497578119159628597164141)
                  ·
                    refine ⟨936591794684860723936553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497578119159628597164141 936591794684860723936553)
                    ·
                      rfl

theorem cell22_2736009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_2736009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736009 prefixEnd_2736009 := by exact prefixLift 2736009
  have htrace : WordTrace (prefixWord ++ tailWord_2736009) baseStart_2736009 baseEnd_2736009 := by
    simpa [prefixWord, tailWord_2736009, baseEnd_2736009] using wordTrace_append hprefix tailTrace_2736009
  have hstable : (prefixWord ++ tailWord_2736009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736009).length < 2 ^ (prefixWord ++ tailWord_2736009).sum := by decide
  have hdescent : baseEnd_2736009 < baseStart_2736009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736037 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2736037 : Nat := 118140960795 + 2736037 * 2 ^ 59
def prefixEnd_2736037 : Nat := 4983230072969 + 3 ^ 40 * 2736037 * 2
def baseEnd_2736037 : Nat := 936601379657077984236467

theorem tailTrace_2736037 : CollatzResearch.WordTrace tailWord_2736037 prefixEnd_2736037 936601379657077984236467 := by
  unfold tailWord_2736037
  simp only [CollatzResearch.WordTrace]
  refine ⟨99791467588812701762814365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66527645059208467841876243 99791467588812701762814365)
  ·
    refine ⟨37421800345804763161055387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99791467588812701762814365 37421800345804763161055387)
    ·
      refine ⟨56132700518707144741583081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37421800345804763161055387 56132700518707144741583081)
      ·
        refine ⟨42099525389030358556187311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56132700518707144741583081 42099525389030358556187311)
        ·
          refine ⟨63149288083545537834280967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42099525389030358556187311 63149288083545537834280967)
          ·
            refine ⟨94723932125318306751421451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63149288083545537834280967 94723932125318306751421451)
            ·
              refine ⟨142085898187977460127132177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94723932125318306751421451 142085898187977460127132177)
              ·
                refine ⟨106564423640983095095349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142085898187977460127132177 106564423640983095095349133)
                ·
                  refine ⟨39961658865368660660755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106564423640983095095349133 39961658865368660660755925)
                  ·
                    refine ⟨936601379657077984236467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39961658865368660660755925 936601379657077984236467)
                    ·
                      rfl

theorem cell22_2736037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2736037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736037 prefixEnd_2736037 := by exact prefixLift 2736037
  have htrace : WordTrace (prefixWord ++ tailWord_2736037) baseStart_2736037 baseEnd_2736037 := by
    simpa [prefixWord, tailWord_2736037, baseEnd_2736037] using wordTrace_append hprefix tailTrace_2736037
  have hstable : (prefixWord ++ tailWord_2736037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736037).length < 2 ^ (prefixWord ++ tailWord_2736037).sum := by decide
  have hdescent : baseEnd_2736037 < baseStart_2736037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736084 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2736084 : Nat := 118140960795 + 2736084 * 2 ^ 59
def prefixEnd_2736084 : Nat := 4983230072969 + 3 ^ 40 * 2736084 * 2
def baseEnd_2736084 : Nat := 312205822905861842770441

theorem tailTrace_2736084 : CollatzResearch.WordTrace tailWord_2736084 prefixEnd_2736084 312205822905861842770441 := by
  unfold tailWord_2736084
  simp only [CollatzResearch.WordTrace]
  refine ⟨49896590909821214394887653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66528787879761619193183537 49896590909821214394887653)
  ·
    refine ⟨9355610795591477699041435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49896590909821214394887653 9355610795591477699041435)
    ·
      refine ⟨14033416193387216548562153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9355610795591477699041435 14033416193387216548562153)
      ·
        refine ⟨10525062145040412411421615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14033416193387216548562153 10525062145040412411421615)
        ·
          refine ⟨15787593217560618617132423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10525062145040412411421615 15787593217560618617132423)
          ·
            refine ⟨23681389826340927925698635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15787593217560618617132423 23681389826340927925698635)
            ·
              refine ⟨35522084739511391888547953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23681389826340927925698635 35522084739511391888547953)
              ·
                refine ⟨26641563554633543916410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35522084739511391888547953 26641563554633543916410965)
                ·
                  refine ⟨312205822905861842770441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26641563554633543916410965 312205822905861842770441)
                  ·
                    rfl

theorem cell22_2736084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2736084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736084 prefixEnd_2736084 := by exact prefixLift 2736084
  have htrace : WordTrace (prefixWord ++ tailWord_2736084) baseStart_2736084 baseEnd_2736084 := by
    simpa [prefixWord, tailWord_2736084, baseEnd_2736084] using wordTrace_append hprefix tailTrace_2736084
  have hstable : (prefixWord ++ tailWord_2736084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736084).length < 2 ^ (prefixWord ++ tailWord_2736084).sum := by decide
  have hdescent : baseEnd_2736084 < baseStart_2736084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736129 : List Nat := [1, 2, 4, 1, 2, 1, 3, 8]
def baseStart_2736129 : Nat := 118140960795 + 2736129 * 2 ^ 59
def prefixEnd_2736129 : Nat := 4983230072969 + 3 ^ 40 * 2736129 * 2
def baseEnd_2736129 : Nat := 104070319237468934548465

theorem tailTrace_2736129 : CollatzResearch.WordTrace tailWord_2736129 prefixEnd_2736129 104070319237468934548465 := by
  unfold tailWord_2736129
  simp only [CollatzResearch.WordTrace]
  refine ⟨99794823104479401475163441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66529882069652934316775627 99794823104479401475163441)
  ·
    refine ⟨74846117328359551106372581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99794823104479401475163441 74846117328359551106372581)
    ·
      refine ⟨14033646999067415832444859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74846117328359551106372581 14033646999067415832444859)
      ·
        refine ⟨21050470498601123748667289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14033646999067415832444859 21050470498601123748667289)
        ·
          refine ⟨15787852873950842811500467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21050470498601123748667289 15787852873950842811500467)
          ·
            refine ⟨23681779310926264217250701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15787852873950842811500467 23681779310926264217250701)
            ·
              refine ⟨8880667241597349081469013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23681779310926264217250701 8880667241597349081469013)
              ·
                refine ⟨104070319237468934548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8880667241597349081469013 104070319237468934548465)
                ·
                  rfl

theorem cell22_2736129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 8].length) (baseStart_2736129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736129 prefixEnd_2736129 := by exact prefixLift 2736129
  have htrace : WordTrace (prefixWord ++ tailWord_2736129) baseStart_2736129 baseEnd_2736129 := by
    simpa [prefixWord, tailWord_2736129, baseEnd_2736129] using wordTrace_append hprefix tailTrace_2736129
  have hstable : (prefixWord ++ tailWord_2736129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736129).length < 2 ^ (prefixWord ++ tailWord_2736129).sum := by decide
  have hdescent : baseEnd_2736129 < baseStart_2736129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736159 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_2736159 : Nat := 118140960795 + 2736159 * 2 ^ 59
def prefixEnd_2736159 : Nat := 4983230072969 + 3 ^ 40 * 2736159 * 2
def baseEnd_2736159 : Nat := 936643142750310332686093

theorem tailTrace_2736159 : CollatzResearch.WordTrace tailWord_2736159 prefixEnd_2736159 936643142750310332686093 := by
  unfold tailWord_2736159
  simp only [CollatzResearch.WordTrace]
  refine ⟨99795917294370716598755531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66530611529580477732503687 99795917294370716598755531)
  ·
    refine ⟨149693875941556074898133297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99795917294370716598755531 149693875941556074898133297)
    ·
      refine ⟨112270406956167056173599973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149693875941556074898133297 112270406956167056173599973)
      ·
        refine ⟨21050701304281323032549995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112270406956167056173599973 21050701304281323032549995)
        ·
          refine ⟨31576051956421984548824993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21050701304281323032549995 31576051956421984548824993)
          ·
            refine ⟨23682038967316488411618745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31576051956421984548824993 23682038967316488411618745)
            ·
              refine ⟨17761529225487366308714059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23682038967316488411618745 17761529225487366308714059)
              ·
                refine ⟨26642293838231049463071089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17761529225487366308714059 26642293838231049463071089)
                ·
                  refine ⟨19981720378673287097303317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26642293838231049463071089 19981720378673287097303317)
                  ·
                    refine ⟨936643142750310332686093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19981720378673287097303317 936643142750310332686093)
                    ·
                      rfl

theorem cell22_2736159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_2736159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736159 prefixEnd_2736159 := by exact prefixLift 2736159
  have htrace : WordTrace (prefixWord ++ tailWord_2736159) baseStart_2736159 baseEnd_2736159 := by
    simpa [prefixWord, tailWord_2736159, baseEnd_2736159] using wordTrace_append hprefix tailTrace_2736159
  have hstable : (prefixWord ++ tailWord_2736159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736159).length < 2 ^ (prefixWord ++ tailWord_2736159).sum := by decide
  have hdescent : baseEnd_2736159 < baseStart_2736159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736236 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_2736236 : Nat := 118140960795 + 2736236 * 2 ^ 59
def prefixEnd_2736236 : Nat := 4983230072969 + 3 ^ 40 * 2736236 * 2
def baseEnd_2736236 : Nat := 312223167141302599503619

theorem tailTrace_2736236 : CollatzResearch.WordTrace tailWord_2736236 prefixEnd_2736236 312223167141302599503619 := by
  unfold tailWord_2736236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49899362857545879374654281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66532483810061172499539041 49899362857545879374654281)
  ·
    refine ⟨37424522143159409530990711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49899362857545879374654281 37424522143159409530990711)
    ·
      refine ⟨56136783214739114296486067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37424522143159409530990711 56136783214739114296486067)
      ·
        refine ⟨84205174822108671444729101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56136783214739114296486067 84205174822108671444729101)
        ·
          refine ⟨31576940558290751791773413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84205174822108671444729101 31576940558290751791773413)
          ·
            refine ⟨5920676354679515960957515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31576940558290751791773413 5920676354679515960957515)
            ·
              refine ⟨8881014532019273941436273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920676354679515960957515 8881014532019273941436273)
              ·
                refine ⟨6660760899014455456077205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881014532019273941436273 6660760899014455456077205)
                ·
                  refine ⟨312223167141302599503619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6660760899014455456077205 312223167141302599503619)
                  ·
                    rfl

theorem cell22_2736236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_2736236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736236 prefixEnd_2736236 := by exact prefixLift 2736236
  have htrace : WordTrace (prefixWord ++ tailWord_2736236) baseStart_2736236 baseEnd_2736236 := by
    simpa [prefixWord, tailWord_2736236, baseEnd_2736236] using wordTrace_append hprefix tailTrace_2736236
  have hstable : (prefixWord ++ tailWord_2736236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736236).length < 2 ^ (prefixWord ++ tailWord_2736236).sum := by decide
  have hdescent : baseEnd_2736236 < baseStart_2736236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736238 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2736238 : Nat := 118140960795 + 2736238 * 2 ^ 59
def prefixEnd_2736238 : Nat := 4983230072969 + 3 ^ 40 * 2736238 * 2
def baseEnd_2736238 : Nat := 936670186064780459960851

theorem tailTrace_2736238 : CollatzResearch.WordTrace tailWord_2736238 prefixEnd_2736238 936670186064780459960851 := by
  unfold tailWord_2736238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474849832635564136360171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66532532440723008727254245 12474849832635564136360171)
  ·
    refine ⟨18712274748953346204540257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12474849832635564136360171 18712274748953346204540257)
    ·
      refine ⟨14034206061715009653405193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18712274748953346204540257 14034206061715009653405193)
      ·
        refine ⟨10525654546286257240053895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14034206061715009653405193 10525654546286257240053895)
        ·
          refine ⟨15788481819429385860080843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10525654546286257240053895 15788481819429385860080843)
          ·
            refine ⟨23682722729144078790121265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15788481819429385860080843 23682722729144078790121265)
            ·
              refine ⟨17762042046858059092590949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23682722729144078790121265 17762042046858059092590949)
              ·
                refine ⟨3330382883785886079860803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17762042046858059092590949 3330382883785886079860803)
                ·
                  refine ⟨4995574325678829119791205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330382883785886079860803 4995574325678829119791205)
                  ·
                    refine ⟨936670186064780459960851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4995574325678829119791205 936670186064780459960851)
                    ·
                      rfl

theorem cell22_2736238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2736238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736238 prefixEnd_2736238 := by exact prefixLift 2736238
  have htrace : WordTrace (prefixWord ++ tailWord_2736238) baseStart_2736238 baseEnd_2736238 := by
    simpa [prefixWord, tailWord_2736238, baseEnd_2736238] using wordTrace_append hprefix tailTrace_2736238
  have hstable : (prefixWord ++ tailWord_2736238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736238).length < 2 ^ (prefixWord ++ tailWord_2736238).sum := by decide
  have hdescent : baseEnd_2736238 < baseStart_2736238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736253 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 4]
def baseStart_2736253 : Nat := 118140960795 + 2736253 * 2 ^ 59
def prefixEnd_2736253 : Nat := 4983230072969 + 3 ^ 40 * 2736253 * 2
def baseEnd_2736253 : Nat := 312225106957108473611935

theorem tailTrace_2736253 : CollatzResearch.WordTrace tailWord_2736253 prefixEnd_2736253 312225106957108473611935 := by
  unfold tailWord_2736253
  simp only [CollatzResearch.WordTrace]
  refine ⟨99799345756030170652677413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66532897170686780435118275 99799345756030170652677413)
  ·
    refine ⟨18712377329255656997377015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99799345756030170652677413 18712377329255656997377015)
    ·
      refine ⟨28068565993883485496065523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18712377329255656997377015 28068565993883485496065523)
      ·
        refine ⟨42102848990825228244098285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28068565993883485496065523 42102848990825228244098285)
        ·
          refine ⟨15788568371559460591536857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42102848990825228244098285 15788568371559460591536857)
          ·
            refine ⟨11841426278669595443652643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15788568371559460591536857 11841426278669595443652643)
            ·
              refine ⟨17762139418004393165478965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11841426278669595443652643 17762139418004393165478965)
              ·
                refine ⟨1665200570437911859263653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17762139418004393165478965 1665200570437911859263653)
                ·
                  refine ⟨312225106957108473611935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665200570437911859263653 312225106957108473611935)
                  ·
                    rfl

theorem cell22_2736253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_2736253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736253 prefixEnd_2736253 := by exact prefixLift 2736253
  have htrace : WordTrace (prefixWord ++ tailWord_2736253) baseStart_2736253 baseEnd_2736253 := by
    simpa [prefixWord, tailWord_2736253, baseEnd_2736253] using wordTrace_append hprefix tailTrace_2736253
  have hstable : (prefixWord ++ tailWord_2736253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736253).length < 2 ^ (prefixWord ++ tailWord_2736253).sum := by decide
  have hdescent : baseEnd_2736253 < baseStart_2736253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736424 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2736424 : Nat := 118140960795 + 2736424 * 2 ^ 59
def prefixEnd_2736424 : Nat := 4983230072969 + 3 ^ 40 * 2736424 * 2
def baseEnd_2736424 : Nat := 936733857665937974810281

theorem tailTrace_2736424 : CollatzResearch.WordTrace tailWord_2736424 prefixEnd_2736424 936733857665937974810281 := by
  unfold tailWord_2736424
  simp only [CollatzResearch.WordTrace]
  refine ⟨49902791319205333428576163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66537055092273777904768217 49902791319205333428576163)
  ·
    refine ⟨74854186978808000142864245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49902791319205333428576163 74854186978808000142864245)
    ·
      refine ⟨7017580029263250013393523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74854186978808000142864245 7017580029263250013393523)
      ·
        refine ⟨10526370043894875020090285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7017580029263250013393523 10526370043894875020090285)
        ·
          refine ⟨3947388766460578132533857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10526370043894875020090285 3947388766460578132533857)
          ·
            refine ⟨2960541574845433599400393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3947388766460578132533857 2960541574845433599400393)
            ·
              refine ⟨2220406181134075199550295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2960541574845433599400393 2220406181134075199550295)
              ·
                refine ⟨3330609271701112799325443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220406181134075199550295 3330609271701112799325443)
                ·
                  refine ⟨4995913907551669198988165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330609271701112799325443 4995913907551669198988165)
                  ·
                    refine ⟨936733857665937974810281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4995913907551669198988165 936733857665937974810281)
                    ·
                      rfl

theorem cell22_2736424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2736424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736424 prefixEnd_2736424 := by exact prefixLift 2736424
  have htrace : WordTrace (prefixWord ++ tailWord_2736424) baseStart_2736424 baseEnd_2736424 := by
    simpa [prefixWord, tailWord_2736424, baseEnd_2736424] using wordTrace_append hprefix tailTrace_2736424
  have hstable : (prefixWord ++ tailWord_2736424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736424).length < 2 ^ (prefixWord ++ tailWord_2736424).sum := by decide
  have hdescent : baseEnd_2736424 < baseStart_2736424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736433 : List Nat := [1, 2, 2, 3, 4, 1, 9]
def baseStart_2736433 : Nat := 118140960795 + 2736433 * 2 ^ 59
def prefixEnd_2736433 : Nat := 4983230072969 + 3 ^ 40 * 2736433 * 2
def baseEnd_2736433 : Nat := 34693960687032035234639

theorem tailTrace_2736433 : CollatzResearch.WordTrace tailWord_2736433 prefixEnd_2736433 34693960687032035234639 := by
  unfold tailWord_2736433
  simp only [CollatzResearch.WordTrace]
  refine ⟨99805910895378061394229953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66537273930252040929486635 99805910895378061394229953)
  ·
    refine ⟨74854433171533546045672465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99805910895378061394229953 74854433171533546045672465)
    ·
      refine ⟨56140824878650159534254349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74854433171533546045672465 56140824878650159534254349)
      ·
        refine ⟨21052809329493809825345381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56140824878650159534254349 21052809329493809825345381)
        ·
          refine ⟨3947401749280089342252259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21052809329493809825345381 3947401749280089342252259)
          ·
            refine ⟨5921102623920134013378389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947401749280089342252259 5921102623920134013378389)
            ·
              refine ⟨34693960687032035234639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5921102623920134013378389 34693960687032035234639)
              ·
                rfl

theorem cell22_2736433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 9].length) (baseStart_2736433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736433 prefixEnd_2736433 := by exact prefixLift 2736433
  have htrace : WordTrace (prefixWord ++ tailWord_2736433) baseStart_2736433 baseEnd_2736433 := by
    simpa [prefixWord, tailWord_2736433, baseEnd_2736433] using wordTrace_append hprefix tailTrace_2736433
  have hstable : (prefixWord ++ tailWord_2736433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736433).length < 2 ^ (prefixWord ++ tailWord_2736433).sum := by decide
  have hdescent : baseEnd_2736433 < baseStart_2736433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736465 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2736465 : Nat := 118140960795 + 2736465 * 2 ^ 59
def prefixEnd_2736465 : Nat := 4983230072969 + 3 ^ 40 * 2736465 * 2
def baseEnd_2736465 : Nat := 936747892803827534535155

theorem tailTrace_2736465 : CollatzResearch.WordTrace tailWord_2736465 prefixEnd_2736465 936747892803827534535155 := by
  unfold tailWord_2736465
  simp only [CollatzResearch.WordTrace]
  refine ⟨99807078031262130859394849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66538052020841420572929899 99807078031262130859394849)
  ·
    refine ⟨74855308523446598144546137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99807078031262130859394849 74855308523446598144546137)
    ·
      refine ⟨56141481392584948608409603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74855308523446598144546137 56141481392584948608409603)
      ·
        refine ⟨84212222088877422912614405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56141481392584948608409603 84212222088877422912614405)
        ·
          refine ⟨15789791641664516796115201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84212222088877422912614405 15789791641664516796115201)
          ·
            refine ⟨11842343731248387597086401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15789791641664516796115201 11842343731248387597086401)
            ·
              refine ⟨8881757798436290697814801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11842343731248387597086401 8881757798436290697814801)
              ·
                refine ⟨6661318348827218023361101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881757798436290697814801 6661318348827218023361101)
                ·
                  refine ⟨2497994380810206758760413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6661318348827218023361101 2497994380810206758760413)
                  ·
                    refine ⟨936747892803827534535155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497994380810206758760413 936747892803827534535155)
                    ·
                      rfl

theorem cell22_2736465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2736465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736465 prefixEnd_2736465 := by exact prefixLift 2736465
  have htrace : WordTrace (prefixWord ++ tailWord_2736465) baseStart_2736465 baseEnd_2736465 := by
    simpa [prefixWord, tailWord_2736465, baseEnd_2736465] using wordTrace_append hprefix tailTrace_2736465
  have hstable : (prefixWord ++ tailWord_2736465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736465).length < 2 ^ (prefixWord ++ tailWord_2736465).sum := by decide
  have hdescent : baseEnd_2736465 < baseStart_2736465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736572 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_2736572 : Nat := 118140960795 + 2736572 * 2 ^ 59
def prefixEnd_2736572 : Nat := 4983230072969 + 3 ^ 40 * 2736572 * 2
def baseEnd_2736572 : Nat := 936784521090514922109827

theorem tailTrace_2736572 : CollatzResearch.WordTrace tailWord_2736572 prefixEnd_2736572 936784521090514922109827 := by
  unfold tailWord_2736572
  simp only [CollatzResearch.WordTrace]
  refine ⟨49905490320937244066769985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66540653761249658755693313 49905490320937244066769985)
  ·
    refine ⟨37429117740702933050077489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49905490320937244066769985 37429117740702933050077489)
    ·
      refine ⟨28071838305527199787558117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37429117740702933050077489 28071838305527199787558117)
      ·
        refine ⟨5263469682286349960167147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28071838305527199787558117 5263469682286349960167147)
        ·
          refine ⟨7895204523429524940250721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263469682286349960167147 7895204523429524940250721)
          ·
            refine ⟨5921403392572143705188041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7895204523429524940250721 5921403392572143705188041)
            ·
              refine ⟨4441052544429107778891031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5921403392572143705188041 4441052544429107778891031)
              ·
                refine ⟨6661578816643661668336547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441052544429107778891031 6661578816643661668336547)
                ·
                  refine ⟨9992368224965492502504821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6661578816643661668336547 9992368224965492502504821)
                  ·
                    refine ⟨936784521090514922109827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9992368224965492502504821 936784521090514922109827)
                    ·
                      rfl

theorem cell22_2736572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_2736572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736572 prefixEnd_2736572 := by exact prefixLift 2736572
  have htrace : WordTrace (prefixWord ++ tailWord_2736572) baseStart_2736572 baseEnd_2736572 := by
    simpa [prefixWord, tailWord_2736572, baseEnd_2736572] using wordTrace_append hprefix tailTrace_2736572
  have hstable : (prefixWord ++ tailWord_2736572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736572).length < 2 ^ (prefixWord ++ tailWord_2736572).sum := by decide
  have hdescent : baseEnd_2736572 < baseStart_2736572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736600 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_2736600 : Nat := 118140960795 + 2736600 * 2 ^ 59
def prefixEnd_2736600 : Nat := 4983230072969 + 3 ^ 40 * 2736600 * 2
def baseEnd_2736600 : Nat := 936794106062732182409741

theorem tailTrace_2736600 : CollatzResearch.WordTrace tailWord_2736600 prefixEnd_2736600 936794106062732182409741 := by
  unfold tailWord_2736600
  simp only [CollatzResearch.WordTrace]
  refine ⟨49906000942886524457779627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66541334590515365943706169 49906000942886524457779627)
  ·
    refine ⟨74859001414329786686669441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49906000942886524457779627 74859001414329786686669441)
    ·
      refine ⟨56144251060747340015002081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74859001414329786686669441 56144251060747340015002081)
      ·
        refine ⟨42108188295560505011251561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56144251060747340015002081 42108188295560505011251561)
        ·
          refine ⟨31581141221670378758438671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42108188295560505011251561 31581141221670378758438671)
          ·
            refine ⟨47371711832505568137658007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31581141221670378758438671 47371711832505568137658007)
            ·
              refine ⟨71057567748758352206487011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47371711832505568137658007 71057567748758352206487011)
              ·
                refine ⟨106586351623137528309730517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71057567748758352206487011 106586351623137528309730517)
                ·
                  refine ⟨2498117616167285819759309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106586351623137528309730517 2498117616167285819759309)
                  ·
                    refine ⟨936794106062732182409741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498117616167285819759309 936794106062732182409741)
                    ·
                      rfl

theorem cell22_2736600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_2736600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736600 prefixEnd_2736600 := by exact prefixLift 2736600
  have htrace : WordTrace (prefixWord ++ tailWord_2736600) baseStart_2736600 baseEnd_2736600 := by
    simpa [prefixWord, tailWord_2736600, baseEnd_2736600] using wordTrace_append hprefix tailTrace_2736600
  have hstable : (prefixWord ++ tailWord_2736600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736600).length < 2 ^ (prefixWord ++ tailWord_2736600).sum := by decide
  have hdescent : baseEnd_2736600 < baseStart_2736600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736651 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 1, 3]
def baseStart_2736651 : Nat := 118140960795 + 2736651 * 2 ^ 59
def prefixEnd_2736651 : Nat := 4983230072969 + 3 ^ 40 * 2736651 * 2
def baseEnd_2736651 : Nat := 936811564404985049384585

theorem tailTrace_2736651 : CollatzResearch.WordTrace tailWord_2736651 prefixEnd_2736651 936811564404985049384585 := by
  unfold tailWord_2736651
  simp only [CollatzResearch.WordTrace]
  refine ⟨99813862008588284625665807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66542574672392189750443871 99813862008588284625665807)
  ·
    refine ⟨149720793012882426938498711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99813862008588284625665807 149720793012882426938498711)
    ·
      refine ⟨224581189519323640407748067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149720793012882426938498711 224581189519323640407748067)
      ·
        refine ⟨336871784278985460611622101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224581189519323640407748067 336871784278985460611622101)
        ·
          refine ⟨7895432444038721733084893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 336871784278985460611622101 7895432444038721733084893)
          ·
            refine ⟨2960787166514520649906835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7895432444038721733084893 2960787166514520649906835)
            ·
              refine ⟨4441180749771780974860253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960787166514520649906835 4441180749771780974860253)
              ·
                refine ⟨1665442781164417865572595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4441180749771780974860253 1665442781164417865572595)
                ·
                  refine ⟨2498164171746626798358893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665442781164417865572595 2498164171746626798358893)
                  ·
                    refine ⟨936811564404985049384585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498164171746626798358893 936811564404985049384585)
                    ·
                      rfl

theorem cell22_2736651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 3].length) (baseStart_2736651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736651 prefixEnd_2736651 := by exact prefixLift 2736651
  have htrace : WordTrace (prefixWord ++ tailWord_2736651) baseStart_2736651 baseEnd_2736651 := by
    simpa [prefixWord, tailWord_2736651, baseEnd_2736651] using wordTrace_append hprefix tailTrace_2736651
  have hstable : (prefixWord ++ tailWord_2736651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736651).length < 2 ^ (prefixWord ++ tailWord_2736651).sum := by decide
  have hdescent : baseEnd_2736651 < baseStart_2736651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736694 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2736694 : Nat := 118140960795 + 2736694 * 2 ^ 59
def prefixEnd_2736694 : Nat := 4983230072969 + 3 ^ 40 * 2736694 * 2
def baseEnd_2736694 : Nat := 936826284183747270559453

theorem tailTrace_2736694 : CollatzResearch.WordTrace tailWord_2736694 prefixEnd_2736694 936826284183747270559453 := by
  unfold tailWord_2736694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6238464396714531435592571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66543620231621668646320757 6238464396714531435592571)
  ·
    refine ⟨9357696595071797153388857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6238464396714531435592571 9357696595071797153388857)
    ·
      refine ⟨7018272446303847865041643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9357696595071797153388857 7018272446303847865041643)
      ·
        refine ⟨10527408669455771797562465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018272446303847865041643 10527408669455771797562465)
        ·
          refine ⟨7895556502091828848171849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10527408669455771797562465 7895556502091828848171849)
          ·
            refine ⟨5921667376568871636128887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7895556502091828848171849 5921667376568871636128887)
            ·
              refine ⟨8882501064853307454193331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5921667376568871636128887 8882501064853307454193331)
              ·
                refine ⟨13323751597279961181289997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882501064853307454193331 13323751597279961181289997)
                ·
                  refine ⟨4996406848979985442983749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13323751597279961181289997 4996406848979985442983749)
                  ·
                    refine ⟨936826284183747270559453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996406848979985442983749 936826284183747270559453)
                    ·
                      rfl

theorem cell22_2736694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2736694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736694 prefixEnd_2736694 := by exact prefixLift 2736694
  have htrace : WordTrace (prefixWord ++ tailWord_2736694) baseStart_2736694 baseEnd_2736694 := by
    simpa [prefixWord, tailWord_2736694, baseEnd_2736694] using wordTrace_append hprefix tailTrace_2736694
  have hstable : (prefixWord ++ tailWord_2736694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736694).length < 2 ^ (prefixWord ++ tailWord_2736694).sum := by decide
  have hdescent : baseEnd_2736694 < baseStart_2736694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736722 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2736722 : Nat := 118140960795 + 2736722 * 2 ^ 59
def prefixEnd_2736722 : Nat := 4983230072969 + 3 ^ 40 * 2736722 * 2
def baseEnd_2736722 : Nat := 936835869155964530859367

theorem tailTrace_2736722 : CollatzResearch.WordTrace tailWord_2736722 prefixEnd_2736722 936835869155964530859367 := by
  unfold tailWord_2736722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954112897832765937875105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66544301060887375834333613 24954112897832765937875105)
  ·
    refine ⟨18715584673374574453406329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24954112897832765937875105 18715584673374574453406329)
    ·
      refine ⟨14036688505030930840054747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18715584673374574453406329 14036688505030930840054747)
      ·
        refine ⟨21055032757546396260082121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14036688505030930840054747 21055032757546396260082121)
        ·
          refine ⟨15791274568159797195061591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21055032757546396260082121 15791274568159797195061591)
          ·
            refine ⟨23686911852239695792592387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15791274568159797195061591 23686911852239695792592387)
            ·
              refine ⟨35530367778359543688888581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23686911852239695792592387 35530367778359543688888581)
              ·
                refine ⟨6661943958442414441666609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35530367778359543688888581 6661943958442414441666609)
                ·
                  refine ⟨4996457968831810831249957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6661943958442414441666609 4996457968831810831249957)
                  ·
                    refine ⟨936835869155964530859367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996457968831810831249957 936835869155964530859367)
                    ·
                      rfl

theorem cell22_2736722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2736722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736722 prefixEnd_2736722 := by exact prefixLift 2736722
  have htrace : WordTrace (prefixWord ++ tailWord_2736722) baseStart_2736722 baseEnd_2736722 := by
    simpa [prefixWord, tailWord_2736722, baseEnd_2736722] using wordTrace_append hprefix tailTrace_2736722
  have hstable : (prefixWord ++ tailWord_2736722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736722).length < 2 ^ (prefixWord ++ tailWord_2736722).sum := by decide
  have hdescent : baseEnd_2736722 < baseStart_2736722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736724 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_2736724 : Nat := 118140960795 + 2736724 * 2 ^ 59
def prefixEnd_2736724 : Nat := 4983230072969 + 3 ^ 40 * 2736724 * 2
def baseEnd_2736724 : Nat := 936836553796837192309361

theorem tailTrace_2736724 : CollatzResearch.WordTrace tailWord_2736724 prefixEnd_2736724 936836553796837192309361 := by
  unfold tailWord_2736724
  simp only [CollatzResearch.WordTrace]
  refine ⟨49908262268661909046536613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66544349691549212062048817 49908262268661909046536613)
  ·
    refine ⟨9357799175374107946225615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49908262268661909046536613 9357799175374107946225615)
    ·
      refine ⟨14036698763061161919338423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9357799175374107946225615 14036698763061161919338423)
      ·
        refine ⟨21055048144591742879007635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14036698763061161919338423 21055048144591742879007635)
        ·
          refine ⟨31582572216887614318511453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21055048144591742879007635 31582572216887614318511453)
          ·
            refine ⟨11843464581332855369441795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31582572216887614318511453 11843464581332855369441795)
            ·
              refine ⟨17765196871999283054162693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11843464581332855369441795 17765196871999283054162693)
              ·
                refine ⟨3330974413499865572655505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17765196871999283054162693 3330974413499865572655505)
                ·
                  refine ⟨2498230810124899179491629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330974413499865572655505 2498230810124899179491629)
                  ·
                    refine ⟨936836553796837192309361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498230810124899179491629 936836553796837192309361)
                    ·
                      rfl

theorem cell22_2736724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_2736724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736724 prefixEnd_2736724 := by exact prefixLift 2736724
  have htrace : WordTrace (prefixWord ++ tailWord_2736724) baseStart_2736724 baseEnd_2736724 := by
    simpa [prefixWord, tailWord_2736724, baseEnd_2736724] using wordTrace_append hprefix tailTrace_2736724
  have hstable : (prefixWord ++ tailWord_2736724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736724).length < 2 ^ (prefixWord ++ tailWord_2736724).sum := by decide
  have hdescent : baseEnd_2736724 < baseStart_2736724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736737 : List Nat := [1, 2, 3, 1, 1, 6, 1, 7]
def baseStart_2736737 : Nat := 118140960795 + 2736737 * 2 ^ 59
def prefixEnd_2736737 : Nat := 4983230072969 + 3 ^ 40 * 2736737 * 2
def baseEnd_2736737 : Nat := 104093444884723276859369

theorem tailTrace_2736737 : CollatzResearch.WordTrace tailWord_2736737 prefixEnd_2736737 104093444884723276859369 := by
  unfold tailWord_2736737
  simp only [CollatzResearch.WordTrace]
  refine ⟨99816998686276721313296465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66544665790851147542197643 99816998686276721313296465)
  ·
    refine ⟨74862749014707540984972349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99816998686276721313296465 74862749014707540984972349)
    ·
      refine ⟨28073530880515327869364631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74862749014707540984972349 28073530880515327869364631)
      ·
        refine ⟨42110296320772991804046947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28073530880515327869364631 42110296320772991804046947)
        ·
          refine ⟨63165444481159487706070421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42110296320772991804046947 63165444481159487706070421)
          ·
            refine ⟨2960880210054350986222051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63165444481159487706070421 2960880210054350986222051)
            ·
              refine ⟨4441320315081526479333077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960880210054350986222051 4441320315081526479333077)
              ·
                refine ⟨104093444884723276859369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4441320315081526479333077 104093444884723276859369)
                ·
                  rfl

theorem cell22_2736737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 7].length) (baseStart_2736737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736737 prefixEnd_2736737 := by exact prefixLift 2736737
  have htrace : WordTrace (prefixWord ++ tailWord_2736737) baseStart_2736737 baseEnd_2736737 := by
    simpa [prefixWord, tailWord_2736737, baseEnd_2736737] using wordTrace_append hprefix tailTrace_2736737
  have hstable : (prefixWord ++ tailWord_2736737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736737).length < 2 ^ (prefixWord ++ tailWord_2736737).sum := by decide
  have hdescent : baseEnd_2736737 < baseStart_2736737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736754 : List Nat := [3, 2, 1, 2, 4, 1, 3, 6]
def baseStart_2736754 : Nat := 118140960795 + 2736754 * 2 ^ 59
def prefixEnd_2736754 : Nat := 4983230072969 + 3 ^ 40 * 2736754 * 2
def baseEnd_2736754 : Nat := 104094091489991901562141

theorem tailTrace_2736754 : CollatzResearch.WordTrace tailWord_2736754 prefixEnd_2736754 104094091489991901562141 := by
  unfold tailWord_2736754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954404681803783304166329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66545079151476755477776877 24954404681803783304166329)
  ·
    refine ⟨18715803511352837478124747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24954404681803783304166329 18715803511352837478124747)
    ·
      refine ⟨28073705267029256217187121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18715803511352837478124747 28073705267029256217187121)
      ·
        refine ⟨21055278950271942162890341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28073705267029256217187121 21055278950271942162890341)
        ·
          refine ⟨3947864803175989155541939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21055278950271942162890341 3947864803175989155541939)
          ·
            refine ⟨5921797204763983733312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947864803175989155541939 5921797204763983733312909)
            ·
              refine ⟨2220673951786493899992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5921797204763983733312909 2220673951786493899992341)
              ·
                refine ⟨104094091489991901562141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2220673951786493899992341 104094091489991901562141)
                ·
                  rfl

theorem cell22_2736754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_2736754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736754 prefixEnd_2736754 := by exact prefixLift 2736754
  have htrace : WordTrace (prefixWord ++ tailWord_2736754) baseStart_2736754 baseEnd_2736754 := by
    simpa [prefixWord, tailWord_2736754, baseEnd_2736754] using wordTrace_append hprefix tailTrace_2736754
  have hstable : (prefixWord ++ tailWord_2736754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736754).length < 2 ^ (prefixWord ++ tailWord_2736754).sum := by decide
  have hdescent : baseEnd_2736754 < baseStart_2736754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736782 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_2736782 : Nat := 118140960795 + 2736782 * 2 ^ 59
def prefixEnd_2736782 : Nat := 4983230072969 + 3 ^ 40 * 2736782 * 2
def baseEnd_2736782 : Nat := 312285469460714791453061

theorem tailTrace_2736782 : CollatzResearch.WordTrace tailWord_2736782 prefixEnd_2736782 312285469460714791453061 := by
  unfold tailWord_2736782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477329996389211749835575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66545759980742462665789733 12477329996389211749835575)
  ·
    refine ⟨18715994994583817624753363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477329996389211749835575 18715994994583817624753363)
    ·
      refine ⟨28073992491875726437130045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18715994994583817624753363 28073992491875726437130045)
      ·
        refine ⟨10527747184453397413923767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28073992491875726437130045 10527747184453397413923767)
        ·
          refine ⟨15791620776680096120885651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527747184453397413923767 15791620776680096120885651)
          ·
            refine ⟨23687431165020144181328477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15791620776680096120885651 23687431165020144181328477)
            ·
              refine ⟨8882786686882554067998179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23687431165020144181328477 8882786686882554067998179)
              ·
                refine ⟨13324180030323831101997269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882786686882554067998179 13324180030323831101997269)
                ·
                  refine ⟨312285469460714791453061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13324180030323831101997269 312285469460714791453061)
                  ·
                    rfl

theorem cell22_2736782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_2736782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736782 prefixEnd_2736782 := by exact prefixLift 2736782
  have htrace : WordTrace (prefixWord ++ tailWord_2736782) baseStart_2736782 baseEnd_2736782 := by
    simpa [prefixWord, tailWord_2736782, baseEnd_2736782] using wordTrace_append hprefix tailTrace_2736782
  have hstable : (prefixWord ++ tailWord_2736782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736782).length < 2 ^ (prefixWord ++ tailWord_2736782).sum := by decide
  have hdescent : baseEnd_2736782 < baseStart_2736782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736786 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2736786 : Nat := 118140960795 + 2736786 * 2 ^ 59
def prefixEnd_2736786 : Nat := 4983230072969 + 3 ^ 40 * 2736786 * 2
def baseEnd_2736786 : Nat := 936857777663889697259171

theorem tailTrace_2736786 : CollatzResearch.WordTrace tailWord_2736786 prefixEnd_2736786 936857777663889697259171 := by
  unfold tailWord_2736786
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954696465774800670457553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66545857242066135121220141 24954696465774800670457553)
  ·
    refine ⟨18716022349331100502843165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24954696465774800670457553 18716022349331100502843165)
    ·
      refine ⟨7018508380999162688566187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18716022349331100502843165 7018508380999162688566187)
      ·
        refine ⟨10527762571498744032849281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018508380999162688566187 10527762571498744032849281)
        ·
          refine ⟨7895821928624058024636961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10527762571498744032849281 7895821928624058024636961)
          ·
            refine ⟨5921866446468043518477721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7895821928624058024636961 5921866446468043518477721)
            ·
              refine ⟨4441399834851032638858291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5921866446468043518477721 4441399834851032638858291)
              ·
                refine ⟨6662099752276548958287437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441399834851032638858291 6662099752276548958287437)
                ·
                  refine ⟨2498287407103705859357789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6662099752276548958287437 2498287407103705859357789)
                  ·
                    refine ⟨936857777663889697259171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498287407103705859357789 936857777663889697259171)
                    ·
                      rfl

theorem cell22_2736786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2736786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736786 prefixEnd_2736786 := by exact prefixLift 2736786
  have htrace : WordTrace (prefixWord ++ tailWord_2736786) baseStart_2736786 baseEnd_2736786 := by
    simpa [prefixWord, tailWord_2736786, baseEnd_2736786] using wordTrace_append hprefix tailTrace_2736786
  have hstable : (prefixWord ++ tailWord_2736786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736786).length < 2 ^ (prefixWord ++ tailWord_2736786).sum := by decide
  have hdescent : baseEnd_2736786 < baseStart_2736786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736797 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2736797 : Nat := 118140960795 + 2736797 * 2 ^ 59
def prefixEnd_2736797 : Nat := 4983230072969 + 3 ^ 40 * 2736797 * 2
def baseEnd_2736797 : Nat := 936861543188689335234137

theorem tailTrace_2736797 : CollatzResearch.WordTrace tailWord_2736797 prefixEnd_2736797 936861543188689335234137 := by
  unfold tailWord_2736797
  simp only [CollatzResearch.WordTrace]
  refine ⟨99819187066059351560480645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66546124710706234373653763 99819187066059351560480645)
  ·
    refine ⟨18716097574886128417590121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99819187066059351560480645 18716097574886128417590121)
    ·
      refine ⟨14037073181164596313192591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18716097574886128417590121 14037073181164596313192591)
      ·
        refine ⟨21055609771746894469788887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14037073181164596313192591 21055609771746894469788887)
        ·
          refine ⟨31583414657620341704683331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21055609771746894469788887 31583414657620341704683331)
          ·
            refine ⟨47375121986430512557024997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31583414657620341704683331 47375121986430512557024997)
            ·
              refine ⟨8882835372455721104442187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47375121986430512557024997 8882835372455721104442187)
              ·
                refine ⟨13324253058683581656663281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882835372455721104442187 13324253058683581656663281)
                ·
                  refine ⟨9993189794012686242497461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13324253058683581656663281 9993189794012686242497461)
                  ·
                    refine ⟨936861543188689335234137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9993189794012686242497461 936861543188689335234137)
                    ·
                      rfl

theorem cell22_2736797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2736797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736797 prefixEnd_2736797 := by exact prefixLift 2736797
  have htrace : WordTrace (prefixWord ++ tailWord_2736797) baseStart_2736797 baseEnd_2736797 := by
    simpa [prefixWord, tailWord_2736797, baseEnd_2736797] using wordTrace_append hprefix tailTrace_2736797
  have hstable : (prefixWord ++ tailWord_2736797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736797).length < 2 ^ (prefixWord ++ tailWord_2736797).sum := by decide
  have hdescent : baseEnd_2736797 < baseStart_2736797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736829 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2736829 : Nat := 118140960795 + 2736829 * 2 ^ 59
def prefixEnd_2736829 : Nat := 4983230072969 + 3 ^ 40 * 2736829 * 2
def baseEnd_2736829 : Nat := 936872497442651918434039

theorem tailTrace_2736829 : CollatzResearch.WordTrace tailWord_2736829 prefixEnd_2736829 936872497442651918434039 := by
  unfold tailWord_2736829
  simp only [CollatzResearch.WordTrace]
  refine ⟨99820354201943421025645541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66546902801295614017097027 99820354201943421025645541)
  ·
    refine ⟨18716316412864391442308539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99820354201943421025645541 18716316412864391442308539)
    ·
      refine ⟨28074474619296587163462809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716316412864391442308539 28074474619296587163462809)
      ·
        refine ⟨21055855964472440372597107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28074474619296587163462809 21055855964472440372597107)
        ·
          refine ⟨31583783946708660558895661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21055855964472440372597107 31583783946708660558895661)
          ·
            refine ⟨11843918980015747709585873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31583783946708660558895661 11843918980015747709585873)
            ·
              refine ⟨8882939235011810782189405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11843918980015747709585873 8882939235011810782189405)
              ·
                refine ⟨3331102213129429043321027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8882939235011810782189405 3331102213129429043321027)
                ·
                  refine ⟨4996653319694143564981541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331102213129429043321027 4996653319694143564981541)
                  ·
                    refine ⟨936872497442651918434039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996653319694143564981541 936872497442651918434039)
                    ·
                      rfl

theorem cell22_2736829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2736829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736829 prefixEnd_2736829 := by exact prefixLift 2736829
  have htrace : WordTrace (prefixWord ++ tailWord_2736829) baseStart_2736829 baseEnd_2736829 := by
    simpa [prefixWord, tailWord_2736829, baseEnd_2736829] using wordTrace_append hprefix tailTrace_2736829
  have hstable : (prefixWord ++ tailWord_2736829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736829).length < 2 ^ (prefixWord ++ tailWord_2736829).sum := by decide
  have hdescent : baseEnd_2736829 < baseStart_2736829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736844 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_2736844 : Nat := 118140960795 + 2736844 * 2 ^ 59
def prefixEnd_2736844 : Nat := 4983230072969 + 3 ^ 40 * 2736844 * 2
def baseEnd_2736844 : Nat := 312292544083065626436331

theorem tailTrace_2736844 : CollatzResearch.WordTrace tailWord_2736844 prefixEnd_2736844 312292544083065626436331 := by
  unfold tailWord_2736844
  simp only [CollatzResearch.WordTrace]
  refine ⟨49910450648444539293720793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66547267531259385724961057 49910450648444539293720793)
  ·
    refine ⟨37432837986333404470290595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49910450648444539293720793 37432837986333404470290595)
    ·
      refine ⟨56149256979500106705435893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37432837986333404470290595 56149256979500106705435893)
      ·
        refine ⟨5263992841828135003634615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56149256979500106705435893 5263992841828135003634615)
        ·
          refine ⟨7895989262742202505451923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263992841828135003634615 7895989262742202505451923)
          ·
            refine ⟨11843983894113303758177885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7895989262742202505451923 11843983894113303758177885)
            ·
              refine ⟨4441493960292488909316707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11843983894113303758177885 4441493960292488909316707)
              ·
                refine ⟨6662240940438733363975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441493960292488909316707 6662240940438733363975061)
                ·
                  refine ⟨312292544083065626436331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6662240940438733363975061 312292544083065626436331)
                  ·
                    rfl

theorem cell22_2736844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_2736844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736844 prefixEnd_2736844 := by exact prefixLift 2736844
  have htrace : WordTrace (prefixWord ++ tailWord_2736844) baseStart_2736844 baseEnd_2736844 := by
    simpa [prefixWord, tailWord_2736844, baseEnd_2736844] using wordTrace_append hprefix tailTrace_2736844
  have hstable : (prefixWord ++ tailWord_2736844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736844).length < 2 ^ (prefixWord ++ tailWord_2736844).sum := by decide
  have hdescent : baseEnd_2736844 < baseStart_2736844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736857 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_2736857 : Nat := 118140960795 + 2736857 * 2 ^ 59
def prefixEnd_2736857 : Nat := 4983230072969 + 3 ^ 40 * 2736857 * 2
def baseEnd_2736857 : Nat := 936882082414869178733953

theorem tailTrace_2736857 : CollatzResearch.WordTrace tailWord_2736857 prefixEnd_2736857 936882082414869178733953 := by
  unfold tailWord_2736857
  simp only [CollatzResearch.WordTrace]
  refine ⟨99821375445841981807664825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66547583630561321205109883 99821375445841981807664825)
  ·
    refine ⟨74866031584381486355748619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99821375445841981807664825 74866031584381486355748619)
    ·
      refine ⟨112299047376572229533622929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74866031584381486355748619 112299047376572229533622929)
      ·
        refine ⟨84224285532429172150217197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112299047376572229533622929 84224285532429172150217197)
        ·
          refine ⟨31584107074660939556331449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84224285532429172150217197 31584107074660939556331449)
          ·
            refine ⟨23688080305995704667248587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31584107074660939556331449 23688080305995704667248587)
            ·
              refine ⟨35532120458993557000872881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23688080305995704667248587 35532120458993557000872881)
              ·
                refine ⟨26649090344245167750654661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35532120458993557000872881 26649090344245167750654661)
                ·
                  refine ⟨4996704439545968953247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26649090344245167750654661 4996704439545968953247749)
                  ·
                    refine ⟨936882082414869178733953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996704439545968953247749 936882082414869178733953)
                    ·
                      rfl

theorem cell22_2736857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_2736857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736857 prefixEnd_2736857 := by exact prefixLift 2736857
  have htrace : WordTrace (prefixWord ++ tailWord_2736857) baseStart_2736857 baseEnd_2736857 := by
    simpa [prefixWord, tailWord_2736857, baseEnd_2736857] using wordTrace_append hprefix tailTrace_2736857
  have hstable : (prefixWord ++ tailWord_2736857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736857).length < 2 ^ (prefixWord ++ tailWord_2736857).sum := by decide
  have hdescent : baseEnd_2736857 < baseStart_2736857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736925 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2736925 : Nat := 118140960795 + 2736925 * 2 ^ 59
def prefixEnd_2736925 : Nat := 4983230072969 + 3 ^ 40 * 2736925 * 2
def baseEnd_2736925 : Nat := 936905360204539668033745

theorem tailTrace_2736925 : CollatzResearch.WordTrace tailWord_2736925 prefixEnd_2736925 936905360204539668033745 := by
  unfold tailWord_2736925
  simp only [CollatzResearch.WordTrace]
  refine ⟨99823855609595629421140229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66549237073063752947426819 99823855609595629421140229)
  ·
    refine ⟨18716972926799180516463793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99823855609595629421140229 18716972926799180516463793)
    ·
      refine ⟨14037729695099385387347845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18716972926799180516463793 14037729695099385387347845)
      ·
        refine ⟨2632074317831134760127721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14037729695099385387347845 2632074317831134760127721)
        ·
          refine ⟨1974055738373351070095791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632074317831134760127721 1974055738373351070095791)
          ·
            refine ⟨2961083607560026605143687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974055738373351070095791 2961083607560026605143687)
            ·
              refine ⟨4441625411340039907715531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961083607560026605143687 4441625411340039907715531)
              ·
                refine ⟨6662438117010059861573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441625411340039907715531 6662438117010059861573297)
                ·
                  refine ⟨4996828587757544896179973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6662438117010059861573297 4996828587757544896179973)
                  ·
                    refine ⟨936905360204539668033745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996828587757544896179973 936905360204539668033745)
                    ·
                      rfl

theorem cell22_2736925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2736925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736925 prefixEnd_2736925 := by exact prefixLift 2736925
  have htrace : WordTrace (prefixWord ++ tailWord_2736925) baseStart_2736925 baseEnd_2736925 := by
    simpa [prefixWord, tailWord_2736925, baseEnd_2736925] using wordTrace_append hprefix tailTrace_2736925
  have hstable : (prefixWord ++ tailWord_2736925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736925).length < 2 ^ (prefixWord ++ tailWord_2736925).sum := by decide
  have hdescent : baseEnd_2736925 < baseStart_2736925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736949 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2736949 : Nat := 118140960795 + 2736949 * 2 ^ 59
def prefixEnd_2736949 : Nat := 4983230072969 + 3 ^ 40 * 2736949 * 2
def baseEnd_2736949 : Nat := 936913575895011605433671

theorem tailTrace_2736949 : CollatzResearch.WordTrace tailWord_2736949 prefixEnd_2736949 936913575895011605433671 := by
  unfold tailWord_2736949
  simp only [CollatzResearch.WordTrace]
  refine ⟨99824730961508681520013901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66549820641005787680009267 99824730961508681520013901)
  ·
    refine ⟨37434274110565755570005213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99824730961508681520013901 37434274110565755570005213)
    ·
      refine ⟨14037852791462158338751955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37434274110565755570005213 14037852791462158338751955)
      ·
        refine ⟨21056779187193237508127933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14037852791462158338751955 21056779187193237508127933)
        ·
          refine ⟨7896292195197464065547975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21056779187193237508127933 7896292195197464065547975)
          ·
            refine ⟨11844438292796196098321963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7896292195197464065547975 11844438292796196098321963)
            ·
              refine ⟨17766657439194294147482945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11844438292796196098321963 17766657439194294147482945)
              ·
                refine ⟨13324993079395720610612209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17766657439194294147482945 13324993079395720610612209)
                ·
                  refine ⟨9993744809546790457959157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13324993079395720610612209 9993744809546790457959157)
                  ·
                    refine ⟨936913575895011605433671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9993744809546790457959157 936913575895011605433671)
                    ·
                      rfl

theorem cell22_2736949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2736949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736949 prefixEnd_2736949 := by exact prefixLift 2736949
  have htrace : WordTrace (prefixWord ++ tailWord_2736949) baseStart_2736949 baseEnd_2736949 := by
    simpa [prefixWord, tailWord_2736949, baseEnd_2736949] using wordTrace_append hprefix tailTrace_2736949
  have hstable : (prefixWord ++ tailWord_2736949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736949).length < 2 ^ (prefixWord ++ tailWord_2736949).sum := by decide
  have hdescent : baseEnd_2736949 < baseStart_2736949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736981 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2736981 : Nat := 118140960795 + 2736981 * 2 ^ 59
def prefixEnd_2736981 : Nat := 4983230072969 + 3 ^ 40 * 2736981 * 2
def baseEnd_2736981 : Nat := 936924530148974188633573

theorem tailTrace_2736981 : CollatzResearch.WordTrace tailWord_2736981 prefixEnd_2736981 936924530148974188633573 := by
  unfold tailWord_2736981
  simp only [CollatzResearch.WordTrace]
  refine ⟨99825898097392750985178797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66550598731595167323452531 99825898097392750985178797)
  ·
    refine ⟨37434711786522281619442049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99825898097392750985178797 37434711786522281619442049)
    ·
      refine ⟨28076033839891711214581537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37434711786522281619442049 28076033839891711214581537)
      ·
        refine ⟨21057025379918783410936153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28076033839891711214581537 21057025379918783410936153)
        ·
          refine ⟨15792769034939087558202115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21057025379918783410936153 15792769034939087558202115)
          ·
            refine ⟨23689153552408631337303173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15792769034939087558202115 23689153552408631337303173)
            ·
              refine ⟨4441716291076618375744345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23689153552408631337303173 4441716291076618375744345)
              ·
                refine ⟨3331287218307463781808259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441716291076618375744345 3331287218307463781808259)
                ·
                  refine ⟨4996930827461195672712389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331287218307463781808259 4996930827461195672712389)
                  ·
                    refine ⟨936924530148974188633573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996930827461195672712389 936924530148974188633573)
                    ·
                      rfl

theorem cell22_2736981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2736981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2736981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2736981 prefixEnd_2736981 := by exact prefixLift 2736981
  have htrace : WordTrace (prefixWord ++ tailWord_2736981) baseStart_2736981 baseEnd_2736981 := by
    simpa [prefixWord, tailWord_2736981, baseEnd_2736981] using wordTrace_append hprefix tailTrace_2736981
  have hstable : (prefixWord ++ tailWord_2736981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736981).length < 2 ^ (prefixWord ++ tailWord_2736981).sum := by decide
  have hdescent : baseEnd_2736981 < baseStart_2736981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737009 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2737009 : Nat := 118140960795 + 2737009 * 2 ^ 59
def prefixEnd_2737009 : Nat := 4983230072969 + 3 ^ 40 * 2737009 * 2
def baseEnd_2737009 : Nat := 936934115121191448933487

theorem tailTrace_2737009 : CollatzResearch.WordTrace tailWord_2737009 prefixEnd_2737009 936934115121191448933487 := by
  unfold tailWord_2737009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99826919341291311767198081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66551279560860874511465387 99826919341291311767198081)
  ·
    refine ⟨74870189505968483825398561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99826919341291311767198081 74870189505968483825398561)
    ·
      refine ⟨56152642129476362869048921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74870189505968483825398561 56152642129476362869048921)
      ·
        refine ⟨42114481597107272151786691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56152642129476362869048921 42114481597107272151786691)
        ·
          refine ⟨63171722395660908227680037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42114481597107272151786691 63171722395660908227680037)
          ·
            refine ⟨11844697949186420292690007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63171722395660908227680037 11844697949186420292690007)
            ·
              refine ⟨17767046923779630439035011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11844697949186420292690007 17767046923779630439035011)
              ·
                refine ⟨26650570385669445658552517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17767046923779630439035011 26650570385669445658552517)
                ·
                  refine ⟨4996981947313021060978597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26650570385669445658552517 4996981947313021060978597)
                  ·
                    refine ⟨936934115121191448933487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996981947313021060978597 936934115121191448933487)
                    ·
                      rfl

theorem cell22_2737009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2737009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737009 prefixEnd_2737009 := by exact prefixLift 2737009
  have htrace : WordTrace (prefixWord ++ tailWord_2737009) baseStart_2737009 baseEnd_2737009 := by
    simpa [prefixWord, tailWord_2737009, baseEnd_2737009] using wordTrace_append hprefix tailTrace_2737009
  have hstable : (prefixWord ++ tailWord_2737009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737009).length < 2 ^ (prefixWord ++ tailWord_2737009).sum := by decide
  have hdescent : baseEnd_2737009 < baseStart_2737009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737086 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_2737086 : Nat := 118140960795 + 2737086 * 2 ^ 59
def prefixEnd_2737086 : Nat := 4983230072969 + 3 ^ 40 * 2737086 * 2
def baseEnd_2737086 : Nat := 312320157931596304919417

theorem tailTrace_2737086 : CollatzResearch.WordTrace tailWord_2737086 prefixEnd_2737086 312320157931596304919417 := by
  unfold tailWord_2737086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478715970251544239718889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66553151841341569278500741 12478715970251544239718889)
  ·
    refine ⟨9359036977688658179789167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12478715970251544239718889 9359036977688658179789167)
    ·
      refine ⟨14038555466532987269683751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359036977688658179789167 14038555466532987269683751)
      ·
        refine ⟨21057833199799480904525627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14038555466532987269683751 21057833199799480904525627)
        ·
          refine ⟨31586749799699221356788441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21057833199799480904525627 31586749799699221356788441)
          ·
            refine ⟨23690062349774416017591331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31586749799699221356788441 23690062349774416017591331)
            ·
              refine ⟨35535093524661624026386997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23690062349774416017591331 35535093524661624026386997)
              ·
                refine ⟨3331415017937027252473781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35535093524661624026386997 3331415017937027252473781)
                ·
                  refine ⟨312320157931596304919417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3331415017937027252473781 312320157931596304919417)
                  ·
                    rfl

theorem cell22_2737086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_2737086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737086 prefixEnd_2737086 := by exact prefixLift 2737086
  have htrace : WordTrace (prefixWord ++ tailWord_2737086) baseStart_2737086 baseEnd_2737086 := by
    simpa [prefixWord, tailWord_2737086, baseEnd_2737086] using wordTrace_append hprefix tailTrace_2737086
  have hstable : (prefixWord ++ tailWord_2737086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737086).length < 2 ^ (prefixWord ++ tailWord_2737086).sum := by decide
  have hdescent : baseEnd_2737086 < baseStart_2737086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737176 : List Nat := [2, 1, 2, 3, 2, 4, 8]
def baseStart_2737176 : Nat := 118140960795 + 2737176 * 2 ^ 59
def prefixEnd_2737176 : Nat := 4983230072969 + 3 ^ 40 * 2737176 * 2
def baseEnd_2737176 : Nat := 34703380838298469629925

theorem tailTrace_2737176 : CollatzResearch.WordTrace tailWord_2737176 prefixEnd_2737176 34703380838298469629925 := by
  unfold tailWord_2737176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49916505165843149644263691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66555340221124199525684921 49916505165843149644263691)
  ·
    refine ⟨74874757748764724466395537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49916505165843149644263691 74874757748764724466395537)
    ·
      refine ⟨56156068311573543349796653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74874757748764724466395537 56156068311573543349796653)
      ·
        refine ⟨21058525616840078756173745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56156068311573543349796653 21058525616840078756173745)
        ·
          refine ⟨15793894212630059067130309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21058525616840078756173745 15793894212630059067130309)
          ·
            refine ⟨2961355164868136075086933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15793894212630059067130309 2961355164868136075086933)
            ·
              refine ⟨34703380838298469629925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2961355164868136075086933 34703380838298469629925)
              ·
                rfl

theorem cell22_2737176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 8].length) (baseStart_2737176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737176 prefixEnd_2737176 := by exact prefixLift 2737176
  have htrace : WordTrace (prefixWord ++ tailWord_2737176) baseStart_2737176 baseEnd_2737176 := by
    simpa [prefixWord, tailWord_2737176, baseEnd_2737176] using wordTrace_append hprefix tailTrace_2737176
  have hstable : (prefixWord ++ tailWord_2737176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737176).length < 2 ^ (prefixWord ++ tailWord_2737176).sum := by decide
  have hdescent : baseEnd_2737176 < baseStart_2737176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737285 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2737285 : Nat := 118140960795 + 2737285 * 2 ^ 59
def prefixEnd_2737285 : Nat := 4983230072969 + 3 ^ 40 * 2737285 * 2
def baseEnd_2737285 : Nat := 937028595561618729032641

theorem tailTrace_2737285 : CollatzResearch.WordTrace tailWord_2737285 prefixEnd_2737285 937028595561618729032641 := by
  unfold tailWord_2737285
  simp only [CollatzResearch.WordTrace]
  refine ⟨99836985888291410904245309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66557990592194273936163539 99836985888291410904245309)
  ·
    refine ⟨37438869708109279089091991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99836985888291410904245309 37438869708109279089091991)
    ·
      refine ⟨56158304562163918633637987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37438869708109279089091991 56158304562163918633637987)
      ·
        refine ⟨84237456843245877950456981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56158304562163918633637987 84237456843245877950456981)
        ·
          refine ⟨3948630789527150528927671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84237456843245877950456981 3948630789527150528927671)
          ·
            refine ⟨5922946184290725793391507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948630789527150528927671 5922946184290725793391507)
            ·
              refine ⟨8884419276436088690087261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922946184290725793391507 8884419276436088690087261)
              ·
                refine ⟨3331657228663533258782723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8884419276436088690087261 3331657228663533258782723)
                ·
                  refine ⟨4997485842995299888174085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331657228663533258782723 4997485842995299888174085)
                  ·
                    refine ⟨937028595561618729032641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4997485842995299888174085 937028595561618729032641)
                    ·
                      rfl

theorem cell22_2737285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2737285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737285 prefixEnd_2737285 := by exact prefixLift 2737285
  have htrace : WordTrace (prefixWord ++ tailWord_2737285) baseStart_2737285 baseEnd_2737285 := by
    simpa [prefixWord, tailWord_2737285, baseEnd_2737285] using wordTrace_append hprefix tailTrace_2737285
  have hstable : (prefixWord ++ tailWord_2737285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737285).length < 2 ^ (prefixWord ++ tailWord_2737285).sum := by decide
  have hdescent : baseEnd_2737285 < baseStart_2737285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737343 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 5, 3]
def baseStart_2737343 : Nat := 118140960795 + 2737343 * 2 ^ 59
def prefixEnd_2737343 : Nat := 4983230072969 + 3 ^ 40 * 2737343 * 2
def baseEnd_2737343 : Nat := 937048450146925911082463

theorem tailTrace_2737343 : CollatzResearch.WordTrace tailWord_2737343 prefixEnd_2737343 937048450146925911082463 := by
  unfold tailWord_2737343
  simp only [CollatzResearch.WordTrace]
  refine ⟨99839101322081286809856683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66559400881387524539904455 99839101322081286809856683)
  ·
    refine ⟨149758651983121930214785025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99839101322081286809856683 149758651983121930214785025)
    ·
      refine ⟨112318988987341447661088769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149758651983121930214785025 112318988987341447661088769)
      ·
        refine ⟨84239241740506085745816577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112318988987341447661088769 84239241740506085745816577)
        ·
          refine ⟨63179431305379564309362433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84239241740506085745816577 63179431305379564309362433)
          ·
            refine ⟨47384573479034673232021825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63179431305379564309362433 47384573479034673232021825)
            ·
              refine ⟨35538430109276004924016369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47384573479034673232021825 35538430109276004924016369)
              ·
                refine ⟨26653822581957003693012277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35538430109276004924016369 26653822581957003693012277)
                ·
                  refine ⟨2498795867058469096219901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26653822581957003693012277 2498795867058469096219901)
                  ·
                    refine ⟨937048450146925911082463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498795867058469096219901 937048450146925911082463)
                    ·
                      rfl

theorem cell22_2737343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_2737343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737343 prefixEnd_2737343 := by exact prefixLift 2737343
  have htrace : WordTrace (prefixWord ++ tailWord_2737343) baseStart_2737343 baseEnd_2737343 := by
    simpa [prefixWord, tailWord_2737343, baseEnd_2737343] using wordTrace_append hprefix tailTrace_2737343
  have hstable : (prefixWord ++ tailWord_2737343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737343).length < 2 ^ (prefixWord ++ tailWord_2737343).sum := by decide
  have hdescent : baseEnd_2737343 < baseStart_2737343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737345 : List Nat := [1, 2, 6, 1, 1, 3, 8]
def baseStart_2737345 : Nat := 118140960795 + 2737345 * 2 ^ 59
def prefixEnd_2737345 : Nat := 4983230072969 + 3 ^ 40 * 2737345 * 2
def baseEnd_2737345 : Nat := 34705523510659206390091

theorem tailTrace_2737345 : CollatzResearch.WordTrace tailWord_2737345 prefixEnd_2737345 34705523510659206390091 := by
  unfold tailWord_2737345
  simp only [CollatzResearch.WordTrace]
  refine ⟨99839174268074041151429489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66559449512049360767619659 99839174268074041151429489)
  ·
    refine ⟨74879380701055530863572117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99839174268074041151429489 74879380701055530863572117)
    ·
      refine ⟨3509970970361978009229943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74879380701055530863572117 3509970970361978009229943)
      ·
        refine ⟨5264956455542967013844915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509970970361978009229943 5264956455542967013844915)
        ·
          refine ⟨7897434683314450520767373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264956455542967013844915 7897434683314450520767373)
          ·
            refine ⟨2961538006242918945287765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7897434683314450520767373 2961538006242918945287765)
            ·
              refine ⟨34705523510659206390091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2961538006242918945287765 34705523510659206390091)
              ·
                rfl

theorem cell22_2737345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 8].length) (baseStart_2737345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737345 prefixEnd_2737345 := by exact prefixLift 2737345
  have htrace : WordTrace (prefixWord ++ tailWord_2737345) baseStart_2737345 baseEnd_2737345 := by
    simpa [prefixWord, tailWord_2737345, baseEnd_2737345] using wordTrace_append hprefix tailTrace_2737345
  have hstable : (prefixWord ++ tailWord_2737345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737345).length < 2 ^ (prefixWord ++ tailWord_2737345).sum := by decide
  have hdescent : baseEnd_2737345 < baseStart_2737345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737418 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_2737418 : Nat := 118140960795 + 2737418 * 2 ^ 59
def prefixEnd_2737418 : Nat := 4983230072969 + 3 ^ 40 * 2737418 * 2
def baseEnd_2737418 : Nat := 312358041393216905152411

theorem tailTrace_2737418 : CollatzResearch.WordTrace tailWord_2737418 prefixEnd_2737418 312358041393216905152411 := by
  unfold tailWord_2737418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960459199202393654709227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66561224531206383079224605 24960459199202393654709227)
  ·
    refine ⟨37440688798803590482063841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24960459199202393654709227 37440688798803590482063841)
    ·
      refine ⟨28080516599102692861547881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37440688798803590482063841 28080516599102692861547881)
      ·
        refine ⟨21060387449327019646160911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28080516599102692861547881 21060387449327019646160911)
        ·
          refine ⟨31590581173990529469241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060387449327019646160911 31590581173990529469241367)
          ·
            refine ⟨47385871760985794203862051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31590581173990529469241367 47385871760985794203862051)
            ·
              refine ⟨71078807641478691305793077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47385871760985794203862051 71078807641478691305793077)
              ·
                refine ⟨6663638216388627309918101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71078807641478691305793077 6663638216388627309918101)
                ·
                  refine ⟨312358041393216905152411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6663638216388627309918101 312358041393216905152411)
                  ·
                    rfl

theorem cell22_2737418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_2737418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737418 prefixEnd_2737418 := by exact prefixLift 2737418
  have htrace : WordTrace (prefixWord ++ tailWord_2737418) baseStart_2737418 baseEnd_2737418 := by
    simpa [prefixWord, tailWord_2737418, baseEnd_2737418] using wordTrace_append hprefix tailTrace_2737418
  have hstable : (prefixWord ++ tailWord_2737418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737418).length < 2 ^ (prefixWord ++ tailWord_2737418).sum := by decide
  have hdescent : baseEnd_2737418 < baseStart_2737418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737484 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_2737484 : Nat := 118140960795 + 2737484 * 2 ^ 59
def prefixEnd_2737484 : Nat := 4983230072969 + 3 ^ 40 * 2737484 * 2
def baseEnd_2737484 : Nat := 937096717328448543307031

theorem tailTrace_2737484 : CollatzResearch.WordTrace tailWord_2737484 prefixEnd_2737484 937096717328448543307031 := by
  unfold tailWord_2737484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49922122007285233945369753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66562829343046978593826337 49922122007285233945369753)
  ·
    refine ⟨37441591505463925459027315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49922122007285233945369753 37441591505463925459027315)
    ·
      refine ⟨56162387258195888188540973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37441591505463925459027315 56162387258195888188540973)
      ·
        refine ⟨21060895221823458070702865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56162387258195888188540973 21060895221823458070702865)
        ·
          refine ⟨15795671416367593553027149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21060895221823458070702865 15795671416367593553027149)
          ·
            refine ⟨5923376781137847582385181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15795671416367593553027149 5923376781137847582385181)
            ·
              refine ⟨2221266292926692843394443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5923376781137847582385181 2221266292926692843394443)
              ·
                refine ⟨3331899439390039265091665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221266292926692843394443 3331899439390039265091665)
                ·
                  refine ⟨2498924579542529448818749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331899439390039265091665 2498924579542529448818749)
                  ·
                    refine ⟨937096717328448543307031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498924579542529448818749 937096717328448543307031)
                    ·
                      rfl

theorem cell22_2737484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_2737484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737484 prefixEnd_2737484 := by exact prefixLift 2737484
  have htrace : WordTrace (prefixWord ++ tailWord_2737484) baseStart_2737484 baseEnd_2737484 := by
    simpa [prefixWord, tailWord_2737484, baseEnd_2737484] using wordTrace_append hprefix tailTrace_2737484
  have hstable : (prefixWord ++ tailWord_2737484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737484).length < 2 ^ (prefixWord ++ tailWord_2737484).sum := by decide
  have hdescent : baseEnd_2737484 < baseStart_2737484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737585 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2737585 : Nat := 118140960795 + 2737585 * 2 ^ 59
def prefixEnd_2737585 : Nat := 4983230072969 + 3 ^ 40 * 2737585 * 2
def baseEnd_2737585 : Nat := 937131291692517946531721

theorem tailTrace_2737585 : CollatzResearch.WordTrace tailWord_2737585 prefixEnd_2737585 937131291692517946531721 := by
  unfold tailWord_2737585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99847927787204562140166209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66565285191469708093444139 99847927787204562140166209)
  ·
    refine ⟨74885945840403421605124657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99847927787204562140166209 74885945840403421605124657)
    ·
      refine ⟨56164459380302566203843493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74885945840403421605124657 56164459380302566203843493)
      ·
        refine ⟨10530836133806731163220655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56164459380302566203843493 10530836133806731163220655)
        ·
          refine ⟨15796254200710096744830983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10530836133806731163220655 15796254200710096744830983)
          ·
            refine ⟨23694381301065145117246475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15796254200710096744830983 23694381301065145117246475)
            ·
              refine ⟨35541571951597717675869713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23694381301065145117246475 35541571951597717675869713)
              ·
                refine ⟨26656178963698288256902285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35541571951597717675869713 26656178963698288256902285)
                ·
                  refine ⟨9996067111386858096338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26656178963698288256902285 9996067111386858096338357)
                  ·
                    refine ⟨937131291692517946531721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996067111386858096338357 937131291692517946531721)
                    ·
                      rfl

theorem cell22_2737585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2737585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737585 prefixEnd_2737585 := by exact prefixLift 2737585
  have htrace : WordTrace (prefixWord ++ tailWord_2737585) baseStart_2737585 baseEnd_2737585 := by
    simpa [prefixWord, tailWord_2737585, baseEnd_2737585] using wordTrace_append hprefix tailTrace_2737585
  have hstable : (prefixWord ++ tailWord_2737585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737585).length < 2 ^ (prefixWord ++ tailWord_2737585).sum := by decide
  have hdescent : baseEnd_2737585 < baseStart_2737585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737600 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_2737600 : Nat := 118140960795 + 2737600 * 2 ^ 59
def prefixEnd_2737600 : Nat := 4983230072969 + 3 ^ 40 * 2737600 * 2
def baseEnd_2737600 : Nat := 937136426499062907406675

theorem tailTrace_2737600 : CollatzResearch.WordTrace tailWord_2737600 prefixEnd_2737600 937136426499062907406675 := by
  unfold tailWord_2737600
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924237441075109850981127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66565649921433479801308169 49924237441075109850981127)
  ·
    refine ⟨74886356161612664776471691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49924237441075109850981127 74886356161612664776471691)
    ·
      refine ⟨112329534242418997164707537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74886356161612664776471691 112329534242418997164707537)
      ·
        refine ⟨84247150681814247873530653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112329534242418997164707537 84247150681814247873530653)
        ·
          refine ⟨31592681505680342952573995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84247150681814247873530653 31592681505680342952573995)
          ·
            refine ⟨47389022258520514428860993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31592681505680342952573995 47389022258520514428860993)
            ·
              refine ⟨35541766693890385821645745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47389022258520514428860993 35541766693890385821645745)
              ·
                refine ⟨26656325020417789366234309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35541766693890385821645745 26656325020417789366234309)
                ·
                  refine ⟨4998060941328335506168933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26656325020417789366234309 4998060941328335506168933)
                  ·
                    refine ⟨937136426499062907406675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998060941328335506168933 937136426499062907406675)
                    ·
                      rfl

theorem cell22_2737600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_2737600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737600 prefixEnd_2737600 := by exact prefixLift 2737600
  have htrace : WordTrace (prefixWord ++ tailWord_2737600) baseStart_2737600 baseEnd_2737600 := by
    simpa [prefixWord, tailWord_2737600, baseEnd_2737600] using wordTrace_append hprefix tailTrace_2737600
  have hstable : (prefixWord ++ tailWord_2737600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737600).length < 2 ^ (prefixWord ++ tailWord_2737600).sum := by decide
  have hdescent : baseEnd_2737600 < baseStart_2737600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737647 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 3, 3]
def baseStart_2737647 : Nat := 118140960795 + 2737647 * 2 ^ 59
def prefixEnd_2737647 : Nat := 4983230072969 + 3 ^ 40 * 2737647 * 2
def baseEnd_2737647 : Nat := 937152515559570451481531

theorem tailTrace_2737647 : CollatzResearch.WordTrace tailWord_2737647 prefixEnd_2737647 937152515559570451481531 := by
  unfold tailWord_2737647
  simp only [CollatzResearch.WordTrace]
  refine ⟨99850189112979946728923195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66566792741986631152615463 99850189112979946728923195)
  ·
    refine ⟨149775283669469920093384793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99850189112979946728923195 149775283669469920093384793)
    ·
      refine ⟨112331462752102440070038595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149775283669469920093384793 112331462752102440070038595)
      ·
        refine ⟨168497194128153660105057893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112331462752102440070038595 168497194128153660105057893)
        ·
          refine ⟨31593223899028811269698355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168497194128153660105057893 31593223899028811269698355)
          ·
            refine ⟨47389835848543216904547533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31593223899028811269698355 47389835848543216904547533)
            ·
              refine ⟨17771188443203706339205325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47389835848543216904547533 17771188443203706339205325)
              ·
                refine ⟨6664195666201389877201997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17771188443203706339205325 6664195666201389877201997)
                ·
                  refine ⟨2499073374825521203950749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6664195666201389877201997 2499073374825521203950749)
                  ·
                    refine ⟨937152515559570451481531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499073374825521203950749 937152515559570451481531)
                    ·
                      rfl

theorem cell22_2737647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_2737647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737647 prefixEnd_2737647 := by exact prefixLift 2737647
  have htrace : WordTrace (prefixWord ++ tailWord_2737647) baseStart_2737647 baseEnd_2737647 := by
    simpa [prefixWord, tailWord_2737647, baseEnd_2737647] using wordTrace_append hprefix tailTrace_2737647
  have hstable : (prefixWord ++ tailWord_2737647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737647).length < 2 ^ (prefixWord ++ tailWord_2737647).sum := by decide
  have hdescent : baseEnd_2737647 < baseStart_2737647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737653 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2737653 : Nat := 118140960795 + 2737653 * 2 ^ 59
def prefixEnd_2737653 : Nat := 4983230072969 + 3 ^ 40 * 2737653 * 2
def baseEnd_2737653 : Nat := 937154569482188435831513

theorem tailTrace_2737653 : CollatzResearch.WordTrace tailWord_2737653 prefixEnd_2737653 937154569482188435831513 := by
  unfold tailWord_2737653
  simp only [CollatzResearch.WordTrace]
  refine ⟨99850407950958209753641613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66566938633972139835761075 99850407950958209753641613)
  ·
    refine ⟨37443902981609328657615605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99850407950958209753641613 37443902981609328657615605)
    ·
      refine ⟨3510365904525874561651463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37443902981609328657615605 3510365904525874561651463)
      ·
        refine ⟨5265548856788811842477195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510365904525874561651463 5265548856788811842477195)
        ·
          refine ⟨7898323285183217763715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265548856788811842477195 7898323285183217763715793)
          ·
            refine ⟨5923742463887413322786845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7898323285183217763715793 5923742463887413322786845)
            ·
              refine ⟨2221403423957779996045067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5923742463887413322786845 2221403423957779996045067)
              ·
                refine ⟨3332105135936669994067601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221403423957779996045067 3332105135936669994067601)
                ·
                  refine ⟨2499078851952502495550701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332105135936669994067601 2499078851952502495550701)
                  ·
                    refine ⟨937154569482188435831513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499078851952502495550701 937154569482188435831513)
                    ·
                      rfl

theorem cell22_2737653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2737653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737653 prefixEnd_2737653 := by exact prefixLift 2737653
  have htrace : WordTrace (prefixWord ++ tailWord_2737653) baseStart_2737653 baseEnd_2737653 := by
    simpa [prefixWord, tailWord_2737653, baseEnd_2737653] using wordTrace_append hprefix tailTrace_2737653
  have hstable : (prefixWord ++ tailWord_2737653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737653).length < 2 ^ (prefixWord ++ tailWord_2737653).sum := by decide
  have hdescent : baseEnd_2737653 < baseStart_2737653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737666 : List Nat := [3, 4, 1, 2, 1, 3, 2, 6]
def baseStart_2737666 : Nat := 118140960795 + 2737666 * 2 ^ 59
def prefixEnd_2737666 : Nat := 4983230072969 + 3 ^ 40 * 2737666 * 2
def baseEnd_2737666 : Nat := 104128779960873415028497

theorem tailTrace_2737666 : CollatzResearch.WordTrace tailWord_2737666 prefixEnd_2737666 104128779960873415028497 := by
  unfold tailWord_2737666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24962720524977778243466213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66567254733274075315909901 24962720524977778243466213)
  ·
    refine ⟨4680510098433333420649915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24962720524977778243466213 4680510098433333420649915)
    ·
      refine ⟨7020765147650000130974873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680510098433333420649915 7020765147650000130974873)
      ·
        refine ⟨5265573860737500098231155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7020765147650000130974873 5265573860737500098231155)
        ·
          refine ⟨7898360791106250147346733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265573860737500098231155 7898360791106250147346733)
          ·
            refine ⟨2961885296664843805255025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7898360791106250147346733 2961885296664843805255025)
            ·
              refine ⟨2221413972498632853941269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961885296664843805255025 2221413972498632853941269)
              ·
                refine ⟨104128779960873415028497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2221413972498632853941269 104128779960873415028497)
                ·
                  rfl

theorem cell22_2737666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_2737666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737666 prefixEnd_2737666 := by exact prefixLift 2737666
  have htrace : WordTrace (prefixWord ++ tailWord_2737666) baseStart_2737666 baseEnd_2737666 := by
    simpa [prefixWord, tailWord_2737666, baseEnd_2737666] using wordTrace_append hprefix tailTrace_2737666
  have hstable : (prefixWord ++ tailWord_2737666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737666).length < 2 ^ (prefixWord ++ tailWord_2737666).sum := by decide
  have hdescent : baseEnd_2737666 < baseStart_2737666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737724 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_2737724 : Nat := 118140960795 + 2737724 * 2 ^ 59
def prefixEnd_2737724 : Nat := 4983230072969 + 3 ^ 40 * 2737724 * 2
def baseEnd_2737724 : Nat := 937178874233167917306295

theorem tailTrace_2737724 : CollatzResearch.WordTrace tailWord_2737724 prefixEnd_2737724 937178874233167917306295 := by
  unfold tailWord_2737724
  simp only [CollatzResearch.WordTrace]
  refine ⟨49926498766850494439738113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66568665022467325919650817 49926498766850494439738113)
  ·
    refine ⟨37444874075137870829803585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49926498766850494439738113 37444874075137870829803585)
    ·
      refine ⟨28083655556353403122352689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37444874075137870829803585 28083655556353403122352689)
      ·
        refine ⟨21062741667265052341764517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28083655556353403122352689 21062741667265052341764517)
        ·
          refine ⟨3949264062612197314080847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21062741667265052341764517 3949264062612197314080847)
          ·
            refine ⟨5923896093918295971121271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949264062612197314080847 5923896093918295971121271)
            ·
              refine ⟨8885844140877443956681907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923896093918295971121271 8885844140877443956681907)
              ·
                refine ⟨13328766211316165935022861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885844140877443956681907 13328766211316165935022861)
                ·
                  refine ⟨4998287329243562225633573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13328766211316165935022861 4998287329243562225633573)
                  ·
                    refine ⟨937178874233167917306295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998287329243562225633573 937178874233167917306295)
                    ·
                      rfl

theorem cell22_2737724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_2737724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737724 prefixEnd_2737724 := by exact prefixLift 2737724
  have htrace : WordTrace (prefixWord ++ tailWord_2737724) baseStart_2737724 baseEnd_2737724 := by
    simpa [prefixWord, tailWord_2737724, baseEnd_2737724] using wordTrace_append hprefix tailTrace_2737724
  have hstable : (prefixWord ++ tailWord_2737724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737724).length < 2 ^ (prefixWord ++ tailWord_2737724).sum := by decide
  have hdescent : baseEnd_2737724 < baseStart_2737724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737737 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_2737737 : Nat := 118140960795 + 2737737 * 2 ^ 59
def prefixEnd_2737737 : Nat := 4983230072969 + 3 ^ 40 * 2737737 * 2
def baseEnd_2737737 : Nat := 937183324398840216731255

theorem tailTrace_2737737 : CollatzResearch.WordTrace tailWord_2737737 prefixEnd_2737737 937183324398840216731255 := by
  unfold tailWord_2737737
  simp only [CollatzResearch.WordTrace]
  refine ⟨99853471682653892099699465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66568981121769261399799643 99853471682653892099699465)
  ·
    refine ⟨74890103761990419074774599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99853471682653892099699465 74890103761990419074774599)
    ·
      refine ⟨112335155642985628612161899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74890103761990419074774599 112335155642985628612161899)
      ·
        refine ⟨168502733464478442918242849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112335155642985628612161899 168502733464478442918242849)
        ·
          refine ⟨126377050098358832188682137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168502733464478442918242849 126377050098358832188682137)
          ·
            refine ⟨94782787573769124141511603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126377050098358832188682137 94782787573769124141511603)
            ·
              refine ⟨142174181360653686212267405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94782787573769124141511603 142174181360653686212267405)
              ·
                refine ⟨53315318010245132329600277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142174181360653686212267405 53315318010245132329600277)
                ·
                  refine ⟨2499155531730240577950013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53315318010245132329600277 2499155531730240577950013)
                  ·
                    refine ⟨937183324398840216731255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499155531730240577950013 937183324398840216731255)
                    ·
                      rfl

theorem cell22_2737737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_2737737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737737 prefixEnd_2737737 := by exact prefixLift 2737737
  have htrace : WordTrace (prefixWord ++ tailWord_2737737) baseStart_2737737 baseEnd_2737737 := by
    simpa [prefixWord, tailWord_2737737, baseEnd_2737737] using wordTrace_append hprefix tailTrace_2737737
  have hstable : (prefixWord ++ tailWord_2737737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737737).length < 2 ^ (prefixWord ++ tailWord_2737737).sum := by decide
  have hdescent : baseEnd_2737737 < baseStart_2737737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737756 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_2737756 : Nat := 118140960795 + 2737756 * 2 ^ 59
def prefixEnd_2737756 : Nat := 4983230072969 + 3 ^ 40 * 2737756 * 2
def baseEnd_2737756 : Nat := 312396609495710166835399

theorem tailTrace_2737756 : CollatzResearch.WordTrace tailWord_2737756 prefixEnd_2737756 312396609495710166835399 := by
  unfold tailWord_2737756
  simp only [CollatzResearch.WordTrace]
  refine ⟨49927082334792529172320561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66569443113056705563094081 49927082334792529172320561)
  ·
    refine ⟨37445311751094396879240421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49927082334792529172320561 37445311751094396879240421)
    ·
      refine ⟨7020995953330199414857579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37445311751094396879240421 7020995953330199414857579)
      ·
        refine ⟨10531493929995299122286369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7020995953330199414857579 10531493929995299122286369)
        ·
          refine ⟨7898620447496474341714777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10531493929995299122286369 7898620447496474341714777)
          ·
            refine ⟨5923965335622355756286083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7898620447496474341714777 5923965335622355756286083)
            ·
              refine ⟨8885948003433533634429125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923965335622355756286083 8885948003433533634429125)
              ·
                refine ⟨1666115250643787556455461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8885948003433533634429125 1666115250643787556455461)
                ·
                  refine ⟨312396609495710166835399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666115250643787556455461 312396609495710166835399)
                  ·
                    rfl

theorem cell22_2737756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_2737756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737756 prefixEnd_2737756 := by exact prefixLift 2737756
  have htrace : WordTrace (prefixWord ++ tailWord_2737756) baseStart_2737756 baseEnd_2737756 := by
    simpa [prefixWord, tailWord_2737756, baseEnd_2737756] using wordTrace_append hprefix tailTrace_2737756
  have hstable : (prefixWord ++ tailWord_2737756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737756).length < 2 ^ (prefixWord ++ tailWord_2737756).sum := by decide
  have hdescent : baseEnd_2737756 < baseStart_2737756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737767 : List Nat := [1, 1, 5, 1, 1, 1, 5, 7]
def baseStart_2737767 : Nat := 118140960795 + 2737767 * 2 ^ 59
def prefixEnd_2737767 : Nat := 4983230072969 + 3 ^ 40 * 2737767 * 2
def baseEnd_2737767 : Nat := 104132621556881126497907

theorem tailTrace_2737767 : CollatzResearch.WordTrace tailWord_2737767 prefixEnd_2737767 104132621556881126497907 := by
  unfold tailWord_2737767
  simp only [CollatzResearch.WordTrace]
  refine ⟨99854565872545207223291555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66569710581696804815527703 99854565872545207223291555)
  ·
    refine ⟨149781848808817810834937333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99854565872545207223291555 149781848808817810834937333)
    ·
      refine ⟨14042048325826669765775375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149781848808817810834937333 14042048325826669765775375)
      ·
        refine ⟨21063072488740004648663063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14042048325826669765775375 21063072488740004648663063)
        ·
          refine ⟨31594608733110006972994595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21063072488740004648663063 31594608733110006972994595)
          ·
            refine ⟨47391913099665010459491893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31594608733110006972994595 47391913099665010459491893)
            ·
              refine ⟨4442991853093594730577365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47391913099665010459491893 4442991853093594730577365)
              ·
                refine ⟨104132621556881126497907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4442991853093594730577365 104132621556881126497907)
                ·
                  rfl

theorem cell22_2737767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 7].length) (baseStart_2737767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737767 prefixEnd_2737767 := by exact prefixLift 2737767
  have htrace : WordTrace (prefixWord ++ tailWord_2737767) baseStart_2737767 baseEnd_2737767 := by
    simpa [prefixWord, tailWord_2737767, baseEnd_2737767] using wordTrace_append hprefix tailTrace_2737767
  have hstable : (prefixWord ++ tailWord_2737767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737767).length < 2 ^ (prefixWord ++ tailWord_2737767).sum := by decide
  have hdescent : baseEnd_2737767 < baseStart_2737767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737816 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_2737816 : Nat := 118140960795 + 2737816 * 2 ^ 59
def prefixEnd_2737816 : Nat := 4983230072969 + 3 ^ 40 * 2737816 * 2
def baseEnd_2737816 : Nat := 937210367713310344006013

theorem tailTrace_2737816 : CollatzResearch.WordTrace tailWord_2737816 prefixEnd_2737816 937210367713310344006013 := by
  unfold tailWord_2737816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928176524683844295912651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66570902032911792394550201 49928176524683844295912651)
  ·
    refine ⟨74892264787025766443868977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49928176524683844295912651 74892264787025766443868977)
    ·
      refine ⟨56169198590269324832901733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74892264787025766443868977 56169198590269324832901733)
      ·
        refine ⟨10531724735675498406169075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56169198590269324832901733 10531724735675498406169075)
        ·
          refine ⟨15797587103513247609253613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531724735675498406169075 15797587103513247609253613)
          ·
            refine ⟨5924095163817467853470105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15797587103513247609253613 5924095163817467853470105)
            ·
              refine ⟨4443071372863100890102579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5924095163817467853470105 4443071372863100890102579)
              ·
                refine ⟨6664607059294651335153869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443071372863100890102579 6664607059294651335153869)
                ·
                  refine ⟨2499227647235494250682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6664607059294651335153869 2499227647235494250682701)
                  ·
                    refine ⟨937210367713310344006013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499227647235494250682701 937210367713310344006013)
                    ·
                      rfl

theorem cell22_2737816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_2737816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737816 prefixEnd_2737816 := by exact prefixLift 2737816
  have htrace : WordTrace (prefixWord ++ tailWord_2737816) baseStart_2737816 baseEnd_2737816 := by
    simpa [prefixWord, tailWord_2737816, baseEnd_2737816] using wordTrace_append hprefix tailTrace_2737816
  have hstable : (prefixWord ++ tailWord_2737816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737816).length < 2 ^ (prefixWord ++ tailWord_2737816).sum := by decide
  have hdescent : baseEnd_2737816 < baseStart_2737816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737827 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_2737827 : Nat := 118140960795 + 2737827 * 2 ^ 59
def prefixEnd_2737827 : Nat := 4983230072969 + 3 ^ 40 * 2737827 * 2
def baseEnd_2737827 : Nat := 937214133238109981980979

theorem tailTrace_2737827 : CollatzResearch.WordTrace tailWord_2737827 prefixEnd_2737827 937214133238109981980979 := by
  unfold tailWord_2737827
  simp only [CollatzResearch.WordTrace]
  refine ⟨99856754252327837470475735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66571169501551891646983823 99856754252327837470475735)
  ·
    refine ⟨149785131378491756205713603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99856754252327837470475735 149785131378491756205713603)
    ·
      refine ⟨224677697067737634308570405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149785131378491756205713603 224677697067737634308570405)
      ·
        refine ⟨42127068200200806432856951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224677697067737634308570405 42127068200200806432856951)
        ·
          refine ⟨63190602300301209649285427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42127068200200806432856951 63190602300301209649285427)
          ·
            refine ⟨94785903450451814473928141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63190602300301209649285427 94785903450451814473928141)
            ·
              refine ⟨35544713793919430427723053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94785903450451814473928141 35544713793919430427723053)
              ·
                refine ⟨13329267672719786410396145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35544713793919430427723053 13329267672719786410396145)
                ·
                  refine ⟨9996950754539839807797109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13329267672719786410396145 9996950754539839807797109)
                  ·
                    refine ⟨937214133238109981980979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996950754539839807797109 937214133238109981980979)
                    ·
                      rfl

theorem cell22_2737827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_2737827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737827 prefixEnd_2737827 := by exact prefixLift 2737827
  have htrace : WordTrace (prefixWord ++ tailWord_2737827) baseStart_2737827 baseEnd_2737827 := by
    simpa [prefixWord, tailWord_2737827, baseEnd_2737827] using wordTrace_append hprefix tailTrace_2737827
  have hstable : (prefixWord ++ tailWord_2737827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737827).length < 2 ^ (prefixWord ++ tailWord_2737827).sum := by decide
  have hdescent : baseEnd_2737827 < baseStart_2737827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737846 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2737846 : Nat := 118140960795 + 2737846 * 2 ^ 59
def prefixEnd_2737846 : Nat := 4983230072969 + 3 ^ 40 * 2737846 * 2
def baseEnd_2737846 : Nat := 312406879108800088585307

theorem tailTrace_2737846 : CollatzResearch.WordTrace tailWord_2737846 prefixEnd_2737846 312406879108800088585307 := by
  unfold tailWord_2737846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241090452453687732213587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66571631492839335810278261 6241090452453687732213587)
  ·
    refine ⟨9361635678680531598320381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6241090452453687732213587 9361635678680531598320381)
    ·
      refine ⟨3510613379505199349370143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9361635678680531598320381 3510613379505199349370143)
      ·
        refine ⟨5265920069257799024055215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510613379505199349370143 5265920069257799024055215)
        ·
          refine ⟨7898880103886698536082823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265920069257799024055215 7898880103886698536082823)
          ·
            refine ⟨11848320155830047804124235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898880103886698536082823 11848320155830047804124235)
            ·
              refine ⟨17772480233745071706186353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848320155830047804124235 17772480233745071706186353)
              ·
                refine ⟨13329360175308803779639765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17772480233745071706186353 13329360175308803779639765)
                ·
                  refine ⟨312406879108800088585307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13329360175308803779639765 312406879108800088585307)
                  ·
                    rfl

theorem cell22_2737846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2737846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737846 prefixEnd_2737846 := by exact prefixLift 2737846
  have htrace : WordTrace (prefixWord ++ tailWord_2737846) baseStart_2737846 baseEnd_2737846 := by
    simpa [prefixWord, tailWord_2737846, baseEnd_2737846] using wordTrace_append hprefix tailTrace_2737846
  have hstable : (prefixWord ++ tailWord_2737846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737846).length < 2 ^ (prefixWord ++ tailWord_2737846).sum := by decide
  have hdescent : baseEnd_2737846 < baseStart_2737846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737872 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_2737872 : Nat := 118140960795 + 2737872 * 2 ^ 59
def prefixEnd_2737872 : Nat := 4983230072969 + 3 ^ 40 * 2737872 * 2
def baseEnd_2737872 : Nat := 937229537657744864605841

theorem tailTrace_2737872 : CollatzResearch.WordTrace tailWord_2737872 prefixEnd_2737872 937229537657744864605841 := by
  unfold tailWord_2737872
  simp only [CollatzResearch.WordTrace]
  refine ⟨49929197768582405077931935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66572263691443206770575913 49929197768582405077931935)
  ·
    refine ⟨74893796652873607616897903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49929197768582405077931935 74893796652873607616897903)
    ·
      refine ⟨112340694979310411425346855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74893796652873607616897903 112340694979310411425346855)
      ·
        refine ⟨168511042468965617138020283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112340694979310411425346855 168511042468965617138020283)
        ·
          refine ⟨252766563703448425707030425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168511042468965617138020283 252766563703448425707030425)
          ·
            refine ⟨189574922777586319280272819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252766563703448425707030425 189574922777586319280272819)
            ·
              refine ⟨284362384166379478920409229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189574922777586319280272819 284362384166379478920409229)
              ·
                refine ⟨106635894062392304595153461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284362384166379478920409229 106635894062392304595153461)
                ·
                  refine ⟨9997115068349278555795637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106635894062392304595153461 9997115068349278555795637)
                  ·
                    refine ⟨937229537657744864605841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9997115068349278555795637 937229537657744864605841)
                    ·
                      rfl

theorem cell22_2737872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_2737872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737872 prefixEnd_2737872 := by exact prefixLift 2737872
  have htrace : WordTrace (prefixWord ++ tailWord_2737872) baseStart_2737872 baseEnd_2737872 := by
    simpa [prefixWord, tailWord_2737872, baseEnd_2737872] using wordTrace_append hprefix tailTrace_2737872
  have hstable : (prefixWord ++ tailWord_2737872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737872).length < 2 ^ (prefixWord ++ tailWord_2737872).sum := by decide
  have hdescent : baseEnd_2737872 < baseStart_2737872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737951 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 3, 3]
def baseStart_2737951 : Nat := 118140960795 + 2737951 * 2 ^ 59
def prefixEnd_2737951 : Nat := 4983230072969 + 3 ^ 40 * 2737951 * 2
def baseEnd_2737951 : Nat := 937256580972214991880599

theorem tailTrace_2737951 : CollatzResearch.WordTrace tailWord_2737951 prefixEnd_2737951 937256580972214991880599 := by
  unfold tailWord_2737951
  simp only [CollatzResearch.WordTrace]
  refine ⟨99861276903878606647989707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66574184602585737765326471 99861276903878606647989707)
  ·
    refine ⟨149791915355817909971984561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99861276903878606647989707 149791915355817909971984561)
    ·
      refine ⟨112343936516863432478988421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149791915355817909971984561 112343936516863432478988421)
      ·
        refine ⟨21064488096911893589810329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112343936516863432478988421 21064488096911893589810329)
        ·
          refine ⟨15798366072683920192357747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21064488096911893589810329 15798366072683920192357747)
          ·
            refine ⟨23697549109025880288536621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15798366072683920192357747 23697549109025880288536621)
            ·
              refine ⟨8886580915884705108201233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23697549109025880288536621 8886580915884705108201233)
              ·
                refine ⟨6664935686913528831150925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8886580915884705108201233 6664935686913528831150925)
                ·
                  refine ⟨2499350882592573311681597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6664935686913528831150925 2499350882592573311681597)
                  ·
                    refine ⟨937256580972214991880599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499350882592573311681597 937256580972214991880599)
                    ·
                      rfl

theorem cell22_2737951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_2737951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737951 prefixEnd_2737951 := by exact prefixLift 2737951
  have htrace : WordTrace (prefixWord ++ tailWord_2737951) baseStart_2737951 baseEnd_2737951 := by
    simpa [prefixWord, tailWord_2737951, baseEnd_2737951] using wordTrace_append hprefix tailTrace_2737951
  have hstable : (prefixWord ++ tailWord_2737951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737951).length < 2 ^ (prefixWord ++ tailWord_2737951).sum := by decide
  have hdescent : baseEnd_2737951 < baseStart_2737951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737981 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 7]
def baseStart_2737981 : Nat := 118140960795 + 2737981 * 2 ^ 59
def prefixEnd_2737981 : Nat := 4983230072969 + 3 ^ 40 * 2737981 * 2
def baseEnd_2737981 : Nat := 312422283528434971210169

theorem tailTrace_2737981 : CollatzResearch.WordTrace tailWord_2737981 prefixEnd_2737981 312422283528434971210169 := by
  unfold tailWord_2737981
  simp only [CollatzResearch.WordTrace]
  refine ⟨99862371093769921771581797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66574914062513281181054531 99862371093769921771581797)
  ·
    refine ⟨18724194580081860332171587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99862371093769921771581797 18724194580081860332171587)
    ·
      refine ⟨28086291870122790498257381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18724194580081860332171587 28086291870122790498257381)
      ·
        refine ⟨5266179725648023218423259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28086291870122790498257381 5266179725648023218423259)
        ·
          refine ⟨7899269588472034827634889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266179725648023218423259 7899269588472034827634889)
          ·
            refine ⟨5924452191354026120726167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7899269588472034827634889 5924452191354026120726167)
            ·
              refine ⟨8886678287031039181089251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924452191354026120726167 8886678287031039181089251)
              ·
                refine ⟨13330017430546558771633877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8886678287031039181089251 13330017430546558771633877)
                ·
                  refine ⟨312422283528434971210169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13330017430546558771633877 312422283528434971210169)
                  ·
                    rfl

theorem cell22_2737981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_2737981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2737981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2737981 prefixEnd_2737981 := by exact prefixLift 2737981
  have htrace : WordTrace (prefixWord ++ tailWord_2737981) baseStart_2737981 baseEnd_2737981 := by
    simpa [prefixWord, tailWord_2737981, baseEnd_2737981] using wordTrace_append hprefix tailTrace_2737981
  have hstable : (prefixWord ++ tailWord_2737981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737981).length < 2 ^ (prefixWord ++ tailWord_2737981).sum := by decide
  have hdescent : baseEnd_2737981 < baseStart_2737981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738009 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 6]
def baseStart_2738009 : Nat := 118140960795 + 2738009 * 2 ^ 59
def prefixEnd_2738009 : Nat := 4983230072969 + 3 ^ 40 * 2738009 * 2
def baseEnd_2738009 : Nat := 312425478519174057976807

theorem tailTrace_2738009 : CollatzResearch.WordTrace tailWord_2738009 prefixEnd_2738009 312425478519174057976807 := by
  unfold tailWord_2738009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99863392337668482553601081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66575594891778988369067387 99863392337668482553601081)
  ·
    refine ⟨74897544253251361915200811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99863392337668482553601081 74897544253251361915200811)
    ·
      refine ⟨112346316379877042872801217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74897544253251361915200811 112346316379877042872801217)
      ·
        refine ⟨84259737284907782154600913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112346316379877042872801217 84259737284907782154600913)
        ·
          refine ⟨63194802963680836615950685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84259737284907782154600913 63194802963680836615950685)
          ·
            refine ⟨23698051111380313730981507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63194802963680836615950685 23698051111380313730981507)
            ·
              refine ⟨35547076667070470596472261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23698051111380313730981507 35547076667070470596472261)
              ·
                refine ⟨6665076875075713236838549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35547076667070470596472261 6665076875075713236838549)
                ·
                  refine ⟨312425478519174057976807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6665076875075713236838549 312425478519174057976807)
                  ·
                    rfl

theorem cell22_2738009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_2738009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738009 prefixEnd_2738009 := by exact prefixLift 2738009
  have htrace : WordTrace (prefixWord ++ tailWord_2738009) baseStart_2738009 baseEnd_2738009 := by
    simpa [prefixWord, tailWord_2738009, baseEnd_2738009] using wordTrace_append hprefix tailTrace_2738009
  have hstable : (prefixWord ++ tailWord_2738009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738009).length < 2 ^ (prefixWord ++ tailWord_2738009).sum := by decide
  have hdescent : baseEnd_2738009 < baseStart_2738009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738041 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_2738041 : Nat := 118140960795 + 2738041 * 2 ^ 59
def prefixEnd_2738041 : Nat := 4983230072969 + 3 ^ 40 * 2738041 * 2
def baseEnd_2738041 : Nat := 937287389811484757130323

theorem tailTrace_2738041 : CollatzResearch.WordTrace tailWord_2738041 prefixEnd_2738041 937287389811484757130323 := by
  unfold tailWord_2738041
  simp only [CollatzResearch.WordTrace]
  refine ⟨99864559473552552018765977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66576372982368368012510651 99864559473552552018765977)
  ·
    refine ⟨74898419605164414014074483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99864559473552552018765977 74898419605164414014074483)
    ·
      refine ⟨112347629407746621021111725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74898419605164414014074483 112347629407746621021111725)
      ·
        refine ⟨42130361027904982882916897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112347629407746621021111725 42130361027904982882916897)
        ·
          refine ⟨31597770770928737162187673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42130361027904982882916897 31597770770928737162187673)
          ·
            refine ⟨23698328078196552871640755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31597770770928737162187673 23698328078196552871640755)
            ·
              refine ⟨35547492117294829307461133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23698328078196552871640755 35547492117294829307461133)
              ·
                refine ⟨13330309543985560990297925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35547492117294829307461133 13330309543985560990297925)
                ·
                  refine ⟨2499433039497292685680861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13330309543985560990297925 2499433039497292685680861)
                  ·
                    refine ⟨937287389811484757130323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499433039497292685680861 937287389811484757130323)
                    ·
                      rfl

theorem cell22_2738041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_2738041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738041 prefixEnd_2738041 := by exact prefixLift 2738041
  have htrace : WordTrace (prefixWord ++ tailWord_2738041) baseStart_2738041 baseEnd_2738041 := by
    simpa [prefixWord, tailWord_2738041, baseEnd_2738041] using wordTrace_append hprefix tailTrace_2738041
  have hstable : (prefixWord ++ tailWord_2738041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738041).length < 2 ^ (prefixWord ++ tailWord_2738041).sum := by decide
  have hdescent : baseEnd_2738041 < baseStart_2738041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738062 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2738062 : Nat := 118140960795 + 2738062 * 2 ^ 59
def prefixEnd_2738062 : Nat := 4983230072969 + 3 ^ 40 * 2738062 * 2
def baseEnd_2738062 : Nat := 937294578540647702355259

theorem tailTrace_2738062 : CollatzResearch.WordTrace tailWord_2738062 prefixEnd_2738062 937294578540647702355259 := by
  unfold tailWord_2738062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483165675809559075660055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66576883604317648403520293 12483165675809559075660055)
  ·
    refine ⟨18724748513714338613490083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483165675809559075660055 18724748513714338613490083)
    ·
      refine ⟨28087122770571507920235125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18724748513714338613490083 28087122770571507920235125)
      ·
        refine ⟨2633167759741078867522043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28087122770571507920235125 2633167759741078867522043)
        ·
          refine ⟨3949751639611618301283065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633167759741078867522043 3949751639611618301283065)
          ·
            refine ⟨2962313729708713725962299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3949751639611618301283065 2962313729708713725962299)
            ·
              refine ⟨4443470594563070588943449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962313729708713725962299 4443470594563070588943449)
              ·
                refine ⟨3332602945922302941707587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4443470594563070588943449 3332602945922302941707587)
                ·
                  refine ⟨4998904418883454412561381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332602945922302941707587 4998904418883454412561381)
                  ·
                    refine ⟨937294578540647702355259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998904418883454412561381 937294578540647702355259)
                    ·
                      rfl

theorem cell22_2738062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2738062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738062 prefixEnd_2738062 := by exact prefixLift 2738062
  have htrace : WordTrace (prefixWord ++ tailWord_2738062) baseStart_2738062 baseEnd_2738062 := by
    simpa [prefixWord, tailWord_2738062, baseEnd_2738062] using wordTrace_append hprefix tailTrace_2738062
  have hstable : (prefixWord ++ tailWord_2738062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738062).length < 2 ^ (prefixWord ++ tailWord_2738062).sum := by decide
  have hdescent : baseEnd_2738062 < baseStart_2738062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738088 : List Nat := [2, 1, 6, 2, 1, 10]
def baseStart_2738088 : Nat := 118140960795 + 2738088 * 2 ^ 59
def prefixEnd_2738088 : Nat := 4983230072969 + 3 ^ 40 * 2738088 * 2
def baseEnd_2738088 : Nat := 11571647887308546928459

theorem tailTrace_2738088 : CollatzResearch.WordTrace tailWord_2738088 prefixEnd_2738088 11571647887308546928459 := by
  unfold tailWord_2738088
  simp only [CollatzResearch.WordTrace]
  refine ⟨49933136852191139522863459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66577515802921519363817945 49933136852191139522863459)
  ·
    refine ⟨74899705278286709284295189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49933136852191139522863459 74899705278286709284295189)
    ·
      refine ⟨3510923684919689497701337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74899705278286709284295189 3510923684919689497701337)
      ·
        refine ⟨2633192763689767123276003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510923684919689497701337 2633192763689767123276003)
        ·
          refine ⟨3949789145534650684914005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633192763689767123276003 3949789145534650684914005)
          ·
            refine ⟨11571647887308546928459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3949789145534650684914005 11571647887308546928459)
            ·
              rfl

theorem cell22_2738088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 10].length) (baseStart_2738088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738088 prefixEnd_2738088 := by exact prefixLift 2738088
  have htrace : WordTrace (prefixWord ++ tailWord_2738088) baseStart_2738088 baseEnd_2738088 := by
    simpa [prefixWord, tailWord_2738088, baseEnd_2738088] using wordTrace_append hprefix tailTrace_2738088
  have hstable : (prefixWord ++ tailWord_2738088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738088).length < 2 ^ (prefixWord ++ tailWord_2738088).sum := by decide
  have hdescent : baseEnd_2738088 < baseStart_2738088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738094 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_2738094 : Nat := 118140960795 + 2738094 * 2 ^ 59
def prefixEnd_2738094 : Nat := 4983230072969 + 3 ^ 40 * 2738094 * 2
def baseEnd_2738094 : Nat := 312435177598203428518387

theorem tailTrace_2738094 : CollatzResearch.WordTrace tailWord_2738094 prefixEnd_2738094 312435177598203428518387 := by
  unfold tailWord_2738094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483311567795067758805667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66577661694907028046963557 12483311567795067758805667)
  ·
    refine ⟨18724967351692601638208501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483311567795067758805667 18724967351692601638208501)
    ·
      refine ⟨1755465689221181403582047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18724967351692601638208501 1755465689221181403582047)
      ·
        refine ⟨2633198533831772105373071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755465689221181403582047 2633198533831772105373071)
        ·
          refine ⟨3949797800747658158059607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633198533831772105373071 3949797800747658158059607)
          ·
            refine ⟨5924696701121487237089411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949797800747658158059607 5924696701121487237089411)
            ·
              refine ⟨8887045051682230855634117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924696701121487237089411 8887045051682230855634117)
              ·
                refine ⟨1666320947190418285431397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8887045051682230855634117 1666320947190418285431397)
                ·
                  refine ⟨312435177598203428518387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666320947190418285431397 312435177598203428518387)
                  ·
                    rfl

theorem cell22_2738094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_2738094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738094 prefixEnd_2738094 := by exact prefixLift 2738094
  have htrace : WordTrace (prefixWord ++ tailWord_2738094) baseStart_2738094 baseEnd_2738094 := by
    simpa [prefixWord, tailWord_2738094, baseEnd_2738094] using wordTrace_append hprefix tailTrace_2738094
  have hstable : (prefixWord ++ tailWord_2738094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738094).length < 2 ^ (prefixWord ++ tailWord_2738094).sum := by decide
  have hdescent : baseEnd_2738094 < baseStart_2738094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738101 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2738101 : Nat := 118140960795 + 2738101 * 2 ^ 59
def prefixEnd_2738101 : Nat := 4983230072969 + 3 ^ 40 * 2738101 * 2
def baseEnd_2738101 : Nat := 937307929037664600630139

theorem tailTrace_2738101 : CollatzResearch.WordTrace tailWord_2738101 prefixEnd_2738101 937307929037664600630139 := by
  unfold tailWord_2738101
  simp only [CollatzResearch.WordTrace]
  refine ⟨99866747853335182265950157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66577831902223454843966771 99866747853335182265950157)
  ·
    refine ⟨37450030445000693349731309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99866747853335182265950157 37450030445000693349731309)
    ·
      refine ⟨14043761416875260006149241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37450030445000693349731309 14043761416875260006149241)
      ·
        refine ⟨10532821062656445004611931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14043761416875260006149241 10532821062656445004611931)
        ·
          refine ⟨15799231593984667506917897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10532821062656445004611931 15799231593984667506917897)
          ·
            refine ⟨11849423695488500630188423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15799231593984667506917897 11849423695488500630188423)
            ·
              refine ⟨17774135543232750945282635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11849423695488500630188423 17774135543232750945282635)
              ·
                refine ⟨26661203314849126417923953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17774135543232750945282635 26661203314849126417923953)
                ·
                  refine ⟨19995902486136844813442965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26661203314849126417923953 19995902486136844813442965)
                  ·
                    refine ⟨937307929037664600630139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19995902486136844813442965 937307929037664600630139)
                    ·
                      rfl

theorem cell22_2738101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2738101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738101 prefixEnd_2738101 := by exact prefixLift 2738101
  have htrace : WordTrace (prefixWord ++ tailWord_2738101) baseStart_2738101 baseEnd_2738101 := by
    simpa [prefixWord, tailWord_2738101, baseEnd_2738101] using wordTrace_append hprefix tailTrace_2738101
  have hstable : (prefixWord ++ tailWord_2738101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738101).length < 2 ^ (prefixWord ++ tailWord_2738101).sum := by decide
  have hdescent : baseEnd_2738101 < baseStart_2738101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738137 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_2738137 : Nat := 118140960795 + 2738137 * 2 ^ 59
def prefixEnd_2738137 : Nat := 4983230072969 + 3 ^ 40 * 2738137 * 2
def baseEnd_2738137 : Nat := 937320252573372506730029

theorem tailTrace_2738137 : CollatzResearch.WordTrace tailWord_2738137 prefixEnd_2738137 937320252573372506730029 := by
  unfold tailWord_2738137
  simp only [CollatzResearch.WordTrace]
  refine ⟨99868060881204760414260665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66578707254136506942840443 99868060881204760414260665)
  ·
    refine ⟨74901045660903570310695499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99868060881204760414260665 74901045660903570310695499)
    ·
      refine ⟨112351568491355355466043249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74901045660903570310695499 112351568491355355466043249)
      ·
        refine ⟨84263676368516516599532437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112351568491355355466043249 84263676368516516599532437)
        ·
          refine ⟨3949859829774211715603083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84263676368516516599532437 3949859829774211715603083)
          ·
            refine ⟨5924789744661317573404625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949859829774211715603083 5924789744661317573404625)
            ·
              refine ⟨4443592308495988180053469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5924789744661317573404625 4443592308495988180053469)
              ·
                refine ⟨1666347115685995567520051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4443592308495988180053469 1666347115685995567520051)
                ·
                  refine ⟨2499520673528993351280077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666347115685995567520051 2499520673528993351280077)
                  ·
                    refine ⟨937320252573372506730029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499520673528993351280077 937320252573372506730029)
                    ·
                      rfl

theorem cell22_2738137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_2738137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738137 prefixEnd_2738137 := by exact prefixLift 2738137
  have htrace : WordTrace (prefixWord ++ tailWord_2738137) baseStart_2738137 baseEnd_2738137 := by
    simpa [prefixWord, tailWord_2738137, baseEnd_2738137] using wordTrace_append hprefix tailTrace_2738137
  have hstable : (prefixWord ++ tailWord_2738137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738137).length < 2 ^ (prefixWord ++ tailWord_2738137).sum := by decide
  have hdescent : baseEnd_2738137 < baseStart_2738137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738176 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_2738176 : Nat := 118140960795 + 2738176 * 2 ^ 59
def prefixEnd_2738176 : Nat := 4983230072969 + 3 ^ 40 * 2738176 * 2
def baseEnd_2738176 : Nat := 937333603070389405004909

theorem tailTrace_2738176 : CollatzResearch.WordTrace tailWord_2738176 prefixEnd_2738176 937333603070389405004909 := by
  unfold tailWord_2738176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49934741664031735037465191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66579655552042313383286921 49934741664031735037465191)
  ·
    refine ⟨74902112496047602556197787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49934741664031735037465191 74902112496047602556197787)
    ·
      refine ⟨112353168744071403834296681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74902112496047602556197787 112353168744071403834296681)
      ·
        refine ⟨84264876558053552875722511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112353168744071403834296681 84264876558053552875722511)
        ·
          refine ⟨126397314837080329313583767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84264876558053552875722511 126397314837080329313583767)
          ·
            refine ⟨189595972255620493970375651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126397314837080329313583767 189595972255620493970375651)
            ·
              refine ⟨284393958383430740955563477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189595972255620493970375651 284393958383430740955563477)
              ·
                refine ⟨6665483399611657991146019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284393958383430740955563477 6665483399611657991146019)
                ·
                  refine ⟨9998225099417486986719029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6665483399611657991146019 9998225099417486986719029)
                  ·
                    refine ⟨937333603070389405004909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9998225099417486986719029 937333603070389405004909)
                    ·
                      rfl

theorem cell22_2738176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_2738176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738176 prefixEnd_2738176 := by exact prefixLift 2738176
  have htrace : WordTrace (prefixWord ++ tailWord_2738176) baseStart_2738176 baseEnd_2738176 := by
    simpa [prefixWord, tailWord_2738176, baseEnd_2738176] using wordTrace_append hprefix tailTrace_2738176
  have hstable : (prefixWord ++ tailWord_2738176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738176).length < 2 ^ (prefixWord ++ tailWord_2738176).sum := by decide
  have hdescent : baseEnd_2738176 < baseStart_2738176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738210 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2738210 : Nat := 118140960795 + 2738210 * 2 ^ 59
def prefixEnd_2738210 : Nat := 4983230072969 + 3 ^ 40 * 2738210 * 2
def baseEnd_2738210 : Nat := 937345241965224649654805

theorem tailTrace_2738210 : CollatzResearch.WordTrace tailWord_2738210 prefixEnd_2738210 937345241965224649654805 := by
  unfold tailWord_2738210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24967680852485073470417021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66580482273293529254445389 24967680852485073470417021)
  ·
    refine ⟨9362880319681902551406383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24967680852485073470417021 9362880319681902551406383)
    ·
      refine ⟨14044320479522853827109575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362880319681902551406383 14044320479522853827109575)
      ·
        refine ⟨21066480719284280740664363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044320479522853827109575 21066480719284280740664363)
        ·
          refine ⟨31599721078926421110996545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21066480719284280740664363 31599721078926421110996545)
          ·
            refine ⟨23699790809194815833247409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31599721078926421110996545 23699790809194815833247409)
            ·
              refine ⟨17774843106896111874935557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23699790809194815833247409 17774843106896111874935557)
              ·
                refine ⟨3332783082543020976550417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17774843106896111874935557 3332783082543020976550417)
                ·
                  refine ⟨2499587311907265732412813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332783082543020976550417 2499587311907265732412813)
                  ·
                    refine ⟨937345241965224649654805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499587311907265732412813 937345241965224649654805)
                    ·
                      rfl

theorem cell22_2738210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2738210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738210 prefixEnd_2738210 := by exact prefixLift 2738210
  have htrace : WordTrace (prefixWord ++ tailWord_2738210) baseStart_2738210 baseEnd_2738210 := by
    simpa [prefixWord, tailWord_2738210, baseEnd_2738210] using wordTrace_append hprefix tailTrace_2738210
  have hstable : (prefixWord ++ tailWord_2738210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738210).length < 2 ^ (prefixWord ++ tailWord_2738210).sum := by decide
  have hdescent : baseEnd_2738210 < baseStart_2738210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738212 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2738212 : Nat := 118140960795 + 2738212 * 2 ^ 59
def prefixEnd_2738212 : Nat := 4983230072969 + 3 ^ 40 * 2738212 * 2
def baseEnd_2738212 : Nat := 312448642202032437034933

theorem tailTrace_2738212 : CollatzResearch.WordTrace tailWord_2738212 prefixEnd_2738212 312448642202032437034933 := by
  unfold tailWord_2738212
  simp only [CollatzResearch.WordTrace]
  refine ⟨49935398177966524111620445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66580530903955365482160593 49935398177966524111620445)
  ·
    refine ⟨18725774316737446541857667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49935398177966524111620445 18725774316737446541857667)
    ·
      refine ⟨28088661475106169812786501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18725774316737446541857667 28088661475106169812786501)
      ·
        refine ⟨5266624026582406839897469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28088661475106169812786501 5266624026582406839897469)
        ·
          refine ⟨1974984009968402564961551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5266624026582406839897469 1974984009968402564961551)
          ·
            refine ⟨2962476014952603847442327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974984009968402564961551 2962476014952603847442327)
            ·
              refine ⟨4443714022428905771163491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962476014952603847442327 4443714022428905771163491)
              ·
                refine ⟨6665571033643358656745237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443714022428905771163491 6665571033643358656745237)
                ·
                  refine ⟨312448642202032437034933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6665571033643358656745237 312448642202032437034933)
                  ·
                    rfl

theorem cell22_2738212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2738212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738212 prefixEnd_2738212 := by exact prefixLift 2738212
  have htrace : WordTrace (prefixWord ++ tailWord_2738212) baseStart_2738212 baseEnd_2738212 := by
    simpa [prefixWord, tailWord_2738212, baseEnd_2738212] using wordTrace_append hprefix tailTrace_2738212
  have hstable : (prefixWord ++ tailWord_2738212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738212).length < 2 ^ (prefixWord ++ tailWord_2738212).sum := by decide
  have hdescent : baseEnd_2738212 < baseStart_2738212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738272 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_2738272 : Nat := 118140960795 + 2738272 * 2 ^ 59
def prefixEnd_2738272 : Nat := 4983230072969 + 3 ^ 40 * 2738272 * 2
def baseEnd_2738272 : Nat := 937366465832277154604615

theorem tailTrace_2738272 : CollatzResearch.WordTrace tailWord_2738272 prefixEnd_2738272 937366465832277154604615 := by
  unfold tailWord_2738272
  simp only [CollatzResearch.WordTrace]
  refine ⟨49936492367857839235212535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66581989823810452313616713 49936492367857839235212535)
  ·
    refine ⟨74904738551786758852818803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49936492367857839235212535 74904738551786758852818803)
    ·
      refine ⟨112357107827680138279228205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74904738551786758852818803 112357107827680138279228205)
      ·
        refine ⟨42133915435380051854710577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112357107827680138279228205 42133915435380051854710577)
        ·
          refine ⟨31600436576535038891032933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42133915435380051854710577 31600436576535038891032933)
          ·
            refine ⟨5925081858100319792068675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31600436576535038891032933 5925081858100319792068675)
            ·
              refine ⟨8887622787150479688103013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925081858100319792068675 8887622787150479688103013)
              ·
                refine ⟨1666429272590714941519315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8887622787150479688103013 1666429272590714941519315)
                ·
                  refine ⟨2499643908886072412278973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666429272590714941519315 2499643908886072412278973)
                  ·
                    refine ⟨937366465832277154604615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499643908886072412278973 937366465832277154604615)
                    ·
                      rfl

theorem cell22_2738272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_2738272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738272 prefixEnd_2738272 := by exact prefixLift 2738272
  have htrace : WordTrace (prefixWord ++ tailWord_2738272) baseStart_2738272 baseEnd_2738272 := by
    simpa [prefixWord, tailWord_2738272, baseEnd_2738272] using wordTrace_append hprefix tailTrace_2738272
  have hstable : (prefixWord ++ tailWord_2738272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738272).length < 2 ^ (prefixWord ++ tailWord_2738272).sum := by decide
  have hdescent : baseEnd_2738272 < baseStart_2738272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738364 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_2738364 : Nat := 118140960795 + 2738364 * 2 ^ 59
def prefixEnd_2738364 : Nat := 4983230072969 + 3 ^ 40 * 2738364 * 2
def baseEnd_2738364 : Nat := 312465986437473193768111

theorem tailTrace_2738364 : CollatzResearch.WordTrace tailWord_2738364 prefixEnd_2738364 312465986437473193768111 := by
  unfold tailWord_2738364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938170125691189091387073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66584226834254918788516097 49938170125691189091387073)
  ·
    refine ⟨37453627594268391818540305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49938170125691189091387073 37453627594268391818540305)
    ·
      refine ⟨28090220695701293863905229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37453627594268391818540305 28090220695701293863905229)
      ·
        refine ⟨10533832760887985198964461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28090220695701293863905229 10533832760887985198964461)
        ·
          refine ⟨3950187285332994449611673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10533832760887985198964461 3950187285332994449611673)
          ·
            refine ⟨2962640463999745837208755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950187285332994449611673 2962640463999745837208755)
            ·
              refine ⟨4443960695999618755813133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962640463999745837208755 4443960695999618755813133)
              ·
                refine ⟨1666485260999857033429925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4443960695999618755813133 1666485260999857033429925)
                ·
                  refine ⟨312465986437473193768111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666485260999857033429925 312465986437473193768111)
                  ·
                    rfl

theorem cell22_2738364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_2738364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738364 prefixEnd_2738364 := by exact prefixLift 2738364
  have htrace : WordTrace (prefixWord ++ tailWord_2738364) baseStart_2738364 baseEnd_2738364 := by
    simpa [prefixWord, tailWord_2738364, baseEnd_2738364] using wordTrace_append hprefix tailTrace_2738364
  have hstable : (prefixWord ++ tailWord_2738364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738364).length < 2 ^ (prefixWord ++ tailWord_2738364).sum := by decide
  have hdescent : baseEnd_2738364 < baseStart_2738364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738396 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2738396 : Nat := 118140960795 + 2738396 * 2 ^ 59
def prefixEnd_2738396 : Nat := 4983230072969 + 3 ^ 40 * 2738396 * 2
def baseEnd_2738396 : Nat := 937408913566382164504235

theorem tailTrace_2738396 : CollatzResearch.WordTrace tailWord_2738396 prefixEnd_2738396 937408913566382164504235 := by
  unfold tailWord_2738396
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938753693633223823969521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66585004924844298431959361 49938753693633223823969521)
  ·
    refine ⟨37454065270224917867977141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49938753693633223823969521 37454065270224917867977141)
    ·
      refine ⟨3511318619083586050122857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37454065270224917867977141 3511318619083586050122857)
      ·
        refine ⟨2633488964312689537592143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511318619083586050122857 2633488964312689537592143)
        ·
          refine ⟨3950233446469034306388215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633488964312689537592143 3950233446469034306388215)
          ·
            refine ⟨5925350169703551459582323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950233446469034306388215 5925350169703551459582323)
            ·
              refine ⟨8888025254555327189373485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925350169703551459582323 8888025254555327189373485)
              ·
                refine ⟨3333009470458247696015057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8888025254555327189373485 3333009470458247696015057)
                ·
                  refine ⟨2499757102843685772011293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333009470458247696015057 2499757102843685772011293)
                  ·
                    refine ⟨937408913566382164504235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499757102843685772011293 937408913566382164504235)
                    ·
                      rfl

theorem cell22_2738396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2738396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738396 prefixEnd_2738396 := by exact prefixLift 2738396
  have htrace : WordTrace (prefixWord ++ tailWord_2738396) baseStart_2738396 baseEnd_2738396 := by
    simpa [prefixWord, tailWord_2738396, baseEnd_2738396] using wordTrace_append hprefix tailTrace_2738396
  have hstable : (prefixWord ++ tailWord_2738396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738396).length < 2 ^ (prefixWord ++ tailWord_2738396).sum := by decide
  have hdescent : baseEnd_2738396 < baseStart_2738396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738441 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_2738441 : Nat := 118140960795 + 2738441 * 2 ^ 59
def prefixEnd_2738441 : Nat := 4983230072969 + 3 ^ 40 * 2738441 * 2
def baseEnd_2738441 : Nat := 937424317986017047129097

theorem tailTrace_2738441 : CollatzResearch.WordTrace tailWord_2738441 prefixEnd_2738441 937424317986017047129097 := by
  unfold tailWord_2738441
  simp only [CollatzResearch.WordTrace]
  refine ⟨99879148672103420333327177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66586099114735613555551451 99879148672103420333327177)
  ·
    refine ⟨74909361504077565249995383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99879148672103420333327177 74909361504077565249995383)
    ·
      refine ⟨112364042256116347874993075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74909361504077565249995383 112364042256116347874993075)
      ·
        refine ⟨168546063384174521812489613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112364042256116347874993075 168546063384174521812489613)
        ·
          refine ⟨63204773769065445679683605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168546063384174521812489613 63204773769065445679683605)
          ·
            refine ⟨2962723770424942766235169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63204773769065445679683605 2962723770424942766235169)
            ·
              refine ⟨2222042827818707074676377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962723770424942766235169 2222042827818707074676377)
              ·
                refine ⟨1666532120864030306007283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222042827818707074676377 1666532120864030306007283)
                ·
                  refine ⟨2499798181296045459010925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666532120864030306007283 2499798181296045459010925)
                  ·
                    refine ⟨937424317986017047129097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499798181296045459010925 937424317986017047129097)
                    ·
                      rfl

theorem cell22_2738441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_2738441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738441 prefixEnd_2738441 := by exact prefixLift 2738441
  have htrace : WordTrace (prefixWord ++ tailWord_2738441) baseStart_2738441 baseEnd_2738441 := by
    simpa [prefixWord, tailWord_2738441, baseEnd_2738441] using wordTrace_append hprefix tailTrace_2738441
  have hstable : (prefixWord ++ tailWord_2738441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738441).length < 2 ^ (prefixWord ++ tailWord_2738441).sum := by decide
  have hdescent : baseEnd_2738441 < baseStart_2738441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738484 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2738484 : Nat := 118140960795 + 2738484 * 2 ^ 59
def prefixEnd_2738484 : Nat := 4983230072969 + 3 ^ 40 * 2738484 * 2
def baseEnd_2738484 : Nat := 937439037764779268303965

theorem tailTrace_2738484 : CollatzResearch.WordTrace tailWord_2738484 prefixEnd_2738484 937439037764779268303965 := by
  unfold tailWord_2738484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49940358505473819338571253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66587144673965092451428337 49940358505473819338571253)
  ·
    refine ⟨4681908609888170562991055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49940358505473819338571253 4681908609888170562991055)
    ·
      refine ⟨7022862914832255844486583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681908609888170562991055 7022862914832255844486583)
      ·
        refine ⟨10534294372248383766729875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7022862914832255844486583 10534294372248383766729875)
        ·
          refine ⟨15801441558372575650094813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534294372248383766729875 15801441558372575650094813)
          ·
            refine ⟨5925540584389715868785555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15801441558372575650094813 5925540584389715868785555)
            ·
              refine ⟨8888310876584573803178333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925540584389715868785555 8888310876584573803178333)
              ·
                refine ⟨3333116578719215176191875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8888310876584573803178333 3333116578719215176191875)
                ·
                  refine ⟨4999674868078822764287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333116578719215176191875 4999674868078822764287813)
                  ·
                    refine ⟨937439037764779268303965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999674868078822764287813 937439037764779268303965)
                    ·
                      rfl

theorem cell22_2738484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2738484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738484 prefixEnd_2738484 := by exact prefixLift 2738484
  have htrace : WordTrace (prefixWord ++ tailWord_2738484) baseStart_2738484 baseEnd_2738484 := by
    simpa [prefixWord, tailWord_2738484, baseEnd_2738484] using wordTrace_append hprefix tailTrace_2738484
  have hstable : (prefixWord ++ tailWord_2738484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738484).length < 2 ^ (prefixWord ++ tailWord_2738484).sum := by decide
  have hdescent : baseEnd_2738484 < baseStart_2738484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738495 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_2738495 : Nat := 118140960795 + 2738495 * 2 ^ 59
def prefixEnd_2738495 : Nat := 4983230072969 + 3 ^ 40 * 2738495 * 2
def baseEnd_2738495 : Nat := 937442803289578906278931

theorem tailTrace_2738495 : CollatzResearch.WordTrace tailWord_2738495 prefixEnd_2738495 937442803289578906278931 := by
  unfold tailWord_2738495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99881118213907787555792939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66587412142605191703861959 99881118213907787555792939)
  ·
    refine ⟨149821677320861681333689409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99881118213907787555792939 149821677320861681333689409)
    ·
      refine ⟨112366257990646261000267057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149821677320861681333689409 112366257990646261000267057)
      ·
        refine ⟨84274693492984695750200293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112366257990646261000267057 84274693492984695750200293)
        ·
          refine ⟨15801505029934630453162555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84274693492984695750200293 15801505029934630453162555)
          ·
            refine ⟨23702257544901945679743833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15801505029934630453162555 23702257544901945679743833)
            ·
              refine ⟨17776693158676459259807875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23702257544901945679743833 17776693158676459259807875)
              ·
                refine ⟨26665039738014688889711813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17776693158676459259807875 26665039738014688889711813)
                ·
                  refine ⟨4999694950877754166820965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26665039738014688889711813 4999694950877754166820965)
                  ·
                    refine ⟨937442803289578906278931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999694950877754166820965 937442803289578906278931)
                    ·
                      rfl

theorem cell22_2738495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_2738495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738495 prefixEnd_2738495 := by exact prefixLift 2738495
  have htrace : WordTrace (prefixWord ++ tailWord_2738495) baseStart_2738495 baseEnd_2738495 := by
    simpa [prefixWord, tailWord_2738495, baseEnd_2738495] using wordTrace_append hprefix tailTrace_2738495
  have hstable : (prefixWord ++ tailWord_2738495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738495).length < 2 ^ (prefixWord ++ tailWord_2738495).sum := by decide
  have hdescent : baseEnd_2738495 < baseStart_2738495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738555 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 7]
def baseStart_2738555 : Nat := 118140960795 + 2738555 * 2 ^ 59
def prefixEnd_2738555 : Nat := 4983230072969 + 3 ^ 40 * 2738555 * 2
def baseEnd_2738555 : Nat := 312487780838586249926249

theorem tailTrace_2738555 : CollatzResearch.WordTrace tailWord_2738555 prefixEnd_2738555 312487780838586249926249 := by
  unfold tailWord_2738555
  simp only [CollatzResearch.WordTrace]
  refine ⟨99883306593690417802977119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66588871062460278535318079 99883306593690417802977119)
  ·
    refine ⟨149824959890535626704465679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99883306593690417802977119 149824959890535626704465679)
    ·
      refine ⟨224737439835803440056698519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149824959890535626704465679 224737439835803440056698519)
      ·
        refine ⟨337106159753705160085047779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224737439835803440056698519 337106159753705160085047779)
        ·
          refine ⟨505659239630557740127571669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337106159753705160085047779 505659239630557740127571669)
          ·
            refine ⟨11851388428841197034239961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 505659239630557740127571669 11851388428841197034239961)
            ·
              refine ⟨8888541321630897775679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11851388428841197034239961 8888541321630897775679971)
              ·
                refine ⟨13332811982446346663519957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888541321630897775679971 13332811982446346663519957)
                ·
                  refine ⟨312487780838586249926249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13332811982446346663519957 312487780838586249926249)
                  ·
                    rfl

theorem cell22_2738555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_2738555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738555 prefixEnd_2738555 := by exact prefixLift 2738555
  have htrace : WordTrace (prefixWord ++ tailWord_2738555) baseStart_2738555 baseEnd_2738555 := by
    simpa [prefixWord, tailWord_2738555, baseEnd_2738555] using wordTrace_append hprefix tailTrace_2738555
  have hstable : (prefixWord ++ tailWord_2738555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738555).length < 2 ^ (prefixWord ++ tailWord_2738555).sum := by decide
  have hdescent : baseEnd_2738555 < baseStart_2738555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738572 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_2738572 : Nat := 118140960795 + 2738572 * 2 ^ 59
def prefixEnd_2738572 : Nat := 4983230072969 + 3 ^ 40 * 2738572 * 2
def baseEnd_2738572 : Nat := 312489720654392124034565

theorem tailTrace_2738572 : CollatzResearch.WordTrace tailWord_2738572 prefixEnd_2738572 312489720654392124034565 := by
  unfold tailWord_2738572
  simp only [CollatzResearch.WordTrace]
  refine ⟨49941963317314414853172985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66589284423085886470897313 49941963317314414853172985)
  ·
    refine ⟨37456472487985811139879739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49941963317314414853172985 37456472487985811139879739)
    ·
      refine ⟨56184708731978716709819609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37456472487985811139879739 56184708731978716709819609)
      ·
        refine ⟨42138531548984037532364707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56184708731978716709819609 42138531548984037532364707)
        ·
          refine ⟨63207797323476056298547061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42138531548984037532364707 63207797323476056298547061)
          ·
            refine ⟨5925730999075880277988787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63207797323476056298547061 5925730999075880277988787)
            ·
              refine ⟨8888596498613820416983181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925730999075880277988787 8888596498613820416983181)
              ·
                refine ⟨3333223686980182656368693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8888596498613820416983181 3333223686980182656368693)
                ·
                  refine ⟨312489720654392124034565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333223686980182656368693 312489720654392124034565)
                  ·
                    rfl

theorem cell22_2738572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_2738572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738572 prefixEnd_2738572 := by exact prefixLift 2738572
  have htrace : WordTrace (prefixWord ++ tailWord_2738572) baseStart_2738572 baseEnd_2738572 := by
    simpa [prefixWord, tailWord_2738572, baseEnd_2738572] using wordTrace_append hprefix tailTrace_2738572
  have hstable : (prefixWord ++ tailWord_2738572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738572).length < 2 ^ (prefixWord ++ tailWord_2738572).sum := by decide
  have hdescent : baseEnd_2738572 < baseStart_2738572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738632 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_2738632 : Nat := 118140960795 + 2738632 * 2 ^ 59
def prefixEnd_2738632 : Nat := 4983230072969 + 3 ^ 40 * 2738632 * 2
def baseEnd_2738632 : Nat := 937489701189356215603511

theorem tailTrace_2738632 : CollatzResearch.WordTrace tailWord_2738632 prefixEnd_2738632 937489701189356215603511 := by
  unfold tailWord_2738632
  simp only [CollatzResearch.WordTrace]
  refine ⟨49943057507205729976765075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66590743342940973302353433 49943057507205729976765075)
  ·
    refine ⟨74914586260808594965147613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49943057507205729976765075 74914586260808594965147613)
    ·
      refine ⟨28092969847803223111930355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74914586260808594965147613 28092969847803223111930355)
      ·
        refine ⟨42139454771704834667895533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28092969847803223111930355 42139454771704834667895533)
        ·
          refine ⟨15802295539389313000460825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42139454771704834667895533 15802295539389313000460825)
          ·
            refine ⟨11851721654541984750345619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15802295539389313000460825 11851721654541984750345619)
            ·
              refine ⟨17777582481812977125518429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11851721654541984750345619 17777582481812977125518429)
              ·
                refine ⟨6666593430679866422069411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17777582481812977125518429 6666593430679866422069411)
                ·
                  refine ⟨9999890146019799633104117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6666593430679866422069411 9999890146019799633104117)
                  ·
                    refine ⟨937489701189356215603511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9999890146019799633104117 937489701189356215603511)
                    ·
                      rfl

theorem cell22_2738632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_2738632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738632 prefixEnd_2738632 := by exact prefixLift 2738632
  have htrace : WordTrace (prefixWord ++ tailWord_2738632) baseStart_2738632 baseEnd_2738632 := by
    simpa [prefixWord, tailWord_2738632, baseEnd_2738632] using wordTrace_append hprefix tailTrace_2738632
  have hstable : (prefixWord ++ tailWord_2738632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738632).length < 2 ^ (prefixWord ++ tailWord_2738632).sum := by decide
  have hdescent : baseEnd_2738632 < baseStart_2738632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738666 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2738666 : Nat := 118140960795 + 2738666 * 2 ^ 59
def prefixEnd_2738666 : Nat := 4983230072969 + 3 ^ 40 * 2738666 * 2
def baseEnd_2738666 : Nat := 937501340084191460253407

theorem tailTrace_2738666 : CollatzResearch.WordTrace tailWord_2738666 prefixEnd_2738666 937501340084191460253407 := by
  unfold tailWord_2738666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24971838774072070940066963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66591570064192189173511901 24971838774072070940066963)
  ·
    refine ⟨37457758161108106410100445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24971838774072070940066963 37457758161108106410100445)
    ·
      refine ⟨14046659310415539903787667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37457758161108106410100445 14046659310415539903787667)
      ·
        refine ⟨21069988965623309855681501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14046659310415539903787667 21069988965623309855681501)
        ·
          refine ⟨7901245862108741195880563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21069988965623309855681501 7901245862108741195880563)
          ·
            refine ⟨11851868793163111793820845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901245862108741195880563 11851868793163111793820845)
            ·
              refine ⟨4444450797436166922682817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11851868793163111793820845 4444450797436166922682817)
              ·
                refine ⟨3333338098077125192012113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4444450797436166922682817 3333338098077125192012113)
                ·
                  refine ⟨2500003573557843894009085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333338098077125192012113 2500003573557843894009085)
                  ·
                    refine ⟨937501340084191460253407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500003573557843894009085 937501340084191460253407)
                    ·
                      rfl

theorem cell22_2738666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2738666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738666 prefixEnd_2738666 := by exact prefixLift 2738666
  have htrace : WordTrace (prefixWord ++ tailWord_2738666) baseStart_2738666 baseEnd_2738666 := by
    simpa [prefixWord, tailWord_2738666, baseEnd_2738666] using wordTrace_append hprefix tailTrace_2738666
  have hstable : (prefixWord ++ tailWord_2738666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738666).length < 2 ^ (prefixWord ++ tailWord_2738666).sum := by decide
  have hdescent : baseEnd_2738666 < baseStart_2738666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738728 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2738728 : Nat := 118140960795 + 2738728 * 2 ^ 59
def prefixEnd_2738728 : Nat := 4983230072969 + 3 ^ 40 * 2738728 * 2
def baseEnd_2738728 : Nat := 937522563951243965203217

theorem tailTrace_2738728 : CollatzResearch.WordTrace tailWord_2738728 prefixEnd_2738728 937522563951243965203217 := by
  unfold tailWord_2738728
  simp only [CollatzResearch.WordTrace]
  refine ⟨49944808211031834174512419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66593077614709112232683225 49944808211031834174512419)
  ·
    refine ⟨74917212316547751261768629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49944808211031834174512419 74917212316547751261768629)
    ·
      refine ⟨7023488654676351680790809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74917212316547751261768629 7023488654676351680790809)
      ·
        refine ⟨5267616491007263760593107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7023488654676351680790809 5267616491007263760593107)
        ·
          refine ⟨7901424736510895640889661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267616491007263760593107 7901424736510895640889661)
          ·
            refine ⟨2963034276191585865333623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7901424736510895640889661 2963034276191585865333623)
            ·
              refine ⟨4444551414287378798000435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963034276191585865333623 4444551414287378798000435)
              ·
                refine ⟨6666827121431068197000653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444551414287378798000435 6666827121431068197000653)
                ·
                  refine ⟨2500060170536650573875245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6666827121431068197000653 2500060170536650573875245)
                  ·
                    refine ⟨937522563951243965203217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500060170536650573875245 937522563951243965203217)
                    ·
                      rfl

theorem cell22_2738728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2738728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738728 prefixEnd_2738728 := by exact prefixLift 2738728
  have htrace : WordTrace (prefixWord ++ tailWord_2738728) baseStart_2738728 baseEnd_2738728 := by
    simpa [prefixWord, tailWord_2738728, baseEnd_2738728] using wordTrace_append hprefix tailTrace_2738728
  have hstable : (prefixWord ++ tailWord_2738728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738728).length < 2 ^ (prefixWord ++ tailWord_2738728).sum := by decide
  have hdescent : baseEnd_2738728 < baseStart_2738728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738752 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_2738752 : Nat := 118140960795 + 2738752 * 2 ^ 59
def prefixEnd_2738752 : Nat := 4983230072969 + 3 ^ 40 * 2738752 * 2
def baseEnd_2738752 : Nat := 312510259880571967534381

theorem tailTrace_2738752 : CollatzResearch.WordTrace tailWord_2738752 prefixEnd_2738752 312510259880571967534381 := by
  unfold tailWord_2738752
  simp only [CollatzResearch.WordTrace]
  refine ⟨49945245886988360223949255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66593661182651146965265673 49945245886988360223949255)
  ·
    refine ⟨74917868830482540335923883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49945245886988360223949255 74917868830482540335923883)
    ·
      refine ⟨112376803245723810503885825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74917868830482540335923883 112376803245723810503885825)
      ·
        refine ⟨84282602434292857877914369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112376803245723810503885825 84282602434292857877914369)
        ·
          refine ⟨63211951825719643408435777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84282602434292857877914369 63211951825719643408435777)
          ·
            refine ⟨47408963869289732556326833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63211951825719643408435777 47408963869289732556326833)
            ·
              refine ⟨35556722901967299417245125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47408963869289732556326833 35556722901967299417245125)
              ·
                refine ⟨6666885544118868640733461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35556722901967299417245125 6666885544118868640733461)
                ·
                  refine ⟨312510259880571967534381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6666885544118868640733461 312510259880571967534381)
                  ·
                    rfl

theorem cell22_2738752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_2738752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738752 prefixEnd_2738752 := by exact prefixLift 2738752
  have htrace : WordTrace (prefixWord ++ tailWord_2738752) baseStart_2738752 baseEnd_2738752 := by
    simpa [prefixWord, tailWord_2738752, baseEnd_2738752] using wordTrace_append hprefix tailTrace_2738752
  have hstable : (prefixWord ++ tailWord_2738752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738752).length < 2 ^ (prefixWord ++ tailWord_2738752).sum := by decide
  have hdescent : baseEnd_2738752 < baseStart_2738752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738767 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2738767 : Nat := 118140960795 + 2738767 * 2 ^ 59
def prefixEnd_2738767 : Nat := 4983230072969 + 3 ^ 40 * 2738767 * 2
def baseEnd_2738767 : Nat := 937535914448260863478097

theorem tailTrace_2738767 : CollatzResearch.WordTrace tailWord_2738767 prefixEnd_2738767 937535914448260863478097 := by
  unfold tailWord_2738767
  simp only [CollatzResearch.WordTrace]
  refine ⟨99891038868922378009694555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66594025912614918673129703 99891038868922378009694555)
  ·
    refine ⟨149836558303383567014541833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99891038868922378009694555 149836558303383567014541833)
    ·
      refine ⟨112377418727537675260906375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149836558303383567014541833 112377418727537675260906375)
      ·
        refine ⟨168566128091306512891359563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112377418727537675260906375 168566128091306512891359563)
        ·
          refine ⟨252849192136959769337039345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168566128091306512891359563 252849192136959769337039345)
          ·
            refine ⟨189636894102719827002779509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252849192136959769337039345 189636894102719827002779509)
            ·
              refine ⟨17778458822129983781510579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189636894102719827002779509 17778458822129983781510579)
              ·
                refine ⟨26667688233194975672265869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17778458822129983781510579 26667688233194975672265869)
                ·
                  refine ⟨10000383087448115877099701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26667688233194975672265869 10000383087448115877099701)
                  ·
                    refine ⟨937535914448260863478097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10000383087448115877099701 937535914448260863478097)
                    ·
                      rfl

theorem cell22_2738767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2738767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738767 prefixEnd_2738767 := by exact prefixLift 2738767
  have htrace : WordTrace (prefixWord ++ tailWord_2738767) baseStart_2738767 baseEnd_2738767 := by
    simpa [prefixWord, tailWord_2738767, baseEnd_2738767] using wordTrace_append hprefix tailTrace_2738767
  have hstable : (prefixWord ++ tailWord_2738767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738767).length < 2 ^ (prefixWord ++ tailWord_2738767).sum := by decide
  have hdescent : baseEnd_2738767 < baseStart_2738767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738784 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_2738784 : Nat := 118140960795 + 2738784 * 2 ^ 59
def prefixEnd_2738784 : Nat := 4983230072969 + 3 ^ 40 * 2738784 * 2
def baseEnd_2738784 : Nat := 937541733895678485803045

theorem tailTrace_2738784 : CollatzResearch.WordTrace tailWord_2738784 prefixEnd_2738784 937541733895678485803045 := by
  unfold tailWord_2738784
  simp only [CollatzResearch.WordTrace]
  refine ⟨49945829454930394956531703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66594439273240526608708937 49945829454930394956531703)
  ·
    refine ⟨74918744182395592434797555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49945829454930394956531703 74918744182395592434797555)
    ·
      refine ⟨112378116273593388652196333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74918744182395592434797555 112378116273593388652196333)
      ·
        refine ⟨42141793602597520744573625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112378116273593388652196333 42141793602597520744573625)
        ·
          refine ⟨31606345201948140558430219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42141793602597520744573625 31606345201948140558430219)
          ·
            refine ⟨47409517802922210837645329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31606345201948140558430219 47409517802922210837645329)
            ·
              refine ⟨35557138352191658128233997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47409517802922210837645329 35557138352191658128233997)
              ·
                refine ⟨13333926882071871798087749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35557138352191658128233997 13333926882071871798087749)
                ·
                  refine ⟨2500111290388475962141453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13333926882071871798087749 2500111290388475962141453)
                  ·
                    refine ⟨937541733895678485803045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500111290388475962141453 937541733895678485803045)
                    ·
                      rfl

theorem cell22_2738784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_2738784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738784 prefixEnd_2738784 := by exact prefixLift 2738784
  have htrace : WordTrace (prefixWord ++ tailWord_2738784) baseStart_2738784 baseEnd_2738784 := by
    simpa [prefixWord, tailWord_2738784, baseEnd_2738784] using wordTrace_append hprefix tailTrace_2738784
  have hstable : (prefixWord ++ tailWord_2738784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738784).length < 2 ^ (prefixWord ++ tailWord_2738784).sum := by decide
  have hdescent : baseEnd_2738784 < baseStart_2738784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738816 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_2738816 : Nat := 118140960795 + 2738816 * 2 ^ 59
def prefixEnd_2738816 : Nat := 4983230072969 + 3 ^ 40 * 2738816 * 2
def baseEnd_2738816 : Nat := 937552688149641069002947

theorem tailTrace_2738816 : CollatzResearch.WordTrace tailWord_2738816 prefixEnd_2738816 937552688149641069002947 := by
  unfold tailWord_2738816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49946413022872429689114151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66595217363829906252152201 49946413022872429689114151)
  ·
    refine ⟨74919619534308644533671227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49946413022872429689114151 74919619534308644533671227)
    ·
      refine ⟨112379429301462966800506841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74919619534308644533671227 112379429301462966800506841)
      ·
        refine ⟨84284571976097225100380131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112379429301462966800506841 84284571976097225100380131)
        ·
          refine ⟨126426857964145837650570197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84284571976097225100380131 126426857964145837650570197)
          ·
            refine ⟨2963129483534668069935239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126426857964145837650570197 2963129483534668069935239)
            ·
              refine ⟨4444694225302002104902859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963129483534668069935239 4444694225302002104902859)
              ·
                refine ⟨6667041337953003157354289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444694225302002104902859 6667041337953003157354289)
                ·
                  refine ⟨5000281003464752368015717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667041337953003157354289 5000281003464752368015717)
                  ·
                    refine ⟨937552688149641069002947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000281003464752368015717 937552688149641069002947)
                    ·
                      rfl

theorem cell22_2738816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_2738816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738816 prefixEnd_2738816 := by exact prefixLift 2738816
  have htrace : WordTrace (prefixWord ++ tailWord_2738816) baseStart_2738816 baseEnd_2738816 := by
    simpa [prefixWord, tailWord_2738816, baseEnd_2738816] using wordTrace_append hprefix tailTrace_2738816
  have hstable : (prefixWord ++ tailWord_2738816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738816).length < 2 ^ (prefixWord ++ tailWord_2738816).sum := by decide
  have hdescent : baseEnd_2738816 < baseStart_2738816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738827 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_2738827 : Nat := 118140960795 + 2738827 * 2 ^ 59
def prefixEnd_2738827 : Nat := 4983230072969 + 3 ^ 40 * 2738827 * 2
def baseEnd_2738827 : Nat := 937556453674440706977913

theorem tailTrace_2738827 : CollatzResearch.WordTrace tailWord_2738827 prefixEnd_2738827 937556453674440706977913 := by
  unfold tailWord_2738827
  simp only [CollatzResearch.WordTrace]
  refine ⟨99893227248705008256878735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66595484832470005504585823 99893227248705008256878735)
  ·
    refine ⟨149839840873057512385318103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99893227248705008256878735 149839840873057512385318103)
    ·
      refine ⟨224759761309586268577977155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149839840873057512385318103 224759761309586268577977155)
      ·
        refine ⟨337139641964379402866965733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224759761309586268577977155 337139641964379402866965733)
        ·
          refine ⟨63213682868321138037556075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337139641964379402866965733 63213682868321138037556075)
          ·
            refine ⟨94820524302481707056334113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63213682868321138037556075 94820524302481707056334113)
            ·
              refine ⟨71115393226861280292250585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94820524302481707056334113 71115393226861280292250585)
              ·
                refine ⟨53336544920145960219187939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71115393226861280292250585 53336544920145960219187939)
                ·
                  refine ⟨80004817380218940328781909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53336544920145960219187939 80004817380218940328781909)
                  ·
                    refine ⟨937556453674440706977913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80004817380218940328781909 937556453674440706977913)
                    ·
                      rfl

theorem cell22_2738827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_2738827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738827 prefixEnd_2738827 := by exact prefixLift 2738827
  have htrace : WordTrace (prefixWord ++ tailWord_2738827) baseStart_2738827 baseEnd_2738827 := by
    simpa [prefixWord, tailWord_2738827, baseEnd_2738827] using wordTrace_append hprefix tailTrace_2738827
  have hstable : (prefixWord ++ tailWord_2738827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738827).length < 2 ^ (prefixWord ++ tailWord_2738827).sum := by decide
  have hdescent : baseEnd_2738827 < baseStart_2738827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738865 : List Nat := [1, 2, 2, 6, 2, 1, 2, 6]
def baseStart_2738865 : Nat := 118140960795 + 2738865 * 2 ^ 59
def prefixEnd_2738865 : Nat := 4983230072969 + 3 ^ 40 * 2738865 * 2
def baseEnd_2738865 : Nat := 104174384650113474947533

theorem tailTrace_2738865 : CollatzResearch.WordTrace tailWord_2738865 prefixEnd_2738865 104174384650113474947533 := by
  unfold tailWord_2738865
  simp only [CollatzResearch.WordTrace]
  refine ⟨99894613222567340746762049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66596408815044893831174699 99894613222567340746762049)
  ·
    refine ⟨74920959916925505560071537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99894613222567340746762049 74920959916925505560071537)
    ·
      refine ⟨56190719937694129170053653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74920959916925505560071537 56190719937694129170053653)
      ·
        refine ⟨2633939997079412304846265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56190719937694129170053653 2633939997079412304846265)
        ·
          refine ⟨1975454997809559228634699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2633939997079412304846265 1975454997809559228634699)
          ·
            refine ⟨2963182496714338842952049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975454997809559228634699 2963182496714338842952049)
            ·
              refine ⟨2222386872535754132214037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963182496714338842952049 2222386872535754132214037)
              ·
                refine ⟨104174384650113474947533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2222386872535754132214037 104174384650113474947533)
                ·
                  rfl

theorem cell22_2738865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 6].length) (baseStart_2738865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738865 prefixEnd_2738865 := by exact prefixLift 2738865
  have htrace : WordTrace (prefixWord ++ tailWord_2738865) baseStart_2738865 baseEnd_2738865 := by
    simpa [prefixWord, tailWord_2738865, baseEnd_2738865] using wordTrace_append hprefix tailTrace_2738865
  have hstable : (prefixWord ++ tailWord_2738865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738865).length < 2 ^ (prefixWord ++ tailWord_2738865).sum := by decide
  have hdescent : baseEnd_2738865 < baseStart_2738865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738880 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_2738880 : Nat := 118140960795 + 2738880 * 2 ^ 59
def prefixEnd_2738880 : Nat := 4983230072969 + 3 ^ 40 * 2738880 * 2
def baseEnd_2738880 : Nat := 937574596657566235402751

theorem tailTrace_2738880 : CollatzResearch.WordTrace tailWord_2738880 prefixEnd_2738880 937574596657566235402751 := by
  unfold tailWord_2738880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49947580158756499154279047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66596773545008665539038729 49947580158756499154279047)
  ·
    refine ⟨74921370238134748731418571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49947580158756499154279047 74921370238134748731418571)
    ·
      refine ⟨112382055357202123097127857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74921370238134748731418571 112382055357202123097127857)
      ·
        refine ⟨84286541517901592322845893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112382055357202123097127857 84286541517901592322845893)
        ·
          refine ⟨15803726534606548560533605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84286541517901592322845893 15803726534606548560533605)
          ·
            refine ⟨2963198725238727855100051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15803726534606548560533605 2963198725238727855100051)
            ·
              refine ⟨4444798087858091782650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963198725238727855100051 4444798087858091782650077)
              ·
                refine ⟨1666799282946784418493779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4444798087858091782650077 1666799282946784418493779)
                ·
                  refine ⟨2500198924420176627740669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666799282946784418493779 2500198924420176627740669)
                  ·
                    refine ⟨937574596657566235402751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500198924420176627740669 937574596657566235402751)
                    ·
                      rfl

theorem cell22_2738880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_2738880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738880 prefixEnd_2738880 := by exact prefixLift 2738880
  have htrace : WordTrace (prefixWord ++ tailWord_2738880) baseStart_2738880 baseEnd_2738880 := by
    simpa [prefixWord, tailWord_2738880, baseEnd_2738880] using wordTrace_append hprefix tailTrace_2738880
  have hstable : (prefixWord ++ tailWord_2738880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738880).length < 2 ^ (prefixWord ++ tailWord_2738880).sum := by decide
  have hdescent : baseEnd_2738880 < baseStart_2738880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738979 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_2738979 : Nat := 118140960795 + 2738979 * 2 ^ 59
def prefixEnd_2738979 : Nat := 4983230072969 + 3 ^ 40 * 2738979 * 2
def baseEnd_2738979 : Nat := 937608486380762977177447

theorem tailTrace_2738979 : CollatzResearch.WordTrace tailWord_2738979 prefixEnd_2738979 937608486380762977177447 := by
  unfold tailWord_2738979
  simp only [CollatzResearch.WordTrace]
  refine ⟨99898771144154338216411991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66599180762769558810941327 99898771144154338216411991)
  ·
    refine ⟨149848156716231507324617987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99898771144154338216411991 149848156716231507324617987)
    ·
      refine ⟨224772235074347260986926981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149848156716231507324617987 224772235074347260986926981)
      ·
        refine ⟨42144794076440111435048809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224772235074347260986926981 42144794076440111435048809)
        ·
          refine ⟨31608595557330083576286607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42144794076440111435048809 31608595557330083576286607)
          ·
            refine ⟨47412893335995125364429911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31608595557330083576286607 47412893335995125364429911)
            ·
              refine ⟨71119340003992688046644867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47412893335995125364429911 71119340003992688046644867)
              ·
                refine ⟨106679010005989032069967301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71119340003992688046644867 106679010005989032069967301)
                ·
                  refine ⟨20002314376122943513118869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106679010005989032069967301 20002314376122943513118869)
                  ·
                    refine ⟨937608486380762977177447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20002314376122943513118869 937608486380762977177447)
                    ·
                      rfl

theorem cell22_2738979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_2738979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2738979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2738979 prefixEnd_2738979 := by exact prefixLift 2738979
  have htrace : WordTrace (prefixWord ++ tailWord_2738979) baseStart_2738979 baseEnd_2738979 := by
    simpa [prefixWord, tailWord_2738979, baseEnd_2738979] using wordTrace_append hprefix tailTrace_2738979
  have hstable : (prefixWord ++ tailWord_2738979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738979).length < 2 ^ (prefixWord ++ tailWord_2738979).sum := by decide
  have hdescent : baseEnd_2738979 < baseStart_2738979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
