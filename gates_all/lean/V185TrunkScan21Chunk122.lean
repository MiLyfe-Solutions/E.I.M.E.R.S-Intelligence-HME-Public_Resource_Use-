import V185TrunkScan21Chunk121

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1485870 : List Nat := [4, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1485870 : Nat := 118140960795 + 1485870 * 2 ^ 59
def prefixEnd_1485870 : Nat := 4983230072969 + 3 ^ 40 * 1485870 * 2
def baseEnd_1485870 : Nat := 113031925940178779332091

theorem tailTrace_1485870 : CollatzResearch.WordTrace tailWord_1485870 prefixEnd_1485870 113031925940178779332091 := by
  unfold tailWord_1485870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774266390869278904716883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36129420751302820825156709 6774266390869278904716883)
  ·
    refine ⟨10161399586303918357075325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6774266390869278904716883 10161399586303918357075325)
    ·
      refine ⟨3810524844863969383903247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10161399586303918357075325 3810524844863969383903247)
      ·
        refine ⟨5715787267295954075854871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810524844863969383903247 5715787267295954075854871)
        ·
          refine ⟨8573680900943931113782307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715787267295954075854871 8573680900943931113782307)
          ·
            refine ⟨12860521351415896670673461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573680900943931113782307 12860521351415896670673461)
            ·
              refine ⟨1205673876695240312875637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12860521351415896670673461 1205673876695240312875637)
              ·
                refine ⟨113031925940178779332091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1205673876695240312875637 113031925940178779332091)
                ·
                  rfl

theorem cell21_1485870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1485870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485870 prefixEnd_1485870 := by exact prefixLift 1485870
  have htrace : WordTrace (prefixWord ++ tailWord_1485870) baseStart_1485870 baseEnd_1485870 := by
    simpa [prefixWord, tailWord_1485870, baseEnd_1485870] using wordTrace_append hprefix tailTrace_1485870
  have hstable : (prefixWord ++ tailWord_1485870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485870).length < 2 ^ (prefixWord ++ tailWord_1485870).sum := by decide
  have hdescent : baseEnd_1485870 < baseStart_1485870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485901 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1485901 : Nat := 118140960795 + 1485901 * 2 ^ 59
def prefixEnd_1485901 : Nat := 4983230072969 + 3 ^ 40 * 1485901 * 2
def baseEnd_1485901 : Nat := 339102852442887172979543

theorem tailTrace_1485901 : CollatzResearch.WordTrace tailWord_1485901 prefixEnd_1485901 339102852442887172979543 := by
  unfold tailWord_1485901
  simp only [CollatzResearch.WordTrace]
  refine ⟨54195261789841923532113557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36130174526561282354742371 54195261789841923532113557)
  ·
    refine ⟨2540402896398840165567823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54195261789841923532113557 2540402896398840165567823)
    ·
      refine ⟨3810604344598260248351735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540402896398840165567823 3810604344598260248351735)
      ·
        refine ⟨5715906516897390372527603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810604344598260248351735 5715906516897390372527603)
        ·
          refine ⟨8573859775346085558791405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715906516897390372527603 8573859775346085558791405)
          ·
            refine ⟨3215197415754782084546777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8573859775346085558791405 3215197415754782084546777)
            ·
              refine ⟨2411398061816086563410083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215197415754782084546777 2411398061816086563410083)
              ·
                refine ⟨3617097092724129845115125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411398061816086563410083 3617097092724129845115125)
                ·
                  refine ⟨339102852442887172979543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617097092724129845115125 339102852442887172979543)
                  ·
                    rfl

theorem cell21_1485901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1485901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485901 prefixEnd_1485901 := by exact prefixLift 1485901
  have htrace : WordTrace (prefixWord ++ tailWord_1485901) baseStart_1485901 baseEnd_1485901 := by
    simpa [prefixWord, tailWord_1485901, baseEnd_1485901] using wordTrace_append hprefix tailTrace_1485901
  have hstable : (prefixWord ++ tailWord_1485901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485901).length < 2 ^ (prefixWord ++ tailWord_1485901).sum := by decide
  have hdescent : baseEnd_1485901 < baseStart_1485901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485912 : List Nat := [2, 1, 2, 2, 1, 3, 2, 8]
def baseStart_1485912 : Nat := 118140960795 + 1485912 * 2 ^ 59
def prefixEnd_1485912 : Nat := 4983230072969 + 3 ^ 40 * 1485912 * 2
def baseEnd_1485912 : Nat := 113035120930917866098729

theorem tailTrace_1485912 : CollatzResearch.WordTrace tailWord_1485912 prefixEnd_1485912 113035120930917866098729 := by
  unfold tailWord_1485912
  simp only [CollatzResearch.WordTrace]
  refine ⟨27097831496401036205381995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36130441995201381607175993 27097831496401036205381995)
  ·
    refine ⟨40646747244601554308072993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27097831496401036205381995 40646747244601554308072993)
    ·
      refine ⟨30485060433451165731054745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40646747244601554308072993 30485060433451165731054745)
      ·
        refine ⟨22863795325088374298291059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30485060433451165731054745 22863795325088374298291059)
        ·
          refine ⟨34295692987632561447436589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22863795325088374298291059 34295692987632561447436589)
          ·
            refine ⟨12860884870362210542788721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34295692987632561447436589 12860884870362210542788721)
            ·
              refine ⟨9645663652771657907091541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12860884870362210542788721 9645663652771657907091541)
              ·
                refine ⟨113035120930917866098729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9645663652771657907091541 113035120930917866098729)
                ·
                  rfl

theorem cell21_1485912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_1485912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485912 prefixEnd_1485912 := by exact prefixLift 1485912
  have htrace : WordTrace (prefixWord ++ tailWord_1485912) baseStart_1485912 baseEnd_1485912 := by
    simpa [prefixWord, tailWord_1485912, baseEnd_1485912] using wordTrace_append hprefix tailTrace_1485912
  have hstable : (prefixWord ++ tailWord_1485912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485912).length < 2 ^ (prefixWord ++ tailWord_1485912).sum := by decide
  have hdescent : baseEnd_1485912 < baseStart_1485912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485918 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1485918 : Nat := 118140960795 + 1485918 * 2 ^ 59
def prefixEnd_1485918 : Nat := 4983230072969 + 3 ^ 40 * 1485918 * 2
def baseEnd_1485918 : Nat := 339106732074498921196175

theorem tailTrace_1485918 : CollatzResearch.WordTrace tailWord_1485918 prefixEnd_1485918 339106732074498921196175 := by
  unfold tailWord_1485918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774485228847541929435301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36130587887186890290321605 6774485228847541929435301)
  ·
    refine ⟨1270215980408914111769119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6774485228847541929435301 1270215980408914111769119)
    ·
      refine ⟨1905323970613371167653679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270215980408914111769119 1905323970613371167653679)
      ·
        refine ⟨2857985955920056751480519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905323970613371167653679 2857985955920056751480519)
        ·
          refine ⟨4286978933880085127220779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857985955920056751480519 4286978933880085127220779)
          ·
            refine ⟨6430468400820127690831169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286978933880085127220779 6430468400820127690831169)
            ·
              refine ⟨4822851300615095768123377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430468400820127690831169 4822851300615095768123377)
              ·
                refine ⟨3617138475461321826092533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822851300615095768123377 3617138475461321826092533)
                ·
                  refine ⟨339106732074498921196175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617138475461321826092533 339106732074498921196175)
                  ·
                    rfl

theorem cell21_1485918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1485918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485918 prefixEnd_1485918 := by exact prefixLift 1485918
  have htrace : WordTrace (prefixWord ++ tailWord_1485918) baseStart_1485918 baseEnd_1485918 := by
    simpa [prefixWord, tailWord_1485918, baseEnd_1485918] using wordTrace_append hprefix tailTrace_1485918
  have hstable : (prefixWord ++ tailWord_1485918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485918).length < 2 ^ (prefixWord ++ tailWord_1485918).sum := by decide
  have hdescent : baseEnd_1485918 < baseStart_1485918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485929 : List Nat := [1, 2, 1, 1, 1, 6, 4, 5]
def baseStart_1485929 : Nat := 118140960795 + 1485929 * 2 ^ 59
def prefixEnd_1485929 : Nat := 4983230072969 + 3 ^ 40 * 1485929 * 2
def baseEnd_1485929 : Nat := 113036414141455115504273

theorem tailTrace_1485929 : CollatzResearch.WordTrace tailWord_1485929 prefixEnd_1485929 113036414141455115504273 := by
  unfold tailWord_1485929
  simp only [CollatzResearch.WordTrace]
  refine ⟨54196283033740484314132841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36130855355826989542755227 54196283033740484314132841)
  ·
    refine ⟨40647212275305363235599631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54196283033740484314132841 40647212275305363235599631)
    ·
      refine ⟨60970818412958044853399447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40647212275305363235599631 60970818412958044853399447)
      ·
        refine ⟨91456227619437067280099171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60970818412958044853399447 91456227619437067280099171)
        ·
          refine ⟨137184341429155600920148757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91456227619437067280099171 137184341429155600920148757)
          ·
            refine ⟨6430516004491668793131973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137184341429155600920148757 6430516004491668793131973)
            ·
              refine ⟨1205721750842187898712245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6430516004491668793131973 1205721750842187898712245)
              ·
                refine ⟨113036414141455115504273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1205721750842187898712245 113036414141455115504273)
                ·
                  rfl

theorem cell21_1485929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 5].length) (baseStart_1485929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485929 prefixEnd_1485929 := by exact prefixLift 1485929
  have htrace : WordTrace (prefixWord ++ tailWord_1485929) baseStart_1485929 baseEnd_1485929 := by
    simpa [prefixWord, tailWord_1485929, baseEnd_1485929] using wordTrace_append hprefix tailTrace_1485929
  have hstable : (prefixWord ++ tailWord_1485929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485929).length < 2 ^ (prefixWord ++ tailWord_1485929).sum := by decide
  have hdescent : baseEnd_1485929 < baseStart_1485929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486033 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1486033 : Nat := 118140960795 + 1486033 * 2 ^ 59
def prefixEnd_1486033 : Nat := 4983230072969 + 3 ^ 40 * 1486033 * 2
def baseEnd_1486033 : Nat := 339132976641284276779273

theorem tailTrace_1486033 : CollatzResearch.WordTrace tailWord_1486033 prefixEnd_1486033 339132976641284276779273 := by
  unfold tailWord_1486033
  simp only [CollatzResearch.WordTrace]
  refine ⟨54200076225363710075918753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36133384150242473383945835 54200076225363710075918753)
  ·
    refine ⟨40650057169022782556939065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54200076225363710075918753 40650057169022782556939065)
    ·
      refine ⟨30487542876767086917704299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40650057169022782556939065 30487542876767086917704299)
      ·
        refine ⟨45731314315150630376556449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30487542876767086917704299 45731314315150630376556449)
        ·
          refine ⟨34298485736362972782417337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45731314315150630376556449 34298485736362972782417337)
          ·
            refine ⟨25723864302272229586813003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34298485736362972782417337 25723864302272229586813003)
            ·
              refine ⟨38585796453408344380219505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25723864302272229586813003 38585796453408344380219505)
              ·
                refine ⟨28939347340056258285164629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38585796453408344380219505 28939347340056258285164629)
                ·
                  refine ⟨339132976641284276779273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28939347340056258285164629 339132976641284276779273)
                  ·
                    rfl

theorem cell21_1486033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1486033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486033 prefixEnd_1486033 := by exact prefixLift 1486033
  have htrace : WordTrace (prefixWord ++ tailWord_1486033) baseStart_1486033 baseEnd_1486033 := by
    simpa [prefixWord, tailWord_1486033, baseEnd_1486033] using wordTrace_append hprefix tailTrace_1486033
  have hstable : (prefixWord ++ tailWord_1486033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486033).length < 2 ^ (prefixWord ++ tailWord_1486033).sum := by decide
  have hdescent : baseEnd_1486033 < baseStart_1486033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486067 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_1486067 : Nat := 118140960795 + 1486067 * 2 ^ 59
def prefixEnd_1486067 : Nat := 4983230072969 + 3 ^ 40 * 1486067 * 2
def baseEnd_1486067 : Nat := 339140735904507773212537

theorem tailTrace_1486067 : CollatzResearch.WordTrace tailWord_1486067 prefixEnd_1486067 339140735904507773212537 := by
  unfold tailWord_1486067
  simp only [CollatzResearch.WordTrace]
  refine ⟨54201316307240533882656455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36134210871493689255104303 54201316307240533882656455)
  ·
    refine ⟨81301974460860800823984683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54201316307240533882656455 81301974460860800823984683)
    ·
      refine ⟨121952961691291201235977025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81301974460860800823984683 121952961691291201235977025)
      ·
        refine ⟨91464721268468400926982769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121952961691291201235977025 91464721268468400926982769)
        ·
          refine ⟨68598540951351300695237077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91464721268468400926982769 68598540951351300695237077)
          ·
            refine ⟨1607778303547296110044619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68598540951351300695237077 1607778303547296110044619)
            ·
              refine ⟨2411667455320944165066929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607778303547296110044619 2411667455320944165066929)
              ·
                refine ⟨1808750591490708123800197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411667455320944165066929 1808750591490708123800197)
                ·
                  refine ⟨339140735904507773212537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808750591490708123800197 339140735904507773212537)
                  ·
                    rfl

theorem cell21_1486067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_1486067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486067 prefixEnd_1486067 := by exact prefixLift 1486067
  have htrace : WordTrace (prefixWord ++ tailWord_1486067) baseStart_1486067 baseEnd_1486067 := by
    simpa [prefixWord, tailWord_1486067, baseEnd_1486067] using wordTrace_append hprefix tailTrace_1486067
  have hstable : (prefixWord ++ tailWord_1486067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486067).length < 2 ^ (prefixWord ++ tailWord_1486067).sum := by decide
  have hdescent : baseEnd_1486067 < baseStart_1486067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486084 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1486084 : Nat := 118140960795 + 1486084 * 2 ^ 59
def prefixEnd_1486084 : Nat := 4983230072969 + 3 ^ 40 * 1486084 * 2
def baseEnd_1486084 : Nat := 339144615536119521429169

theorem tailTrace_1486084 : CollatzResearch.WordTrace tailWord_1486084 prefixEnd_1486084 339144615536119521429169 := by
  unfold tailWord_1486084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27100968174089472893012653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36134624232119297190683537 27100968174089472893012653)
  ·
    refine ⟨10162863065283552334879745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27100968174089472893012653 10162863065283552334879745)
    ·
      refine ⟨7622147298962664251159809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10162863065283552334879745 7622147298962664251159809)
      ·
        refine ⟨5716610474221998188369857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7622147298962664251159809 5716610474221998188369857)
        ·
          refine ⟨4287457855666498641277393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5716610474221998188369857 4287457855666498641277393)
          ·
            refine ⟨3215593391749873980958045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4287457855666498641277393 3215593391749873980958045)
            ·
              refine ⟨1205847521906202742859267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3215593391749873980958045 1205847521906202742859267)
              ·
                refine ⟨1808771282859304114288901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205847521906202742859267 1808771282859304114288901)
                ·
                  refine ⟨339144615536119521429169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808771282859304114288901 339144615536119521429169)
                  ·
                    rfl

theorem cell21_1486084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1486084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486084 prefixEnd_1486084 := by exact prefixLift 1486084
  have htrace : WordTrace (prefixWord ++ tailWord_1486084) baseStart_1486084 baseEnd_1486084 := by
    simpa [prefixWord, tailWord_1486084, baseEnd_1486084] using wordTrace_append hprefix tailTrace_1486084
  have hstable : (prefixWord ++ tailWord_1486084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486084).length < 2 ^ (prefixWord ++ tailWord_1486084).sum := by decide
  have hdescent : baseEnd_1486084 < baseStart_1486084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486140 : List Nat := [2, 2, 2, 2, 1, 3, 1, 8]
def baseStart_1486140 : Nat := 118140960795 + 1486140 * 2 ^ 59
def prefixEnd_1486140 : Nat := 4983230072969 + 3 ^ 40 * 1486140 * 2
def baseEnd_1486140 : Nat := 113052465166358622831907

theorem tailTrace_1486140 : CollatzResearch.WordTrace tailWord_1486140 prefixEnd_1486140 113052465166358622831907 := by
  unfold tailWord_1486140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27101989417988033675031937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36135985890650711566709249 27101989417988033675031937)
  ·
    refine ⟨20326492063491025256273953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27101989417988033675031937 20326492063491025256273953)
    ·
      refine ⟨15244869047618268942205465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20326492063491025256273953 15244869047618268942205465)
      ·
        refine ⟨11433651785713701706654099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15244869047618268942205465 11433651785713701706654099)
        ·
          refine ⟨17150477678570552559981149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433651785713701706654099 17150477678570552559981149)
          ·
            refine ⟨6431429129463957209992931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17150477678570552559981149 6431429129463957209992931)
            ·
              refine ⟨9647143694195935814989397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431429129463957209992931 9647143694195935814989397)
              ·
                refine ⟨113052465166358622831907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9647143694195935814989397 113052465166358622831907)
                ·
                  rfl

theorem cell21_1486140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_1486140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486140 prefixEnd_1486140 := by exact prefixLift 1486140
  have htrace : WordTrace (prefixWord ++ tailWord_1486140) baseStart_1486140 baseEnd_1486140 := by
    simpa [prefixWord, tailWord_1486140, baseEnd_1486140] using wordTrace_append hprefix tailTrace_1486140
  have hstable : (prefixWord ++ tailWord_1486140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486140).length < 2 ^ (prefixWord ++ tailWord_1486140).sum := by decide
  have hdescent : baseEnd_1486140 < baseStart_1486140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486143 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 4]
def baseStart_1486143 : Nat := 118140960795 + 1486143 * 2 ^ 59
def prefixEnd_1486143 : Nat := 4983230072969 + 3 ^ 40 * 1486143 * 2
def baseEnd_1486143 : Nat := 339158080139948529945715

theorem tailTrace_1486143 : CollatzResearch.WordTrace tailWord_1486143 prefixEnd_1486143 339158080139948529945715 := by
  unfold tailWord_1486143
  simp only [CollatzResearch.WordTrace]
  refine ⟨54204088254965198862423083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36136058836643465908282055 54204088254965198862423083)
  ·
    refine ⟨81306132382447798293634625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54204088254965198862423083 81306132382447798293634625)
    ·
      refine ⟨60979599286835848720225969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81306132382447798293634625 60979599286835848720225969)
      ·
        refine ⟨45734699465126886540169477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60979599286835848720225969 45734699465126886540169477)
        ·
          refine ⟨8575256149711291226281777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45734699465126886540169477 8575256149711291226281777)
          ·
            refine ⟨6431442112283468419711333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575256149711291226281777 6431442112283468419711333)
            ·
              refine ⟨1205895396053150328695875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6431442112283468419711333 1205895396053150328695875)
              ·
                refine ⟨1808843094079725493043813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205895396053150328695875 1808843094079725493043813)
                ·
                  refine ⟨339158080139948529945715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808843094079725493043813 339158080139948529945715)
                  ·
                    rfl

theorem cell21_1486143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_1486143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486143 prefixEnd_1486143 := by exact prefixLift 1486143
  have htrace : WordTrace (prefixWord ++ tailWord_1486143) baseStart_1486143 baseEnd_1486143 := by
    simpa [prefixWord, tailWord_1486143, baseEnd_1486143] using wordTrace_append hprefix tailTrace_1486143
  have hstable : (prefixWord ++ tailWord_1486143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486143).length < 2 ^ (prefixWord ++ tailWord_1486143).sum := by decide
  have hdescent : baseEnd_1486143 < baseStart_1486143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486174 : List Nat := [4, 4, 2, 11]
def baseStart_1486174 : Nat := 118140960795 + 1486174 * 2 ^ 59
def prefixEnd_1486174 : Nat := 4983230072969 + 3 ^ 40 * 1486174 * 2
def baseEnd_1486174 : Nat := 1395741377622631131395

theorem tailTrace_1486174 : CollatzResearch.WordTrace tailWord_1486174 prefixEnd_1486174 1395741377622631131395 := by
  unfold tailWord_1486174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775652364731611394600197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36136812611901927437867717 6775652364731611394600197)
  ·
    refine ⟨1270434818387177136487537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6775652364731611394600197 1270434818387177136487537)
    ·
      refine ⟨952826113790382852365653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270434818387177136487537 952826113790382852365653)
      ·
        refine ⟨1395741377622631131395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 952826113790382852365653 1395741377622631131395)
        ·
          rfl

theorem cell21_1486174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 11].length) (baseStart_1486174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486174 prefixEnd_1486174 := by exact prefixLift 1486174
  have htrace : WordTrace (prefixWord ++ tailWord_1486174) baseStart_1486174 baseEnd_1486174 := by
    simpa [prefixWord, tailWord_1486174, baseEnd_1486174] using wordTrace_append hprefix tailTrace_1486174
  have hstable : (prefixWord ++ tailWord_1486174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486174).length < 2 ^ (prefixWord ++ tailWord_1486174).sum := by decide
  have hdescent : baseEnd_1486174 < baseStart_1486174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486222 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1486222 : Nat := 118140960795 + 1486222 * 2 ^ 59
def prefixEnd_1486222 : Nat := 4983230072969 + 3 ^ 40 * 1486222 * 2
def baseEnd_1486222 : Nat := 339176109016261948128887

theorem tailTrace_1486222 : CollatzResearch.WordTrace tailWord_1486222 prefixEnd_1486222 339176109016261948128887 := by
  unfold tailWord_1486222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775871202709874419318615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36137979747785996903032613 6775871202709874419318615)
  ·
    refine ⟨10163806804064811628977923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775871202709874419318615 10163806804064811628977923)
    ·
      refine ⟨15245710206097217443466885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163806804064811628977923 15245710206097217443466885)
      ·
        refine ⟨2858570663643228270650041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15245710206097217443466885 2858570663643228270650041)
        ·
          refine ⟨2143927997732421202987531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858570663643228270650041 2143927997732421202987531)
          ·
            refine ⟨3215891996598631804481297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143927997732421202987531 3215891996598631804481297)
            ·
              refine ⟨2411918997448973853360973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215891996598631804481297 2411918997448973853360973)
              ·
                refine ⟨904469624043365195010365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2411918997448973853360973 904469624043365195010365)
                ·
                  refine ⟨339176109016261948128887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904469624043365195010365 339176109016261948128887)
                  ·
                    rfl

theorem cell21_1486222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1486222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486222 prefixEnd_1486222 := by exact prefixLift 1486222
  have htrace : WordTrace (prefixWord ++ tailWord_1486222) baseStart_1486222 baseEnd_1486222 := by
    simpa [prefixWord, tailWord_1486222, baseEnd_1486222] using wordTrace_append hprefix tailTrace_1486222
  have hstable : (prefixWord ++ tailWord_1486222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486222).length < 2 ^ (prefixWord ++ tailWord_1486222).sum := by decide
  have hdescent : baseEnd_1486222 < baseStart_1486222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486309 : List Nat := [1, 3, 1, 5, 1, 2, 2, 6]
def baseStart_1486309 : Nat := 118140960795 + 1486309 * 2 ^ 59
def prefixEnd_1486309 : Nat := 4983230072969 + 3 ^ 40 * 1486309 * 2
def baseEnd_1486309 : Nat := 113065321200523043392903

theorem tailTrace_1486309 : CollatzResearch.WordTrace tailWord_1486309 prefixEnd_1486309 113065321200523043392903 := by
  unfold tailWord_1486309
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210142772363809212965981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36140095181575872808643987 54210142772363809212965981)
  ·
    refine ⟨20328803539636428454862243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54210142772363809212965981 20328803539636428454862243)
    ·
      refine ⟨30493205309454642682293365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20328803539636428454862243 30493205309454642682293365)
      ·
        refine ⟨2858737997761372751465003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30493205309454642682293365 2858737997761372751465003)
        ·
          refine ⟨4288106996642059127197505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858737997761372751465003 4288106996642059127197505)
          ·
            refine ⟨3216080247481544345398129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4288106996642059127197505 3216080247481544345398129)
            ·
              refine ⟨2412060185611158259048597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216080247481544345398129 2412060185611158259048597)
              ·
                refine ⟨113065321200523043392903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2412060185611158259048597 113065321200523043392903)
                ·
                  rfl

theorem cell21_1486309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_1486309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486309 prefixEnd_1486309 := by exact prefixLift 1486309
  have htrace : WordTrace (prefixWord ++ tailWord_1486309) baseStart_1486309 baseEnd_1486309 := by
    simpa [prefixWord, tailWord_1486309, baseEnd_1486309] using wordTrace_append hprefix tailTrace_1486309
  have hstable : (prefixWord ++ tailWord_1486309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486309).length < 2 ^ (prefixWord ++ tailWord_1486309).sum := by decide
  have hdescent : baseEnd_1486309 < baseStart_1486309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486349 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1486349 : Nat := 118140960795 + 1486349 * 2 ^ 59
def prefixEnd_1486349 : Nat := 4983230072969 + 3 ^ 40 * 1486349 * 2
def baseEnd_1486349 : Nat := 339205092146537949511961

theorem tailTrace_1486349 : CollatzResearch.WordTrace tailWord_1486349 prefixEnd_1486349 339205092146537949511961 := by
  unfold tailWord_1486349
  simp only [CollatzResearch.WordTrace]
  refine ⟨54211601692218896044422101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36141067794812597362948067 54211601692218896044422101)
  ·
    refine ⟨1270584414661380376041143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54211601692218896044422101 1270584414661380376041143)
    ·
      refine ⟨1905876621992070564061715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270584414661380376041143 1905876621992070564061715)
      ·
        refine ⟨2858814932988105846092573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905876621992070564061715 2858814932988105846092573)
        ·
          refine ⟨1072055599870539692284715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2858814932988105846092573 1072055599870539692284715)
          ·
            refine ⟨1608083399805809538427073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072055599870539692284715 1608083399805809538427073)
            ·
              refine ⟨1206062549854357153820305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608083399805809538427073 1206062549854357153820305)
              ·
                refine ⟨904546912390767865365229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206062549854357153820305 904546912390767865365229)
                ·
                  refine ⟨339205092146537949511961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904546912390767865365229 339205092146537949511961)
                  ·
                    rfl

theorem cell21_1486349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1486349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486349 prefixEnd_1486349 := by exact prefixLift 1486349
  have htrace : WordTrace (prefixWord ++ tailWord_1486349) baseStart_1486349 baseEnd_1486349 := by
    simpa [prefixWord, tailWord_1486349, baseEnd_1486349] using wordTrace_append hprefix tailTrace_1486349
  have hstable : (prefixWord ++ tailWord_1486349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486349).length < 2 ^ (prefixWord ++ tailWord_1486349).sum := by decide
  have hdescent : baseEnd_1486349 < baseStart_1486349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486357 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1486357 : Nat := 118140960795 + 1486357 * 2 ^ 59
def prefixEnd_1486357 : Nat := 4983230072969 + 3 ^ 40 * 1486357 * 2
def baseEnd_1486357 : Nat := 339206917855531713378611

theorem tailTrace_1486357 : CollatzResearch.WordTrace tailWord_1486357 prefixEnd_1486357 339206917855531713378611 := by
  unfold tailWord_1486357
  simp only [CollatzResearch.WordTrace]
  refine ⟨54211893476189913410713325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36141262317459942273808883 54211893476189913410713325)
  ·
    refine ⟨20329460053571217529017497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54211893476189913410713325 20329460053571217529017497)
    ·
      refine ⟨15247095040178413146763123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20329460053571217529017497 15247095040178413146763123)
      ·
        refine ⟨22870642560267619720144685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15247095040178413146763123 22870642560267619720144685)
        ·
          refine ⟨8576490960100357395054257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22870642560267619720144685 8576490960100357395054257)
          ·
            refine ⟨6432368220075268046290693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8576490960100357395054257 6432368220075268046290693)
            ·
              refine ⟨1206069041264112758679505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6432368220075268046290693 1206069041264112758679505)
              ·
                refine ⟨904551780948084569009629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206069041264112758679505 904551780948084569009629)
                ·
                  refine ⟨339206917855531713378611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904551780948084569009629 339206917855531713378611)
                  ·
                    rfl

theorem cell21_1486357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1486357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486357 prefixEnd_1486357 := by exact prefixLift 1486357
  have htrace : WordTrace (prefixWord ++ tailWord_1486357) baseStart_1486357 baseEnd_1486357 := by
    simpa [prefixWord, tailWord_1486357, baseEnd_1486357] using wordTrace_append hprefix tailTrace_1486357
  have hstable : (prefixWord ++ tailWord_1486357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486357).length < 2 ^ (prefixWord ++ tailWord_1486357).sum := by decide
  have hdescent : baseEnd_1486357 < baseStart_1486357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486422 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1486422 : Nat := 118140960795 + 1486422 * 2 ^ 59
def prefixEnd_1486422 : Nat := 4983230072969 + 3 ^ 40 * 1486422 * 2
def baseEnd_1486422 : Nat := 339221751741106044795145

theorem tailTrace_1486422 : CollatzResearch.WordTrace tailWord_1486422 prefixEnd_1486422 339221751741106044795145 := by
  unfold tailWord_1486422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388391513809651844489345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36142842813969619674553013 3388391513809651844489345)
  ·
    refine ⟨2541293635357238883367009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3388391513809651844489345 2541293635357238883367009)
    ·
      refine ⟨1905970226517929162525257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541293635357238883367009 1905970226517929162525257)
      ·
        refine ⟨1429477669888446871893943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905970226517929162525257 1429477669888446871893943)
        ·
          refine ⟨2144216504832670307840915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429477669888446871893943 2144216504832670307840915)
          ·
            refine ⟨3216324757249005461761373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144216504832670307840915 3216324757249005461761373)
            ·
              refine ⟨1206121783968377048160515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3216324757249005461761373 1206121783968377048160515)
              ·
                refine ⟨1809182675952565572240773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206121783968377048160515 1809182675952565572240773)
                ·
                  refine ⟨339221751741106044795145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809182675952565572240773 339221751741106044795145)
                  ·
                    rfl

theorem cell21_1486422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1486422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486422 prefixEnd_1486422 := by exact prefixLift 1486422
  have htrace : WordTrace (prefixWord ++ tailWord_1486422) baseStart_1486422 baseEnd_1486422 := by
    simpa [prefixWord, tailWord_1486422, baseEnd_1486422] using wordTrace_append hprefix tailTrace_1486422
  have hstable : (prefixWord ++ tailWord_1486422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486422).length < 2 ^ (prefixWord ++ tailWord_1486422).sum := by decide
  have hdescent : baseEnd_1486422 < baseStart_1486422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486526 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_1486526 : Nat := 118140960795 + 1486526 * 2 ^ 59
def prefixEnd_1486526 : Nat := 4983230072969 + 3 ^ 40 * 1486526 * 2
def baseEnd_1486526 : Nat := 339245485958024975061599

theorem tailTrace_1486526 : CollatzResearch.WordTrace tailWord_1486526 prefixEnd_1486526 339245485958024975061599 := by
  unfold tailWord_1486526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6777257176572206909201929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36145371608385103515743621 6777257176572206909201929)
  ·
    refine ⟨5082942882429155181901447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6777257176572206909201929 5082942882429155181901447)
    ·
      refine ⟨7624414323643732772852171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082942882429155181901447 7624414323643732772852171)
      ·
        refine ⟨11436621485465599159278257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624414323643732772852171 11436621485465599159278257)
        ·
          refine ⟨8577466114099199369458693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11436621485465599159278257 8577466114099199369458693)
          ·
            refine ⟨1608274896393599881773505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8577466114099199369458693 1608274896393599881773505)
            ·
              refine ⟨1206206172295199911330129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608274896393599881773505 1206206172295199911330129)
              ·
                refine ⟨904654629221399933497597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206206172295199911330129 904654629221399933497597)
                ·
                  refine ⟨339245485958024975061599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904654629221399933497597 339245485958024975061599)
                  ·
                    rfl

theorem cell21_1486526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_1486526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486526 prefixEnd_1486526 := by exact prefixLift 1486526
  have htrace : WordTrace (prefixWord ++ tailWord_1486526) baseStart_1486526 baseEnd_1486526 := by
    simpa [prefixWord, tailWord_1486526, baseEnd_1486526] using wordTrace_append hprefix tailTrace_1486526
  have hstable : (prefixWord ++ tailWord_1486526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486526).length < 2 ^ (prefixWord ++ tailWord_1486526).sum := by decide
  have hdescent : baseEnd_1486526 < baseStart_1486526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486565 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1486565 : Nat := 118140960795 + 1486565 * 2 ^ 59
def prefixEnd_1486565 : Nat := 4983230072969 + 3 ^ 40 * 1486565 * 2
def baseEnd_1486565 : Nat := 339254386289369573911519

theorem tailTrace_1486565 : CollatzResearch.WordTrace tailWord_1486565 prefixEnd_1486565 339254386289369573911519 := by
  unfold tailWord_1486565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54219479859436364934285149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36146319906290909956190099 54219479859436364934285149)
  ·
    refine ⟨20332304947288636850356931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54219479859436364934285149 20332304947288636850356931)
    ·
      refine ⟨30498457420932955275535397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20332304947288636850356931 30498457420932955275535397)
      ·
        refine ⟨5718460766424929114162887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30498457420932955275535397 5718460766424929114162887)
        ·
          refine ⟨8577691149637393671244331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718460766424929114162887 8577691149637393671244331)
          ·
            refine ⟨12866536724456090506866497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577691149637393671244331 12866536724456090506866497)
            ·
              refine ⟨9649902543342067880149873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12866536724456090506866497 9649902543342067880149873)
              ·
                refine ⟨7237426907506550910112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649902543342067880149873 7237426907506550910112405)
                ·
                  refine ⟨339254386289369573911519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7237426907506550910112405 339254386289369573911519)
                  ·
                    rfl

theorem cell21_1486565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1486565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486565 prefixEnd_1486565 := by exact prefixLift 1486565
  have htrace : WordTrace (prefixWord ++ tailWord_1486565) baseStart_1486565 baseEnd_1486565 := by
    simpa [prefixWord, tailWord_1486565, baseEnd_1486565] using wordTrace_append hprefix tailTrace_1486565
  have hstable : (prefixWord ++ tailWord_1486565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486565).length < 2 ^ (prefixWord ++ tailWord_1486565).sum := by decide
  have hdescent : baseEnd_1486565 < baseStart_1486565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486568 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_1486568 : Nat := 118140960795 + 1486568 * 2 ^ 59
def prefixEnd_1486568 : Nat := 4983230072969 + 3 ^ 40 * 1486568 * 2
def baseEnd_1486568 : Nat := 339255070930242235361513

theorem tailTrace_1486568 : CollatzResearch.WordTrace tailWord_1486568 prefixEnd_1486568 339255070930242235361513 := by
  unfold tailWord_1486568
  simp only [CollatzResearch.WordTrace]
  refine ⟨27109794639212748223322179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36146392852283664297762905 27109794639212748223322179)
  ·
    refine ⟨40664691958819122334983269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27109794639212748223322179 40664691958819122334983269)
    ·
      refine ⟨7624629742278585437809363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40664691958819122334983269 7624629742278585437809363)
      ·
        refine ⟨11436944613417878156714045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624629742278585437809363 11436944613417878156714045)
        ·
          refine ⟨4288854230031704308767767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11436944613417878156714045 4288854230031704308767767)
          ·
            refine ⟨6433281345047556463151651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288854230031704308767767 6433281345047556463151651)
            ·
              refine ⟨9649922017571334694727477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433281345047556463151651 9649922017571334694727477)
              ·
                refine ⟨904680189147312627630701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9649922017571334694727477 904680189147312627630701)
                ·
                  refine ⟨339255070930242235361513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904680189147312627630701 339255070930242235361513)
                  ·
                    rfl

theorem cell21_1486568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_1486568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486568 prefixEnd_1486568 := by exact prefixLift 1486568
  have htrace : WordTrace (prefixWord ++ tailWord_1486568) baseStart_1486568 baseEnd_1486568 := by
    simpa [prefixWord, tailWord_1486568, baseEnd_1486568] using wordTrace_append hprefix tailTrace_1486568
  have hstable : (prefixWord ++ tailWord_1486568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486568).length < 2 ^ (prefixWord ++ tailWord_1486568).sum := by decide
  have hdescent : baseEnd_1486568 < baseStart_1486568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486582 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1486582 : Nat := 118140960795 + 1486582 * 2 ^ 59
def prefixEnd_1486582 : Nat := 4983230072969 + 3 ^ 40 * 1486582 * 2
def baseEnd_1486582 : Nat := 339258265920981322128151

theorem tailTrace_1486582 : CollatzResearch.WordTrace tailWord_1486582 prefixEnd_1486582 339258265920981322128151 := by
  unfold tailWord_1486582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388756243773423552353375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36146733266916517891769333 3388756243773423552353375)
  ·
    refine ⟨5083134365660135328530063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3388756243773423552353375 5083134365660135328530063)
    ·
      refine ⟨7624701548490202992795095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083134365660135328530063 7624701548490202992795095)
      ·
        refine ⟨11437052322735304489192643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624701548490202992795095 11437052322735304489192643)
        ·
          refine ⟨17155578484102956733788965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11437052322735304489192643 17155578484102956733788965)
          ·
            refine ⟨3216670965769304387585431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17155578484102956733788965 3216670965769304387585431)
            ·
              refine ⟨4825006448653956581378147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216670965769304387585431 4825006448653956581378147)
              ·
                refine ⟨7237509672980934872067221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825006448653956581378147 7237509672980934872067221)
                ·
                  refine ⟨339258265920981322128151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7237509672980934872067221 339258265920981322128151)
                  ·
                    rfl

theorem cell21_1486582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1486582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486582 prefixEnd_1486582 := by exact prefixLift 1486582
  have htrace : WordTrace (prefixWord ++ tailWord_1486582) baseStart_1486582 baseEnd_1486582 := by
    simpa [prefixWord, tailWord_1486582, baseEnd_1486582] using wordTrace_append hprefix tailTrace_1486582
  have hstable : (prefixWord ++ tailWord_1486582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486582).length < 2 ^ (prefixWord ++ tailWord_1486582).sum := by decide
  have hdescent : baseEnd_1486582 < baseStart_1486582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486605 : List Nat := [1, 7, 2, 1, 1, 2, 2, 5]
def baseStart_1486605 : Nat := 118140960795 + 1486605 * 2 ^ 59
def prefixEnd_1486605 : Nat := 4983230072969 + 3 ^ 40 * 1486605 * 2
def baseEnd_1486605 : Nat := 113087838278112797748257

theorem tailTrace_1486605 : CollatzResearch.WordTrace tailWord_1486605 prefixEnd_1486605 113087838278112797748257 := by
  unfold tailWord_1486605
  simp only [CollatzResearch.WordTrace]
  refine ⟨54220938779291451765741269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36147292519527634510494179 54220938779291451765741269)
  ·
    refine ⟨1270803252639643400759561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54220938779291451765741269 1270803252639643400759561)
    ·
      refine ⟨953102439479732550569671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270803252639643400759561 953102439479732550569671)
      ·
        refine ⟨1429653659219598825854507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953102439479732550569671 1429653659219598825854507)
        ·
          refine ⟨2144480488829398238781761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429653659219598825854507 2144480488829398238781761)
          ·
            refine ⟨1608360366622048679086321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144480488829398238781761 1608360366622048679086321)
            ·
              refine ⟨1206270274966536509314741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608360366622048679086321 1206270274966536509314741)
              ·
                refine ⟨113087838278112797748257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206270274966536509314741 113087838278112797748257)
                ·
                  rfl

theorem cell21_1486605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].length) (baseStart_1486605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486605 prefixEnd_1486605 := by exact prefixLift 1486605
  have htrace : WordTrace (prefixWord ++ tailWord_1486605) baseStart_1486605 baseEnd_1486605 := by
    simpa [prefixWord, tailWord_1486605, baseEnd_1486605] using wordTrace_append hprefix tailTrace_1486605
  have hstable : (prefixWord ++ tailWord_1486605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486605).length < 2 ^ (prefixWord ++ tailWord_1486605).sum := by decide
  have hdescent : baseEnd_1486605 < baseStart_1486605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486613 : List Nat := [1, 3, 2, 1, 2, 5, 2, 5]
def baseStart_1486613 : Nat := 118140960795 + 1486613 * 2 ^ 59
def prefixEnd_1486613 : Nat := 4983230072969 + 3 ^ 40 * 1486613 * 2
def baseEnd_1486613 : Nat := 113088446847777385703807

theorem tailTrace_1486613 : CollatzResearch.WordTrace tailWord_1486613 prefixEnd_1486613 113088446847777385703807 := by
  unfold tailWord_1486613
  simp only [CollatzResearch.WordTrace]
  refine ⟨54221230563262469132032493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36147487042174979421354995 54221230563262469132032493)
  ·
    refine ⟨20332961461223425924512185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54221230563262469132032493 20332961461223425924512185)
    ·
      refine ⟨15249721095917569443384139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20332961461223425924512185 15249721095917569443384139)
      ·
        refine ⟨22874581643876354165076209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15249721095917569443384139 22874581643876354165076209)
        ·
          refine ⟨17155936232907265623807157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22874581643876354165076209 17155936232907265623807157)
          ·
            refine ⟨1608369021835056152231921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17155936232907265623807157 1608369021835056152231921)
            ·
              refine ⟨1206276766376292114173941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608369021835056152231921 1206276766376292114173941)
              ·
                refine ⟨113088446847777385703807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206276766376292114173941 113088446847777385703807)
                ·
                  rfl

theorem cell21_1486613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 5].length) (baseStart_1486613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486613 prefixEnd_1486613 := by exact prefixLift 1486613
  have htrace : WordTrace (prefixWord ++ tailWord_1486613) baseStart_1486613 baseEnd_1486613 := by
    simpa [prefixWord, tailWord_1486613, baseEnd_1486613] using wordTrace_append hprefix tailTrace_1486613
  have hstable : (prefixWord ++ tailWord_1486613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486613).length < 2 ^ (prefixWord ++ tailWord_1486613).sum := by decide
  have hdescent : baseEnd_1486613 < baseStart_1486613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486641 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1486641 : Nat := 118140960795 + 1486641 * 2 ^ 59
def prefixEnd_1486641 : Nat := 4983230072969 + 3 ^ 40 * 1486641 * 2
def baseEnd_1486641 : Nat := 339271730524810330644697

theorem tailTrace_1486641 : CollatzResearch.WordTrace tailWord_1486641 prefixEnd_1486641 339271730524810330644697 := by
  unfold tailWord_1486641
  simp only [CollatzResearch.WordTrace]
  refine ⟨54222251807161029914051777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36148167871440686609367851 54222251807161029914051777)
  ·
    refine ⟨40666688855370772435538833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54222251807161029914051777 40666688855370772435538833)
    ·
      refine ⟨30500016641528079326654125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40666688855370772435538833 30500016641528079326654125)
      ·
        refine ⟨11437506240573029747495297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30500016641528079326654125 11437506240573029747495297)
        ·
          refine ⟨8578129680429772310621473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11437506240573029747495297 8578129680429772310621473)
          ·
            refine ⟨6433597260322329232966105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578129680429772310621473 6433597260322329232966105)
            ·
              refine ⟨4825197945241746924724579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433597260322329232966105 4825197945241746924724579)
              ·
                refine ⟨7237796917862620387086869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825197945241746924724579 7237796917862620387086869)
                ·
                  refine ⟨339271730524810330644697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7237796917862620387086869 339271730524810330644697)
                  ·
                    rfl

theorem cell21_1486641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1486641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486641 prefixEnd_1486641 := by exact prefixLift 1486641
  have htrace : WordTrace (prefixWord ++ tailWord_1486641) baseStart_1486641 baseEnd_1486641 := by
    simpa [prefixWord, tailWord_1486641, baseEnd_1486641] using wordTrace_append hprefix tailTrace_1486641
  have hstable : (prefixWord ++ tailWord_1486641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486641).length < 2 ^ (prefixWord ++ tailWord_1486641).sum := by decide
  have hdescent : baseEnd_1486641 < baseStart_1486641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486644 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1486644 : Nat := 118140960795 + 1486644 * 2 ^ 59
def prefixEnd_1486644 : Nat := 4983230072969 + 3 ^ 40 * 1486644 * 2
def baseEnd_1486644 : Nat := 339272415165682992094691

theorem tailTrace_1486644 : CollatzResearch.WordTrace tailWord_1486644 prefixEnd_1486644 339272415165682992094691 := by
  unfold tailWord_1486644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27111180613075080713205493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36148240817433440950940657 27111180613075080713205493)
  ·
    refine ⟨2541673182475788816863015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27111180613075080713205493 2541673182475788816863015)
    ·
      refine ⟨3812509773713683225294523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2541673182475788816863015 3812509773713683225294523)
      ·
        refine ⟨5718764660570524837941785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812509773713683225294523 5718764660570524837941785)
        ·
          refine ⟨4289073495427893628456339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718764660570524837941785 4289073495427893628456339)
          ·
            refine ⟨6433610243141840442684509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289073495427893628456339 6433610243141840442684509)
            ·
              refine ⟨2412603841178190166006691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6433610243141840442684509 2412603841178190166006691)
              ·
                refine ⟨3618905761767285249010037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412603841178190166006691 3618905761767285249010037)
                ·
                  refine ⟨339272415165682992094691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3618905761767285249010037 339272415165682992094691)
                  ·
                    rfl

theorem cell21_1486644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1486644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486644 prefixEnd_1486644 := by exact prefixLift 1486644
  have htrace : WordTrace (prefixWord ++ tailWord_1486644) baseStart_1486644 baseEnd_1486644 := by
    simpa [prefixWord, tailWord_1486644, baseEnd_1486644] using wordTrace_append hprefix tailTrace_1486644
  have hstable : (prefixWord ++ tailWord_1486644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486644).length < 2 ^ (prefixWord ++ tailWord_1486644).sum := by decide
  have hdescent : baseEnd_1486644 < baseStart_1486644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486748 : List Nat := [2, 2, 3, 3, 1, 2, 8]
def baseStart_1486748 : Nat := 118140960795 + 1486748 * 2 ^ 59
def prefixEnd_1486748 : Nat := 4983230072969 + 3 ^ 40 * 1486748 * 2
def baseEnd_1486748 : Nat := 37699572153622435817905

theorem tailTrace_1486748 : CollatzResearch.WordTrace tailWord_1486748 prefixEnd_1486748 37699572153622435817905 := by
  unfold tailWord_1486748
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113077208886693594098449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36150769611848924792131265 27113077208886693594098449)
  ·
    refine ⟨20334807906665020195573837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27113077208886693594098449 20334807906665020195573837)
    ·
      refine ⟨7625552964999382573340189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20334807906665020195573837 7625552964999382573340189)
      ·
        refine ⟨2859582361874768465002571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7625552964999382573340189 2859582361874768465002571)
        ·
          refine ⟨4289373542812152697503857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859582361874768465002571 4289373542812152697503857)
          ·
            refine ⟨3217030157109114523127893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289373542812152697503857 3217030157109114523127893)
            ·
              refine ⟨37699572153622435817905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3217030157109114523127893 37699572153622435817905)
              ·
                rfl

theorem cell21_1486748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 8].length) (baseStart_1486748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486748 prefixEnd_1486748 := by exact prefixLift 1486748
  have htrace : WordTrace (prefixWord ++ tailWord_1486748) baseStart_1486748 baseEnd_1486748 := by
    simpa [prefixWord, tailWord_1486748, baseEnd_1486748] using wordTrace_append hprefix tailTrace_1486748
  have hstable : (prefixWord ++ tailWord_1486748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486748).length < 2 ^ (prefixWord ++ tailWord_1486748).sum := by decide
  have hdescent : baseEnd_1486748 < baseStart_1486748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486751 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_1486751 : Nat := 118140960795 + 1486751 * 2 ^ 59
def prefixEnd_1486751 : Nat := 4983230072969 + 3 ^ 40 * 1486751 * 2
def baseEnd_1486751 : Nat := 339296834023474583811139

theorem tailTrace_1486751 : CollatzResearch.WordTrace tailWord_1486751 prefixEnd_1486751 339296834023474583811139 := by
  unfold tailWord_1486751
  simp only [CollatzResearch.WordTrace]
  refine ⟨54226263836762518700556107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36150842557841679133704071 54226263836762518700556107)
  ·
    refine ⟨81339395755143778050834161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54226263836762518700556107 81339395755143778050834161)
    ·
      refine ⟨61004546816357833538125621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81339395755143778050834161 61004546816357833538125621)
      ·
        refine ⟨5719176264033546894199277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61004546816357833538125621 5719176264033546894199277)
        ·
          refine ⟨2144691099012580085324729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5719176264033546894199277 2144691099012580085324729)
          ·
            refine ⟨1608518324259435063993547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144691099012580085324729 1608518324259435063993547)
            ·
              refine ⟨2412777486389152595990321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608518324259435063993547 2412777486389152595990321)
              ·
                refine ⟨1809583114791864446992741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412777486389152595990321 1809583114791864446992741)
                ·
                  refine ⟨339296834023474583811139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809583114791864446992741 339296834023474583811139)
                  ·
                    rfl

theorem cell21_1486751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_1486751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486751 prefixEnd_1486751 := by exact prefixLift 1486751
  have htrace : WordTrace (prefixWord ++ tailWord_1486751) baseStart_1486751 baseEnd_1486751 := by
    simpa [prefixWord, tailWord_1486751, baseEnd_1486751] using wordTrace_append hprefix tailTrace_1486751
  have hstable : (prefixWord ++ tailWord_1486751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486751).length < 2 ^ (prefixWord ++ tailWord_1486751).sum := by decide
  have hdescent : baseEnd_1486751 < baseStart_1486751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486796 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_1486796 : Nat := 118140960795 + 1486796 * 2 ^ 59
def prefixEnd_1486796 : Nat := 4983230072969 + 3 ^ 40 * 1486796 * 2
def baseEnd_1486796 : Nat := 339307103636564505561047

theorem tailTrace_1486796 : CollatzResearch.WordTrace tailWord_1486796 prefixEnd_1486796 339307103636564505561047 := by
  unfold tailWord_1486796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113952560799745692972121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36151936747732994257296161 27113952560799745692972121)
  ·
    refine ⟨20335464420599809269729091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27113952560799745692972121 20335464420599809269729091)
    ·
      refine ⟨30503196630899713904593637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20335464420599809269729091 30503196630899713904593637)
      ·
        refine ⟨5719349368293696357111307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30503196630899713904593637 5719349368293696357111307)
        ·
          refine ⟨8579024052440544535666961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719349368293696357111307 8579024052440544535666961)
          ·
            refine ⟨6434268039330408401750221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8579024052440544535666961 6434268039330408401750221)
            ·
              refine ⟨2412850514748903150656333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6434268039330408401750221 2412850514748903150656333)
              ·
                refine ⟨904818943030838681496125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2412850514748903150656333 904818943030838681496125)
                ·
                  refine ⟨339307103636564505561047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904818943030838681496125 339307103636564505561047)
                  ·
                    rfl

theorem cell21_1486796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_1486796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486796 prefixEnd_1486796 := by exact prefixLift 1486796
  have htrace : WordTrace (prefixWord ++ tailWord_1486796) baseStart_1486796 baseEnd_1486796 := by
    simpa [prefixWord, tailWord_1486796, baseEnd_1486796] using wordTrace_append hprefix tailTrace_1486796
  have hstable : (prefixWord ++ tailWord_1486796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486796).length < 2 ^ (prefixWord ++ tailWord_1486796).sum := by decide
  have hdescent : baseEnd_1486796 < baseStart_1486796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486813 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1486813 : Nat := 118140960795 + 1486813 * 2 ^ 59
def prefixEnd_1486813 : Nat := 4983230072969 + 3 ^ 40 * 1486813 * 2
def baseEnd_1486813 : Nat := 339310983268176253777679

theorem tailTrace_1486813 : CollatzResearch.WordTrace tailWord_1486813 prefixEnd_1486813 339310983268176253777679 := by
  unfold tailWord_1486813
  simp only [CollatzResearch.WordTrace]
  refine ⟨54228525162537903289313093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36152350108358602192875395 54228525162537903289313093)
  ·
    refine ⟨10167848467975856866746205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54228525162537903289313093 10167848467975856866746205)
    ·
      refine ⟨3812943175490946325029827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10167848467975856866746205 3812943175490946325029827)
      ·
        refine ⟨5719414763236419487544741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812943175490946325029827 5719414763236419487544741)
        ·
          refine ⟨1072390268106828653914639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5719414763236419487544741 1072390268106828653914639)
          ·
            refine ⟨1608585402160242980871959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072390268106828653914639 1608585402160242980871959)
            ·
              refine ⟨2412878103240364471307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608585402160242980871959 2412878103240364471307939)
              ·
                refine ⟨3619317154860546706961909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412878103240364471307939 3619317154860546706961909)
                ·
                  refine ⟨339310983268176253777679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619317154860546706961909 339310983268176253777679)
                  ·
                    rfl

theorem cell21_1486813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1486813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486813 prefixEnd_1486813 := by exact prefixLift 1486813
  have htrace : WordTrace (prefixWord ++ tailWord_1486813) baseStart_1486813 baseEnd_1486813 := by
    simpa [prefixWord, tailWord_1486813, baseEnd_1486813] using wordTrace_append hprefix tailTrace_1486813
  have hstable : (prefixWord ++ tailWord_1486813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486813).length < 2 ^ (prefixWord ++ tailWord_1486813).sum := by decide
  have hdescent : baseEnd_1486813 < baseStart_1486813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486861 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1486861 : Nat := 118140960795 + 1486861 * 2 ^ 59
def prefixEnd_1486861 : Nat := 4983230072969 + 3 ^ 40 * 1486861 * 2
def baseEnd_1486861 : Nat := 339321937522138836977581

theorem tailTrace_1486861 : CollatzResearch.WordTrace tailWord_1486861 prefixEnd_1486861 339321937522138836977581 := by
  unfold tailWord_1486861
  simp only [CollatzResearch.WordTrace]
  refine ⟨54230275866364007487060437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36153517244242671658040291 54230275866364007487060437)
  ·
    refine ⟨1271022090617906425477979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54230275866364007487060437 1271022090617906425477979)
    ·
      refine ⟨1906533135926859638216969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271022090617906425477979 1906533135926859638216969)
      ·
        refine ⟨1429899851945144728662727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906533135926859638216969 1429899851945144728662727)
        ·
          refine ⟨2144849777917717092994091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429899851945144728662727 2144849777917717092994091)
          ·
            refine ⟨3217274666876575639491137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144849777917717092994091 3217274666876575639491137)
            ·
              refine ⟨2412956000157431729618353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217274666876575639491137 2412956000157431729618353)
              ·
                refine ⟨1809717000118073797213765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412956000157431729618353 1809717000118073797213765)
                ·
                  refine ⟨339321937522138836977581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809717000118073797213765 339321937522138836977581)
                  ·
                    rfl

theorem cell21_1486861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1486861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486861 prefixEnd_1486861 := by exact prefixLift 1486861
  have htrace : WordTrace (prefixWord ++ tailWord_1486861) baseStart_1486861 baseEnd_1486861 := by
    simpa [prefixWord, tailWord_1486861, baseEnd_1486861] using wordTrace_append hprefix tailTrace_1486861
  have hstable : (prefixWord ++ tailWord_1486861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486861).length < 2 ^ (prefixWord ++ tailWord_1486861).sum := by decide
  have hdescent : baseEnd_1486861 < baseStart_1486861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486959 : List Nat := [1, 1, 2, 1, 3, 5, 1, 7]
def baseStart_1486959 : Nat := 118140960795 + 1486959 * 2 ^ 59
def prefixEnd_1486959 : Nat := 4983230072969 + 3 ^ 40 * 1486959 * 2
def baseEnd_1486959 : Nat := 113114767485770814781349

theorem tailTrace_1486959 : CollatzResearch.WordTrace tailWord_1486959 prefixEnd_1486959 113114767485770814781349 := by
  unfold tailWord_1486959
  simp only [CollatzResearch.WordTrace]
  refine ⟨54233850220008970224127931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36155900146672646816085287 54233850220008970224127931)
  ·
    refine ⟨81350775330013455336191897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54233850220008970224127931 81350775330013455336191897)
    ·
      refine ⟨61013081497510091502143923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81350775330013455336191897 61013081497510091502143923)
      ·
        refine ⟨91519622246265137253215885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61013081497510091502143923 91519622246265137253215885)
        ·
          refine ⟨34319858342349426469955957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91519622246265137253215885 34319858342349426469955957)
          ·
            refine ⟨3217486719595258731558371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34319858342349426469955957 3217486719595258731558371)
            ·
              refine ⟨4826230079392888097337557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217486719595258731558371 4826230079392888097337557)
              ·
                refine ⟨113114767485770814781349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4826230079392888097337557 113114767485770814781349)
                ·
                  rfl

theorem cell21_1486959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_1486959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1486959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1486959 prefixEnd_1486959 := by exact prefixLift 1486959
  have htrace : WordTrace (prefixWord ++ tailWord_1486959) baseStart_1486959 baseEnd_1486959 := by
    simpa [prefixWord, tailWord_1486959, baseEnd_1486959] using wordTrace_append hprefix tailTrace_1486959
  have hstable : (prefixWord ++ tailWord_1486959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486959).length < 2 ^ (prefixWord ++ tailWord_1486959).sum := by decide
  have hdescent : baseEnd_1486959 < baseStart_1486959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487041 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 3]
def baseStart_1487041 : Nat := 118140960795 + 1487041 * 2 ^ 59
def prefixEnd_1487041 : Nat := 4983230072969 + 3 ^ 40 * 1487041 * 2
def baseEnd_1487041 : Nat := 339363015974498523977213

theorem tailTrace_1487041 : CollatzResearch.WordTrace tailWord_1487041 prefixEnd_1487041 339363015974498523977213 := by
  unfold tailWord_1487041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54236841005711898228612977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36157894003807932152408651 54236841005711898228612977)
  ·
    refine ⟨40677630754283923671459733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54236841005711898228612977 40677630754283923671459733)
    ·
      refine ⟨1906763941607058922099675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40677630754283923671459733 1906763941607058922099675)
      ·
        refine ⟨2860145912410588383149513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906763941607058922099675 2860145912410588383149513)
        ·
          refine ⟨2145109434307941287362135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860145912410588383149513 2145109434307941287362135)
          ·
            refine ⟨3217664151461911931043203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145109434307941287362135 3217664151461911931043203)
            ·
              refine ⟨4826496227192867896564805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217664151461911931043203 4826496227192867896564805)
              ·
                refine ⟨904968042598662730605901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4826496227192867896564805 904968042598662730605901)
                ·
                  refine ⟨339363015974498523977213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904968042598662730605901 339363015974498523977213)
                  ·
                    rfl

theorem cell21_1487041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_1487041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487041 prefixEnd_1487041 := by exact prefixLift 1487041
  have htrace : WordTrace (prefixWord ++ tailWord_1487041) baseStart_1487041 baseEnd_1487041 := by
    simpa [prefixWord, tailWord_1487041, baseEnd_1487041] using wordTrace_append hprefix tailTrace_1487041
  have hstable : (prefixWord ++ tailWord_1487041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487041).length < 2 ^ (prefixWord ++ tailWord_1487041).sum := by decide
  have hdescent : baseEnd_1487041 < baseStart_1487041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487069 : List Nat := [1, 4, 3, 2, 1, 2, 3, 5]
def baseStart_1487069 : Nat := 118140960795 + 1487069 * 2 ^ 59
def prefixEnd_1487069 : Nat := 4983230072969 + 3 ^ 40 * 1487069 * 2
def baseEnd_1487069 : Nat := 113123135318658899170163

theorem tailTrace_1487069 : CollatzResearch.WordTrace tailWord_1487069 prefixEnd_1487069 113123135318658899170163 := by
  unfold tailWord_1487069
  simp only [CollatzResearch.WordTrace]
  refine ⟨54237862249610459010632261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36158574833073639340421507 54237862249610459010632261)
  ·
    refine ⟨10169599171801961064493549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54237862249610459010632261 10169599171801961064493549)
    ·
      refine ⟨3813599689425735399185081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10169599171801961064493549 3813599689425735399185081)
      ·
        refine ⟨2860199767069301549388811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813599689425735399185081 2860199767069301549388811)
        ·
          refine ⟨4290299650603952324083217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860199767069301549388811 4290299650603952324083217)
          ·
            refine ⟨3217724737952964243062413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290299650603952324083217 3217724737952964243062413)
            ·
              refine ⟨1206646776732361591148405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3217724737952964243062413 1206646776732361591148405)
              ·
                refine ⟨113123135318658899170163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206646776732361591148405 113123135318658899170163)
                ·
                  rfl

theorem cell21_1487069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].length) (baseStart_1487069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487069 prefixEnd_1487069 := by exact prefixLift 1487069
  have htrace : WordTrace (prefixWord ++ tailWord_1487069) baseStart_1487069 baseEnd_1487069 := by
    simpa [prefixWord, tailWord_1487069, baseEnd_1487069] using wordTrace_append hprefix tailTrace_1487069
  have hstable : (prefixWord ++ tailWord_1487069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487069).length < 2 ^ (prefixWord ++ tailWord_1487069).sum := by decide
  have hdescent : baseEnd_1487069 < baseStart_1487069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487083 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 3]
def baseStart_1487083 : Nat := 118140960795 + 1487083 * 2 ^ 59
def prefixEnd_1487083 : Nat := 4983230072969 + 3 ^ 40 * 1487083 * 2
def baseEnd_1487083 : Nat := 339372600946715784277127

theorem tailTrace_1487083 : CollatzResearch.WordTrace tailWord_1487083 prefixEnd_1487083 339372600946715784277127 := by
  unfold tailWord_1487083
  simp only [CollatzResearch.WordTrace]
  refine ⟨54238372871559739401641903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36158915247706492934427935 54238372871559739401641903)
  ·
    refine ⟨81357559307339609102462855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54238372871559739401641903 81357559307339609102462855)
    ·
      refine ⟨122036338961009413653694283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81357559307339609102462855 122036338961009413653694283)
      ·
        refine ⟨183054508441514120480541425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122036338961009413653694283 183054508441514120480541425)
        ·
          refine ⟨137290881331135590360406069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183054508441514120480541425 137290881331135590360406069)
          ·
            refine ⟨12871020124793961596288069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137290881331135590360406069 12871020124793961596288069)
            ·
              refine ⟨2413316273398867799304013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12871020124793961596288069 2413316273398867799304013)
              ·
                refine ⟨904993602524575424739005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413316273398867799304013 904993602524575424739005)
                ·
                  refine ⟨339372600946715784277127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904993602524575424739005 339372600946715784277127)
                  ·
                    rfl

theorem cell21_1487083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].length) (baseStart_1487083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487083 prefixEnd_1487083 := by exact prefixLift 1487083
  have htrace : WordTrace (prefixWord ++ tailWord_1487083) baseStart_1487083 baseEnd_1487083 := by
    simpa [prefixWord, tailWord_1487083, baseEnd_1487083] using wordTrace_append hprefix tailTrace_1487083
  have hstable : (prefixWord ++ tailWord_1487083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487083).length < 2 ^ (prefixWord ++ tailWord_1487083).sum := by decide
  have hdescent : baseEnd_1487083 < baseStart_1487083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487134 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1487134 : Nat := 118140960795 + 1487134 * 2 ^ 59
def prefixEnd_1487134 : Nat := 4983230072969 + 3 ^ 40 * 1487134 * 2
def baseEnd_1487134 : Nat := 339384239841551028927023

theorem tailTrace_1487134 : CollatzResearch.WordTrace tailWord_1487134 prefixEnd_1487134 339384239841551028927023 := by
  unfold tailWord_1487134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780029124296871888968557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36160155329583316741165637 6780029124296871888968557)
  ·
    refine ⟨2542510921611326958363209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6780029124296871888968557 2542510921611326958363209)
    ·
      refine ⟨1906883191208495218772407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542510921611326958363209 1906883191208495218772407)
      ·
        refine ⟨2860324786812742828158611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906883191208495218772407 2860324786812742828158611)
        ·
          refine ⟨4290487180219114242237917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860324786812742828158611 4290487180219114242237917)
          ·
            refine ⟨1608932692582167840839219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4290487180219114242237917 1608932692582167840839219)
            ·
              refine ⟨2413399038873251761258829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608932692582167840839219 2413399038873251761258829)
              ·
                refine ⟨905024639577469410472061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413399038873251761258829 905024639577469410472061)
                ·
                  refine ⟨339384239841551028927023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905024639577469410472061 339384239841551028927023)
                  ·
                    rfl

theorem cell21_1487134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1487134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487134 prefixEnd_1487134 := by exact prefixLift 1487134
  have htrace : WordTrace (prefixWord ++ tailWord_1487134) baseStart_1487134 baseEnd_1487134 := by
    simpa [prefixWord, tailWord_1487134, baseEnd_1487134] using wordTrace_append hprefix tailTrace_1487134
  have hstable : (prefixWord ++ tailWord_1487134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487134).length < 2 ^ (prefixWord ++ tailWord_1487134).sum := by decide
  have hdescent : baseEnd_1487134 < baseStart_1487134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487294 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1487294 : Nat := 118140960795 + 1487294 * 2 ^ 59
def prefixEnd_1487294 : Nat := 4983230072969 + 3 ^ 40 * 1487294 * 2
def baseEnd_1487294 : Nat := 339420754021426306260029

theorem tailTrace_1487294 : CollatzResearch.WordTrace tailWord_1487294 prefixEnd_1487294 339420754021426306260029 := by
  unfold tailWord_1487294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780758584224415304696617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36164045782530214958381957 6780758584224415304696617)
  ·
    refine ⟨5085568938168311478522463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6780758584224415304696617 5085568938168311478522463)
    ·
      refine ⟨7628353407252467217783695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085568938168311478522463 7628353407252467217783695)
      ·
        refine ⟨11442530110878700826675543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628353407252467217783695 11442530110878700826675543)
        ·
          refine ⟨17163795166318051240013315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442530110878700826675543 17163795166318051240013315)
          ·
            refine ⟨25745692749477076860019973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17163795166318051240013315 25745692749477076860019973)
            ·
              refine ⟨4827317390526951911253745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25745692749477076860019973 4827317390526951911253745)
              ·
                refine ⟨3620488042895213933440309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827317390526951911253745 3620488042895213933440309)
                ·
                  refine ⟨339420754021426306260029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620488042895213933440309 339420754021426306260029)
                  ·
                    rfl

theorem cell21_1487294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1487294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487294 prefixEnd_1487294 := by exact prefixLift 1487294
  have htrace : WordTrace (prefixWord ++ tailWord_1487294) baseStart_1487294 baseEnd_1487294 := by
    simpa [prefixWord, tailWord_1487294, baseEnd_1487294] using wordTrace_append hprefix tailTrace_1487294
  have hstable : (prefixWord ++ tailWord_1487294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487294).length < 2 ^ (prefixWord ++ tailWord_1487294).sum := by decide
  have hdescent : baseEnd_1487294 < baseStart_1487294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487325 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1487325 : Nat := 118140960795 + 1487325 * 2 ^ 59
def prefixEnd_1487325 : Nat := 4983230072969 + 3 ^ 40 * 1487325 * 2
def baseEnd_1487325 : Nat := 339427828643777141243299

theorem tailTrace_1487325 : CollatzResearch.WordTrace tailWord_1487325 prefixEnd_1487325 339427828643777141243299 := by
  unfold tailWord_1487325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54247199336683014731951429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36164799557788676487967619 54247199336683014731951429)
  ·
    refine ⟨10171349875628065262240893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54247199336683014731951429 10171349875628065262240893)
    ·
      refine ⟨3814256203360524473340335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10171349875628065262240893 3814256203360524473340335)
      ·
        refine ⟨5721384305040786710010503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814256203360524473340335 5721384305040786710010503)
        ·
          refine ⟨8582076457561180065015755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721384305040786710010503 8582076457561180065015755)
          ·
            refine ⟨12873114686341770097523633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582076457561180065015755 12873114686341770097523633)
            ·
              refine ⟨9654836014756327573142725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12873114686341770097523633 9654836014756327573142725)
              ·
                refine ⟨1810281752766811419964261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9654836014756327573142725 1810281752766811419964261)
                ·
                  refine ⟨339427828643777141243299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810281752766811419964261 339427828643777141243299)
                  ·
                    rfl

theorem cell21_1487325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1487325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487325 prefixEnd_1487325 := by exact prefixLift 1487325
  have htrace : WordTrace (prefixWord ++ tailWord_1487325) baseStart_1487325 baseEnd_1487325 := by
    simpa [prefixWord, tailWord_1487325, baseEnd_1487325] using wordTrace_append hprefix tailTrace_1487325
  have hstable : (prefixWord ++ tailWord_1487325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487325).length < 2 ^ (prefixWord ++ tailWord_1487325).sum := by decide
  have hdescent : baseEnd_1487325 < baseStart_1487325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487342 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_1487342 : Nat := 118140960795 + 1487342 * 2 ^ 59
def prefixEnd_1487342 : Nat := 4983230072969 + 3 ^ 40 * 1487342 * 2
def baseEnd_1487342 : Nat := 339431708275388889459931

theorem tailTrace_1487342 : CollatzResearch.WordTrace tailWord_1487342 prefixEnd_1487342 339431708275388889459931 := by
  unfold tailWord_1487342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780977422202678329415035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36165212918414284423546853 6780977422202678329415035)
  ·
    refine ⟨10171466133304017494122553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6780977422202678329415035 10171466133304017494122553)
    ·
      refine ⟨7628599599978013120591915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10171466133304017494122553 7628599599978013120591915)
      ·
        refine ⟨11442899399967019680887873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628599599978013120591915 11442899399967019680887873)
        ·
          refine ⟨8582174549975264760665905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11442899399967019680887873 8582174549975264760665905)
          ·
            refine ⟨6436630912481448570499429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582174549975264760665905 6436630912481448570499429)
            ·
              refine ⟨1206868296090271606968643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6436630912481448570499429 1206868296090271606968643)
              ·
                refine ⟨1810302444135407410452965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206868296090271606968643 1810302444135407410452965)
                ·
                  refine ⟨339431708275388889459931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810302444135407410452965 339431708275388889459931)
                  ·
                    rfl

theorem cell21_1487342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_1487342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487342 prefixEnd_1487342 := by exact prefixLift 1487342
  have htrace : WordTrace (prefixWord ++ tailWord_1487342) baseStart_1487342 baseEnd_1487342 := by
    simpa [prefixWord, tailWord_1487342, baseEnd_1487342] using wordTrace_append hprefix tailTrace_1487342
  have hstable : (prefixWord ++ tailWord_1487342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487342).length < 2 ^ (prefixWord ++ tailWord_1487342).sum := by decide
  have hdescent : baseEnd_1487342 < baseStart_1487342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487353 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1487353 : Nat := 118140960795 + 1487353 * 2 ^ 59
def prefixEnd_1487353 : Nat := 4983230072969 + 3 ^ 40 * 1487353 * 2
def baseEnd_1487353 : Nat := 339434218625255314776575

theorem tailTrace_1487353 : CollatzResearch.WordTrace tailWord_1487353 prefixEnd_1487353 339434218625255314776575 := by
  unfold tailWord_1487353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54248220580581575513970713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36165480387054383675980475 54248220580581575513970713)
  ·
    refine ⟨40686165435436181635478035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54248220580581575513970713 40686165435436181635478035)
    ·
      refine ⟨61029248153154272453217053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40686165435436181635478035 61029248153154272453217053)
      ·
        refine ⟨22885968057432852169956395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61029248153154272453217053 22885968057432852169956395)
        ·
          refine ⟨34328952086149278254934593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22885968057432852169956395 34328952086149278254934593)
          ·
            refine ⟨25746714064611958691200945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34328952086149278254934593 25746714064611958691200945)
            ·
              refine ⟨19310035548458969018400709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25746714064611958691200945 19310035548458969018400709)
              ·
                refine ⟨3620631665336056690950133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19310035548458969018400709 3620631665336056690950133)
                ·
                  refine ⟨339434218625255314776575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620631665336056690950133 339434218625255314776575)
                  ·
                    rfl

theorem cell21_1487353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1487353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487353 prefixEnd_1487353 := by exact prefixLift 1487353
  have htrace : WordTrace (prefixWord ++ tailWord_1487353) baseStart_1487353 baseEnd_1487353 := by
    simpa [prefixWord, tailWord_1487353, baseEnd_1487353] using wordTrace_append hprefix tailTrace_1487353
  have hstable : (prefixWord ++ tailWord_1487353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487353).length < 2 ^ (prefixWord ++ tailWord_1487353).sum := by decide
  have hdescent : baseEnd_1487353 < baseStart_1487353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487415 : List Nat := [1, 1, 3, 1, 2, 3, 5, 5]
def baseStart_1487415 : Nat := 118140960795 + 1487415 * 2 ^ 59
def prefixEnd_1487415 : Nat := 4983230072969 + 3 ^ 40 * 1487415 * 2
def baseEnd_1487415 : Nat := 113149455956652328247705

theorem tailTrace_1487415 : CollatzResearch.WordTrace tailWord_1487415 prefixEnd_1487415 113149455956652328247705 := by
  unfold tailWord_1487415
  simp only [CollatzResearch.WordTrace]
  refine ⟨54250481906356960102727699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36166987937571306735151799 54250481906356960102727699)
  ·
    refine ⟨81375722859535440154091549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54250481906356960102727699 81375722859535440154091549)
    ·
      refine ⟨30515896072325790057784331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81375722859535440154091549 30515896072325790057784331)
      ·
        refine ⟨45773844108488685086676497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30515896072325790057784331 45773844108488685086676497)
        ·
          refine ⟨34330383081366513815007373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45773844108488685086676497 34330383081366513815007373)
          ·
            refine ⟨12873893655512442680627765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34330383081366513815007373 12873893655512442680627765)
            ·
              refine ⟨1206927530204291501308853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12873893655512442680627765 1206927530204291501308853)
              ·
                refine ⟨113149455956652328247705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206927530204291501308853 113149455956652328247705)
                ·
                  rfl

theorem cell21_1487415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].length) (baseStart_1487415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487415 prefixEnd_1487415 := by exact prefixLift 1487415
  have htrace : WordTrace (prefixWord ++ tailWord_1487415) baseStart_1487415 baseEnd_1487415 := by
    simpa [prefixWord, tailWord_1487415, baseEnd_1487415] using wordTrace_append hprefix tailTrace_1487415
  have hstable : (prefixWord ++ tailWord_1487415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487415).length < 2 ^ (prefixWord ++ tailWord_1487415).sum := by decide
  have hdescent : baseEnd_1487415 < baseStart_1487415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487508 : List Nat := [2, 4, 2, 2, 1, 2, 2, 6]
def baseStart_1487508 : Nat := 118140960795 + 1487508 * 2 ^ 59
def prefixEnd_1487508 : Nat := 4983230072969 + 3 ^ 40 * 1487508 * 2
def baseEnd_1487508 : Nat := 113156530579003163230975

theorem tailTrace_1487508 : CollatzResearch.WordTrace tailWord_1487508 prefixEnd_1487508 113156530579003163230975 := by
  unfold tailWord_1487508
  simp only [CollatzResearch.WordTrace]
  refine ⟨27126936947510018492931589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36169249263346691323908785 27126936947510018492931589)
  ·
    refine ⟨5086300677658128467424673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27126936947510018492931589 5086300677658128467424673)
    ·
      refine ⟨3814725508243596350568505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086300677658128467424673 3814725508243596350568505)
      ·
        refine ⟨2861044131182697262926379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3814725508243596350568505 2861044131182697262926379)
        ·
          refine ⟨4291566196774045894389569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861044131182697262926379 4291566196774045894389569)
          ·
            refine ⟨3218674647580534420792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4291566196774045894389569 3218674647580534420792177)
            ·
              refine ⟨2414005985685400815594133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218674647580534420792177 2414005985685400815594133)
              ·
                refine ⟨113156530579003163230975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2414005985685400815594133 113156530579003163230975)
                ·
                  rfl

theorem cell21_1487508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_1487508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487508 prefixEnd_1487508 := by exact prefixLift 1487508
  have htrace : WordTrace (prefixWord ++ tailWord_1487508) baseStart_1487508 baseEnd_1487508 := by
    simpa [prefixWord, tailWord_1487508, baseEnd_1487508] using wordTrace_append hprefix tailTrace_1487508
  have hstable : (prefixWord ++ tailWord_1487508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487508).length < 2 ^ (prefixWord ++ tailWord_1487508).sum := by decide
  have hdescent : baseEnd_1487508 < baseStart_1487508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487556 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1487556 : Nat := 118140960795 + 1487556 * 2 ^ 59
def prefixEnd_1487556 : Nat := 4983230072969 + 3 ^ 40 * 1487556 * 2
def baseEnd_1487556 : Nat := 339480545990972072892827

theorem tailTrace_1487556 : CollatzResearch.WordTrace tailWord_1487556 prefixEnd_1487556 339480545990972072892827 := by
  unfold tailWord_1487556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127812299423070591805261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36170416399230760789073681 27127812299423070591805261)
  ·
    refine ⟨10172929612283651471926973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27127812299423070591805261 10172929612283651471926973)
    ·
      refine ⟨3814848604606369301972615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10172929612283651471926973 3814848604606369301972615)
      ·
        refine ⟨5722272906909553952958923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814848604606369301972615 5722272906909553952958923)
        ·
          refine ⟨8583409360364330929438385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722272906909553952958923 8583409360364330929438385)
          ·
            refine ⟨6437557020273248197078789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8583409360364330929438385 6437557020273248197078789)
            ·
              refine ⟨1207041941301234036952273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6437557020273248197078789 1207041941301234036952273)
              ·
                refine ⟨905281455975925527714205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207041941301234036952273 905281455975925527714205)
                ·
                  refine ⟨339480545990972072892827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905281455975925527714205 339480545990972072892827)
                  ·
                    rfl

theorem cell21_1487556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1487556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487556 prefixEnd_1487556 := by exact prefixLift 1487556
  have htrace : WordTrace (prefixWord ++ tailWord_1487556) baseStart_1487556 baseEnd_1487556 := by
    simpa [prefixWord, tailWord_1487556, baseEnd_1487556] using wordTrace_append hprefix tailTrace_1487556
  have hstable : (prefixWord ++ tailWord_1487556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487556).length < 2 ^ (prefixWord ++ tailWord_1487556).sum := by decide
  have hdescent : baseEnd_1487556 < baseStart_1487556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487595 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_1487595 : Nat := 118140960795 + 1487595 * 2 ^ 59
def prefixEnd_1487595 : Nat := 4983230072969 + 3 ^ 40 * 1487595 * 2
def baseEnd_1487595 : Nat := 339489446322316671742747

theorem tailTrace_1487595 : CollatzResearch.WordTrace tailWord_1487595 prefixEnd_1487595 339489446322316671742747 := by
  unfold tailWord_1487595
  simp only [CollatzResearch.WordTrace]
  refine ⟨54257047045704850844280239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36171364697136567229520159 54257047045704850844280239)
  ·
    refine ⟨81385570568557276266420359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54257047045704850844280239 81385570568557276266420359)
    ·
      refine ⟨122078355852835914399630539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81385570568557276266420359 122078355852835914399630539)
      ·
        refine ⟨183117533779253871599445809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122078355852835914399630539 183117533779253871599445809)
        ·
          refine ⟨137338150334440403699584357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183117533779253871599445809 137338150334440403699584357)
          ·
            refine ⟨25750903187707575693672067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137338150334440403699584357 25750903187707575693672067)
            ·
              refine ⟨38626354781561363540508101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25750903187707575693672067 38626354781561363540508101)
              ·
                refine ⟨7242441521542755663845269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38626354781561363540508101 7242441521542755663845269)
                ·
                  refine ⟨339489446322316671742747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242441521542755663845269 339489446322316671742747)
                  ·
                    rfl

theorem cell21_1487595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_1487595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487595 prefixEnd_1487595 := by exact prefixLift 1487595
  have htrace : WordTrace (prefixWord ++ tailWord_1487595) baseStart_1487595 baseEnd_1487595 := by
    simpa [prefixWord, tailWord_1487595, baseEnd_1487595] using wordTrace_append hprefix tailTrace_1487595
  have hstable : (prefixWord ++ tailWord_1487595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487595).length < 2 ^ (prefixWord ++ tailWord_1487595).sum := by decide
  have hdescent : baseEnd_1487595 < baseStart_1487595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487604 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1487604 : Nat := 118140960795 + 1487604 * 2 ^ 59
def prefixEnd_1487604 : Nat := 4983230072969 + 3 ^ 40 * 1487604 * 2
def baseEnd_1487604 : Nat := 339491500244934656092729

theorem tailTrace_1487604 : CollatzResearch.WordTrace tailWord_1487604 prefixEnd_1487604 339491500244934656092729 := by
  unfold tailWord_1487604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27128687651336122690678933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36171583535114830254238577 27128687651336122690678933)
  ·
    refine ⟨1271657233656380751125575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27128687651336122690678933 1271657233656380751125575)
    ·
      refine ⟨1907485850484571126688363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271657233656380751125575 1907485850484571126688363)
      ·
        refine ⟨2861228775726856690032545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907485850484571126688363 2861228775726856690032545)
        ·
          refine ⟨2145921581795142517524409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2861228775726856690032545 2145921581795142517524409)
          ·
            refine ⟨1609441186346356888143307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145921581795142517524409 1609441186346356888143307)
            ·
              refine ⟨2414161779519535332214961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609441186346356888143307 2414161779519535332214961)
              ·
                refine ⟨1810621334639651499161221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414161779519535332214961 1810621334639651499161221)
                ·
                  refine ⟨339491500244934656092729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810621334639651499161221 339491500244934656092729)
                  ·
                    rfl

theorem cell21_1487604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1487604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487604 prefixEnd_1487604 := by exact prefixLift 1487604
  have htrace : WordTrace (prefixWord ++ tailWord_1487604) baseStart_1487604 baseEnd_1487604 := by
    simpa [prefixWord, tailWord_1487604, baseEnd_1487604] using wordTrace_append hprefix tailTrace_1487604
  have hstable : (prefixWord ++ tailWord_1487604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487604).length < 2 ^ (prefixWord ++ tailWord_1487604).sum := by decide
  have hdescent : baseEnd_1487604 < baseStart_1487604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487612 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1487612 : Nat := 118140960795 + 1487612 * 2 ^ 59
def prefixEnd_1487612 : Nat := 4983230072969 + 3 ^ 40 * 1487612 * 2
def baseEnd_1487612 : Nat := 339493325953928419959379

theorem tailTrace_1487612 : CollatzResearch.WordTrace tailWord_1487612 prefixEnd_1487612 339493325953928419959379 := by
  unfold tailWord_1487612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27128833543321631373824545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36171778057762175165099393 27128833543321631373824545)
  ·
    refine ⟨20346625157491223530368409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27128833543321631373824545 20346625157491223530368409)
    ·
      refine ⟨15259968868118417647776307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20346625157491223530368409 15259968868118417647776307)
      ·
        refine ⟨22889953302177626471664461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259968868118417647776307 22889953302177626471664461)
        ·
          refine ⟨8583732488316609926874173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22889953302177626471664461 8583732488316609926874173)
          ·
            refine ⟨3218899683118728722577815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8583732488316609926874173 3218899683118728722577815)
            ·
              refine ⟨4828349524678093083866723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218899683118728722577815 4828349524678093083866723)
              ·
                refine ⟨7242524287017139625800085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828349524678093083866723 7242524287017139625800085)
                ·
                  refine ⟨339493325953928419959379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242524287017139625800085 339493325953928419959379)
                  ·
                    rfl

theorem cell21_1487612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1487612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487612 prefixEnd_1487612 := by exact prefixLift 1487612
  have htrace : WordTrace (prefixWord ++ tailWord_1487612) baseStart_1487612 baseEnd_1487612 := by
    simpa [prefixWord, tailWord_1487612, baseEnd_1487612] using wordTrace_append hprefix tailTrace_1487612
  have hstable : (prefixWord ++ tailWord_1487612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487612).length < 2 ^ (prefixWord ++ tailWord_1487612).sum := by decide
  have hdescent : baseEnd_1487612 < baseStart_1487612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487626 : List Nat := [3, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1487626 : Nat := 118140960795 + 1487626 * 2 ^ 59
def prefixEnd_1487626 : Nat := 4983230072969 + 3 ^ 40 * 1487626 * 2
def baseEnd_1487626 : Nat := 113165506981555835575339

theorem tailTrace_1487626 : CollatzResearch.WordTrace tailWord_1487626 prefixEnd_1487626 113165506981555835575339 := by
  unfold tailWord_1487626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564544427148135784664683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36172118472395028759105821 13564544427148135784664683)
  ·
    refine ⟨20346816640722203676997025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13564544427148135784664683 20346816640722203676997025)
    ·
      refine ⟨15260112480541652757747769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20346816640722203676997025 15260112480541652757747769)
      ·
        refine ⟨11445084360406239568310827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15260112480541652757747769 11445084360406239568310827)
        ·
          refine ⟨17167626540609359352466241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11445084360406239568310827 17167626540609359352466241)
          ·
            refine ⟨12875719905457019514349681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17167626540609359352466241 12875719905457019514349681)
            ·
              refine ⟨9656789929092764635762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12875719905457019514349681 9656789929092764635762261)
              ·
                refine ⟨113165506981555835575339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9656789929092764635762261 113165506981555835575339)
                ·
                  rfl

theorem cell21_1487626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1487626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487626 prefixEnd_1487626 := by exact prefixLift 1487626
  have htrace : WordTrace (prefixWord ++ tailWord_1487626) baseStart_1487626 baseEnd_1487626 := by
    simpa [prefixWord, tailWord_1487626, baseEnd_1487626] using wordTrace_append hprefix tailTrace_1487626
  have hstable : (prefixWord ++ tailWord_1487626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487626).length < 2 ^ (prefixWord ++ tailWord_1487626).sum := by decide
  have hdescent : baseEnd_1487626 < baseStart_1487626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487671 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_1487671 : Nat := 118140960795 + 1487671 * 2 ^ 59
def prefixEnd_1487671 : Nat := 4983230072969 + 3 ^ 40 * 1487671 * 2
def baseEnd_1487671 : Nat := 339506790557757428475925

theorem tailTrace_1487671 : CollatzResearch.WordTrace tailWord_1487671 prefixEnd_1487671 339506790557757428475925 := by
  unfold tailWord_1487671
  simp only [CollatzResearch.WordTrace]
  refine ⟨54259818993429515824046867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36173212662286343882697911 54259818993429515824046867)
  ·
    refine ⟨81389728490144273736070301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54259818993429515824046867 81389728490144273736070301)
    ·
      refine ⟨30521148183804102651026363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81389728490144273736070301 30521148183804102651026363)
      ·
        refine ⟨45781722275706153976539545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30521148183804102651026363 45781722275706153976539545)
        ·
          refine ⟨34336291706779615482404659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45781722275706153976539545 34336291706779615482404659)
          ·
            refine ⟨51504437560169423223606989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34336291706779615482404659 51504437560169423223606989)
            ·
              refine ⟨19314164085063533708852621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51504437560169423223606989 19314164085063533708852621)
              ·
                refine ⟨7242811531898825140819733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19314164085063533708852621 7242811531898825140819733)
                ·
                  refine ⟨339506790557757428475925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7242811531898825140819733 339506790557757428475925)
                  ·
                    rfl

theorem cell21_1487671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_1487671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487671 prefixEnd_1487671 := by exact prefixLift 1487671
  have htrace : WordTrace (prefixWord ++ tailWord_1487671) baseStart_1487671 baseEnd_1487671 := by
    simpa [prefixWord, tailWord_1487671, baseEnd_1487671] using wordTrace_append hprefix tailTrace_1487671
  have hstable : (prefixWord ++ tailWord_1487671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487671).length < 2 ^ (prefixWord ++ tailWord_1487671).sum := by decide
  have hdescent : baseEnd_1487671 < baseStart_1487671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487688 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1487688 : Nat := 118140960795 + 1487688 * 2 ^ 59
def prefixEnd_1487688 : Nat := 4983230072969 + 3 ^ 40 * 1487688 * 2
def baseEnd_1487688 : Nat := 339510670189369176692557

theorem tailTrace_1487688 : CollatzResearch.WordTrace tailWord_1487688 prefixEnd_1487688 339510670189369176692557 := by
  unfold tailWord_1487688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130219517183963863707859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36173626022911951818277145 27130219517183963863707859)
  ·
    refine ⟨40695329275775945795561789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27130219517183963863707859 40695329275775945795561789)
    ·
      refine ⟨15260748478415979673335671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40695329275775945795561789 15260748478415979673335671)
      ·
        refine ⟨22891122717623969510003507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15260748478415979673335671 22891122717623969510003507)
        ·
          refine ⟨34336684076435954265005261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22891122717623969510003507 34336684076435954265005261)
          ·
            refine ⟨12876256528663482849376973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34336684076435954265005261 12876256528663482849376973)
            ·
              refine ⟨4828596198248806068516365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12876256528663482849376973 4828596198248806068516365)
              ·
                refine ⟨1810723574343302275693637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4828596198248806068516365 1810723574343302275693637)
                ·
                  refine ⟨339510670189369176692557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810723574343302275693637 339510670189369176692557)
                  ·
                    rfl

theorem cell21_1487688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1487688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487688 prefixEnd_1487688 := by exact prefixLift 1487688
  have htrace : WordTrace (prefixWord ++ tailWord_1487688) baseStart_1487688 baseEnd_1487688 := by
    simpa [prefixWord, tailWord_1487688, baseEnd_1487688] using wordTrace_append hprefix tailTrace_1487688
  have hstable : (prefixWord ++ tailWord_1487688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487688).length < 2 ^ (prefixWord ++ tailWord_1487688).sum := by decide
  have hdescent : baseEnd_1487688 < baseStart_1487688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487764 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1487764 : Nat := 118140960795 + 1487764 * 2 ^ 59
def prefixEnd_1487764 : Nat := 4983230072969 + 3 ^ 40 * 1487764 * 2
def baseEnd_1487764 : Nat := 339528014424809933425735

theorem tailTrace_1487764 : CollatzResearch.WordTrace tailWord_1487764 prefixEnd_1487764 339528014424809933425735 := by
  unfold tailWord_1487764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131605491046296353591173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36175473988061728471454897 27131605491046296353591173)
  ·
    refine ⟨5087176029571180566298345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27131605491046296353591173 5087176029571180566298345)
    ·
      refine ⟨3815382022178385424723759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5087176029571180566298345 3815382022178385424723759)
      ·
        refine ⟨5723073033267578137085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815382022178385424723759 5723073033267578137085639)
        ·
          refine ⟨8584609549901367205628459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723073033267578137085639 8584609549901367205628459)
          ·
            refine ⟨12876914324852050808442689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584609549901367205628459 12876914324852050808442689)
            ·
              refine ⟨9657685743639038106332017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12876914324852050808442689 9657685743639038106332017)
              ·
                refine ⟨7243264307729278579749013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657685743639038106332017 7243264307729278579749013)
                ·
                  refine ⟨339528014424809933425735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7243264307729278579749013 339528014424809933425735)
                  ·
                    rfl

theorem cell21_1487764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1487764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487764 prefixEnd_1487764 := by exact prefixLift 1487764
  have htrace : WordTrace (prefixWord ++ tailWord_1487764) baseStart_1487764 baseEnd_1487764 := by
    simpa [prefixWord, tailWord_1487764, baseEnd_1487764] using wordTrace_append hprefix tailTrace_1487764
  have hstable : (prefixWord ++ tailWord_1487764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487764).length < 2 ^ (prefixWord ++ tailWord_1487764).sum := by decide
  have hdescent : baseEnd_1487764 < baseStart_1487764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487812 : List Nat := [2, 3, 3, 3, 1, 1, 1, 7]
def baseStart_1487812 : Nat := 118140960795 + 1487812 * 2 ^ 59
def prefixEnd_1487812 : Nat := 4983230072969 + 3 ^ 40 * 1487812 * 2
def baseEnd_1487812 : Nat := 113179656226257505541879

theorem tailTrace_1487812 : CollatzResearch.WordTrace tailWord_1487812 prefixEnd_1487812 113179656226257505541879 := by
  unfold tailWord_1487812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27132480842959348452464845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36176641123945797936619793 27132480842959348452464845)
  ·
    refine ⟨10174680316109755669674317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27132480842959348452464845 10174680316109755669674317)
    ·
      refine ⟨3815505118541158376127869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10174680316109755669674317 3815505118541158376127869)
      ·
        refine ⟨1430814419452934391047951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3815505118541158376127869 1430814419452934391047951)
        ·
          refine ⟨2146221629179401586571927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430814419452934391047951 2146221629179401586571927)
          ·
            refine ⟨3219332443769102379857891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146221629179401586571927 3219332443769102379857891)
            ·
              refine ⟨4828998665653653569786837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219332443769102379857891 4828998665653653569786837)
              ·
                refine ⟨113179656226257505541879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4828998665653653569786837 113179656226257505541879)
                ·
                  rfl

theorem cell21_1487812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_1487812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487812 prefixEnd_1487812 := by exact prefixLift 1487812
  have htrace : WordTrace (prefixWord ++ tailWord_1487812) baseStart_1487812 baseEnd_1487812 := by
    simpa [prefixWord, tailWord_1487812, baseEnd_1487812] using wordTrace_append hprefix tailTrace_1487812
  have hstable : (prefixWord ++ tailWord_1487812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487812).length < 2 ^ (prefixWord ++ tailWord_1487812).sum := by decide
  have hdescent : baseEnd_1487812 < baseStart_1487812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487823 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_1487823 : Nat := 118140960795 + 1487823 * 2 ^ 59
def prefixEnd_1487823 : Nat := 4983230072969 + 3 ^ 40 * 1487823 * 2
def baseEnd_1487823 : Nat := 339541479028638941942281

theorem tailTrace_1487823 : CollatzResearch.WordTrace tailWord_1487823 prefixEnd_1487823 339541479028638941942281 := by
  unfold tailWord_1487823
  simp only [CollatzResearch.WordTrace]
  refine ⟨54265362888878845783580123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36176908592585897189053415 54265362888878845783580123)
  ·
    refine ⟨81398044333318268675370185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54265362888878845783580123 81398044333318268675370185)
    ·
      refine ⟨61048533249988701506527639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81398044333318268675370185 61048533249988701506527639)
      ·
        refine ⟨91572799874983052259791459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61048533249988701506527639 91572799874983052259791459)
        ·
          refine ⟨137359199812474578389687189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91572799874983052259791459 137359199812474578389687189)
          ·
            refine ⟨6438712491209745862016587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137359199812474578389687189 6438712491209745862016587)
            ·
              refine ⟨9658068736814618793024881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438712491209745862016587 9658068736814618793024881)
              ·
                refine ⟨7243551552610964094768661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9658068736814618793024881 7243551552610964094768661)
                ·
                  refine ⟨339541479028638941942281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7243551552610964094768661 339541479028638941942281)
                  ·
                    rfl

theorem cell21_1487823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_1487823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487823 prefixEnd_1487823 := by exact prefixLift 1487823
  have htrace : WordTrace (prefixWord ++ tailWord_1487823) baseStart_1487823 baseEnd_1487823 := by
    simpa [prefixWord, tailWord_1487823, baseEnd_1487823] using wordTrace_append hprefix tailTrace_1487823
  have hstable : (prefixWord ++ tailWord_1487823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487823).length < 2 ^ (prefixWord ++ tailWord_1487823).sum := by decide
  have hdescent : baseEnd_1487823 < baseStart_1487823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487843 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 3]
def baseStart_1487843 : Nat := 118140960795 + 1487843 * 2 ^ 59
def prefixEnd_1487843 : Nat := 4983230072969 + 3 ^ 40 * 1487843 * 2
def baseEnd_1487843 : Nat := 339546043301123351608907

theorem tailTrace_1487843 : CollatzResearch.WordTrace tailWord_1487843 prefixEnd_1487843 339546043301123351608907 := by
  unfold tailWord_1487843
  simp only [CollatzResearch.WordTrace]
  refine ⟨54266092348806389199308183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36177394899204259466205455 54266092348806389199308183)
  ·
    refine ⟨81399138523209583798962275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54266092348806389199308183 81399138523209583798962275)
    ·
      refine ⟨122098707784814375698443413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81399138523209583798962275 122098707784814375698443413)
      ·
        refine ⟨5723376927413173860864535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122098707784814375698443413 5723376927413173860864535)
        ·
          refine ⟨8585065391119760791296803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723376927413173860864535 8585065391119760791296803)
          ·
            refine ⟨12877598086679641186945205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585065391119760791296803 12877598086679641186945205)
            ·
              refine ⟨1207274820626216361276113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12877598086679641186945205 1207274820626216361276113)
              ·
                refine ⟨905456115469662270957085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207274820626216361276113 905456115469662270957085)
                ·
                  refine ⟨339546043301123351608907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905456115469662270957085 339546043301123351608907)
                  ·
                    rfl

theorem cell21_1487843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 3].length) (baseStart_1487843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487843 prefixEnd_1487843 := by exact prefixLift 1487843
  have htrace : WordTrace (prefixWord ++ tailWord_1487843) baseStart_1487843 baseEnd_1487843 := by
    simpa [prefixWord, tailWord_1487843, baseEnd_1487843] using wordTrace_append hprefix tailTrace_1487843
  have hstable : (prefixWord ++ tailWord_1487843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487843).length < 2 ^ (prefixWord ++ tailWord_1487843).sum := by decide
  have hdescent : baseEnd_1487843 < baseStart_1487843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487857 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 4]
def baseStart_1487857 : Nat := 118140960795 + 1487857 * 2 ^ 59
def prefixEnd_1487857 : Nat := 4983230072969 + 3 ^ 40 * 1487857 * 2
def baseEnd_1487857 : Nat := 339549238291862438375545

theorem tailTrace_1487857 : CollatzResearch.WordTrace tailWord_1487857 prefixEnd_1487857 339549238291862438375545 := by
  unfold tailWord_1487857
  simp only [CollatzResearch.WordTrace]
  refine ⟨54266602970755669590317825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36177735313837113060211883 54266602970755669590317825)
  ·
    refine ⟨40699952228066752192738369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54266602970755669590317825 40699952228066752192738369)
    ·
      refine ⟨30524964171050064144553777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40699952228066752192738369 30524964171050064144553777)
      ·
        refine ⟨22893723128287548108415333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30524964171050064144553777 22893723128287548108415333)
        ·
          refine ⟨4292573086553915270327875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22893723128287548108415333 4292573086553915270327875)
          ·
            refine ⟨6438859629830872905491813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292573086553915270327875 6438859629830872905491813)
            ·
              refine ⟨1207286180593288669779715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6438859629830872905491813 1207286180593288669779715)
              ·
                refine ⟨1810929270889933004669573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207286180593288669779715 1810929270889933004669573)
                ·
                  refine ⟨339549238291862438375545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810929270889933004669573 339549238291862438375545)
                  ·
                    rfl

theorem cell21_1487857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_1487857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487857 prefixEnd_1487857 := by exact prefixLift 1487857
  have htrace : WordTrace (prefixWord ++ tailWord_1487857) baseStart_1487857 baseEnd_1487857 := by
    simpa [prefixWord, tailWord_1487857, baseEnd_1487857] using wordTrace_append hprefix tailTrace_1487857
  have hstable : (prefixWord ++ tailWord_1487857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487857).length < 2 ^ (prefixWord ++ tailWord_1487857).sum := by decide
  have hdescent : baseEnd_1487857 < baseStart_1487857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487944 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_1487944 : Nat := 118140960795 + 1487944 * 2 ^ 59
def prefixEnd_1487944 : Nat := 4983230072969 + 3 ^ 40 * 1487944 * 2
def baseEnd_1487944 : Nat := 339569092877169620425367

theorem tailTrace_1487944 : CollatzResearch.WordTrace tailWord_1487944 prefixEnd_1487944 339569092877169620425367 := by
  unfold tailWord_1487944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134888060720241724367443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36179850747626988965823257 27134888060720241724367443)
  ·
    refine ⟨40702332091080362586551165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134888060720241724367443 40702332091080362586551165)
    ·
      refine ⟨15263374534155135969956687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40702332091080362586551165 15263374534155135969956687)
      ·
        refine ⟨22895061801232703954935031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15263374534155135969956687 22895061801232703954935031)
        ·
          refine ⟨34342592701849055932402547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22895061801232703954935031 34342592701849055932402547)
          ·
            refine ⟨51513889052773583898603821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34342592701849055932402547 51513889052773583898603821)
            ·
              refine ⟨19317708394790093961976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51513889052773583898603821 19317708394790093961976433)
              ·
                refine ⟨14488281296092570471482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19317708394790093961976433 14488281296092570471482325)
                ·
                  refine ⟨339569092877169620425367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14488281296092570471482325 339569092877169620425367)
                  ·
                    rfl

theorem cell21_1487944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_1487944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487944 prefixEnd_1487944 := by exact prefixLift 1487944
  have htrace : WordTrace (prefixWord ++ tailWord_1487944) baseStart_1487944 baseEnd_1487944 := by
    simpa [prefixWord, tailWord_1487944, baseEnd_1487944] using wordTrace_append hprefix tailTrace_1487944
  have hstable : (prefixWord ++ tailWord_1487944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487944).length < 2 ^ (prefixWord ++ tailWord_1487944).sum := by decide
  have hdescent : baseEnd_1487944 < baseStart_1487944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487998 : List Nat := [4, 2, 4, 1, 2, 1, 7]
def baseStart_1487998 : Nat := 118140960795 + 1487998 * 2 ^ 59
def prefixEnd_1487998 : Nat := 4983230072969 + 3 ^ 40 * 1487998 * 2
def baseEnd_1487998 : Nat := 37731268490319725169473

theorem tailTrace_1487998 : CollatzResearch.WordTrace tailWord_1487998 prefixEnd_1487998 37731268490319725169473 := by
  unfold tailWord_1487998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783968207905606333900081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36181163775496567114133765 6783968207905606333900081)
  ·
    refine ⟨5087976155929204750425061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6783968207905606333900081 5087976155929204750425061)
    ·
      refine ⟨953995529236725890704699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5087976155929204750425061 953995529236725890704699)
      ·
        refine ⟨1430993293855088836057049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953995529236725890704699 1430993293855088836057049)
        ·
          refine ⟨1073244970391316627042787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430993293855088836057049 1073244970391316627042787)
          ·
            refine ⟨1609867455586974940564181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073244970391316627042787 1609867455586974940564181)
            ·
              refine ⟨37731268490319725169473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1609867455586974940564181 37731268490319725169473)
              ·
                rfl

theorem cell21_1487998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 7].length) (baseStart_1487998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1487998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1487998 prefixEnd_1487998 := by exact prefixLift 1487998
  have htrace : WordTrace (prefixWord ++ tailWord_1487998) baseStart_1487998 baseEnd_1487998 := by
    simpa [prefixWord, tailWord_1487998, baseEnd_1487998] using wordTrace_append hprefix tailTrace_1487998
  have hstable : (prefixWord ++ tailWord_1487998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487998).length < 2 ^ (prefixWord ++ tailWord_1487998).sum := by decide
  have hdescent : baseEnd_1487998 < baseStart_1487998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488026 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_1488026 : Nat := 118140960795 + 1488026 * 2 ^ 59
def prefixEnd_1488026 : Nat := 4983230072969 + 3 ^ 40 * 1488026 * 2
def baseEnd_1488026 : Nat := 339587806394355700058533

theorem tailTrace_1488026 : CollatzResearch.WordTrace tailWord_1488026 prefixEnd_1488026 339587806394355700058533 := by
  unfold tailWord_1488026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568191726785852863304983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36181844604762274302146621 13568191726785852863304983)
  ·
    refine ⟨20352287590178779294957475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13568191726785852863304983 20352287590178779294957475)
    ·
      refine ⟨30528431385268168942436213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20352287590178779294957475 30528431385268168942436213)
      ·
        refine ⟨2862040442368890838353395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30528431385268168942436213 2862040442368890838353395)
        ·
          refine ⟨4293060663553336257530093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862040442368890838353395 4293060663553336257530093)
          ·
            refine ⟨1609897748832501096573785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4293060663553336257530093 1609897748832501096573785)
            ·
              refine ⟨1207423311624375822430339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609897748832501096573785 1207423311624375822430339)
              ·
                refine ⟨1811134967436563733645509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207423311624375822430339 1811134967436563733645509)
                ·
                  refine ⟨339587806394355700058533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811134967436563733645509 339587806394355700058533)
                  ·
                    rfl

theorem cell21_1488026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_1488026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488026 prefixEnd_1488026 := by exact prefixLift 1488026
  have htrace : WordTrace (prefixWord ++ tailWord_1488026) baseStart_1488026 baseEnd_1488026 := by
    simpa [prefixWord, tailWord_1488026, baseEnd_1488026] using wordTrace_append hprefix tailTrace_1488026
  have hstable : (prefixWord ++ tailWord_1488026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488026).length < 2 ^ (prefixWord ++ tailWord_1488026).sum := by decide
  have hdescent : baseEnd_1488026 < baseStart_1488026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488096 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1488096 : Nat := 118140960795 + 1488096 * 2 ^ 59
def prefixEnd_1488096 : Nat := 4983230072969 + 3 ^ 40 * 1488096 * 2
def baseEnd_1488096 : Nat := 339603781348051133891723

theorem tailTrace_1488096 : CollatzResearch.WordTrace tailWord_1488096 prefixEnd_1488096 339603781348051133891723 := by
  unfold tailWord_1488096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27137660008444906704134071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36183546677926542272178761 27137660008444906704134071)
  ·
    refine ⟨40706490012667360056201107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27137660008444906704134071 40706490012667360056201107)
    ·
      refine ⟨61059735019001040084301661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40706490012667360056201107 61059735019001040084301661)
      ·
        refine ⟨22897400632125390031613123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61059735019001040084301661 22897400632125390031613123)
        ·
          refine ⟨34346100948188085047419685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22897400632125390031613123 34346100948188085047419685)
          ·
            refine ⟨6439893927785265946391191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34346100948188085047419685 6439893927785265946391191)
            ·
              refine ⟨9659840891677898919586787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439893927785265946391191 9659840891677898919586787)
              ·
                refine ⟨14489761337516848379380181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9659840891677898919586787 14489761337516848379380181)
                ·
                  refine ⟨339603781348051133891723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14489761337516848379380181 339603781348051133891723)
                  ·
                    rfl

theorem cell21_1488096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1488096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488096 prefixEnd_1488096 := by exact prefixLift 1488096
  have htrace : WordTrace (prefixWord ++ tailWord_1488096) baseStart_1488096 baseEnd_1488096 := by
    simpa [prefixWord, tailWord_1488096, baseEnd_1488096] using wordTrace_append hprefix tailTrace_1488096
  have hstable : (prefixWord ++ tailWord_1488096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488096).length < 2 ^ (prefixWord ++ tailWord_1488096).sum := by decide
  have hdescent : baseEnd_1488096 < baseStart_1488096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488127 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_1488127 : Nat := 118140960795 + 1488127 * 2 ^ 59
def prefixEnd_1488127 : Nat := 4983230072969 + 3 ^ 40 * 1488127 * 2
def baseEnd_1488127 : Nat := 339610855970401968874993

theorem tailTrace_1488127 : CollatzResearch.WordTrace tailWord_1488127 prefixEnd_1488127 339610855970401968874993 := by
  unfold tailWord_1488127
  simp only [CollatzResearch.WordTrace]
  refine ⟨54276450679777505702646635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36184300453185003801764423 54276450679777505702646635)
  ·
    refine ⟨81414676019666258553969953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54276450679777505702646635 81414676019666258553969953)
    ·
      refine ⟨61061007014749693915477465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81414676019666258553969953 61061007014749693915477465)
      ·
        refine ⟨45795755261062270436608099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61061007014749693915477465 45795755261062270436608099)
        ·
          refine ⟨68693632891593405654912149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45795755261062270436608099 68693632891593405654912149)
          ·
            refine ⟨3220014041793440890074007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68693632891593405654912149 3220014041793440890074007)
            ·
              refine ⟨4830021062690161335111011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220014041793440890074007 4830021062690161335111011)
              ·
                refine ⟨7245031594035242002666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830021062690161335111011 7245031594035242002666517)
                ·
                  refine ⟨339610855970401968874993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7245031594035242002666517 339610855970401968874993)
                  ·
                    rfl

theorem cell21_1488127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_1488127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488127 prefixEnd_1488127 := by exact prefixLift 1488127
  have htrace : WordTrace (prefixWord ++ tailWord_1488127) baseStart_1488127 baseEnd_1488127 := by
    simpa [prefixWord, tailWord_1488127, baseEnd_1488127] using wordTrace_append hprefix tailTrace_1488127
  have hstable : (prefixWord ++ tailWord_1488127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488127).length < 2 ^ (prefixWord ++ tailWord_1488127).sum := by decide
  have hdescent : baseEnd_1488127 < baseStart_1488127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488217 : List Nat := [1, 2, 1, 2, 2, 2, 4, 7]
def baseStart_1488217 : Nat := 118140960795 + 1488217 * 2 ^ 59
def prefixEnd_1488217 : Nat := 4983230072969 + 3 ^ 40 * 1488217 * 2
def baseEnd_1488217 : Nat := 113210465065527270791603

theorem tailTrace_1488217 : CollatzResearch.WordTrace tailWord_1488217 prefixEnd_1488217 113210465065527270791603 := by
  unfold tailWord_1488217
  simp only [CollatzResearch.WordTrace]
  refine ⟨54279733249451451073422905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36186488832967634048948603 54279733249451451073422905)
  ·
    refine ⟨40709799937088588305067179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54279733249451451073422905 40709799937088588305067179)
    ·
      refine ⟨61064699905632882457600769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40709799937088588305067179 61064699905632882457600769)
      ·
        refine ⟨45798524929224661843200577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61064699905632882457600769 45798524929224661843200577)
        ·
          refine ⟨34348893696918496382400433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45798524929224661843200577 34348893696918496382400433)
          ·
            refine ⟨25761670272688872286800325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34348893696918496382400433 25761670272688872286800325)
            ·
              refine ⟨4830313176129163553775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25761670272688872286800325 4830313176129163553775061)
              ·
                refine ⟨113210465065527270791603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4830313176129163553775061 113210465065527270791603)
                ·
                  rfl

theorem cell21_1488217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_1488217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488217 prefixEnd_1488217 := by exact prefixLift 1488217
  have htrace : WordTrace (prefixWord ++ tailWord_1488217) baseStart_1488217 baseEnd_1488217 := by
    simpa [prefixWord, tailWord_1488217, baseEnd_1488217] using wordTrace_append hprefix tailTrace_1488217
  have hstable : (prefixWord ++ tailWord_1488217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488217).length < 2 ^ (prefixWord ++ tailWord_1488217).sum := by decide
  have hdescent : baseEnd_1488217 < baseStart_1488217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488234 : List Nat := [3, 1, 3, 3, 2, 9]
def baseStart_1488234 : Nat := 118140960795 + 1488234 * 2 ^ 59
def prefixEnd_1488234 : Nat := 4983230072969 + 3 ^ 40 * 1488234 * 2
def baseEnd_1488234 : Nat := 12579084252896057799683

theorem tailTrace_1488234 : CollatzResearch.WordTrace tailWord_1488234 prefixEnd_1488234 12579084252896057799683 := by
  unfold tailWord_1488234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570088322597465744197939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36186902193593241984527837 13570088322597465744197939)
  ·
    refine ⟨20355132483896198616296909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13570088322597465744197939 20355132483896198616296909)
    ·
      refine ⟨7633174681461074481111341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20355132483896198616296909 7633174681461074481111341)
      ·
        refine ⟨2862440505547902930416753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7633174681461074481111341 2862440505547902930416753)
        ·
          refine ⟨2146830379160927197812565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862440505547902930416753 2146830379160927197812565)
          ·
            refine ⟨12579084252896057799683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2146830379160927197812565 12579084252896057799683)
            ·
              rfl

theorem cell21_1488234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 9].length) (baseStart_1488234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488234 prefixEnd_1488234 := by exact prefixLift 1488234
  have htrace : WordTrace (prefixWord ++ tailWord_1488234) baseStart_1488234 baseEnd_1488234 := by
    simpa [prefixWord, tailWord_1488234, baseEnd_1488234] using wordTrace_append hprefix tailTrace_1488234
  have hstable : (prefixWord ++ tailWord_1488234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488234).length < 2 ^ (prefixWord ++ tailWord_1488234).sum := by decide
  have hdescent : baseEnd_1488234 < baseStart_1488234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488265 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_1488265 : Nat := 118140960795 + 1488265 * 2 ^ 59
def prefixEnd_1488265 : Nat := 4983230072969 + 3 ^ 40 * 1488265 * 2
def baseEnd_1488265 : Nat := 339642349450544395574711

theorem tailTrace_1488265 : CollatzResearch.WordTrace tailWord_1488265 prefixEnd_1488265 339642349450544395574711 := by
  unfold tailWord_1488265
  simp only [CollatzResearch.WordTrace]
  refine ⟨54281483953277555271170249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36187655968851703514113499 54281483953277555271170249)
  ·
    refine ⟨40711112964958166453377687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54281483953277555271170249 40711112964958166453377687)
    ·
      refine ⟨61066669447437249680066531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40711112964958166453377687 61066669447437249680066531)
      ·
        refine ⟨91600004171155874520099797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61066669447437249680066531 91600004171155874520099797)
        ·
          refine ⟨2146875097761465809064839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91600004171155874520099797 2146875097761465809064839)
          ·
            refine ⟨3220312646642198713597259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146875097761465809064839 3220312646642198713597259)
            ·
              refine ⟨4830468969963298070395889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220312646642198713597259 4830468969963298070395889)
              ·
                refine ⟨3622851727472473552796917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830468969963298070395889 3622851727472473552796917)
                ·
                  refine ⟨339642349450544395574711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3622851727472473552796917 339642349450544395574711)
                  ·
                    rfl

theorem cell21_1488265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_1488265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488265 prefixEnd_1488265 := by exact prefixLift 1488265
  have htrace : WordTrace (prefixWord ++ tailWord_1488265) baseStart_1488265 baseEnd_1488265 := by
    simpa [prefixWord, tailWord_1488265, baseEnd_1488265] using wordTrace_append hprefix tailTrace_1488265
  have hstable : (prefixWord ++ tailWord_1488265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488265).length < 2 ^ (prefixWord ++ tailWord_1488265).sum := by decide
  have hdescent : baseEnd_1488265 < baseStart_1488265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488282 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1488282 : Nat := 118140960795 + 1488282 * 2 ^ 59
def prefixEnd_1488282 : Nat := 4983230072969 + 3 ^ 40 * 1488282 * 2
def baseEnd_1488282 : Nat := 339646229082156143791343

theorem tailTrace_1488282 : CollatzResearch.WordTrace tailWord_1488282 prefixEnd_1488282 339646229082156143791343 := by
  unfold tailWord_1488282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570525998553991793634775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36188069329477311449692733 13570525998553991793634775)
  ·
    refine ⟨20355788997830987690452163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13570525998553991793634775 20355788997830987690452163)
    ·
      refine ⟨30533683496746481535678245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20355788997830987690452163 30533683496746481535678245)
      ·
        refine ⟨5725065655639965287939671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30533683496746481535678245 5725065655639965287939671)
        ·
          refine ⟨8587598483459947931909507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725065655639965287939671 8587598483459947931909507)
          ·
            refine ⟨12881397725189921897864261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587598483459947931909507 12881397725189921897864261)
            ·
              refine ⟨2415262073473110355849549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12881397725189921897864261 2415262073473110355849549)
              ·
                refine ⟨905723277552416383443581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2415262073473110355849549 905723277552416383443581)
                ·
                  refine ⟨339646229082156143791343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905723277552416383443581 339646229082156143791343)
                  ·
                    rfl

theorem cell21_1488282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1488282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488282 prefixEnd_1488282 := by exact prefixLift 1488282
  have htrace : WordTrace (prefixWord ++ tailWord_1488282) baseStart_1488282 baseEnd_1488282 := by
    simpa [prefixWord, tailWord_1488282, baseEnd_1488282] using wordTrace_append hprefix tailTrace_1488282
  have hstable : (prefixWord ++ tailWord_1488282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488282).length < 2 ^ (prefixWord ++ tailWord_1488282).sum := by decide
  have hdescent : baseEnd_1488282 < baseStart_1488282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488313 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 4]
def baseStart_1488313 : Nat := 118140960795 + 1488313 * 2 ^ 59
def prefixEnd_1488313 : Nat := 4983230072969 + 3 ^ 40 * 1488313 * 2
def baseEnd_1488313 : Nat := 339653303704506978774613

theorem tailTrace_1488313 : CollatzResearch.WordTrace tailWord_1488313 prefixEnd_1488313 339653303704506978774613 := by
  unfold tailWord_1488313
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283234657103659468917593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36188823104735772979278395 54283234657103659468917593)
  ·
    refine ⟨40712425992827744601688195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54283234657103659468917593 40712425992827744601688195)
    ·
      refine ⟨61068638989241616902532293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40712425992827744601688195 61068638989241616902532293)
      ·
        refine ⟨11450369810482803169224805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61068638989241616902532293 11450369810482803169224805)
        ·
          refine ⟨2146944339465525594229651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11450369810482803169224805 2146944339465525594229651)
          ·
            refine ⟨3220416509198288391344477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146944339465525594229651 3220416509198288391344477)
            ·
              refine ⟨1207656190949358146754179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3220416509198288391344477 1207656190949358146754179)
              ·
                refine ⟨1811484286424037220131269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207656190949358146754179 1811484286424037220131269)
                ·
                  refine ⟨339653303704506978774613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811484286424037220131269 339653303704506978774613)
                  ·
                    rfl

theorem cell21_1488313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_1488313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488313 prefixEnd_1488313 := by exact prefixLift 1488313
  have htrace : WordTrace (prefixWord ++ tailWord_1488313) baseStart_1488313 baseEnd_1488313 := by
    simpa [prefixWord, tailWord_1488313, baseEnd_1488313] using wordTrace_append hprefix tailTrace_1488313
  have hstable : (prefixWord ++ tailWord_1488313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488313).length < 2 ^ (prefixWord ++ tailWord_1488313).sum := by decide
  have hdescent : baseEnd_1488313 < baseStart_1488313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488355 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_1488355 : Nat := 118140960795 + 1488355 * 2 ^ 59
def prefixEnd_1488355 : Nat := 4983230072969 + 3 ^ 40 * 1488355 * 2
def baseEnd_1488355 : Nat := 339662888676724239074527

theorem tailTrace_1488355 : CollatzResearch.WordTrace tailWord_1488355 prefixEnd_1488355 339662888676724239074527 := by
  unfold tailWord_1488355
  simp only [CollatzResearch.WordTrace]
  refine ⟨54284766522951500641946519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36189844348634333761297679 54284766522951500641946519)
  ·
    refine ⟨81427149784427250962919779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54284766522951500641946519 81427149784427250962919779)
    ·
      refine ⟨122140724676640876444379669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81427149784427250962919779 122140724676640876444379669)
      ·
        refine ⟨5725346469217541083330297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122140724676640876444379669 5725346469217541083330297)
        ·
          refine ⟨4294009851913155812497723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725346469217541083330297 4294009851913155812497723)
          ·
            refine ⟨6441014777869733718746585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294009851913155812497723 6441014777869733718746585)
            ·
              refine ⟨4830761083402300289059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441014777869733718746585 4830761083402300289059939)
              ·
                refine ⟨7246141625103450433589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830761083402300289059939 7246141625103450433589909)
                ·
                  refine ⟨339662888676724239074527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7246141625103450433589909 339662888676724239074527)
                  ·
                    rfl

theorem cell21_1488355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_1488355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488355 prefixEnd_1488355 := by exact prefixLift 1488355
  have htrace : WordTrace (prefixWord ++ tailWord_1488355) baseStart_1488355 baseEnd_1488355 := by
    simpa [prefixWord, tailWord_1488355, baseEnd_1488355] using wordTrace_append hprefix tailTrace_1488355
  have hstable : (prefixWord ++ tailWord_1488355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488355).length < 2 ^ (prefixWord ++ tailWord_1488355).sum := by decide
  have hdescent : baseEnd_1488355 < baseStart_1488355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488369 : List Nat := [1, 2, 2, 2, 3, 2, 1, 8]
def baseStart_1488369 : Nat := 118140960795 + 1488369 * 2 ^ 59
def prefixEnd_1488369 : Nat := 4983230072969 + 3 ^ 40 * 1488369 * 2
def baseEnd_1488369 : Nat := 113222027889154441947055

theorem tailTrace_1488369 : CollatzResearch.WordTrace tailWord_1488369 prefixEnd_1488369 113222027889154441947055 := by
  unfold tailWord_1488369
  simp only [CollatzResearch.WordTrace]
  refine ⟨54285277144900781032956161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36190184763267187355304107 54285277144900781032956161)
  ·
    refine ⟨40713957858675585774717121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54285277144900781032956161 40713957858675585774717121)
    ·
      refine ⟨30535468394006689331037841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40713957858675585774717121 30535468394006689331037841)
      ·
        refine ⟨22901601295505016998278381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30535468394006689331037841 22901601295505016998278381)
        ·
          refine ⟨8588100485814381374354393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22901601295505016998278381 8588100485814381374354393)
          ·
            refine ⟨6441075364360786030765795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8588100485814381374354393 6441075364360786030765795)
            ·
              refine ⟨9661613046541179046148693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441075364360786030765795 9661613046541179046148693)
              ·
                refine ⟨113222027889154441947055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9661613046541179046148693 113222027889154441947055)
                ·
                  rfl

theorem cell21_1488369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_1488369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488369 prefixEnd_1488369 := by exact prefixLift 1488369
  have htrace : WordTrace (prefixWord ++ tailWord_1488369) baseStart_1488369 baseEnd_1488369 := by
    simpa [prefixWord, tailWord_1488369, baseEnd_1488369] using wordTrace_append hprefix tailTrace_1488369
  have hstable : (prefixWord ++ tailWord_1488369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488369).length < 2 ^ (prefixWord ++ tailWord_1488369).sum := by decide
  have hdescent : baseEnd_1488369 < baseStart_1488369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488459 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_1488459 : Nat := 118140960795 + 1488459 * 2 ^ 59
def prefixEnd_1488459 : Nat := 4983230072969 + 3 ^ 40 * 1488459 * 2
def baseEnd_1488459 : Nat := 339686622893643169340981

theorem tailTrace_1488459 : CollatzResearch.WordTrace tailWord_1488459 prefixEnd_1488459 339686622893643169340981 := by
  unfold tailWord_1488459
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288559714574726403732431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36192373143049817602488287 54288559714574726403732431)
  ·
    refine ⟨81432839571862089605598647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54288559714574726403732431 81432839571862089605598647)
    ·
      refine ⟨122149259357793134408397971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81432839571862089605598647 122149259357793134408397971)
      ·
        refine ⟨183223889036689701612596957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122149259357793134408397971 183223889036689701612596957)
        ·
          refine ⟨68708958388758638104723859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183223889036689701612596957 68708958388758638104723859)
          ·
            refine ⟨103063437583137957157085789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68708958388758638104723859 103063437583137957157085789)
            ·
              refine ⟨38648789093676733933907171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103063437583137957157085789 38648789093676733933907171)
              ·
                refine ⟨57973183640515100900860757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38648789093676733933907171 57973183640515100900860757)
                ·
                  refine ⟨339686622893643169340981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57973183640515100900860757 339686622893643169340981)
                  ·
                    rfl

theorem cell21_1488459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_1488459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488459 prefixEnd_1488459 := by exact prefixLift 1488459
  have htrace : WordTrace (prefixWord ++ tailWord_1488459) baseStart_1488459 baseEnd_1488459 := by
    simpa [prefixWord, tailWord_1488459, baseEnd_1488459] using wordTrace_append hprefix tailTrace_1488459
  have hstable : (prefixWord ++ tailWord_1488459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488459).length < 2 ^ (prefixWord ++ tailWord_1488459).sum := by decide
  have hdescent : baseEnd_1488459 < baseStart_1488459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488578 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1488578 : Nat := 118140960795 + 1488578 * 2 ^ 59
def prefixEnd_1488578 : Nat := 4983230072969 + 3 ^ 40 * 1488578 * 2
def baseEnd_1488578 : Nat := 339713780314925406857405

theorem tailTrace_1488578 : CollatzResearch.WordTrace tailWord_1488578 prefixEnd_1488578 339713780314925406857405 := by
  unfold tailWord_1488578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573225000285902431828597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36195266667429073151542925 13573225000285902431828597)
  ·
    refine ⟨1272489843776803352983931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13573225000285902431828597 1272489843776803352983931)
    ·
      refine ⟨1908734765665205029475897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272489843776803352983931 1908734765665205029475897)
      ·
        refine ⟨1431551074248903772106923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1908734765665205029475897 1431551074248903772106923)
        ·
          refine ⟨2147326611373355658160385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431551074248903772106923 2147326611373355658160385)
          ·
            refine ⟨1610494958530016743620289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147326611373355658160385 1610494958530016743620289)
            ·
              refine ⟨1207871218897512557715217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610494958530016743620289 1207871218897512557715217)
              ·
                refine ⟨905903414173134418286413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207871218897512557715217 905903414173134418286413)
                ·
                  refine ⟨339713780314925406857405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905903414173134418286413 339713780314925406857405)
                  ·
                    rfl

theorem cell21_1488578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1488578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488578 prefixEnd_1488578 := by exact prefixLift 1488578
  have htrace : WordTrace (prefixWord ++ tailWord_1488578) baseStart_1488578 baseEnd_1488578 := by
    simpa [prefixWord, tailWord_1488578, baseEnd_1488578] using wordTrace_append hprefix tailTrace_1488578
  have hstable : (prefixWord ++ tailWord_1488578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488578).length < 2 ^ (prefixWord ++ tailWord_1488578).sum := by decide
  have hdescent : baseEnd_1488578 < baseStart_1488578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488583 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_1488583 : Nat := 118140960795 + 1488583 * 2 ^ 59
def prefixEnd_1488583 : Nat := 4983230072969 + 3 ^ 40 * 1488583 * 2
def baseEnd_1488583 : Nat := 339714921383046509274061

theorem tailTrace_1488583 : CollatzResearch.WordTrace tailWord_1488583 prefixEnd_1488583 339714921383046509274061 := by
  unfold tailWord_1488583
  simp only [CollatzResearch.WordTrace]
  refine ⟨54293082366125495581246403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36195388244083663720830935 54293082366125495581246403)
  ·
    refine ⟨81439623549188243371869605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54293082366125495581246403 81439623549188243371869605)
    ·
      refine ⟨15269929415472795632225551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81439623549188243371869605 15269929415472795632225551)
      ·
        refine ⟨22904894123209193448338327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269929415472795632225551 22904894123209193448338327)
        ·
          refine ⟨34357341184813790172507491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22904894123209193448338327 34357341184813790172507491)
          ·
            refine ⟨51536011777220685258761237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34357341184813790172507491 51536011777220685258761237)
            ·
              refine ⟨2415750552057219621504433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51536011777220685258761237 2415750552057219621504433)
              ·
                refine ⟨1811812914042914716128325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415750552057219621504433 1811812914042914716128325)
                ·
                  refine ⟨339714921383046509274061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811812914042914716128325 339714921383046509274061)
                  ·
                    rfl

theorem cell21_1488583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_1488583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488583 prefixEnd_1488583 := by exact prefixLift 1488583
  have htrace : WordTrace (prefixWord ++ tailWord_1488583) baseStart_1488583 baseEnd_1488583 := by
    simpa [prefixWord, tailWord_1488583, baseEnd_1488583] using wordTrace_append hprefix tailTrace_1488583
  have hstable : (prefixWord ++ tailWord_1488583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488583).length < 2 ^ (prefixWord ++ tailWord_1488583).sum := by decide
  have hdescent : baseEnd_1488583 < baseStart_1488583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488586 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1488586 : Nat := 118140960795 + 1488586 * 2 ^ 59
def prefixEnd_1488586 : Nat := 4983230072969 + 3 ^ 40 * 1488586 * 2
def baseEnd_1488586 : Nat := 339715606023919170724055

theorem tailTrace_1488586 : CollatzResearch.WordTrace tailWord_1488586 prefixEnd_1488586 339715606023919170724055 := by
  unfold tailWord_1488586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573297946278656773401403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36195461190076418062403741 13573297946278656773401403)
  ·
    refine ⟨20359946919417985160102105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13573297946278656773401403 20359946919417985160102105)
    ·
      refine ⟨15269960189563488870076579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20359946919417985160102105 15269960189563488870076579)
      ·
        refine ⟨22904940284345233305114869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269960189563488870076579 22904940284345233305114869)
        ·
          refine ⟨2147338151657365622354519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22904940284345233305114869 2147338151657365622354519)
          ·
            refine ⟨3221007227486048433531779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147338151657365622354519 3221007227486048433531779)
            ·
              refine ⟨4831510841229072650297669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221007227486048433531779 4831510841229072650297669)
              ·
                refine ⟨905908282730451121930813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4831510841229072650297669 905908282730451121930813)
                ·
                  refine ⟨339715606023919170724055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905908282730451121930813 339715606023919170724055)
                  ·
                    rfl

theorem cell21_1488586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1488586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488586 prefixEnd_1488586 := by exact prefixLift 1488586
  have htrace : WordTrace (prefixWord ++ tailWord_1488586) baseStart_1488586 baseEnd_1488586 := by
    simpa [prefixWord, tailWord_1488586, baseEnd_1488586] using wordTrace_append hprefix tailTrace_1488586
  have hstable : (prefixWord ++ tailWord_1488586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488586).length < 2 ^ (prefixWord ++ tailWord_1488586).sum := by decide
  have hdescent : baseEnd_1488586 < baseStart_1488586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488673 : List Nat := [1, 2, 3, 2, 1, 4, 1, 7]
def baseStart_1488673 : Nat := 118140960795 + 1488673 * 2 ^ 59
def prefixEnd_1488673 : Nat := 4983230072969 + 3 ^ 40 * 1488673 * 2
def baseEnd_1488673 : Nat := 113245153536408784257959

theorem tailTrace_1488673 : CollatzResearch.WordTrace tailWord_1488673 prefixEnd_1488673 113245153536408784257959 := by
  unfold tailWord_1488673
  simp only [CollatzResearch.WordTrace]
  refine ⟨54296364935799440952022673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36197576623866293968015115 54296364935799440952022673)
  ·
    refine ⟨40722273701849580714017005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54296364935799440952022673 40722273701849580714017005)
    ·
      refine ⟨15270852638193592767756377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40722273701849580714017005 15270852638193592767756377)
      ·
        refine ⟨11453139478645194575817283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15270852638193592767756377 11453139478645194575817283)
        ·
          refine ⟨17179709217967791863725925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453139478645194575817283 17179709217967791863725925)
          ·
            refine ⟨3221195478368960974448611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17179709217967791863725925 3221195478368960974448611)
            ·
              refine ⟨4831793217553441461672917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221195478368960974448611 4831793217553441461672917)
              ·
                refine ⟨113245153536408784257959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4831793217553441461672917 113245153536408784257959)
                ·
                  rfl

theorem cell21_1488673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_1488673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488673 prefixEnd_1488673 := by exact prefixLift 1488673
  have htrace : WordTrace (prefixWord ++ tailWord_1488673) baseStart_1488673 baseEnd_1488673 := by
    simpa [prefixWord, tailWord_1488673, baseEnd_1488673] using wordTrace_append hprefix tailTrace_1488673
  have hstable : (prefixWord ++ tailWord_1488673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488673).length < 2 ^ (prefixWord ++ tailWord_1488673).sum := by decide
  have hdescent : baseEnd_1488673 < baseStart_1488673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488710 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1488710 : Nat := 118140960795 + 1488710 * 2 ^ 59
def prefixEnd_1488710 : Nat := 4983230072969 + 3 ^ 40 * 1488710 * 2
def baseEnd_1488710 : Nat := 339743904513322510657135

theorem tailTrace_1488710 : CollatzResearch.WordTrace tailWord_1488710 prefixEnd_1488710 339743904513322510657135 := by
  unfold tailWord_1488710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696803576145793633472487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36198476291110264180746389 1696803576145793633472487)
  ·
    refine ⟨2545205364218690450208731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696803576145793633472487 2545205364218690450208731)
    ·
      refine ⟨3817808046328035675313097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545205364218690450208731 3817808046328035675313097)
      ·
        refine ⟨2863356034746026756484823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3817808046328035675313097 2863356034746026756484823)
        ·
          refine ⟨4295034052119040134727235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863356034746026756484823 4295034052119040134727235)
          ·
            refine ⟨6442551078178560202090853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295034052119040134727235 6442551078178560202090853)
            ·
              refine ⟨1207978327158480037892035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6442551078178560202090853 1207978327158480037892035)
              ·
                refine ⟨1811967490737720056838053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207978327158480037892035 1811967490737720056838053)
                ·
                  refine ⟨339743904513322510657135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811967490737720056838053 339743904513322510657135)
                  ·
                    rfl

theorem cell21_1488710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1488710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488710 prefixEnd_1488710 := by exact prefixLift 1488710
  have htrace : WordTrace (prefixWord ++ tailWord_1488710) baseStart_1488710 baseEnd_1488710 := by
    simpa [prefixWord, tailWord_1488710, baseEnd_1488710] using wordTrace_append hprefix tailTrace_1488710
  have hstable : (prefixWord ++ tailWord_1488710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488710).length < 2 ^ (prefixWord ++ tailWord_1488710).sum := by decide
  have hdescent : baseEnd_1488710 < baseStart_1488710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488763 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_1488763 : Nat := 118140960795 + 1488763 * 2 ^ 59
def prefixEnd_1488763 : Nat := 4983230072969 + 3 ^ 40 * 1488763 * 2
def baseEnd_1488763 : Nat := 339755999835406196273693

theorem tailTrace_1488763 : CollatzResearch.WordTrace tailWord_1488763 prefixEnd_1488763 339755999835406196273693 := by
  unfold tailWord_1488763
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299647505473386322798943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36199765003648924215199295 54299647505473386322798943)
  ·
    refine ⟨81449471258210079484198415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54299647505473386322798943 81449471258210079484198415)
    ·
      refine ⟨122174206887315119226297623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81449471258210079484198415 122174206887315119226297623)
      ·
        refine ⟨183261310330972678839446435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122174206887315119226297623 183261310330972678839446435)
        ·
          refine ⟨274891965496459018259169653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183261310330972678839446435 274891965496459018259169653)
          ·
            refine ⟨25771121765293032961797155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274891965496459018259169653 25771121765293032961797155)
            ·
              refine ⟨38656682647939549442695733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25771121765293032961797155 38656682647939549442695733)
              ·
                refine ⟨3624063998244332760252725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38656682647939549442695733 3624063998244332760252725)
                ·
                  refine ⟨339755999835406196273693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624063998244332760252725 339755999835406196273693)
                  ·
                    rfl

theorem cell21_1488763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_1488763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488763 prefixEnd_1488763 := by exact prefixLift 1488763
  have htrace : WordTrace (prefixWord ++ tailWord_1488763) baseStart_1488763 baseEnd_1488763 := by
    simpa [prefixWord, tailWord_1488763, baseEnd_1488763] using wordTrace_append hprefix tailTrace_1488763
  have hstable : (prefixWord ++ tailWord_1488763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488763).length < 2 ^ (prefixWord ++ tailWord_1488763).sum := by decide
  have hdescent : baseEnd_1488763 < baseStart_1488763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488797 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1488797 : Nat := 118140960795 + 1488797 * 2 ^ 59
def prefixEnd_1488797 : Nat := 4983230072969 + 3 ^ 40 * 1488797 * 2
def baseEnd_1488797 : Nat := 339763759098629692706957

theorem tailTrace_1488797 : CollatzResearch.WordTrace tailWord_1488797 prefixEnd_1488797 339763759098629692706957 := by
  unfold tailWord_1488797
  simp only [CollatzResearch.WordTrace]
  refine ⟨54300887587350210129536645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36200591724900140086357763 54300887587350210129536645)
  ·
    refine ⟨10181416422628164399288121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54300887587350210129536645 10181416422628164399288121)
    ·
      refine ⟨7636062316971123299466091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10181416422628164399288121 7636062316971123299466091)
      ·
        refine ⟨11454093475456684949199137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636062316971123299466091 11454093475456684949199137)
        ·
          refine ⟨8590570106592513711899353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454093475456684949199137 8590570106592513711899353)
          ·
            refine ⟨6442927579944385283924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8590570106592513711899353 6442927579944385283924515)
            ·
              refine ⟨9664391369916577925886773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442927579944385283924515 9664391369916577925886773)
              ·
                refine ⟨906036690929679180551885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9664391369916577925886773 906036690929679180551885)
                ·
                  refine ⟨339763759098629692706957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906036690929679180551885 339763759098629692706957)
                  ·
                    rfl

theorem cell21_1488797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1488797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488797 prefixEnd_1488797 := by exact prefixLift 1488797
  have htrace : WordTrace (prefixWord ++ tailWord_1488797) baseStart_1488797 baseEnd_1488797 := by
    simpa [prefixWord, tailWord_1488797, baseEnd_1488797] using wordTrace_append hprefix tailTrace_1488797
  have hstable : (prefixWord ++ tailWord_1488797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488797).length < 2 ^ (prefixWord ++ tailWord_1488797).sum := by decide
  have hdescent : baseEnd_1488797 < baseStart_1488797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488935 : List Nat := [1, 1, 7, 1, 2, 2, 1, 6]
def baseStart_1488935 : Nat := 118140960795 + 1488935 * 2 ^ 59
def prefixEnd_1488935 : Nat := 4983230072969 + 3 ^ 40 * 1488935 * 2
def baseEnd_1488935 : Nat := 113265084192924039802225

theorem tailTrace_1488935 : CollatzResearch.WordTrace tailWord_1488935 prefixEnd_1488935 113265084192924039802225 := by
  unfold tailWord_1488935
  simp only [CollatzResearch.WordTrace]
  refine ⟨54305920860850259698060259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36203947240566839798706839 54305920860850259698060259)
  ·
    refine ⟨81458881291275389547090389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54305920860850259698060259 81458881291275389547090389)
    ·
      refine ⟨1909192530264266942509931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 81458881291275389547090389 1909192530264266942509931)
      ·
        refine ⟨2863788795396400413764897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909192530264266942509931 2863788795396400413764897)
        ·
          refine ⟨2147841596547300310323673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2863788795396400413764897 2147841596547300310323673)
          ·
            refine ⟨1610881197410475232742755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147841596547300310323673 1610881197410475232742755)
            ·
              refine ⟨2416321796115712849114133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610881197410475232742755 2416321796115712849114133)
              ·
                refine ⟨113265084192924039802225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2416321796115712849114133 113265084192924039802225)
                ·
                  rfl

theorem cell21_1488935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 6].length) (baseStart_1488935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1488935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1488935 prefixEnd_1488935 := by exact prefixLift 1488935
  have htrace : WordTrace (prefixWord ++ tailWord_1488935) baseStart_1488935 baseEnd_1488935 := by
    simpa [prefixWord, tailWord_1488935, baseEnd_1488935] using wordTrace_append hprefix tailTrace_1488935
  have hstable : (prefixWord ++ tailWord_1488935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488935).length < 2 ^ (prefixWord ++ tailWord_1488935).sum := by decide
  have hdescent : baseEnd_1488935 < baseStart_1488935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489042 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1489042 : Nat := 118140960795 + 1489042 * 2 ^ 59
def prefixEnd_1489042 : Nat := 4983230072969 + 3 ^ 40 * 1489042 * 2
def baseEnd_1489042 : Nat := 339819671436563711123123

theorem tailTrace_1489042 : CollatzResearch.WordTrace tailWord_1489042 prefixEnd_1489042 339819671436563711123123 := by
  unfold tailWord_1489042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577455867865654243051345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36206548980975077981470253 13577455867865654243051345)
  ·
    refine ⟨10183091900899240682288509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13577455867865654243051345 10183091900899240682288509)
    ·
      refine ⟨3818659462837215255858191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10183091900899240682288509 3818659462837215255858191)
      ·
        refine ⟨5727989194255822883787287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818659462837215255858191 5727989194255822883787287)
        ·
          refine ⟨8591983791383734325680931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727989194255822883787287 8591983791383734325680931)
          ·
            refine ⟨12887975687075601488521397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591983791383734325680931 12887975687075601488521397)
            ·
              refine ⟨1208247720663337639548881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12887975687075601488521397 1208247720663337639548881)
              ·
                refine ⟨906185790497503229661661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208247720663337639548881 906185790497503229661661)
                ·
                  refine ⟨339819671436563711123123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906185790497503229661661 339819671436563711123123)
                  ·
                    rfl

theorem cell21_1489042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1489042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489042 prefixEnd_1489042 := by exact prefixLift 1489042
  have htrace : WordTrace (prefixWord ++ tailWord_1489042) baseStart_1489042 baseEnd_1489042 := by
    simpa [prefixWord, tailWord_1489042, baseEnd_1489042] using wordTrace_append hprefix tailTrace_1489042
  have hstable : (prefixWord ++ tailWord_1489042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489042).length < 2 ^ (prefixWord ++ tailWord_1489042).sum := by decide
  have hdescent : baseEnd_1489042 < baseStart_1489042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489053 : List Nat := [1, 4, 2, 1, 1, 4, 2, 6]
def baseStart_1489053 : Nat := 118140960795 + 1489053 * 2 ^ 59
def prefixEnd_1489053 : Nat := 4983230072969 + 3 ^ 40 * 1489053 * 2
def baseEnd_1489053 : Nat := 113274060595476712146589

theorem tailTrace_1489053 : CollatzResearch.WordTrace tailWord_1489053 prefixEnd_1489053 113274060595476712146589 := by
  unfold tailWord_1489053
  simp only [CollatzResearch.WordTrace]
  refine ⟨54310224674422765850855813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36206816449615177233903875 54310224674422765850855813)
  ·
    refine ⟨10183167126454268597035465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54310224674422765850855813 10183167126454268597035465)
    ·
      refine ⟨7637375344840701447776599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10183167126454268597035465 7637375344840701447776599)
      ·
        refine ⟨11456063017261052171664899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637375344840701447776599 11456063017261052171664899)
        ·
          refine ⟨17184094525891578257497349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456063017261052171664899 17184094525891578257497349)
          ·
            refine ⟨3222017723604670923280753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17184094525891578257497349 3222017723604670923280753)
            ·
              refine ⟨2416513292703503192460565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222017723604670923280753 2416513292703503192460565)
              ·
                refine ⟨113274060595476712146589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2416513292703503192460565 113274060595476712146589)
                ·
                  rfl

theorem cell21_1489053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_1489053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489053 prefixEnd_1489053 := by exact prefixLift 1489053
  have htrace : WordTrace (prefixWord ++ tailWord_1489053) baseStart_1489053 baseEnd_1489053 := by
    simpa [prefixWord, tailWord_1489053, baseEnd_1489053] using wordTrace_append hprefix tailTrace_1489053
  have hstable : (prefixWord ++ tailWord_1489053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489053).length < 2 ^ (prefixWord ++ tailWord_1489053).sum := by decide
  have hdescent : baseEnd_1489053 < baseStart_1489053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489056 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1489056 : Nat := 118140960795 + 1489056 * 2 ^ 59
def prefixEnd_1489056 : Nat := 4983230072969 + 3 ^ 40 * 1489056 * 2
def baseEnd_1489056 : Nat := 339822866427302797889761

theorem tailTrace_1489056 : CollatzResearch.WordTrace tailWord_1489056 prefixEnd_1489056 339822866427302797889761 := by
  unfold tailWord_1489056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27155167046705948681607511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36206889395607931575476681 27155167046705948681607511)
  ·
    refine ⟨40732750570058923022411267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27155167046705948681607511 40732750570058923022411267)
    ·
      refine ⟨61099125855088384533616901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40732750570058923022411267 61099125855088384533616901)
      ·
        refine ⟨11456086097829072100053169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61099125855088384533616901 11456086097829072100053169)
        ·
          refine ⟨8592064573371804075039877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11456086097829072100053169 8592064573371804075039877)
          ·
            refine ⟨1611012107507213264069977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8592064573371804075039877 1611012107507213264069977)
            ·
              refine ⟨1208259080630409948052483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611012107507213264069977 1208259080630409948052483)
              ·
                refine ⟨1812388620945614922078725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208259080630409948052483 1812388620945614922078725)
                ·
                  refine ⟨339822866427302797889761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812388620945614922078725 339822866427302797889761)
                  ·
                    rfl

theorem cell21_1489056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1489056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489056 prefixEnd_1489056 := by exact prefixLift 1489056
  have htrace : WordTrace (prefixWord ++ tailWord_1489056) baseStart_1489056 baseEnd_1489056 := by
    simpa [prefixWord, tailWord_1489056, baseEnd_1489056] using wordTrace_append hprefix tailTrace_1489056
  have hstable : (prefixWord ++ tailWord_1489056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489056).length < 2 ^ (prefixWord ++ tailWord_1489056).sum := by decide
  have hdescent : baseEnd_1489056 < baseStart_1489056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489160 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_1489160 : Nat := 118140960795 + 1489160 * 2 ^ 59
def prefixEnd_1489160 : Nat := 4983230072969 + 3 ^ 40 * 1489160 * 2
def baseEnd_1489160 : Nat := 339846600644221728156215

theorem tailTrace_1489160 : CollatzResearch.WordTrace tailWord_1489160 prefixEnd_1489160 339846600644221728156215 := by
  unfold tailWord_1489160
  simp only [CollatzResearch.WordTrace]
  refine ⟨27157063642517561562500467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36209418190023415416667289 27157063642517561562500467)
  ·
    refine ⟨40735595463776342343750701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27157063642517561562500467 40735595463776342343750701)
    ·
      refine ⟨15275848298916128378906513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40735595463776342343750701 15275848298916128378906513)
      ·
        refine ⟨11456886224187096284179885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15275848298916128378906513 11456886224187096284179885)
        ·
          refine ⟨4296332334070161106567457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11456886224187096284179885 4296332334070161106567457)
          ·
            refine ⟨3222249250552620829925593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296332334070161106567457 3222249250552620829925593)
            ·
              refine ⟨2416686937914465622444195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222249250552620829925593 2416686937914465622444195)
              ·
                refine ⟨3625030406871698433666293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416686937914465622444195 3625030406871698433666293)
                ·
                  refine ⟨339846600644221728156215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625030406871698433666293 339846600644221728156215)
                  ·
                    rfl

theorem cell21_1489160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_1489160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489160 prefixEnd_1489160 := by exact prefixLift 1489160
  have htrace : WordTrace (prefixWord ++ tailWord_1489160) baseStart_1489160 baseEnd_1489160 := by
    simpa [prefixWord, tailWord_1489160, baseEnd_1489160] using wordTrace_append hprefix tailTrace_1489160
  have hstable : (prefixWord ++ tailWord_1489160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489160).length < 2 ^ (prefixWord ++ tailWord_1489160).sum := by decide
  have hdescent : baseEnd_1489160 < baseStart_1489160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489219 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_1489219 : Nat := 118140960795 + 1489219 * 2 ^ 59
def prefixEnd_1489219 : Nat := 4983230072969 + 3 ^ 40 * 1489219 * 2
def baseEnd_1489219 : Nat := 339860065248050736672761

theorem tailTrace_1489219 : CollatzResearch.WordTrace tailWord_1489219 prefixEnd_1489219 339860065248050736672761 := by
  unfold tailWord_1489219
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316279191821376201398711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36210852794547584134265807 54316279191821376201398711)
  ·
    refine ⟨81474418787732064302098067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54316279191821376201398711 81474418787732064302098067)
    ·
      refine ⟨122211628181598096453147101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81474418787732064302098067 122211628181598096453147101)
      ·
        refine ⟨45829360568099286169930163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122211628181598096453147101 45829360568099286169930163)
        ·
          refine ⟨68744040852148929254895245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45829360568099286169930163 68744040852148929254895245)
          ·
            refine ⟨25779015319555848470585717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68744040852148929254895245 25779015319555848470585717)
            ·
              refine ⟨2416782686208360794117411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25779015319555848470585717 2416782686208360794117411)
              ·
                refine ⟨3625174029312541191176117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416782686208360794117411 3625174029312541191176117)
                ·
                  refine ⟨339860065248050736672761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625174029312541191176117 339860065248050736672761)
                  ·
                    rfl

theorem cell21_1489219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_1489219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489219 prefixEnd_1489219 := by exact prefixLift 1489219
  have htrace : WordTrace (prefixWord ++ tailWord_1489219) baseStart_1489219 baseEnd_1489219 := by
    simpa [prefixWord, tailWord_1489219, baseEnd_1489219] using wordTrace_append hprefix tailTrace_1489219
  have hstable : (prefixWord ++ tailWord_1489219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489219).length < 2 ^ (prefixWord ++ tailWord_1489219).sum := by decide
  have hdescent : baseEnd_1489219 < baseStart_1489219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489281 : List Nat := [1, 2, 4, 3, 1, 1, 3, 6]
def baseStart_1489281 : Nat := 118140960795 + 1489281 * 2 ^ 59
def prefixEnd_1489281 : Nat := 4983230072969 + 3 ^ 40 * 1489281 * 2
def baseEnd_1489281 : Nat := 113291404830917468879767

theorem tailTrace_1489281 : CollatzResearch.WordTrace tailWord_1489281 prefixEnd_1489281 113291404830917468879767 := by
  unfold tailWord_1489281
  simp only [CollatzResearch.WordTrace]
  refine ⟨54318540517596760790155697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36212360345064507193437131 54318540517596760790155697)
  ·
    refine ⟨40738905388197570592616773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54318540517596760790155697 40738905388197570592616773)
    ·
      refine ⟨7638544760287044486115645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40738905388197570592616773 7638544760287044486115645)
      ·
        refine ⟨2864454285107641682293367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7638544760287044486115645 2864454285107641682293367)
        ·
          refine ⟨4296681427661462523440051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864454285107641682293367 4296681427661462523440051)
          ·
            refine ⟨6445022141492193785160077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296681427661462523440051 6445022141492193785160077)
            ·
              refine ⟨2416883303059572669435029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6445022141492193785160077 2416883303059572669435029)
              ·
                refine ⟨113291404830917468879767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2416883303059572669435029 113291404830917468879767)
                ·
                  rfl

theorem cell21_1489281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_1489281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489281 prefixEnd_1489281 := by exact prefixLift 1489281
  have htrace : WordTrace (prefixWord ++ tailWord_1489281) baseStart_1489281 baseEnd_1489281 := by
    simpa [prefixWord, tailWord_1489281, baseEnd_1489281] using wordTrace_append hprefix tailTrace_1489281
  have hstable : (prefixWord ++ tailWord_1489281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489281).length < 2 ^ (prefixWord ++ tailWord_1489281).sum := by decide
  have hdescent : baseEnd_1489281 < baseStart_1489281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489312 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_1489312 : Nat := 118140960795 + 1489312 * 2 ^ 59
def prefixEnd_1489312 : Nat := 4983230072969 + 3 ^ 40 * 1489312 * 2
def baseEnd_1489312 : Nat := 339881289115103241622571

theorem tailTrace_1489312 : CollatzResearch.WordTrace tailWord_1489312 prefixEnd_1489312 339881289115103241622571 := by
  unfold tailWord_1489312
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159835590242226542267095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36213114120322968723022793 27159835590242226542267095)
  ·
    refine ⟨40739753385363339813400643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27159835590242226542267095 40739753385363339813400643)
    ·
      refine ⟨61109630078045009720100965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40739753385363339813400643 61109630078045009720100965)
      ·
        refine ⟨11458055639633439322518931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61109630078045009720100965 11458055639633439322518931)
        ·
          refine ⟨17187083459450158983778397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11458055639633439322518931 17187083459450158983778397)
          ·
            refine ⟨6445156297293809618916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17187083459450158983778397 6445156297293809618916899)
            ·
              refine ⟨9667734445940714428375349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445156297293809618916899 9667734445940714428375349)
              ·
                refine ⟨906350104306941977660189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9667734445940714428375349 906350104306941977660189)
                ·
                  refine ⟨339881289115103241622571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906350104306941977660189 339881289115103241622571)
                  ·
                    rfl

theorem cell21_1489312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_1489312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489312 prefixEnd_1489312 := by exact prefixLift 1489312
  have htrace : WordTrace (prefixWord ++ tailWord_1489312) baseStart_1489312 baseEnd_1489312 := by
    simpa [prefixWord, tailWord_1489312, baseEnd_1489312] using wordTrace_append hprefix tailTrace_1489312
  have hstable : (prefixWord ++ tailWord_1489312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489312).length < 2 ^ (prefixWord ++ tailWord_1489312).sum := by decide
  have hdescent : baseEnd_1489312 < baseStart_1489312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489475 : List Nat := [1, 1, 1, 3, 1, 2, 1, 11]
def baseStart_1489475 : Nat := 118140960795 + 1489475 * 2 ^ 59
def prefixEnd_1489475 : Nat := 4983230072969 + 3 ^ 40 * 1489475 * 2
def baseEnd_1489475 : Nat := 113306162645283726801857

theorem tailTrace_1489475 : CollatzResearch.WordTrace tailWord_1489475 prefixEnd_1489475 113306162645283726801857 := by
  unfold tailWord_1489475
  simp only [CollatzResearch.WordTrace]
  refine ⟨54325616278893931922717879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36217077519262621281811919 54325616278893931922717879)
  ·
    refine ⟨81488424418340897884076819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54325616278893931922717879 81488424418340897884076819)
    ·
      refine ⟨122232636627511346826115229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81488424418340897884076819 122232636627511346826115229)
      ·
        refine ⟨45837238735316755059793211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122232636627511346826115229 45837238735316755059793211)
        ·
          refine ⟨68755858102975132589689817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45837238735316755059793211 68755858102975132589689817)
          ·
            refine ⟨51566893577231349442267363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68755858102975132589689817 51566893577231349442267363)
            ·
              refine ⟨77350340365847024163401045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51566893577231349442267363 77350340365847024163401045)
              ·
                refine ⟨113306162645283726801857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77350340365847024163401045 113306162645283726801857)
                ·
                  rfl

theorem cell21_1489475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_1489475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489475 prefixEnd_1489475 := by exact prefixLift 1489475
  have htrace : WordTrace (prefixWord ++ tailWord_1489475) baseStart_1489475 baseEnd_1489475 := by
    simpa [prefixWord, tailWord_1489475, baseEnd_1489475] using wordTrace_append hprefix tailTrace_1489475
  have hstable : (prefixWord ++ tailWord_1489475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489475).length < 2 ^ (prefixWord ++ tailWord_1489475).sum := by decide
  have hdescent : baseEnd_1489475 < baseStart_1489475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489492 : List Nat := [2, 4, 1, 1, 1, 4, 8]
def baseStart_1489492 : Nat := 118140960795 + 1489492 * 2 ^ 59
def prefixEnd_1489492 : Nat := 4983230072969 + 3 ^ 40 * 1489492 * 2
def baseEnd_1489492 : Nat := 37769151951940325402467

theorem tailTrace_1489492 : CollatzResearch.WordTrace tailWord_1489492 prefixEnd_1489492 37769151951940325402467 := by
  unfold tailWord_1489492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163118159916171913043365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36217490879888229217391153 27163118159916171913043365)
  ·
    refine ⟨5093084654984282233695631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27163118159916171913043365 5093084654984282233695631)
    ·
      refine ⟨7639626982476423350543447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093084654984282233695631 7639626982476423350543447)
      ·
        refine ⟨11459440473714635025815171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639626982476423350543447 11459440473714635025815171)
        ·
          refine ⟨17189160710571952538722757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459440473714635025815171 17189160710571952538722757)
          ·
            refine ⟨3222967633232241101010517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17189160710571952538722757 3222967633232241101010517)
            ·
              refine ⟨37769151951940325402467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3222967633232241101010517 37769151951940325402467)
              ·
                rfl

theorem cell21_1489492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 8].length) (baseStart_1489492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489492 prefixEnd_1489492 := by exact prefixLift 1489492
  have htrace : WordTrace (prefixWord ++ tailWord_1489492) baseStart_1489492 baseEnd_1489492 := by
    simpa [prefixWord, tailWord_1489492, baseEnd_1489492] using wordTrace_append hprefix tailTrace_1489492
  have hstable : (prefixWord ++ tailWord_1489492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489492).length < 2 ^ (prefixWord ++ tailWord_1489492).sum := by decide
  have hdescent : baseEnd_1489492 < baseStart_1489492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489512 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1489512 : Nat := 118140960795 + 1489512 * 2 ^ 59
def prefixEnd_1489512 : Nat := 4983230072969 + 3 ^ 40 * 1489512 * 2
def baseEnd_1489512 : Nat := 339926931839947338288829

theorem tailTrace_1489512 : CollatzResearch.WordTrace tailWord_1489512 prefixEnd_1489512 339926931839947338288829 := by
  unfold tailWord_1489512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163482889879943620907395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36217977186506591494543193 27163482889879943620907395)
  ·
    refine ⟨40745224334819915431361093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27163482889879943620907395 40745224334819915431361093)
    ·
      refine ⟨7639729562778734143380205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40745224334819915431361093 7639729562778734143380205)
      ·
        refine ⟨2864898586042025303767577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7639729562778734143380205 2864898586042025303767577)
        ·
          refine ⟨2148673939531518977825683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864898586042025303767577 2148673939531518977825683)
          ·
            refine ⟨3223010909297278466738525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148673939531518977825683 3223010909297278466738525)
            ·
              refine ⟨1208629090986479425026947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3223010909297278466738525 1208629090986479425026947)
              ·
                refine ⟨1812943636479719137540421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208629090986479425026947 1812943636479719137540421)
                ·
                  refine ⟨339926931839947338288829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812943636479719137540421 339926931839947338288829)
                  ·
                    rfl

theorem cell21_1489512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1489512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489512 prefixEnd_1489512 := by exact prefixLift 1489512
  have htrace : WordTrace (prefixWord ++ tailWord_1489512) baseStart_1489512 baseEnd_1489512 := by
    simpa [prefixWord, tailWord_1489512, baseEnd_1489512] using wordTrace_append hprefix tailTrace_1489512
  have hstable : (prefixWord ++ tailWord_1489512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489512).length < 2 ^ (prefixWord ++ tailWord_1489512).sum := by decide
  have hdescent : baseEnd_1489512 < baseStart_1489512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489537 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1489537 : Nat := 118140960795 + 1489537 * 2 ^ 59
def prefixEnd_1489537 : Nat := 4983230072969 + 3 ^ 40 * 1489537 * 2
def baseEnd_1489537 : Nat := 339932637180552850372111

theorem tailTrace_1489537 : CollatzResearch.WordTrace tailWord_1489537 prefixEnd_1489537 339932637180552850372111 := by
  unfold tailWord_1489537
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327877604669316511474865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36218585069779544340983243 54327877604669316511474865)
  ·
    refine ⟨40745908203501987383606149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54327877604669316511474865 40745908203501987383606149)
    ·
      refine ⟨7639857788156622634426153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40745908203501987383606149 7639857788156622634426153)
      ·
        refine ⟨5729893341117466975819615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7639857788156622634426153 5729893341117466975819615)
        ·
          refine ⟨8594840011676200463729423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729893341117466975819615 8594840011676200463729423)
          ·
            refine ⟨12892260017514300695594135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594840011676200463729423 12892260017514300695594135)
            ·
              refine ⟨19338390026271451043391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892260017514300695594135 19338390026271451043391203)
              ·
                refine ⟨29007585039407176565086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19338390026271451043391203 29007585039407176565086805)
                ·
                  refine ⟨339932637180552850372111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29007585039407176565086805 339932637180552850372111)
                  ·
                    rfl

theorem cell21_1489537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1489537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489537 prefixEnd_1489537 := by exact prefixLift 1489537
  have htrace : WordTrace (prefixWord ++ tailWord_1489537) baseStart_1489537 baseEnd_1489537 := by
    simpa [prefixWord, tailWord_1489537, baseEnd_1489537] using wordTrace_append hprefix tailTrace_1489537
  have hstable : (prefixWord ++ tailWord_1489537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489537).length < 2 ^ (prefixWord ++ tailWord_1489537).sum := by decide
  have hdescent : baseEnd_1489537 < baseStart_1489537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489554 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1489554 : Nat := 118140960795 + 1489554 * 2 ^ 59
def prefixEnd_1489554 : Nat := 4983230072969 + 3 ^ 40 * 1489554 * 2
def baseEnd_1489554 : Nat := 339936516812164598588743

theorem tailTrace_1489554 : CollatzResearch.WordTrace tailWord_1489554 prefixEnd_1489554 339936516812164598588743 := by
  unfold tailWord_1489554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13582124411401932103710929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36218998430405152276562477 13582124411401932103710929)
  ·
    refine ⟨10186593308551449077783197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13582124411401932103710929 10186593308551449077783197)
    ·
      refine ⟨3819972490706793404168699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10186593308551449077783197 3819972490706793404168699)
      ·
        refine ⟨5729958736060190106253049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819972490706793404168699 5729958736060190106253049)
        ·
          refine ⟨4297469052045142579689787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5729958736060190106253049 4297469052045142579689787)
          ·
            refine ⟨6446203578067713869534681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297469052045142579689787 6446203578067713869534681)
            ·
              refine ⟨4834652683550785402151011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6446203578067713869534681 4834652683550785402151011)
              ·
                refine ⟨7251979025326178103226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834652683550785402151011 7251979025326178103226517)
                ·
                  refine ⟨339936516812164598588743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7251979025326178103226517 339936516812164598588743)
                  ·
                    rfl

theorem cell21_1489554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1489554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489554 prefixEnd_1489554 := by exact prefixLift 1489554
  have htrace : WordTrace (prefixWord ++ tailWord_1489554) baseStart_1489554 baseEnd_1489554 := by
    simpa [prefixWord, tailWord_1489554, baseEnd_1489554] using wordTrace_append hprefix tailTrace_1489554
  have hstable : (prefixWord ++ tailWord_1489554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489554).length < 2 ^ (prefixWord ++ tailWord_1489554).sum := by decide
  have hdescent : baseEnd_1489554 < baseStart_1489554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489726 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1489726 : Nat := 118140960795 + 1489726 * 2 ^ 59
def prefixEnd_1489726 : Nat := 4983230072969 + 3 ^ 40 * 1489726 * 2
def baseEnd_1489726 : Nat := 339975769555530521721725

theorem tailTrace_1489726 : CollatzResearch.WordTrace tailWord_1489726 prefixEnd_1489726 339975769555530521721725 := by
  unfold tailWord_1489726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791846375123075223763129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36223180667323067860070021 6791846375123075223763129)
  ·
    refine ⟨5093884781342306417822347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6791846375123075223763129 5093884781342306417822347)
    ·
      refine ⟨7640827172013459626733521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093884781342306417822347 7640827172013459626733521)
      ·
        refine ⟨5730620379010094720050141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7640827172013459626733521 5730620379010094720050141)
        ·
          refine ⟨2148982642128785520018803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5730620379010094720050141 2148982642128785520018803)
          ·
            refine ⟨3223473963193178280028205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148982642128785520018803 3223473963193178280028205)
            ·
              refine ⟨1208802736197441855010577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3223473963193178280028205 1208802736197441855010577)
              ·
                refine ⟨906602052148081391257933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208802736197441855010577 906602052148081391257933)
                ·
                  refine ⟨339975769555530521721725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906602052148081391257933 339975769555530521721725)
                  ·
                    rfl

theorem cell21_1489726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1489726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489726 prefixEnd_1489726 := by exact prefixLift 1489726
  have htrace : WordTrace (prefixWord ++ tailWord_1489726) baseStart_1489726 baseEnd_1489726 := by
    simpa [prefixWord, tailWord_1489726, baseEnd_1489726] using wordTrace_append hprefix tailTrace_1489726
  have hstable : (prefixWord ++ tailWord_1489726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489726).length < 2 ^ (prefixWord ++ tailWord_1489726).sum := by decide
  have hdescent : baseEnd_1489726 < baseStart_1489726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489785 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 3]
def baseStart_1489785 : Nat := 118140960795 + 1489785 * 2 ^ 59
def prefixEnd_1489785 : Nat := 4983230072969 + 3 ^ 40 * 1489785 * 2
def baseEnd_1489785 : Nat := 339989234159359530238271

theorem tailTrace_1489785 : CollatzResearch.WordTrace tailWord_1489785 prefixEnd_1489785 339989234159359530238271 := by
  unfold tailWord_1489785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54336922907770854866502809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36224615271847236577668539 54336922907770854866502809)
  ·
    refine ⟨40752692180828141149877107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54336922907770854866502809 40752692180828141149877107)
    ·
      refine ⟨61129038271242211724815661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40752692180828141149877107 61129038271242211724815661)
      ·
        refine ⟨22923389351715829396805873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61129038271242211724815661 22923389351715829396805873)
        ·
          refine ⟨17192542013786872047604405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22923389351715829396805873 17192542013786872047604405)
          ·
            refine ⟨1611800813792519254462913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17192542013786872047604405 1611800813792519254462913)
            ·
              refine ⟨1208850610344389440847185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611800813792519254462913 1208850610344389440847185)
              ·
                refine ⟨906637957758292080635389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208850610344389440847185 906637957758292080635389)
                ·
                  refine ⟨339989234159359530238271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906637957758292080635389 339989234159359530238271)
                  ·
                    rfl

theorem cell21_1489785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_1489785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489785 prefixEnd_1489785 := by exact prefixLift 1489785
  have htrace : WordTrace (prefixWord ++ tailWord_1489785) baseStart_1489785 baseEnd_1489785 := by
    simpa [prefixWord, tailWord_1489785, baseEnd_1489785] using wordTrace_append hprefix tailTrace_1489785
  have hstable : (prefixWord ++ tailWord_1489785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489785).length < 2 ^ (prefixWord ++ tailWord_1489785).sum := by decide
  have hdescent : baseEnd_1489785 < baseStart_1489785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489827 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 3]
def baseStart_1489827 : Nat := 118140960795 + 1489827 * 2 ^ 59
def prefixEnd_1489827 : Nat := 4983230072969 + 3 ^ 40 * 1489827 * 2
def baseEnd_1489827 : Nat := 339998819131576790538185

theorem tailTrace_1489827 : CollatzResearch.WordTrace tailWord_1489827 prefixEnd_1489827 339998819131576790538185 := by
  unfold tailWord_1489827
  simp only [CollatzResearch.WordTrace]
  refine ⟨54338454773618696039531735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36225636515745797359687823 54338454773618696039531735)
  ·
    refine ⟨81507682160428044059297603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54338454773618696039531735 81507682160428044059297603)
    ·
      refine ⟨122261523240642066088946405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81507682160428044059297603 122261523240642066088946405)
      ·
        refine ⟨22924035607620387391677451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122261523240642066088946405 22924035607620387391677451)
        ·
          refine ⟨34386053411430581087516177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22924035607620387391677451 34386053411430581087516177)
          ·
            refine ⟨25789540058572935815637133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34386053411430581087516177 25789540058572935815637133)
            ·
              refine ⟨9671077521964850930863925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25789540058572935815637133 9671077521964850930863925)
              ·
                refine ⟨906663517684204774768493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9671077521964850930863925 906663517684204774768493)
                ·
                  refine ⟨339998819131576790538185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906663517684204774768493 339998819131576790538185)
                  ·
                    rfl

theorem cell21_1489827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].length) (baseStart_1489827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489827 prefixEnd_1489827 := by exact prefixLift 1489827
  have htrace : WordTrace (prefixWord ++ tailWord_1489827) baseStart_1489827 baseEnd_1489827 := by
    simpa [prefixWord, tailWord_1489827, baseEnd_1489827] using wordTrace_append hprefix tailTrace_1489827
  have hstable : (prefixWord ++ tailWord_1489827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489827).length < 2 ^ (prefixWord ++ tailWord_1489827).sum := by decide
  have hdescent : baseEnd_1489827 < baseStart_1489827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489844 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1489844 : Nat := 118140960795 + 1489844 * 2 ^ 59
def prefixEnd_1489844 : Nat := 4983230072969 + 3 ^ 40 * 1489844 * 2
def baseEnd_1489844 : Nat := 340002698763188538754817

theorem tailTrace_1489844 : CollatzResearch.WordTrace tailWord_1489844 prefixEnd_1489844 340002698763188538754817 := by
  unfold tailWord_1489844
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169537407278553971450293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36226049876371405295267057 27169537407278553971450293)
  ·
    refine ⟨2547144131932364434823465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27169537407278553971450293 2547144131932364434823465)
    ·
      refine ⟨1910358098949273326117599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547144131932364434823465 1910358098949273326117599)
      ·
        refine ⟨2865537148423909989176399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910358098949273326117599 2865537148423909989176399)
        ·
          refine ⟨4298305722635864983764599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865537148423909989176399 4298305722635864983764599)
          ·
            refine ⟨6447458583953797475646899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298305722635864983764599 6447458583953797475646899)
            ·
              refine ⟨9671187875930696213470349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447458583953797475646899 9671187875930696213470349)
              ·
                refine ⟨3626695453474011080051381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9671187875930696213470349 3626695453474011080051381)
                ·
                  refine ⟨340002698763188538754817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626695453474011080051381 340002698763188538754817)
                  ·
                    rfl

theorem cell21_1489844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1489844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489844 prefixEnd_1489844 := by exact prefixLift 1489844
  have htrace : WordTrace (prefixWord ++ tailWord_1489844) baseStart_1489844 baseEnd_1489844 := by
    simpa [prefixWord, tailWord_1489844, baseEnd_1489844] using wordTrace_append hprefix tailTrace_1489844
  have hstable : (prefixWord ++ tailWord_1489844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489844).length < 2 ^ (prefixWord ++ tailWord_1489844).sum := by decide
  have hdescent : baseEnd_1489844 < baseStart_1489844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489878 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1489878 : Nat := 118140960795 + 1489878 * 2 ^ 59
def prefixEnd_1489878 : Nat := 4983230072969 + 3 ^ 40 * 1489878 * 2
def baseEnd_1489878 : Nat := 340010458026412035188081

theorem tailTrace_1489878 : CollatzResearch.WordTrace tailWord_1489878 prefixEnd_1489878 340010458026412035188081 := by
  unfold tailWord_1489878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396269681027120734352393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36226876597622621166425525 3396269681027120734352393)
  ·
    refine ⟨2547202260770340550764295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396269681027120734352393 2547202260770340550764295)
    ·
      refine ⟨3820803391155510826146443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547202260770340550764295 3820803391155510826146443)
      ·
        refine ⟨5731205086733266239219665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820803391155510826146443 5731205086733266239219665)
        ·
          refine ⟨4298403815049949679414749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5731205086733266239219665 4298403815049949679414749)
          ·
            refine ⟨1611901430643731129780531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4298403815049949679414749 1611901430643731129780531)
            ·
              refine ⟨2417852145965596694670797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611901430643731129780531 2417852145965596694670797)
              ·
                refine ⟨906694554737098760501549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417852145965596694670797 906694554737098760501549)
                ·
                  refine ⟨340010458026412035188081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906694554737098760501549 340010458026412035188081)
                  ·
                    rfl

theorem cell21_1489878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1489878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489878 prefixEnd_1489878 := by exact prefixLift 1489878
  have htrace : WordTrace (prefixWord ++ tailWord_1489878) baseStart_1489878 baseEnd_1489878 := by
    simpa [prefixWord, tailWord_1489878, baseEnd_1489878] using wordTrace_append hprefix tailTrace_1489878
  have hstable : (prefixWord ++ tailWord_1489878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489878).length < 2 ^ (prefixWord ++ tailWord_1489878).sum := by decide
  have hdescent : baseEnd_1489878 < baseStart_1489878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489903 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_1489903 : Nat := 118140960795 + 1489903 * 2 ^ 59
def prefixEnd_1489903 : Nat := 4983230072969 + 3 ^ 40 * 1489903 * 2
def baseEnd_1489903 : Nat := 340016163367017547271363

theorem tailTrace_1489903 : CollatzResearch.WordTrace tailWord_1489903 prefixEnd_1489903 340016163367017547271363 := by
  unfold tailWord_1489903
  simp only [CollatzResearch.WordTrace]
  refine ⟨54341226721343361019298363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36227484480895574012865575 54341226721343361019298363)
  ·
    refine ⟨81511840082015041528947545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54341226721343361019298363 81511840082015041528947545)
    ·
      refine ⟨61133880061511281146710659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81511840082015041528947545 61133880061511281146710659)
      ·
        refine ⟨91700820092266921720065989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61133880061511281146710659 91700820092266921720065989)
        ·
          refine ⟨17193903767300047822512373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91700820092266921720065989 17193903767300047822512373)
          ·
            refine ⟨1611928478184379483360535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17193903767300047822512373 1611928478184379483360535)
            ·
              refine ⟨2417892717276569225040803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611928478184379483360535 2417892717276569225040803)
              ·
                refine ⟨3626839075914853837561205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417892717276569225040803 3626839075914853837561205)
                ·
                  refine ⟨340016163367017547271363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626839075914853837561205 340016163367017547271363)
                  ·
                    rfl

theorem cell21_1489903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_1489903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489903 prefixEnd_1489903 := by exact prefixLift 1489903
  have htrace : WordTrace (prefixWord ++ tailWord_1489903) baseStart_1489903 baseEnd_1489903 := by
    simpa [prefixWord, tailWord_1489903, baseEnd_1489903] using wordTrace_append hprefix tailTrace_1489903
  have hstable : (prefixWord ++ tailWord_1489903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489903).length < 2 ^ (prefixWord ++ tailWord_1489903).sum := by decide
  have hdescent : baseEnd_1489903 < baseStart_1489903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489909 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1489909 : Nat := 118140960795 + 1489909 * 2 ^ 59
def prefixEnd_1489909 : Nat := 4983230072969 + 3 ^ 40 * 1489909 * 2
def baseEnd_1489909 : Nat := 340017532648762870171351

theorem tailTrace_1489909 : CollatzResearch.WordTrace tailWord_1489909 prefixEnd_1489909 340017532648762870171351 := by
  unfold tailWord_1489909
  simp only [CollatzResearch.WordTrace]
  refine ⟨54341445559321624044016781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36227630372881082696011187 54341445559321624044016781)
  ·
    refine ⟨20378042084745609016506293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54341445559321624044016781 20378042084745609016506293)
    ·
      refine ⟨1910441445444900845297465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20378042084745609016506293 1910441445444900845297465)
      ·
        refine ⟨1432831084083675633973099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910441445444900845297465 1432831084083675633973099)
        ·
          refine ⟨2149246626125513450959649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432831084083675633973099 2149246626125513450959649)
          ·
            refine ⟨1611934969594135088219737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149246626125513450959649 1611934969594135088219737)
            ·
              refine ⟨1208951227195601316164803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611934969594135088219737 1208951227195601316164803)
              ·
                refine ⟨1813426840793401974247205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208951227195601316164803 1813426840793401974247205)
                ·
                  refine ⟨340017532648762870171351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813426840793401974247205 340017532648762870171351)
                  ·
                    rfl

theorem cell21_1489909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1489909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489909 prefixEnd_1489909 := by exact prefixLift 1489909
  have htrace : WordTrace (prefixWord ++ tailWord_1489909) baseStart_1489909 baseEnd_1489909 := by
    simpa [prefixWord, tailWord_1489909, baseEnd_1489909] using wordTrace_append hprefix tailTrace_1489909
  have hstable : (prefixWord ++ tailWord_1489909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489909).length < 2 ^ (prefixWord ++ tailWord_1489909).sum := by decide
  have hdescent : baseEnd_1489909 < baseStart_1489909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489931 : List Nat := [1, 1, 1, 1, 6, 2, 2, 7]
def baseStart_1489931 : Nat := 118140960795 + 1489931 * 2 ^ 59
def prefixEnd_1489931 : Nat := 4983230072969 + 3 ^ 40 * 1489931 * 2
def baseEnd_1489931 : Nat := 113340851116165240268213

theorem tailTrace_1489931 : CollatzResearch.WordTrace tailWord_1489931 prefixEnd_1489931 113340851116165240268213 := by
  unfold tailWord_1489931
  simp only [CollatzResearch.WordTrace]
  refine ⟨54342247965241921801317647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36228165310161281200878431 54342247965241921801317647)
  ·
    refine ⟨81513371947862882701976471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54342247965241921801317647 81513371947862882701976471)
    ·
      refine ⟨122270057921794324052964707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81513371947862882701976471 122270057921794324052964707)
      ·
        refine ⟨183405086882691486079447061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122270057921794324052964707 183405086882691486079447061)
        ·
          refine ⟨8597113447626163409974081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183405086882691486079447061 8597113447626163409974081)
          ·
            refine ⟨6447835085719622557480561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597113447626163409974081 6447835085719622557480561)
            ·
              refine ⟨4835876314289716918110421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447835085719622557480561 4835876314289716918110421)
              ·
                refine ⟨113340851116165240268213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4835876314289716918110421 113340851116165240268213)
                ·
                  rfl

theorem cell21_1489931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_1489931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489931 prefixEnd_1489931 := by exact prefixLift 1489931
  have htrace : WordTrace (prefixWord ++ tailWord_1489931) baseStart_1489931 baseEnd_1489931 := by
    simpa [prefixWord, tailWord_1489931, baseEnd_1489931] using wordTrace_append hprefix tailTrace_1489931
  have hstable : (prefixWord ++ tailWord_1489931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489931).length < 2 ^ (prefixWord ++ tailWord_1489931).sum := by decide
  have hdescent : baseEnd_1489931 < baseStart_1489931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489948 : List Nat := [2, 2, 3, 1, 5, 8]
def baseStart_1489948 : Nat := 118140960795 + 1489948 * 2 ^ 59
def prefixEnd_1489948 : Nat := 4983230072969 + 3 ^ 40 * 1489948 * 2
def baseEnd_1489948 : Nat := 12593571591855832185973

theorem tailTrace_1489948 : CollatzResearch.WordTrace tailWord_1489948 prefixEnd_1489948 12593571591855832185973 := by
  unfold tailWord_1489948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27171434003090166852343249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36228578670786889136457665 27171434003090166852343249)
  ·
    refine ⟨20378575502317625139257437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27171434003090166852343249 20378575502317625139257437)
    ·
      refine ⟨7641965813369109427221539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20378575502317625139257437 7641965813369109427221539)
      ·
        refine ⟨11462948720053664140832309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641965813369109427221539 11462948720053664140832309)
        ·
          refine ⟨1074651442505031013203029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11462948720053664140832309 1074651442505031013203029)
          ·
            refine ⟨12593571591855832185973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1074651442505031013203029 12593571591855832185973)
            ·
              rfl

theorem cell21_1489948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 8].length) (baseStart_1489948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1489948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1489948 prefixEnd_1489948 := by exact prefixLift 1489948
  have htrace : WordTrace (prefixWord ++ tailWord_1489948) baseStart_1489948 baseEnd_1489948 := by
    simpa [prefixWord, tailWord_1489948, baseEnd_1489948] using wordTrace_append hprefix tailTrace_1489948
  have hstable : (prefixWord ++ tailWord_1489948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489948).length < 2 ^ (prefixWord ++ tailWord_1489948).sum := by decide
  have hdescent : baseEnd_1489948 < baseStart_1489948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490041 : List Nat := [1, 2, 1, 3, 5, 2, 2, 5]
def baseStart_1490041 : Nat := 118140960795 + 1490041 * 2 ^ 59
def prefixEnd_1490041 : Nat := 4983230072969 + 3 ^ 40 * 1490041 * 2
def baseEnd_1490041 : Nat := 113349218949053324657027

theorem tailTrace_1490041 : CollatzResearch.WordTrace tailWord_1490041 prefixEnd_1490041 113349218949053324657027 := by
  unfold tailWord_1490041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54346259994843410587821977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36230839996562273725214651 54346259994843410587821977)
  ·
    refine ⟨40759694996132557940866483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54346259994843410587821977 40759694996132557940866483)
    ·
      refine ⟨61139542494198836911299725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40759694996132557940866483 61139542494198836911299725)
      ·
        refine ⟨22927328435324563841737397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61139542494198836911299725 22927328435324563841737397)
        ·
          refine ⟨2149437040811677860162881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22927328435324563841737397 2149437040811677860162881)
          ·
            refine ⟨1612077780608758395122161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149437040811677860162881 1612077780608758395122161)
            ·
              refine ⟨1209058335456568796341621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612077780608758395122161 1209058335456568796341621)
              ·
                refine ⟨113349218949053324657027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1209058335456568796341621 113349218949053324657027)
                ·
                  rfl

theorem cell21_1490041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].length) (baseStart_1490041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490041 prefixEnd_1490041 := by exact prefixLift 1490041
  have htrace : WordTrace (prefixWord ++ tailWord_1490041) baseStart_1490041 baseEnd_1490041 := by
    simpa [prefixWord, tailWord_1490041, baseEnd_1490041] using wordTrace_append hprefix tailTrace_1490041
  have hstable : (prefixWord ++ tailWord_1490041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490041).length < 2 ^ (prefixWord ++ tailWord_1490041).sum := by decide
  have hdescent : baseEnd_1490041 < baseStart_1490041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490134 : List Nat := [5, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1490134 : Nat := 118140960795 + 1490134 * 2 ^ 59
def prefixEnd_1490134 : Nat := 4983230072969 + 3 ^ 40 * 1490134 * 2
def baseEnd_1490134 : Nat := 113356293571404159640297

theorem tailTrace_1490134 : CollatzResearch.WordTrace tailWord_1490134 prefixEnd_1490134 113356293571404159640297 := by
  unfold tailWord_1490134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396853248969155466934841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36233101322337658313971637 3396853248969155466934841)
  ·
    refine ⟨2547639936726866600201131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396853248969155466934841 2547639936726866600201131)
    ·
      refine ⟨3821459905090299900301697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547639936726866600201131 3821459905090299900301697)
      ·
        refine ⟨2866094928817724925226273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3821459905090299900301697 2866094928817724925226273)
        ·
          refine ⟨2149571196613293693919705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866094928817724925226273 2149571196613293693919705)
          ·
            refine ⟨1612178397459970270439779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149571196613293693919705 1612178397459970270439779)
            ·
              refine ⟨2418267596189955405659669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612178397459970270439779 2418267596189955405659669)
              ·
                refine ⟨113356293571404159640297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2418267596189955405659669 113356293571404159640297)
                ·
                  rfl

theorem cell21_1490134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1490134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490134 prefixEnd_1490134 := by exact prefixLift 1490134
  have htrace : WordTrace (prefixWord ++ tailWord_1490134) baseStart_1490134 baseEnd_1490134 := by
    simpa [prefixWord, tailWord_1490134, baseEnd_1490134] using wordTrace_append hprefix tailTrace_1490134
  have hstable : (prefixWord ++ tailWord_1490134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490134).length < 2 ^ (prefixWord ++ tailWord_1490134).sum := by decide
  have hdescent : baseEnd_1490134 < baseStart_1490134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490145 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1490145 : Nat := 118140960795 + 1490145 * 2 ^ 59
def prefixEnd_1490145 : Nat := 4983230072969 + 3 ^ 40 * 1490145 * 2
def baseEnd_1490145 : Nat := 340071391064078904237535

theorem tailTrace_1490145 : CollatzResearch.WordTrace tailWord_1490145 prefixEnd_1490145 340071391064078904237535 := by
  unfold tailWord_1490145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54350053186466636349607889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233368790977757566405259 54350053186466636349607889)
  ·
    refine ⟨40762539889849977262205917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54350053186466636349607889 40762539889849977262205917)
    ·
      refine ⟨15285952458693741473327219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40762539889849977262205917 15285952458693741473327219)
      ·
        refine ⟨22928928688040612209990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15285952458693741473327219 22928928688040612209990829)
        ·
          refine ⟨8598348258015229578746561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22928928688040612209990829 8598348258015229578746561)
          ·
            refine ⟨6448761193511422184059921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8598348258015229578746561 6448761193511422184059921)
            ·
              refine ⟨4836570895133566638044941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6448761193511422184059921 4836570895133566638044941)
              ·
                refine ⟨1813714085675087489266853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4836570895133566638044941 1813714085675087489266853)
                ·
                  refine ⟨340071391064078904237535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813714085675087489266853 340071391064078904237535)
                  ·
                    rfl

theorem cell21_1490145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1490145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490145 prefixEnd_1490145 := by exact prefixLift 1490145
  have htrace : WordTrace (prefixWord ++ tailWord_1490145) baseStart_1490145 baseEnd_1490145 := by
    simpa [prefixWord, tailWord_1490145, baseEnd_1490145] using wordTrace_append hprefix tailTrace_1490145
  have hstable : (prefixWord ++ tailWord_1490145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490145).length < 2 ^ (prefixWord ++ tailWord_1490145).sum := by decide
  have hdescent : baseEnd_1490145 < baseStart_1490145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490190 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1490190 : Nat := 118140960795 + 1490190 * 2 ^ 59
def prefixEnd_1490190 : Nat := 4983230072969 + 3 ^ 40 * 1490190 * 2
def baseEnd_1490190 : Nat := 340081660677168825987443

theorem tailTrace_1490190 : CollatzResearch.WordTrace tailWord_1490190 prefixEnd_1490190 340081660677168825987443 := by
  unfold tailWord_1490190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793961808912951129374503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36234462980869072689997349 6793961808912951129374503)
  ·
    refine ⟨10190942713369426694061755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793961808912951129374503 10190942713369426694061755)
    ·
      refine ⟨15286414070054140041092633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10190942713369426694061755 15286414070054140041092633)
      ·
        refine ⟨11464810552540605030819475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15286414070054140041092633 11464810552540605030819475)
        ·
          refine ⟨17197215828810907546229213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11464810552540605030819475 17197215828810907546229213)
          ·
            refine ⟨6448955935804090329835955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17197215828810907546229213 6448955935804090329835955)
            ·
              refine ⟨9673433903706135494753933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448955935804090329835955 9673433903706135494753933)
              ·
                refine ⟨3627537713889800810532725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9673433903706135494753933 3627537713889800810532725)
                ·
                  refine ⟨340081660677168825987443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3627537713889800810532725 340081660677168825987443)
                  ·
                    rfl

theorem cell21_1490190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1490190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490190 prefixEnd_1490190 := by exact prefixLift 1490190
  have htrace : WordTrace (prefixWord ++ tailWord_1490190) baseStart_1490190 baseEnd_1490190 := by
    simpa [prefixWord, tailWord_1490190, baseEnd_1490190] using wordTrace_append hprefix tailTrace_1490190
  have hstable : (prefixWord ++ tailWord_1490190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490190).length < 2 ^ (prefixWord ++ tailWord_1490190).sum := by decide
  have hdescent : baseEnd_1490190 < baseStart_1490190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490210 : List Nat := [3, 3, 1, 1, 5, 1, 2, 5]
def baseStart_1490210 : Nat := 118140960795 + 1490210 * 2 ^ 59
def prefixEnd_1490210 : Nat := 4983230072969 + 3 ^ 40 * 1490210 * 2
def baseEnd_1490210 : Nat := 113362074983217745218023

theorem tailTrace_1490210 : CollatzResearch.WordTrace tailWord_1490210 prefixEnd_1490210 113362074983217745218023 := by
  unfold tailWord_1490210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588105982807788112681021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36234949287487434967149389 13588105982807788112681021)
  ·
    refine ⟨5095539743552920542255383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13588105982807788112681021 5095539743552920542255383)
    ·
      refine ⟨7643309615329380813383075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095539743552920542255383 7643309615329380813383075)
      ·
        refine ⟨11464964422994071220074613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7643309615329380813383075 11464964422994071220074613)
        ·
          refine ⟨1074840414655694176881995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11464964422994071220074613 1074840414655694176881995)
          ·
            refine ⟨1612260621983541265322993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074840414655694176881995 1612260621983541265322993)
            ·
              refine ⟨1209195466487655948992245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612260621983541265322993 1209195466487655948992245)
              ·
                refine ⟨113362074983217745218023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1209195466487655948992245 113362074983217745218023)
                ·
                  rfl

theorem cell21_1490210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_1490210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490210 prefixEnd_1490210 := by exact prefixLift 1490210
  have htrace : WordTrace (prefixWord ++ tailWord_1490210) baseStart_1490210 baseEnd_1490210 := by
    simpa [prefixWord, tailWord_1490210, baseEnd_1490210] using wordTrace_append hprefix tailTrace_1490210
  have hstable : (prefixWord ++ tailWord_1490210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490210).length < 2 ^ (prefixWord ++ tailWord_1490210).sum := by decide
  have hdescent : baseEnd_1490210 < baseStart_1490210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490241 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 3]
def baseStart_1490241 : Nat := 118140960795 + 1490241 * 2 ^ 59
def prefixEnd_1490241 : Nat := 4983230072969 + 3 ^ 40 * 1490241 * 2
def baseEnd_1490241 : Nat := 340093299572004070637339

theorem tailTrace_1490241 : CollatzResearch.WordTrace tailWord_1490241 prefixEnd_1490241 340093299572004070637339 := by
  unfold tailWord_1490241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54353554594118844745102577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36235703062745896496735051 54353554594118844745102577)
  ·
    refine ⟨40765165945589133558826933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54353554594118844745102577 40765165945589133558826933)
    ·
      refine ⟨3821734307398981271140025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40765165945589133558826933 3821734307398981271140025)
      ·
        refine ⟨2866300730549235953355019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3821734307398981271140025 2866300730549235953355019)
        ·
          refine ⟨4299451095823853930032529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866300730549235953355019 4299451095823853930032529)
          ·
            refine ⟨3224588321867890447524397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299451095823853930032529 3224588321867890447524397)
            ·
              refine ⟨1209220620700458917821649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224588321867890447524397 1209220620700458917821649)
              ·
                refine ⟨906915465525344188366237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209220620700458917821649 906915465525344188366237)
                ·
                  refine ⟨340093299572004070637339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906915465525344188366237 340093299572004070637339)
                  ·
                    rfl

theorem cell21_1490241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_1490241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490241 prefixEnd_1490241 := by exact prefixLift 1490241
  have htrace : WordTrace (prefixWord ++ tailWord_1490241) baseStart_1490241 baseEnd_1490241 := by
    simpa [prefixWord, tailWord_1490241, baseEnd_1490241] using wordTrace_append hprefix tailTrace_1490241
  have hstable : (prefixWord ++ tailWord_1490241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490241).length < 2 ^ (prefixWord ++ tailWord_1490241).sum := by decide
  have hdescent : baseEnd_1490241 < baseStart_1490241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490311 : List Nat := [1, 1, 4, 2, 2, 2, 3, 6]
def baseStart_1490311 : Nat := 118140960795 + 1490311 * 2 ^ 59
def prefixEnd_1490311 : Nat := 4983230072969 + 3 ^ 40 * 1490311 * 2
def baseEnd_1490311 : Nat := 113369758175233168156843

theorem tailTrace_1490311 : CollatzResearch.WordTrace tailWord_1490311 prefixEnd_1490311 113369758175233168156843 := by
  unfold tailWord_1490311
  simp only [CollatzResearch.WordTrace]
  refine ⟨54356107703865246700150787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36237405135910164466767191 54356107703865246700150787)
  ·
    refine ⟨81534161555797870050226181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54356107703865246700150787 81534161555797870050226181)
    ·
      refine ⟨15287655291712100634417409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81534161555797870050226181 15287655291712100634417409)
      ·
        refine ⟨11465741468784075475813057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15287655291712100634417409 11465741468784075475813057)
        ·
          refine ⟨8599306101588056606859793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11465741468784075475813057 8599306101588056606859793)
          ·
            refine ⟨6449479576191042455144845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599306101588056606859793 6449479576191042455144845)
            ·
              refine ⟨2418554841071640920679317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6449479576191042455144845 2418554841071640920679317)
              ·
                refine ⟨113369758175233168156843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2418554841071640920679317 113369758175233168156843)
                ·
                  rfl

theorem cell21_1490311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_1490311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490311 prefixEnd_1490311 := by exact prefixLift 1490311
  have htrace : WordTrace (prefixWord ++ tailWord_1490311) baseStart_1490311 baseEnd_1490311 := by
    simpa [prefixWord, tailWord_1490311, baseEnd_1490311] using wordTrace_append hprefix tailTrace_1490311
  have hstable : (prefixWord ++ tailWord_1490311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490311).length < 2 ^ (prefixWord ++ tailWord_1490311).sum := by decide
  have hdescent : baseEnd_1490311 < baseStart_1490311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490325 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1490325 : Nat := 118140960795 + 1490325 * 2 ^ 59
def prefixEnd_1490325 : Nat := 4983230072969 + 3 ^ 40 * 1490325 * 2
def baseEnd_1490325 : Nat := 340112469516438591237167

theorem tailTrace_1490325 : CollatzResearch.WordTrace tailWord_1490325 prefixEnd_1490325 340112469516438591237167 := by
  unfold tailWord_1490325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54356618325814527091160429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36237745550543018060773619 54356618325814527091160429)
  ·
    refine ⟨20383731872180447659185161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54356618325814527091160429 20383731872180447659185161)
    ·
      refine ⟨15287798904135335744388871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20383731872180447659185161 15287798904135335744388871)
      ·
        refine ⟨22931698356203003616583307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15287798904135335744388871 22931698356203003616583307)
        ·
          refine ⟨34397547534304505424874961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22931698356203003616583307 34397547534304505424874961)
          ·
            refine ⟨25798160650728379068656221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34397547534304505424874961 25798160650728379068656221)
            ·
              refine ⟨9674310244023142150746083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25798160650728379068656221 9674310244023142150746083)
              ·
                refine ⟨14511465366034713226119125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674310244023142150746083 14511465366034713226119125)
                ·
                  refine ⟨340112469516438591237167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14511465366034713226119125 340112469516438591237167)
                  ·
                    rfl

theorem cell21_1490325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1490325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490325 prefixEnd_1490325 := by exact prefixLift 1490325
  have htrace : WordTrace (prefixWord ++ tailWord_1490325) baseStart_1490325 baseEnd_1490325 := by
    simpa [prefixWord, tailWord_1490325, baseEnd_1490325] using wordTrace_append hprefix tailTrace_1490325
  have hstable : (prefixWord ++ tailWord_1490325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490325).length < 2 ^ (prefixWord ++ tailWord_1490325).sum := by decide
  have hdescent : baseEnd_1490325 < baseStart_1490325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490553 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1490553 : Nat := 118140960795 + 1490553 * 2 ^ 59
def prefixEnd_1490553 : Nat := 4983230072969 + 3 ^ 40 * 1490553 * 2
def baseEnd_1490553 : Nat := 340164502222760861436701

theorem tailTrace_1490553 : CollatzResearch.WordTrace tailWord_1490553 prefixEnd_1490553 340164502222760861436701 := by
  unfold tailWord_1490553
  simp only [CollatzResearch.WordTrace]
  refine ⟨54364934168988522030460313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36243289445992348020306875 54364934168988522030460313)
  ·
    refine ⟨40773700626741391522845235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54364934168988522030460313 40773700626741391522845235)
    ·
      refine ⟨61160550940112087284267853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40773700626741391522845235 61160550940112087284267853)
      ·
        refine ⟨22935206602542032731600445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61160550940112087284267853 22935206602542032731600445)
        ·
          refine ⟨8600702475953262274350167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22935206602542032731600445 8600702475953262274350167)
          ·
            refine ⟨12901053713929893411525251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600702475953262274350167 12901053713929893411525251)
            ·
              refine ⟨19351580570894840117287877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901053713929893411525251 19351580570894840117287877)
              ·
                refine ⟨3628421357042782521991477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19351580570894840117287877 3628421357042782521991477)
                ·
                  refine ⟨340164502222760861436701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3628421357042782521991477 340164502222760861436701)
                  ·
                    rfl

theorem cell21_1490553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1490553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490553 prefixEnd_1490553 := by exact prefixLift 1490553
  have htrace : WordTrace (prefixWord ++ tailWord_1490553) baseStart_1490553 baseEnd_1490553 := by
    simpa [prefixWord, tailWord_1490553, baseEnd_1490553] using wordTrace_append hprefix tailTrace_1490553
  have hstable : (prefixWord ++ tailWord_1490553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490553).length < 2 ^ (prefixWord ++ tailWord_1490553).sum := by decide
  have hdescent : baseEnd_1490553 < baseStart_1490553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490584 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_1490584 : Nat := 118140960795 + 1490584 * 2 ^ 59
def prefixEnd_1490584 : Nat := 4983230072969 + 3 ^ 40 * 1490584 * 2
def baseEnd_1490584 : Nat := 340171576845111696419971

theorem tailTrace_1490584 : CollatzResearch.WordTrace tailWord_1490584 prefixEnd_1490584 340171576845111696419971 := by
  unfold tailWord_1490584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183032415938107162419403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36244043221250809549892537 27183032415938107162419403)
  ·
    refine ⟨40774548623907160743629105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27183032415938107162419403 40774548623907160743629105)
    ·
      refine ⟨30580911467930370557721829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40774548623907160743629105 30580911467930370557721829)
      ·
        refine ⟨5733920900236944479572843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30580911467930370557721829 5733920900236944479572843)
        ·
          refine ⟨8600881350355416719359265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733920900236944479572843 8600881350355416719359265)
          ·
            refine ⟨6450661012766562539519449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8600881350355416719359265 6450661012766562539519449)
            ·
              refine ⟨4837995759574921904639587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450661012766562539519449 4837995759574921904639587)
              ·
                refine ⟨7256993639362382856959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837995759574921904639587 7256993639362382856959381)
                ·
                  refine ⟨340171576845111696419971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7256993639362382856959381 340171576845111696419971)
                  ·
                    rfl

theorem cell21_1490584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_1490584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490584 prefixEnd_1490584 := by exact prefixLift 1490584
  have htrace : WordTrace (prefixWord ++ tailWord_1490584) baseStart_1490584 baseEnd_1490584 := by
    simpa [prefixWord, tailWord_1490584, baseEnd_1490584] using wordTrace_append hprefix tailTrace_1490584
  have hstable : (prefixWord ++ tailWord_1490584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490584).length < 2 ^ (prefixWord ++ tailWord_1490584).sum := by decide
  have hdescent : baseEnd_1490584 < baseStart_1490584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490660 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1490660 : Nat := 118140960795 + 1490660 * 2 ^ 59
def prefixEnd_1490660 : Nat := 4983230072969 + 3 ^ 40 * 1490660 * 2
def baseEnd_1490660 : Nat := 340188921080552453153149

theorem tailTrace_1490660 : CollatzResearch.WordTrace tailWord_1490660 prefixEnd_1490660 340188921080552453153149 := by
  unfold tailWord_1490660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184418389800439652302717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36245891186400586203070289 27184418389800439652302717)
  ·
    refine ⟨10194156896175164869613519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27184418389800439652302717 10194156896175164869613519)
    ·
      refine ⟨15291235344262747304420279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194156896175164869613519 15291235344262747304420279)
      ·
        refine ⟨22936853016394120956630419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15291235344262747304420279 22936853016394120956630419)
        ·
          refine ⟨34405279524591181434945629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22936853016394120956630419 34405279524591181434945629)
          ·
            refine ⟨12901979821721693038104611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34405279524591181434945629 12901979821721693038104611)
            ·
              refine ⟨19352969732582539557156917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901979821721693038104611 19352969732582539557156917)
              ·
                refine ⟨1814340912429613083483461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19352969732582539557156917 1814340912429613083483461)
                ·
                  refine ⟨340188921080552453153149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814340912429613083483461 340188921080552453153149)
                  ·
                    rfl

theorem cell21_1490660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1490660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490660 prefixEnd_1490660 := by exact prefixLift 1490660
  have htrace : WordTrace (prefixWord ++ tailWord_1490660) baseStart_1490660 baseEnd_1490660 := by
    simpa [prefixWord, tailWord_1490660, baseEnd_1490660] using wordTrace_append hprefix tailTrace_1490660
  have hstable : (prefixWord ++ tailWord_1490660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490660).length < 2 ^ (prefixWord ++ tailWord_1490660).sum := by decide
  have hdescent : baseEnd_1490660 < baseStart_1490660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490663 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_1490663 : Nat := 118140960795 + 1490663 * 2 ^ 59
def prefixEnd_1490663 : Nat := 4983230072969 + 3 ^ 40 * 1490663 * 2
def baseEnd_1490663 : Nat := 340189605721425114603143

theorem tailTrace_1490663 : CollatzResearch.WordTrace tailWord_1490663 prefixEnd_1490663 340189605721425114603143 := by
  unfold tailWord_1490663
  simp only [CollatzResearch.WordTrace]
  refine ⟨54368946198590010816964643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36245964132393340544643095 54368946198590010816964643)
  ·
    refine ⟨81553419297885016225446965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54368946198590010816964643 81553419297885016225446965)
    ·
      refine ⟨7645633059176720271135653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81553419297885016225446965 7645633059176720271135653)
      ·
        refine ⟨1433556198595635050837935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7645633059176720271135653 1433556198595635050837935)
        ·
          refine ⟨2150334297893452576256903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433556198595635050837935 2150334297893452576256903)
          ·
            refine ⟨3225501446840178864385355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150334297893452576256903 3225501446840178864385355)
            ·
              refine ⟨4838252170260268296578033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225501446840178864385355 4838252170260268296578033)
              ·
                refine ⟨3628689127695201222433525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4838252170260268296578033 3628689127695201222433525)
                ·
                  refine ⟨340189605721425114603143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3628689127695201222433525 340189605721425114603143)
                  ·
                    rfl

theorem cell21_1490663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_1490663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490663 prefixEnd_1490663 := by exact prefixLift 1490663
  have htrace : WordTrace (prefixWord ++ tailWord_1490663) baseStart_1490663 baseEnd_1490663 := by
    simpa [prefixWord, tailWord_1490663, baseEnd_1490663] using wordTrace_append hprefix tailTrace_1490663
  have hstable : (prefixWord ++ tailWord_1490663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490663).length < 2 ^ (prefixWord ++ tailWord_1490663).sum := by decide
  have hdescent : baseEnd_1490663 < baseStart_1490663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490770 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1490770 : Nat := 118140960795 + 1490770 * 2 ^ 59
def prefixEnd_1490770 : Nat := 4983230072969 + 3 ^ 40 * 1490770 * 2
def baseEnd_1490770 : Nat := 340214024579216706319591

theorem tailTrace_1490770 : CollatzResearch.WordTrace tailWord_1490770 prefixEnd_1490770 340214024579216706319591 := by
  unfold tailWord_1490770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593212202300592022777441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36248565872801578727406509 13593212202300592022777441)
  ·
    refine ⟨10194909151725444017083081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13593212202300592022777441 10194909151725444017083081)
    ·
      refine ⟨7646181863794083012812311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10194909151725444017083081 7646181863794083012812311)
      ·
        refine ⟨11469272795691124519218467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646181863794083012812311 11469272795691124519218467)
        ·
          refine ⟨17203909193536686778827701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469272795691124519218467 17203909193536686778827701)
          ·
            refine ⟨1612866486894064385515097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17203909193536686778827701 1612866486894064385515097)
            ·
              refine ⟨1209649865170548289136323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612866486894064385515097 1209649865170548289136323)
              ·
                refine ⟨1814474797755822433704485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209649865170548289136323 1814474797755822433704485)
                ·
                  refine ⟨340214024579216706319591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814474797755822433704485 340214024579216706319591)
                  ·
                    rfl

theorem cell21_1490770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1490770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490770 prefixEnd_1490770 := by exact prefixLift 1490770
  have htrace : WordTrace (prefixWord ++ tailWord_1490770) baseStart_1490770 baseEnd_1490770 := by
    simpa [prefixWord, tailWord_1490770, baseEnd_1490770] using wordTrace_append hprefix tailTrace_1490770
  have hstable : (prefixWord ++ tailWord_1490770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490770).length < 2 ^ (prefixWord ++ tailWord_1490770).sum := by decide
  have hdescent : baseEnd_1490770 < baseStart_1490770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490919 : List Nat := [1, 1, 5, 2, 3, 2, 7]
def baseStart_1490919 : Nat := 118140960795 + 1490919 * 2 ^ 59
def prefixEnd_1490919 : Nat := 4983230072969 + 3 ^ 40 * 1490919 * 2
def baseEnd_1490919 : Nat := 37805336489913950926217

theorem tailTrace_1490919 : CollatzResearch.WordTrace tailWord_1490919 prefixEnd_1490919 37805336489913950926217 := by
  unfold tailWord_1490919
  simp only [CollatzResearch.WordTrace]
  refine ⟨54378283285662566538283811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36252188857108377692189207 54378283285662566538283811)
  ·
    refine ⟨81567424928493849807425717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54378283285662566538283811 81567424928493849807425717)
    ·
      refine ⟨7646946087046298419446161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81567424928493849807425717 7646946087046298419446161)
      ·
        refine ⟨5735209565284723814584621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7646946087046298419446161 5735209565284723814584621)
        ·
          refine ⟨2150703586981771430469233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5735209565284723814584621 2150703586981771430469233)
          ·
            refine ⟨1613027690236328572851925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150703586981771430469233 1613027690236328572851925)
            ·
              refine ⟨37805336489913950926217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1613027690236328572851925 37805336489913950926217)
              ·
                rfl

theorem cell21_1490919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 7].length) (baseStart_1490919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490919 prefixEnd_1490919 := by exact prefixLift 1490919
  have htrace : WordTrace (prefixWord ++ tailWord_1490919) baseStart_1490919 baseEnd_1490919 := by
    simpa [prefixWord, tailWord_1490919, baseEnd_1490919] using wordTrace_append hprefix tailTrace_1490919
  have hstable : (prefixWord ++ tailWord_1490919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490919).length < 2 ^ (prefixWord ++ tailWord_1490919).sum := by decide
  have hdescent : baseEnd_1490919 < baseStart_1490919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490925 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1490925 : Nat := 118140960795 + 1490925 * 2 ^ 59
def prefixEnd_1490925 : Nat := 4983230072969 + 3 ^ 40 * 1490925 * 2
def baseEnd_1490925 : Nat := 340249397690970881235941

theorem tailTrace_1490925 : CollatzResearch.WordTrace tailWord_1490925 prefixEnd_1490925 340249397690970881235941 := by
  unfold tailWord_1490925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54378502123640829563002229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36252334749093886375334819 54378502123640829563002229)
  ·
    refine ⟨5097984574091327771531459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54378502123640829563002229 5097984574091327771531459)
    ·
      refine ⟨7646976861136991657297189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5097984574091327771531459 7646976861136991657297189)
      ·
        refine ⟨1433808161463185935743223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7646976861136991657297189 1433808161463185935743223)
        ·
          refine ⟨2150712242194778903614835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433808161463185935743223 2150712242194778903614835)
          ·
            refine ⟨3226068363292168355422253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150712242194778903614835 3226068363292168355422253)
            ·
              refine ⟨1209775636234563133283345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226068363292168355422253 1209775636234563133283345)
              ·
                refine ⟨907331727175922349962509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209775636234563133283345 907331727175922349962509)
                ·
                  refine ⟨340249397690970881235941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907331727175922349962509 340249397690970881235941)
                  ·
                    rfl

theorem cell21_1490925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1490925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490925 prefixEnd_1490925 := by exact prefixLift 1490925
  have htrace : WordTrace (prefixWord ++ tailWord_1490925) baseStart_1490925 baseEnd_1490925 := by
    simpa [prefixWord, tailWord_1490925, baseEnd_1490925] using wordTrace_append hprefix tailTrace_1490925
  have hstable : (prefixWord ++ tailWord_1490925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490925).length < 2 ^ (prefixWord ++ tailWord_1490925).sum := by decide
  have hdescent : baseEnd_1490925 < baseStart_1490925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490984 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_1490984 : Nat := 118140960795 + 1490984 * 2 ^ 59
def prefixEnd_1490984 : Nat := 4983230072969 + 3 ^ 40 * 1490984 * 2
def baseEnd_1490984 : Nat := 340262862294799889752487

theorem tailTrace_1490984 : CollatzResearch.WordTrace tailWord_1490984 prefixEnd_1490984 340262862294799889752487 := by
  unfold tailWord_1490984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27190327015213541319700003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36253769353618055092933337 27190327015213541319700003)
  ·
    refine ⟨40785490522820311979550005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27190327015213541319700003 40785490522820311979550005)
    ·
      refine ⟨3823639736514404248082813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40785490522820311979550005 3823639736514404248082813)
      ·
        refine ⟨1433864901192901593031055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3823639736514404248082813 1433864901192901593031055)
        ·
          refine ⟨2150797351789352389546583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433864901192901593031055 2150797351789352389546583)
          ·
            refine ⟨3226196027684028584319875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150797351789352389546583 3226196027684028584319875)
            ·
              refine ⟨4839294041526042876479813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226196027684028584319875 4839294041526042876479813)
              ·
                refine ⟨907367632786133039339965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4839294041526042876479813 907367632786133039339965)
                ·
                  refine ⟨340262862294799889752487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907367632786133039339965 340262862294799889752487)
                  ·
                    rfl

theorem cell21_1490984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_1490984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1490984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1490984 prefixEnd_1490984 := by exact prefixLift 1490984
  have htrace : WordTrace (prefixWord ++ tailWord_1490984) baseStart_1490984 baseEnd_1490984 := by
    simpa [prefixWord, tailWord_1490984, baseEnd_1490984] using wordTrace_append hprefix tailTrace_1490984
  have hstable : (prefixWord ++ tailWord_1490984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490984).length < 2 ^ (prefixWord ++ tailWord_1490984).sum := by decide
  have hdescent : baseEnd_1490984 < baseStart_1490984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491009 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1491009 : Nat := 118140960795 + 1491009 * 2 ^ 59
def prefixEnd_1491009 : Nat := 4983230072969 + 3 ^ 40 * 1491009 * 2
def baseEnd_1491009 : Nat := 340268567635405401835769

theorem tailTrace_1491009 : CollatzResearch.WordTrace tailWord_1491009 prefixEnd_1491009 340268567635405401835769 := by
  unfold tailWord_1491009
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381565855336511909060081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36254377236891007939373387 54381565855336511909060081)
  ·
    refine ⟨40786174391502383931795061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54381565855336511909060081 40786174391502383931795061)
    ·
      refine ⟨3823703849203348493605787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40786174391502383931795061 3823703849203348493605787)
      ·
        refine ⟨5735555773805022740408681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823703849203348493605787 5735555773805022740408681)
        ·
          refine ⟨4301666830353767055306511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735555773805022740408681 4301666830353767055306511)
          ·
            refine ⟨6452500245530650582959767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301666830353767055306511 6452500245530650582959767)
            ·
              refine ⟨9678750368295975874439651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452500245530650582959767 9678750368295975874439651)
              ·
                refine ⟨14518125552443963811659477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678750368295975874439651 14518125552443963811659477)
                ·
                  refine ⟨340268567635405401835769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14518125552443963811659477 340268567635405401835769)
                  ·
                    rfl

theorem cell21_1491009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1491009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491009 prefixEnd_1491009 := by exact prefixLift 1491009
  have htrace : WordTrace (prefixWord ++ tailWord_1491009) baseStart_1491009 baseEnd_1491009 := by
    simpa [prefixWord, tailWord_1491009, baseEnd_1491009] using wordTrace_append hprefix tailTrace_1491009
  have hstable : (prefixWord ++ tailWord_1491009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491009).length < 2 ^ (prefixWord ++ tailWord_1491009).sum := by decide
  have hdescent : baseEnd_1491009 < baseStart_1491009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491040 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_1491040 : Nat := 118140960795 + 1491040 * 2 ^ 59
def prefixEnd_1491040 : Nat := 4983230072969 + 3 ^ 40 * 1491040 * 2
def baseEnd_1491040 : Nat := 340275642257756236819039

theorem tailTrace_1491040 : CollatzResearch.WordTrace tailWord_1491040 prefixEnd_1491040 340275642257756236819039 := by
  unfold tailWord_1491040
  simp only [CollatzResearch.WordTrace]
  refine ⟨27191348259112102101719287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36255131012149469468959049 27191348259112102101719287)
  ·
    refine ⟨40787022388668153152578931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27191348259112102101719287 40787022388668153152578931)
    ·
      refine ⟨61180533583002229728868397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40787022388668153152578931 61180533583002229728868397)
      ·
        refine ⟨22942700093625836148325649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61180533583002229728868397 22942700093625836148325649)
        ·
          refine ⟨17207025070219377111244237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22942700093625836148325649 17207025070219377111244237)
          ·
            refine ⟨6452634401332266416716589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17207025070219377111244237 6452634401332266416716589)
            ·
              refine ⟨2419737900499599906268721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6452634401332266416716589 2419737900499599906268721)
              ·
                refine ⟨1814803425374699929701541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419737900499599906268721 1814803425374699929701541)
                ·
                  refine ⟨340275642257756236819039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814803425374699929701541 340275642257756236819039)
                  ·
                    rfl

theorem cell21_1491040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_1491040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491040 prefixEnd_1491040 := by exact prefixLift 1491040
  have htrace : WordTrace (prefixWord ++ tailWord_1491040) baseStart_1491040 baseEnd_1491040 := by
    simpa [prefixWord, tailWord_1491040, baseEnd_1491040] using wordTrace_append hprefix tailTrace_1491040
  have hstable : (prefixWord ++ tailWord_1491040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491040).length < 2 ^ (prefixWord ++ tailWord_1491040).sum := by decide
  have hdescent : baseEnd_1491040 < baseStart_1491040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491054 : List Nat := [4, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1491054 : Nat := 118140960795 + 1491054 * 2 ^ 59
def prefixEnd_1491054 : Nat := 4983230072969 + 3 ^ 40 * 1491054 * 2
def baseEnd_1491054 : Nat := 113426279082831774528559

theorem tailTrace_1491054 : CollatzResearch.WordTrace tailWord_1491054 prefixEnd_1491054 113426279082831774528559 := by
  unfold tailWord_1491054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797900892521685574306027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36255471426782323062965477 6797900892521685574306027)
  ·
    refine ⟨10196851338782528361459041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797900892521685574306027 10196851338782528361459041)
    ·
      refine ⟨7647638504086896271094281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10196851338782528361459041 7647638504086896271094281)
      ·
        refine ⟨5735728878065172203320711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7647638504086896271094281 5735728878065172203320711)
        ·
          refine ⟨8603593317097758304981067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735728878065172203320711 8603593317097758304981067)
          ·
            refine ⟨12905389975646637457471601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603593317097758304981067 12905389975646637457471601)
            ·
              refine ⟨9679042481734978093103701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905389975646637457471601 9679042481734978093103701)
              ·
                refine ⟨113426279082831774528559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9679042481734978093103701 113426279082831774528559)
                ·
                  rfl

theorem cell21_1491054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1491054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491054 prefixEnd_1491054 := by exact prefixLift 1491054
  have htrace : WordTrace (prefixWord ++ tailWord_1491054) baseStart_1491054 baseEnd_1491054 := by
    simpa [prefixWord, tailWord_1491054, baseEnd_1491054] using wordTrace_append hprefix tailTrace_1491054
  have hstable : (prefixWord ++ tailWord_1491054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491054).length < 2 ^ (prefixWord ++ tailWord_1491054).sum := by decide
  have hdescent : baseEnd_1491054 < baseStart_1491054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491094 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1491094 : Nat := 118140960795 + 1491094 * 2 ^ 59
def prefixEnd_1491094 : Nat := 4983230072969 + 3 ^ 40 * 1491094 * 2
def baseEnd_1491094 : Nat := 340287965793464142918929

theorem tailTrace_1491094 : CollatzResearch.WordTrace tailWord_1491094 prefixEnd_1491094 340287965793464142918929 := by
  unfold tailWord_1491094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399041628751785714119021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36256444040019047617269557 3399041628751785714119021)
  ·
    refine ⟨1274640610781919642794633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3399041628751785714119021 1274640610781919642794633)
    ·
      refine ⟨955980458086439732095975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274640610781919642794633 955980458086439732095975)
      ·
        refine ⟨1433970687129659598143963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955980458086439732095975 1433970687129659598143963)
        ·
          refine ⟨2150956030694489397215945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433970687129659598143963 2150956030694489397215945)
          ·
            refine ⟨1613217023020867047911959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150956030694489397215945 1613217023020867047911959)
            ·
              refine ⟨2419825534531300571867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613217023020867047911959 2419825534531300571867939)
              ·
                refine ⟨3629738301796950857801909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419825534531300571867939 3629738301796950857801909)
                ·
                  refine ⟨340287965793464142918929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629738301796950857801909 340287965793464142918929)
                  ·
                    rfl

theorem cell21_1491094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1491094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491094 prefixEnd_1491094 := by exact prefixLift 1491094
  have htrace : WordTrace (prefixWord ++ tailWord_1491094) baseStart_1491094 baseEnd_1491094 := by
    simpa [prefixWord, tailWord_1491094, baseEnd_1491094] using wordTrace_append hprefix tailTrace_1491094
  have hstable : (prefixWord ++ tailWord_1491094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491094).length < 2 ^ (prefixWord ++ tailWord_1491094).sum := by decide
  have hdescent : baseEnd_1491094 < baseStart_1491094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491240 : List Nat := [2, 1, 5, 1, 3, 2, 2, 5]
def baseStart_1491240 : Nat := 118140960795 + 1491240 * 2 ^ 59
def prefixEnd_1491240 : Nat := 4983230072969 + 3 ^ 40 * 1491240 * 2
def baseEnd_1491240 : Nat := 113440428327533444495099

theorem tailTrace_1491240 : CollatzResearch.WordTrace tailWord_1491240 prefixEnd_1491240 113440428327533444495099 := by
  unfold tailWord_1491240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27194995558749819180359587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36259994078333092240479449 27194995558749819180359587)
  ·
    refine ⟨40792493338124728770539381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27194995558749819180359587 40792493338124728770539381)
    ·
      refine ⟨3824296250449193322238067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40792493338124728770539381 3824296250449193322238067)
      ·
        refine ⟨5736444375673789983357101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824296250449193322238067 5736444375673789983357101)
        ·
          refine ⟨2151166640877671243758913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5736444375673789983357101 2151166640877671243758913)
          ·
            refine ⟨1613374980658253432819185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151166640877671243758913 1613374980658253432819185)
            ·
              refine ⟨1210031235493690074614389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613374980658253432819185 1210031235493690074614389)
              ·
                refine ⟨113440428327533444495099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210031235493690074614389 113440428327533444495099)
                ·
                  rfl

theorem cell21_1491240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_1491240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491240 prefixEnd_1491240 := by exact prefixLift 1491240
  have htrace : WordTrace (prefixWord ++ tailWord_1491240) baseStart_1491240 baseEnd_1491240 := by
    simpa [prefixWord, tailWord_1491240, baseEnd_1491240] using wordTrace_append hprefix tailTrace_1491240
  have hstable : (prefixWord ++ tailWord_1491240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491240).length < 2 ^ (prefixWord ++ tailWord_1491240).sum := by decide
  have hdescent : baseEnd_1491240 < baseStart_1491240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491313 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 3]
def baseStart_1491313 : Nat := 118140960795 + 1491313 * 2 ^ 59
def prefixEnd_1491313 : Nat := 4983230072969 + 3 ^ 40 * 1491313 * 2
def baseEnd_1491313 : Nat := 340337944577168428768481

theorem tailTrace_1491313 : CollatzResearch.WordTrace tailWord_1491313 prefixEnd_1491313 340337944577168428768481 := by
  unfold tailWord_1491313
  simp only [CollatzResearch.WordTrace]
  refine ⟨54392653646235171828126593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36261769097490114552084395 54392653646235171828126593)
  ·
    refine ⟨40794490234676378871094945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54392653646235171828126593 40794490234676378871094945)
    ·
      refine ⟨30595867676007284153321209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40794490234676378871094945 30595867676007284153321209)
      ·
        refine ⟨22946900757005463114990907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30595867676007284153321209 22946900757005463114990907)
        ·
          refine ⟨34420351135508194672486361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946900757005463114990907 34420351135508194672486361)
          ·
            refine ⟨25815263351631146004364771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34420351135508194672486361 25815263351631146004364771)
            ·
              refine ⟨38722895027446719006547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25815263351631146004364771 38722895027446719006547157)
              ·
                refine ⟨907567852205782476715949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38722895027446719006547157 907567852205782476715949)
                ·
                  refine ⟨340337944577168428768481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907567852205782476715949 340337944577168428768481)
                  ·
                    rfl

theorem cell21_1491313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_1491313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491313 prefixEnd_1491313 := by exact prefixLift 1491313
  have htrace : WordTrace (prefixWord ++ tailWord_1491313) baseStart_1491313 baseEnd_1491313 := by
    simpa [prefixWord, tailWord_1491313, baseEnd_1491313] using wordTrace_append hprefix tailTrace_1491313
  have hstable : (prefixWord ++ tailWord_1491313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491313).length < 2 ^ (prefixWord ++ tailWord_1491313).sum := by decide
  have hdescent : baseEnd_1491313 < baseStart_1491313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491350 : List Nat := [5, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1491350 : Nat := 118140960795 + 1491350 * 2 ^ 59
def prefixEnd_1491350 : Nat := 4983230072969 + 3 ^ 40 * 1491350 * 2
def baseEnd_1491350 : Nat := 113448796160421528883913

theorem tailTrace_1491350 : CollatzResearch.WordTrace tailWord_1491350 prefixEnd_1491350 113448796160421528883913 := by
  unfold tailWord_1491350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399625196693820446701469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36262668764734084764815669 3399625196693820446701469)
  ·
    refine ⟨1274859448760182667513051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3399625196693820446701469 1274859448760182667513051)
    ·
      refine ⟨1912289173140274001269577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274859448760182667513051 1912289173140274001269577)
      ·
        refine ⟨1434216879855205500952183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912289173140274001269577 1434216879855205500952183)
        ·
          refine ⟨2151325319782808251428275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434216879855205500952183 2151325319782808251428275)
          ·
            refine ⟨3226987979674212377142413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151325319782808251428275 3226987979674212377142413)
            ·
              refine ⟨1210120492377829641428405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226987979674212377142413 1210120492377829641428405)
              ·
                refine ⟨113448796160421528883913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210120492377829641428405 113448796160421528883913)
                ·
                  rfl

theorem cell21_1491350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1491350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491350 prefixEnd_1491350 := by exact prefixLift 1491350
  have htrace : WordTrace (prefixWord ++ tailWord_1491350) baseStart_1491350 baseEnd_1491350 := by
    simpa [prefixWord, tailWord_1491350, baseEnd_1491350] using wordTrace_append hprefix tailTrace_1491350
  have hstable : (prefixWord ++ tailWord_1491350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491350).length < 2 ^ (prefixWord ++ tailWord_1491350).sum := by decide
  have hdescent : baseEnd_1491350 < baseStart_1491350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491389 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1491389 : Nat := 118140960795 + 1491389 * 2 ^ 59
def prefixEnd_1491389 : Nat := 4983230072969 + 3 ^ 40 * 1491389 * 2
def baseEnd_1491389 : Nat := 340355288812609185501659

theorem tailTrace_1491389 : CollatzResearch.WordTrace tailWord_1491389 prefixEnd_1491389 340355288812609185501659 := by
  unfold tailWord_1491389
  simp only [CollatzResearch.WordTrace]
  refine ⟨54395425593959836807893221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36263617062639891205262147 54395425593959836807893221)
  ·
    refine ⟨10199142298867469401479979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54395425593959836807893221 10199142298867469401479979)
    ·
      refine ⟨15298713448301204102219969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199142298867469401479979 15298713448301204102219969)
      ·
        refine ⟨11474035086225903076664977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15298713448301204102219969 11474035086225903076664977)
        ·
          refine ⟨8605526314669427307498733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11474035086225903076664977 8605526314669427307498733)
          ·
            refine ⟨3227072368001035240312025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8605526314669427307498733 3227072368001035240312025)
            ·
              refine ⟨2420304276000776430234019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227072368001035240312025 2420304276000776430234019)
              ·
                refine ⟨3630456414001164645351029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420304276000776430234019 3630456414001164645351029)
                ·
                  refine ⟨340355288812609185501659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630456414001164645351029 340355288812609185501659)
                  ·
                    rfl

theorem cell21_1491389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1491389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491389 prefixEnd_1491389 := by exact prefixLift 1491389
  have htrace : WordTrace (prefixWord ++ tailWord_1491389) baseStart_1491389 baseEnd_1491389 := by
    simpa [prefixWord, tailWord_1491389, baseEnd_1491389] using wordTrace_append hprefix tailTrace_1491389
  have hstable : (prefixWord ++ tailWord_1491389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491389).length < 2 ^ (prefixWord ++ tailWord_1491389).sum := by decide
  have hdescent : baseEnd_1491389 < baseStart_1491389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491417 : List Nat := [1, 2, 1, 2, 4, 1, 3, 7]
def baseStart_1491417 : Nat := 118140960795 + 1491417 * 2 ^ 59
def prefixEnd_1491417 : Nat := 4983230072969 + 3 ^ 40 * 1491417 * 2
def baseEnd_1491417 : Nat := 113453892931362453011645

theorem tailTrace_1491417 : CollatzResearch.WordTrace tailWord_1491417 prefixEnd_1491417 113453892931362453011645 := by
  unfold tailWord_1491417
  simp only [CollatzResearch.WordTrace]
  refine ⟨54396446837858397589912505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36264297891905598393275003 54396446837858397589912505)
  ·
    refine ⟨40797335128393798192434379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54396446837858397589912505 40797335128393798192434379)
    ·
      refine ⟨61196002692590697288651569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40797335128393798192434379 61196002692590697288651569)
      ·
        refine ⟨45897002019443022966488677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61196002692590697288651569 45897002019443022966488677)
        ·
          refine ⟨8605687878645566806216627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45897002019443022966488677 8605687878645566806216627)
          ·
            refine ⟨12908531817968350209324941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605687878645566806216627 12908531817968350209324941)
            ·
              refine ⟨4840699431738131328496853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12908531817968350209324941 4840699431738131328496853)
              ·
                refine ⟨113453892931362453011645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4840699431738131328496853 113453892931362453011645)
                ·
                  rfl

theorem cell21_1491417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_1491417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491417 prefixEnd_1491417 := by exact prefixLift 1491417
  have htrace : WordTrace (prefixWord ++ tailWord_1491417) baseStart_1491417 baseEnd_1491417 := by
    simpa [prefixWord, tailWord_1491417, baseEnd_1491417] using wordTrace_append hprefix tailTrace_1491417
  have hstable : (prefixWord ++ tailWord_1491417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491417).length < 2 ^ (prefixWord ++ tailWord_1491417).sum := by decide
  have hdescent : baseEnd_1491417 < baseStart_1491417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491434 : List Nat := [3, 1, 3, 1, 3, 3, 7]
def baseStart_1491434 : Nat := 118140960795 + 1491434 * 2 ^ 59
def prefixEnd_1491434 : Nat := 4983230072969 + 3 ^ 40 * 1491434 * 2
def baseEnd_1491434 : Nat := 37818395380633234139063

theorem tailTrace_1491434 : CollatzResearch.WordTrace tailWord_1491434 prefixEnd_1491434 37818395380633234139063 := by
  unfold tailWord_1491434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599266719699202373320339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36264711252531206328854237 13599266719699202373320339)
  ·
    refine ⟨20398900079548803559980509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13599266719699202373320339 20398900079548803559980509)
    ·
      refine ⟨7649587529830801334992691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20398900079548803559980509 7649587529830801334992691)
      ·
        refine ⟨11474381294746202002489037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649587529830801334992691 11474381294746202002489037)
        ·
          refine ⟨4302892985529825750933389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11474381294746202002489037 4302892985529825750933389)
          ·
            refine ⟨1613584869573684656600021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4302892985529825750933389 1613584869573684656600021)
            ·
              refine ⟨37818395380633234139063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1613584869573684656600021 37818395380633234139063)
              ·
                rfl

theorem cell21_1491434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 7].length) (baseStart_1491434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491434 prefixEnd_1491434 := by exact prefixLift 1491434
  have htrace : WordTrace (prefixWord ++ tailWord_1491434) baseStart_1491434 baseEnd_1491434 := by
    simpa [prefixWord, tailWord_1491434, baseEnd_1491434] using wordTrace_append hprefix tailTrace_1491434
  have hstable : (prefixWord ++ tailWord_1491434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491434).length < 2 ^ (prefixWord ++ tailWord_1491434).sum := by decide
  have hdescent : baseEnd_1491434 < baseStart_1491434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491496 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_1491496 : Nat := 118140960795 + 1491496 * 2 ^ 59
def prefixEnd_1491496 : Nat := 4983230072969 + 3 ^ 40 * 1491496 * 2
def baseEnd_1491496 : Nat := 340379707670400777218107

theorem tailTrace_1491496 : CollatzResearch.WordTrace tailWord_1491496 prefixEnd_1491496 340379707670400777218107 := by
  unfold tailWord_1491496
  simp only [CollatzResearch.WordTrace]
  refine ⟨27199664102286097041019171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36266218803048129388025561 27199664102286097041019171)
  ·
    refine ⟨40799496153429145561528757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27199664102286097041019171 40799496153429145561528757)
    ·
      refine ⟨3824952764383982396393321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40799496153429145561528757 3824952764383982396393321)
      ·
        refine ⟨2868714573287986797294991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3824952764383982396393321 2868714573287986797294991)
        ·
          refine ⟨4303071859931980195942487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868714573287986797294991 4303071859931980195942487)
          ·
            refine ⟨6454607789897970293913731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303071859931980195942487 6454607789897970293913731)
            ·
              refine ⟨9681911684846955440870597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454607789897970293913731 9681911684846955440870597)
              ·
                refine ⟨1815358440908804145163237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9681911684846955440870597 1815358440908804145163237)
                ·
                  refine ⟨340379707670400777218107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815358440908804145163237 340379707670400777218107)
                  ·
                    rfl

theorem cell21_1491496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_1491496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491496 prefixEnd_1491496 := by exact prefixLift 1491496
  have htrace : WordTrace (prefixWord ++ tailWord_1491496) baseStart_1491496 baseEnd_1491496 := by
    simpa [prefixWord, tailWord_1491496, baseEnd_1491496] using wordTrace_append hprefix tailTrace_1491496
  have hstable : (prefixWord ++ tailWord_1491496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491496).length < 2 ^ (prefixWord ++ tailWord_1491496).sum := by decide
  have hdescent : baseEnd_1491496 < baseStart_1491496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491541 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1491541 : Nat := 118140960795 + 1491541 * 2 ^ 59
def prefixEnd_1491541 : Nat := 4983230072969 + 3 ^ 40 * 1491541 * 2
def baseEnd_1491541 : Nat := 340389977283490698968015

theorem tailTrace_1491541 : CollatzResearch.WordTrace tailWord_1491541 prefixEnd_1491541 340389977283490698968015 := by
  unfold tailWord_1491541
  simp only [CollatzResearch.WordTrace]
  refine ⟨54400969489409166767426477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36267312992939444511617651 54400969489409166767426477)
  ·
    refine ⟨20400363558528437537784929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54400969489409166767426477 20400363558528437537784929)
    ·
      refine ⟨15300272668896328153338697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20400363558528437537784929 15300272668896328153338697)
      ·
        refine ⟨11475204501672246115004023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15300272668896328153338697 11475204501672246115004023)
        ·
          refine ⟨17212806752508369172506035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475204501672246115004023 17212806752508369172506035)
          ·
            refine ⟨25819210128762553758759053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212806752508369172506035 25819210128762553758759053)
            ·
              refine ⟨9682203798285957659534645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25819210128762553758759053 9682203798285957659534645)
              ·
                refine ⟨907706606089308530581373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9682203798285957659534645 907706606089308530581373)
                ·
                  refine ⟨340389977283490698968015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907706606089308530581373 340389977283490698968015)
                  ·
                    rfl

theorem cell21_1491541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1491541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491541 prefixEnd_1491541 := by exact prefixLift 1491541
  have htrace : WordTrace (prefixWord ++ tailWord_1491541) baseStart_1491541 baseEnd_1491541 := by
    simpa [prefixWord, tailWord_1491541, baseEnd_1491541] using wordTrace_append hprefix tailTrace_1491541
  have hstable : (prefixWord ++ tailWord_1491541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491541).length < 2 ^ (prefixWord ++ tailWord_1491541).sum := by decide
  have hdescent : baseEnd_1491541 < baseStart_1491541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491583 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_1491583 : Nat := 118140960795 + 1491583 * 2 ^ 59
def prefixEnd_1491583 : Nat := 4983230072969 + 3 ^ 40 * 1491583 * 2
def baseEnd_1491583 : Nat := 340399562255707959267929

theorem tailTrace_1491583 : CollatzResearch.WordTrace tailWord_1491583 prefixEnd_1491583 340399562255707959267929 := by
  unfold tailWord_1491583
  simp only [CollatzResearch.WordTrace]
  refine ⟨54402501355257007940455403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36268334236838005293636935 54402501355257007940455403)
  ·
    refine ⟨81603752032885511910683105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54402501355257007940455403 81603752032885511910683105)
    ·
      refine ⟨61202814024664133933012329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81603752032885511910683105 61202814024664133933012329)
      ·
        refine ⟨45902110518498100449759247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61202814024664133933012329 45902110518498100449759247)
        ·
          refine ⟨68853165777747150674638871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45902110518498100449759247 68853165777747150674638871)
          ·
            refine ⟨103279748666620726011958307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68853165777747150674638871 103279748666620726011958307)
            ·
              refine ⟨154919622999931089017937461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103279748666620726011958307 154919622999931089017937461)
              ·
                refine ⟨14523714656243539595431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154919622999931089017937461 14523714656243539595431637)
                ·
                  refine ⟨340399562255707959267929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14523714656243539595431637 340399562255707959267929)
                  ·
                    rfl

theorem cell21_1491583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_1491583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491583 prefixEnd_1491583 := by exact prefixLift 1491583
  have htrace : WordTrace (prefixWord ++ tailWord_1491583) baseStart_1491583 baseEnd_1491583 := by
    simpa [prefixWord, tailWord_1491583, baseEnd_1491583] using wordTrace_append hprefix tailTrace_1491583
  have hstable : (prefixWord ++ tailWord_1491583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491583).length < 2 ^ (prefixWord ++ tailWord_1491583).sum := by decide
  have hdescent : baseEnd_1491583 < baseStart_1491583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491623 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 4]
def baseStart_1491623 : Nat := 118140960795 + 1491623 * 2 ^ 59
def prefixEnd_1491623 : Nat := 4983230072969 + 3 ^ 40 * 1491623 * 2
def baseEnd_1491623 : Nat := 340408690800676778601181

theorem tailTrace_1491623 : CollatzResearch.WordTrace tailWord_1491623 prefixEnd_1491623 340408690800676778601181 := by
  unfold tailWord_1491623
  simp only [CollatzResearch.WordTrace]
  refine ⟨54403960275112094771911523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36269306850074729847941015 54403960275112094771911523)
  ·
    refine ⟨81605940412668142157867285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54403960275112094771911523 81605940412668142157867285)
    ·
      refine ⟨3825278456843819163650029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81605940412668142157867285 3825278456843819163650029)
      ·
        refine ⟨1434479421316432186368761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3825278456843819163650029 1434479421316432186368761)
        ·
          refine ⟨1075859565987324139776571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434479421316432186368761 1075859565987324139776571)
          ·
            refine ⟨1613789348980986209664857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075859565987324139776571 1613789348980986209664857)
            ·
              refine ⟨1210342011735739657248643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613789348980986209664857 1210342011735739657248643)
              ·
                refine ⟨1815513017603609485872965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210342011735739657248643 1815513017603609485872965)
                ·
                  refine ⟨340408690800676778601181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815513017603609485872965 340408690800676778601181)
                  ·
                    rfl

theorem cell21_1491623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4].length) (baseStart_1491623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491623 prefixEnd_1491623 := by exact prefixLift 1491623
  have htrace : WordTrace (prefixWord ++ tailWord_1491623) baseStart_1491623 baseEnd_1491623 := by
    simpa [prefixWord, tailWord_1491623, baseEnd_1491623] using wordTrace_append hprefix tailTrace_1491623
  have hstable : (prefixWord ++ tailWord_1491623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491623).length < 2 ^ (prefixWord ++ tailWord_1491623).sum := by decide
  have hdescent : baseEnd_1491623 < baseStart_1491623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491631 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_1491631 : Nat := 118140960795 + 1491631 * 2 ^ 59
def prefixEnd_1491631 : Nat := 4983230072969 + 3 ^ 40 * 1491631 * 2
def baseEnd_1491631 : Nat := 340410516509670542467831

theorem tailTrace_1491631 : CollatzResearch.WordTrace tailWord_1491631 prefixEnd_1491631 340410516509670542467831 := by
  unfold tailWord_1491631
  simp only [CollatzResearch.WordTrace]
  refine ⟨54404252059083112138202747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36269501372722074758801831 54404252059083112138202747)
  ·
    refine ⟨81606378088624668207304121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54404252059083112138202747 81606378088624668207304121)
    ·
      refine ⟨61204783566468501155478091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81606378088624668207304121 61204783566468501155478091)
      ·
        refine ⟨91807175349702751733217137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61204783566468501155478091 91807175349702751733217137)
        ·
          refine ⟨68855381512277063799912853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91807175349702751733217137 68855381512277063799912853)
          ·
            refine ⟨3227596008387987365620915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68855381512277063799912853 3227596008387987365620915)
            ·
              refine ⟨4841394012581981048431373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227596008387987365620915 4841394012581981048431373)
              ·
                refine ⟨1815522754718242893161765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841394012581981048431373 1815522754718242893161765)
                ·
                  refine ⟨340410516509670542467831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815522754718242893161765 340410516509670542467831)
                  ·
                    rfl

theorem cell21_1491631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_1491631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491631 prefixEnd_1491631 := by exact prefixLift 1491631
  have htrace : WordTrace (prefixWord ++ tailWord_1491631) baseStart_1491631 baseEnd_1491631 := by
    simpa [prefixWord, tailWord_1491631, baseEnd_1491631] using wordTrace_append hprefix tailTrace_1491631
  have hstable : (prefixWord ++ tailWord_1491631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491631).length < 2 ^ (prefixWord ++ tailWord_1491631).sum := by decide
  have hdescent : baseEnd_1491631 < baseStart_1491631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491645 : List Nat := [1, 4, 1, 2, 1, 3, 2, 7]
def baseStart_1491645 : Nat := 118140960795 + 1491645 * 2 ^ 59
def prefixEnd_1491645 : Nat := 4983230072969 + 3 ^ 40 * 1491645 * 2
def baseEnd_1491645 : Nat := 113471237166803209744823

theorem tailTrace_1491645 : CollatzResearch.WordTrace tailWord_1491645 prefixEnd_1491645 113471237166803209744823 := by
  unfold tailWord_1491645
  simp only [CollatzResearch.WordTrace]
  refine ⟨54404762681032392529212389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36269841787354928352808259 54404762681032392529212389)
  ·
    refine ⟨10200893002693573599227323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54404762681032392529212389 10200893002693573599227323)
    ·
      refine ⟨15301339504040360398840985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200893002693573599227323 15301339504040360398840985)
      ·
        refine ⟨11476004628030270299130739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15301339504040360398840985 11476004628030270299130739)
        ·
          refine ⟨17214006942045405448696109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11476004628030270299130739 17214006942045405448696109)
          ·
            refine ⟨6455252603267027043261041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17214006942045405448696109 6455252603267027043261041)
            ·
              refine ⟨4841439452450270282445781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455252603267027043261041 4841439452450270282445781)
              ·
                refine ⟨113471237166803209744823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4841439452450270282445781 113471237166803209744823)
                ·
                  rfl

theorem cell21_1491645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_1491645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491645 prefixEnd_1491645 := by exact prefixLift 1491645
  have htrace : WordTrace (prefixWord ++ tailWord_1491645) baseStart_1491645 baseEnd_1491645 := by
    simpa [prefixWord, tailWord_1491645, baseEnd_1491645] using wordTrace_append hprefix tailTrace_1491645
  have hstable : (prefixWord ++ tailWord_1491645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491645).length < 2 ^ (prefixWord ++ tailWord_1491645).sum := by decide
  have hdescent : baseEnd_1491645 < baseStart_1491645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491668 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1491668 : Nat := 118140960795 + 1491668 * 2 ^ 59
def prefixEnd_1491668 : Nat := 4983230072969 + 3 ^ 40 * 1491668 * 2
def baseEnd_1491668 : Nat := 340418960413766700351089

theorem tailTrace_1491668 : CollatzResearch.WordTrace tailWord_1491668 prefixEnd_1491668 340418960413766700351089 := by
  unfold tailWord_1491668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202800779974533728649829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36270401039966044971533105 27202800779974533728649829)
  ·
    refine ⟨5100525146245225074121843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27202800779974533728649829 5100525146245225074121843)
    ·
      refine ⟨7650787719367837611182765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100525146245225074121843 7650787719367837611182765)
      ·
        refine ⟨2869045394762939104193537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7650787719367837611182765 2869045394762939104193537)
        ·
          refine ⟨2151784046072204328145153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869045394762939104193537 2151784046072204328145153)
          ·
            refine ⟨1613838034554153246108865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151784046072204328145153 1613838034554153246108865)
            ·
              refine ⟨1210378525915614934581649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613838034554153246108865 1210378525915614934581649)
              ·
                refine ⟨907783894436711200936237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210378525915614934581649 907783894436711200936237)
                ·
                  refine ⟨340418960413766700351089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907783894436711200936237 340418960413766700351089)
                  ·
                    rfl

theorem cell21_1491668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1491668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491668 prefixEnd_1491668 := by exact prefixLift 1491668
  have htrace : WordTrace (prefixWord ++ tailWord_1491668) baseStart_1491668 baseEnd_1491668 := by
    simpa [prefixWord, tailWord_1491668, baseEnd_1491668] using wordTrace_append hprefix tailTrace_1491668
  have hstable : (prefixWord ++ tailWord_1491668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491668).length < 2 ^ (prefixWord ++ tailWord_1491668).sum := by decide
  have hdescent : baseEnd_1491668 < baseStart_1491668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491690 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1491690 : Nat := 118140960795 + 1491690 * 2 ^ 59
def prefixEnd_1491690 : Nat := 4983230072969 + 3 ^ 40 * 1491690 * 2
def baseEnd_1491690 : Nat := 340423981113499550984377

theorem tailTrace_1491690 : CollatzResearch.WordTrace tailWord_1491690 prefixEnd_1491690 340423981113499550984377 := by
  unfold tailWord_1491690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601600991467341303650131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36270935977246243476400349 13601600991467341303650131)
  ·
    refine ⟨20402401487201011955475197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13601600991467341303650131 20402401487201011955475197)
    ·
      refine ⟨7650900557700379483303199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20402401487201011955475197 7650900557700379483303199)
      ·
        refine ⟨11476350836550569224954799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650900557700379483303199 11476350836550569224954799)
        ·
          refine ⟨17214526254825853837432199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11476350836550569224954799 17214526254825853837432199)
          ·
            refine ⟨25821789382238780756148299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17214526254825853837432199 25821789382238780756148299)
            ·
              refine ⟨38732684073358171134222449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25821789382238780756148299 38732684073358171134222449)
              ·
                refine ⟨29049513055018628350666837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38732684073358171134222449 29049513055018628350666837)
                ·
                  refine ⟨340423981113499550984377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29049513055018628350666837 340423981113499550984377)
                  ·
                    rfl

theorem cell21_1491690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1491690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491690 prefixEnd_1491690 := by exact prefixLift 1491690
  have htrace : WordTrace (prefixWord ++ tailWord_1491690) baseStart_1491690 baseEnd_1491690 := by
    simpa [prefixWord, tailWord_1491690, baseEnd_1491690] using wordTrace_append hprefix tailTrace_1491690
  have hstable : (prefixWord ++ tailWord_1491690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491690).length < 2 ^ (prefixWord ++ tailWord_1491690).sum := by decide
  have hdescent : baseEnd_1491690 < baseStart_1491690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491710 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_1491710 : Nat := 118140960795 + 1491710 * 2 ^ 59
def prefixEnd_1491710 : Nat := 4983230072969 + 3 ^ 40 * 1491710 * 2
def baseEnd_1491710 : Nat := 340428545385983960651003

theorem tailTrace_1491710 : CollatzResearch.WordTrace tailWord_1491710 prefixEnd_1491710 340428545385983960651003 := by
  unfold tailWord_1491710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800891678224613578791073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36271422283864605753552389 6800891678224613578791073)
  ·
    refine ⟨5100668758668460184093305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800891678224613578791073 5100668758668460184093305)
    ·
      refine ⟨3825501569001345138069979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5100668758668460184093305 3825501569001345138069979)
      ·
        refine ⟨5738252353502017707104969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825501569001345138069979 5738252353502017707104969)
        ·
          refine ⟨4303689265126513280328727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738252353502017707104969 4303689265126513280328727)
          ·
            refine ⟨6455533897689769920493091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303689265126513280328727 6455533897689769920493091)
            ·
              refine ⟨9683300846534654880739637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455533897689769920493091 9683300846534654880739637)
              ·
                refine ⟨907809454362623895069341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9683300846534654880739637 907809454362623895069341)
                ·
                  refine ⟨340428545385983960651003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907809454362623895069341 340428545385983960651003)
                  ·
                    rfl

theorem cell21_1491710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_1491710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491710 prefixEnd_1491710 := by exact prefixLift 1491710
  have htrace : WordTrace (prefixWord ++ tailWord_1491710) baseStart_1491710 baseEnd_1491710 := by
    simpa [prefixWord, tailWord_1491710, baseEnd_1491710] using wordTrace_append hprefix tailTrace_1491710
  have hstable : (prefixWord ++ tailWord_1491710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491710).length < 2 ^ (prefixWord ++ tailWord_1491710).sum := by decide
  have hdescent : baseEnd_1491710 < baseStart_1491710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491752 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_1491752 : Nat := 118140960795 + 1491752 * 2 ^ 59
def prefixEnd_1491752 : Nat := 4983230072969 + 3 ^ 40 * 1491752 * 2
def baseEnd_1491752 : Nat := 340438130358201220950917

theorem tailTrace_1491752 : CollatzResearch.WordTrace tailWord_1491752 prefixEnd_1491752 340438130358201220950917 := by
  unfold tailWord_1491752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27204332645822374901678755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36272443527763166535571673 27204332645822374901678755)
  ·
    refine ⟨40806498968733562352518133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27204332645822374901678755 40806498968733562352518133)
    ·
      refine ⟨3825609278318771470548575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40806498968733562352518133 3825609278318771470548575)
      ·
        refine ⟨5738413917478157205822863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825609278318771470548575 5738413917478157205822863)
        ·
          refine ⟨8607620876217235808734295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738413917478157205822863 8607620876217235808734295)
          ·
            refine ⟨12911431314325853713101443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607620876217235808734295 12911431314325853713101443)
            ·
              refine ⟨19367146971488780569652165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911431314325853713101443 19367146971488780569652165)
              ·
                refine ⟨3631340057154146356809781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19367146971488780569652165 3631340057154146356809781)
                ·
                  refine ⟨340438130358201220950917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631340057154146356809781 340438130358201220950917)
                  ·
                    rfl

theorem cell21_1491752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_1491752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491752 prefixEnd_1491752 := by exact prefixLift 1491752
  have htrace : WordTrace (prefixWord ++ tailWord_1491752) baseStart_1491752 baseEnd_1491752 := by
    simpa [prefixWord, tailWord_1491752, baseEnd_1491752] using wordTrace_append hprefix tailTrace_1491752
  have hstable : (prefixWord ++ tailWord_1491752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491752).length < 2 ^ (prefixWord ++ tailWord_1491752).sum := by decide
  have hdescent : baseEnd_1491752 < baseStart_1491752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491797 : List Nat := [1, 3, 2, 2, 2, 1, 4, 6]
def baseStart_1491797 : Nat := 118140960795 + 1491797 * 2 ^ 59
def prefixEnd_1491797 : Nat := 4983230072969 + 3 ^ 40 * 1491797 * 2
def baseEnd_1491797 : Nat := 113482799990430380900275

theorem tailTrace_1491797 : CollatzResearch.WordTrace tailWord_1491797 prefixEnd_1491797 113482799990430380900275 := by
  unfold tailWord_1491797
  simp only [CollatzResearch.WordTrace]
  refine ⟨54410306576481722488745645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36273537717654481659163763 54410306576481722488745645)
  ·
    refine ⟨20403864966180645933279617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54410306576481722488745645 20403864966180645933279617)
    ·
      refine ⟨15302898724635484449959713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20403864966180645933279617 15302898724635484449959713)
      ·
        refine ⟨11477174043476613337469785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15302898724635484449959713 11477174043476613337469785)
        ·
          refine ⟨8607880532607460003102339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11477174043476613337469785 8607880532607460003102339)
          ·
            refine ⟨12911820798911190004653509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607880532607460003102339 12911820798911190004653509)
            ·
              refine ⟨2420966399795848125872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12911820798911190004653509 2420966399795848125872533)
              ·
                refine ⟨113482799990430380900275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2420966399795848125872533 113482799990430380900275)
                ·
                  rfl

theorem cell21_1491797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_1491797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491797 prefixEnd_1491797 := by exact prefixLift 1491797
  have htrace : WordTrace (prefixWord ++ tailWord_1491797) baseStart_1491797 baseEnd_1491797 := by
    simpa [prefixWord, tailWord_1491797, baseEnd_1491797] using wordTrace_append hprefix tailTrace_1491797
  have hstable : (prefixWord ++ tailWord_1491797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491797).length < 2 ^ (prefixWord ++ tailWord_1491797).sum := by decide
  have hdescent : baseEnd_1491797 < baseStart_1491797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491845 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1491845 : Nat := 118140960795 + 1491845 * 2 ^ 59
def prefixEnd_1491845 : Nat := 4983230072969 + 3 ^ 40 * 1491845 * 2
def baseEnd_1491845 : Nat := 340459354225253725900727

theorem tailTrace_1491845 : CollatzResearch.WordTrace tailWord_1491845 prefixEnd_1491845 340459354225253725900727 := by
  unfold tailWord_1491845
  simp only [CollatzResearch.WordTrace]
  refine ⟨54412057280307826686492989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36274704853538551124328659 54412057280307826686492989)
  ·
    refine ⟨20404521480115435007434871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54412057280307826686492989 20404521480115435007434871)
    ·
      refine ⟨30606782220173152511152307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20404521480115435007434871 30606782220173152511152307)
      ·
        refine ⟨45910173330259728766728461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30606782220173152511152307 45910173330259728766728461)
        ·
          refine ⟨17216314998847398287523173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45910173330259728766728461 17216314998847398287523173)
          ·
            refine ⟨3228059062283887178910595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17216314998847398287523173 3228059062283887178910595)
            ·
              refine ⟨4842088593425830768365893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228059062283887178910595 4842088593425830768365893)
              ·
                refine ⟨907891611267343269068605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4842088593425830768365893 907891611267343269068605)
                ·
                  refine ⟨340459354225253725900727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907891611267343269068605 340459354225253725900727)
                  ·
                    rfl

theorem cell21_1491845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1491845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491845 prefixEnd_1491845 := by exact prefixLift 1491845
  have htrace : WordTrace (prefixWord ++ tailWord_1491845) baseStart_1491845 baseEnd_1491845 := by
    simpa [prefixWord, tailWord_1491845, baseEnd_1491845] using wordTrace_append hprefix tailTrace_1491845
  have hstable : (prefixWord ++ tailWord_1491845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491845).length < 2 ^ (prefixWord ++ tailWord_1491845).sum := by decide
  have hdescent : baseEnd_1491845 < baseStart_1491845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491862 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1491862 : Nat := 118140960795 + 1491862 * 2 ^ 59
def prefixEnd_1491862 : Nat := 4983230072969 + 3 ^ 40 * 1491862 * 2
def baseEnd_1491862 : Nat := 340463233856865474117359

theorem tailTrace_1491862 : CollatzResearch.WordTrace tailWord_1491862 prefixEnd_1491862 340463233856865474117359 := by
  unfold tailWord_1491862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400792332577889911866365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36275118214164159059907893 3400792332577889911866365)
  ·
    refine ⟨1275297124716708716949887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3400792332577889911866365 1275297124716708716949887)
    ·
      refine ⟨1912945687075063075424831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275297124716708716949887 1912945687075063075424831)
      ·
        refine ⟨2869418530612594613137247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912945687075063075424831 2869418530612594613137247)
        ·
          refine ⟨4304127795918891919705871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869418530612594613137247 4304127795918891919705871)
          ·
            refine ⟨6456191693878337879558807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304127795918891919705871 6456191693878337879558807)
            ·
              refine ⟨9684287540817506819338211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456191693878337879558807 9684287540817506819338211)
              ·
                refine ⟨14526431311226260229007317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684287540817506819338211 14526431311226260229007317)
                ·
                  refine ⟨340463233856865474117359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14526431311226260229007317 340463233856865474117359)
                  ·
                    rfl

theorem cell21_1491862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1491862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491862 prefixEnd_1491862 := by exact prefixLift 1491862
  have htrace : WordTrace (prefixWord ++ tailWord_1491862) baseStart_1491862 baseEnd_1491862 := by
    simpa [prefixWord, tailWord_1491862, baseEnd_1491862] using wordTrace_append hprefix tailTrace_1491862
  have hstable : (prefixWord ++ tailWord_1491862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491862).length < 2 ^ (prefixWord ++ tailWord_1491862).sum := by decide
  have hdescent : baseEnd_1491862 < baseStart_1491862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491904 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_1491904 : Nat := 118140960795 + 1491904 * 2 ^ 59
def prefixEnd_1491904 : Nat := 4983230072969 + 3 ^ 40 * 1491904 * 2
def baseEnd_1491904 : Nat := 340472818829082734417273

theorem tailTrace_1491904 : CollatzResearch.WordTrace tailWord_1491904 prefixEnd_1491904 340472818829082734417273 := by
  unfold tailWord_1491904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207104593547039881445383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36276139458062719841927177 27207104593547039881445383)
  ·
    refine ⟨40810656890320559822168075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27207104593547039881445383 40810656890320559822168075)
    ·
      refine ⟨61215985335480839733252113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40810656890320559822168075 61215985335480839733252113)
      ·
        refine ⟨45911989001610629799939085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61215985335480839733252113 45911989001610629799939085)
        ·
          refine ⟨17216995875603986174977157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45911989001610629799939085 17216995875603986174977157)
          ·
            refine ⟨3228186726675747407808217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17216995875603986174977157 3228186726675747407808217)
            ·
              refine ⟨2421140045006810555856163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228186726675747407808217 2421140045006810555856163)
              ·
                refine ⟨3631710067510215833784245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421140045006810555856163 3631710067510215833784245)
                ·
                  refine ⟨340472818829082734417273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631710067510215833784245 340472818829082734417273)
                  ·
                    rfl

theorem cell21_1491904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_1491904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1491904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1491904 prefixEnd_1491904 := by exact prefixLift 1491904
  have htrace : WordTrace (prefixWord ++ tailWord_1491904) baseStart_1491904 baseEnd_1491904 := by
    simpa [prefixWord, tailWord_1491904, baseEnd_1491904] using wordTrace_append hprefix tailTrace_1491904
  have hstable : (prefixWord ++ tailWord_1491904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491904).length < 2 ^ (prefixWord ++ tailWord_1491904).sum := by decide
  have hdescent : baseEnd_1491904 < baseStart_1491904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492008 : List Nat := [2, 1, 5, 13]
def baseStart_1492008 : Nat := 118140960795 + 1492008 * 2 ^ 59
def prefixEnd_1492008 : Nat := 4983230072969 + 3 ^ 40 * 1492008 * 2
def baseEnd_1492008 : Nat := 1401220382905356644789

theorem tailTrace_1492008 : CollatzResearch.WordTrace tailWord_1492008 prefixEnd_1492008 1401220382905356644789 := by
  unfold tailWord_1492008
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209001189358652762338339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36278668252478203683117785 27209001189358652762338339)
  ·
    refine ⟨40813501784037979143507509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27209001189358652762338339 40813501784037979143507509)
    ·
      refine ⟨3826265792253560544703829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40813501784037979143507509 3826265792253560544703829)
      ·
        refine ⟨1401220382905356644789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3826265792253560544703829 1401220382905356644789)
        ·
          rfl

theorem cell21_1492008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 13].length) (baseStart_1492008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492008 prefixEnd_1492008 := by exact prefixLift 1492008
  have htrace : WordTrace (prefixWord ++ tailWord_1492008) baseStart_1492008 baseEnd_1492008 := by
    simpa [prefixWord, tailWord_1492008, baseEnd_1492008] using wordTrace_append hprefix tailTrace_1492008
  have hstable : (prefixWord ++ tailWord_1492008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492008).length < 2 ^ (prefixWord ++ tailWord_1492008).sum := by decide
  have hdescent : baseEnd_1492008 < baseStart_1492008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492025 : List Nat := [1, 2, 1, 5, 2, 1, 3, 6]
def baseStart_1492025 : Nat := 118140960795 + 1492025 * 2 ^ 59
def prefixEnd_1492025 : Nat := 4983230072969 + 3 ^ 40 * 1492025 * 2
def baseEnd_1492025 : Nat := 113500144225871137633453

theorem tailTrace_1492025 : CollatzResearch.WordTrace tailWord_1492025 prefixEnd_1492025 113500144225871137633453 := by
  unfold tailWord_1492025
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418622419655717428045529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36279081613103811618697019 54418622419655717428045529)
  ·
    refine ⟨40813966814741788071034147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54418622419655717428045529 40813966814741788071034147)
    ·
      refine ⟨61220950222112682106551221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40813966814741788071034147 61220950222112682106551221)
      ·
        refine ⟨5739464083323063947489177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61220950222112682106551221 5739464083323063947489177)
        ·
          refine ⟨4304598062492297960616883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5739464083323063947489177 4304598062492297960616883)
          ·
            refine ⟨6456897093738446940925325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304598062492297960616883 6456897093738446940925325)
            ·
              refine ⟨2421336410151917602846997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6456897093738446940925325 2421336410151917602846997)
              ·
                refine ⟨113500144225871137633453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2421336410151917602846997 113500144225871137633453)
                ·
                  rfl

theorem cell21_1492025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_1492025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492025 prefixEnd_1492025 := by exact prefixLift 1492025
  have htrace : WordTrace (prefixWord ++ tailWord_1492025) baseStart_1492025 baseEnd_1492025 := by
    simpa [prefixWord, tailWord_1492025, baseEnd_1492025] using wordTrace_append hprefix tailTrace_1492025
  have hstable : (prefixWord ++ tailWord_1492025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492025).length < 2 ^ (prefixWord ++ tailWord_1492025).sum := by decide
  have hdescent : baseEnd_1492025 < baseStart_1492025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492039 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_1492039 : Nat := 118140960795 + 1492039 * 2 ^ 59
def prefixEnd_1492039 : Nat := 4983230072969 + 3 ^ 40 * 1492039 * 2
def baseEnd_1492039 : Nat := 340503627668352499666997

theorem tailTrace_1492039 : CollatzResearch.WordTrace tailWord_1492039 prefixEnd_1492039 340503627668352499666997 := by
  unfold tailWord_1492039
  simp only [CollatzResearch.WordTrace]
  refine ⟨54419133041604997819055171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36279422027736665212703447 54419133041604997819055171)
  ·
    refine ⟨81628699562407496728582757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54419133041604997819055171 81628699562407496728582757)
    ·
      refine ⟨15305381167951405636609267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81628699562407496728582757 15305381167951405636609267)
      ·
        refine ⟨22958071751927108454913901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305381167951405636609267 22958071751927108454913901)
        ·
          refine ⟨8609276906972665670592713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22958071751927108454913901 8609276906972665670592713)
          ·
            refine ⟨6456957680229499252944535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609276906972665670592713 6456957680229499252944535)
            ·
              refine ⟨9685436520344248879416803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456957680229499252944535 9685436520344248879416803)
              ·
                refine ⟨14528154780516373319125205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685436520344248879416803 14528154780516373319125205)
                ·
                  refine ⟨340503627668352499666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14528154780516373319125205 340503627668352499666997)
                  ·
                    rfl

theorem cell21_1492039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_1492039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492039 prefixEnd_1492039 := by exact prefixLift 1492039
  have htrace : WordTrace (prefixWord ++ tailWord_1492039) baseStart_1492039 baseEnd_1492039 := by
    simpa [prefixWord, tailWord_1492039, baseEnd_1492039] using wordTrace_append hprefix tailTrace_1492039
  have hstable : (prefixWord ++ tailWord_1492039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492039).length < 2 ^ (prefixWord ++ tailWord_1492039).sum := by decide
  have hdescent : baseEnd_1492039 < baseStart_1492039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492062 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1492062 : Nat := 118140960795 + 1492062 * 2 ^ 59
def prefixEnd_1492062 : Nat := 4983230072969 + 3 ^ 40 * 1492062 * 2
def baseEnd_1492062 : Nat := 340508876581709570783617

theorem tailTrace_1492062 : CollatzResearch.WordTrace tailWord_1492062 prefixEnd_1492062 340508876581709570783617 := by
  unfold tailWord_1492062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802496490065209093392805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36279981280347781831428293 6802496490065209093392805)
  ·
    refine ⟨1275468091887226705011151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6802496490065209093392805 1275468091887226705011151)
    ·
      refine ⟨1913202137830840057516727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275468091887226705011151 1913202137830840057516727)
      ·
        refine ⟨2869803206746260086275091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913202137830840057516727 2869803206746260086275091)
        ·
          refine ⟨4304704810119390129412637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869803206746260086275091 4304704810119390129412637)
          ·
            refine ⟨1614264303794771298529739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4304704810119390129412637 1614264303794771298529739)
            ·
              refine ⟨2421396455692156947794609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614264303794771298529739 2421396455692156947794609)
              ·
                refine ⟨1816047341769117710845957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421396455692156947794609 1816047341769117710845957)
                ·
                  refine ⟨340508876581709570783617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816047341769117710845957 340508876581709570783617)
                  ·
                    rfl

theorem cell21_1492062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1492062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492062 prefixEnd_1492062 := by exact prefixLift 1492062
  have htrace : WordTrace (prefixWord ++ tailWord_1492062) baseStart_1492062 baseEnd_1492062 := by
    simpa [prefixWord, tailWord_1492062, baseEnd_1492062] using wordTrace_append hprefix tailTrace_1492062
  have hstable : (prefixWord ++ tailWord_1492062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492062).length < 2 ^ (prefixWord ++ tailWord_1492062).sum := by decide
  have hdescent : baseEnd_1492062 < baseStart_1492062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492087 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 4]
def baseStart_1492087 : Nat := 118140960795 + 1492087 * 2 ^ 59
def prefixEnd_1492087 : Nat := 4983230072969 + 3 ^ 40 * 1492087 * 2
def baseEnd_1492087 : Nat := 340514581922315082866899

theorem tailTrace_1492087 : CollatzResearch.WordTrace tailWord_1492087 prefixEnd_1492087 340514581922315082866899 := by
  unfold tailWord_1492087
  simp only [CollatzResearch.WordTrace]
  refine ⟨54420883745431102016802515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36280589163620734677868343 54420883745431102016802515)
  ·
    refine ⟨81631325618146653025203773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54420883745431102016802515 81631325618146653025203773)
    ·
      refine ⟨30611747106804994884451415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81631325618146653025203773 30611747106804994884451415)
      ·
        refine ⟨45917620660207492326677123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30611747106804994884451415 45917620660207492326677123)
        ·
          refine ⟨68876430990311238490015685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45917620660207492326677123 68876430990311238490015685)
          ·
            refine ⟨12914330810683357216877941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68876430990311238490015685 12914330810683357216877941)
            ·
              refine ⟨1210718513501564739082307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12914330810683357216877941 1210718513501564739082307)
              ·
                refine ⟨1816077770252347108623461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210718513501564739082307 1816077770252347108623461)
                ·
                  refine ⟨340514581922315082866899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816077770252347108623461 340514581922315082866899)
                  ·
                    rfl

theorem cell21_1492087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_1492087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492087 prefixEnd_1492087 := by exact prefixLift 1492087
  have htrace : WordTrace (prefixWord ++ tailWord_1492087) baseStart_1492087 baseEnd_1492087 := by
    simpa [prefixWord, tailWord_1492087, baseEnd_1492087] using wordTrace_append hprefix tailTrace_1492087
  have hstable : (prefixWord ++ tailWord_1492087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492087).length < 2 ^ (prefixWord ++ tailWord_1492087).sum := by decide
  have hdescent : baseEnd_1492087 < baseStart_1492087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492101 : List Nat := [1, 3, 1, 1, 6, 1, 1, 7]
def baseStart_1492101 : Nat := 118140960795 + 1492101 * 2 ^ 59
def prefixEnd_1492101 : Nat := 4983230072969 + 3 ^ 40 * 1492101 * 2
def baseEnd_1492101 : Nat := 113505925637684723211179

theorem tailTrace_1492101 : CollatzResearch.WordTrace tailWord_1492101 prefixEnd_1492101 113505925637684723211179 := by
  unfold tailWord_1492101
  simp only [CollatzResearch.WordTrace]
  refine ⟨54421394367380382407812157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36280929578253588271874771 54421394367380382407812157)
  ·
    refine ⟨20408022887767643402929559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54421394367380382407812157 20408022887767643402929559)
    ·
      refine ⟨30612034331651465104394339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20408022887767643402929559 30612034331651465104394339)
      ·
        refine ⟨45918051497477197656591509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30612034331651465104394339 45918051497477197656591509)
        ·
          refine ⟨2152408663944243640152727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45918051497477197656591509 2152408663944243640152727)
          ·
            refine ⟨3228612995916365460229091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152408663944243640152727 3228612995916365460229091)
            ·
              refine ⟨4842919493874548190343637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228612995916365460229091 4842919493874548190343637)
              ·
                refine ⟨113505925637684723211179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4842919493874548190343637 113505925637684723211179)
                ·
                  rfl

theorem cell21_1492101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_1492101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492101 prefixEnd_1492101 := by exact prefixLift 1492101
  have htrace : WordTrace (prefixWord ++ tailWord_1492101) baseStart_1492101 baseEnd_1492101 := by
    simpa [prefixWord, tailWord_1492101, baseEnd_1492101] using wordTrace_append hprefix tailTrace_1492101
  have hstable : (prefixWord ++ tailWord_1492101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492101).length < 2 ^ (prefixWord ++ tailWord_1492101).sum := by decide
  have hdescent : baseEnd_1492101 < baseStart_1492101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492132 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1492132 : Nat := 118140960795 + 1492132 * 2 ^ 59
def prefixEnd_1492132 : Nat := 4983230072969 + 3 ^ 40 * 1492132 * 2
def baseEnd_1492132 : Nat := 340524851535405004616807

theorem tailTrace_1492132 : CollatzResearch.WordTrace tailWord_1492132 prefixEnd_1492132 340524851535405004616807 := by
  unfold tailWord_1492132
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211262515134037351095325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36281683353512049801460433 27211262515134037351095325)
  ·
    refine ⟨10204223443175264006660747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27211262515134037351095325 10204223443175264006660747)
    ·
      refine ⟨15306335164762896009991121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10204223443175264006660747 15306335164762896009991121)
      ·
        refine ⟨11479751373572172007493341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15306335164762896009991121 11479751373572172007493341)
        ·
          refine ⟨4304906765089564502810003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11479751373572172007493341 4304906765089564502810003)
          ·
            refine ⟨6457360147634346754215005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304906765089564502810003 6457360147634346754215005)
            ·
              refine ⟨2421510055362880032830627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457360147634346754215005 2421510055362880032830627)
              ·
                refine ⟨3632265083044320049245941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421510055362880032830627 3632265083044320049245941)
                ·
                  refine ⟨340524851535405004616807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3632265083044320049245941 340524851535405004616807)
                  ·
                    rfl

theorem cell21_1492132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1492132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492132 prefixEnd_1492132 := by exact prefixLift 1492132
  have htrace : WordTrace (prefixWord ++ tailWord_1492132) baseStart_1492132 baseEnd_1492132 := by
    simpa [prefixWord, tailWord_1492132, baseEnd_1492132] using wordTrace_append hprefix tailTrace_1492132
  have hstable : (prefixWord ++ tailWord_1492132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492132).length < 2 ^ (prefixWord ++ tailWord_1492132).sum := by decide
  have hdescent : baseEnd_1492132 < baseStart_1492132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492225 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 3]
def baseStart_1492225 : Nat := 118140960795 + 1492225 * 2 ^ 59
def prefixEnd_1492225 : Nat := 4983230072969 + 3 ^ 40 * 1492225 * 2
def baseEnd_1492225 : Nat := 340546075402457509566617

theorem tailTrace_1492225 : CollatzResearch.WordTrace tailWord_1492225 prefixEnd_1492225 340546075402457509566617 := by
  unfold tailWord_1492225
  simp only [CollatzResearch.WordTrace]
  refine ⟨54425917018931151585326129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36283944679287434390217419 54425917018931151585326129)
  ·
    refine ⟨40819437764198363688994597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54425917018931151585326129 40819437764198363688994597)
    ·
      refine ⟨7653644580787193191686487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40819437764198363688994597 7653644580787193191686487)
      ·
        refine ⟨11480466871180789787529731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653644580787193191686487 11480466871180789787529731)
        ·
          refine ⟨17220700306771184681294597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480466871180789787529731 17220700306771184681294597)
          ·
            refine ⟨3228881307519597127742737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17220700306771184681294597 3228881307519597127742737)
            ·
              refine ⟨2421660980639697845807053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228881307519597127742737 2421660980639697845807053)
              ·
                refine ⟨908122867739886692177645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421660980639697845807053 908122867739886692177645)
                ·
                  refine ⟨340546075402457509566617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908122867739886692177645 340546075402457509566617)
                  ·
                    rfl

theorem cell21_1492225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_1492225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492225 prefixEnd_1492225 := by exact prefixLift 1492225
  have htrace : WordTrace (prefixWord ++ tailWord_1492225) baseStart_1492225 baseEnd_1492225 := by
    simpa [prefixWord, tailWord_1492225, baseEnd_1492225] using wordTrace_append hprefix tailTrace_1492225
  have hstable : (prefixWord ++ tailWord_1492225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492225).length < 2 ^ (prefixWord ++ tailWord_1492225).sum := by decide
  have hdescent : baseEnd_1492225 < baseStart_1492225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492236 : List Nat := [2, 2, 1, 2, 2, 4, 8]
def baseStart_1492236 : Nat := 118140960795 + 1492236 * 2 ^ 59
def prefixEnd_1492236 : Nat := 4983230072969 + 3 ^ 40 * 1492236 * 2
def baseEnd_1492236 : Nat := 37838731750258214987029

theorem tailTrace_1492236 : CollatzResearch.WordTrace tailWord_1492236 prefixEnd_1492236 37838731750258214987029 := by
  unfold tailWord_1492236
  simp only [CollatzResearch.WordTrace]
  refine ⟨27213159110945650231988281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36284212147927533642651041 27213159110945650231988281)
  ·
    refine ⟨20409869333209237673991211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27213159110945650231988281 20409869333209237673991211)
    ·
      refine ⟨30614803999813856510986817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20409869333209237673991211 30614803999813856510986817)
      ·
        refine ⟨22961102999860392383240113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30614803999813856510986817 22961102999860392383240113)
        ·
          refine ⟨17220827249895294287430085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22961102999860392383240113 17220827249895294287430085)
          ·
            refine ⟨3228905109355367678893141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17220827249895294287430085 3228905109355367678893141)
            ·
              refine ⟨37838731750258214987029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3228905109355367678893141 37838731750258214987029)
              ·
                rfl

theorem cell21_1492236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 8].length) (baseStart_1492236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492236 prefixEnd_1492236 := by exact prefixLift 1492236
  have htrace : WordTrace (prefixWord ++ tailWord_1492236) baseStart_1492236 baseEnd_1492236 := by
    simpa [prefixWord, tailWord_1492236, baseEnd_1492236] using wordTrace_append hprefix tailTrace_1492236
  have hstable : (prefixWord ++ tailWord_1492236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492236).length < 2 ^ (prefixWord ++ tailWord_1492236).sum := by decide
  have hdescent : baseEnd_1492236 < baseStart_1492236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492242 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1492242 : Nat := 118140960795 + 1492242 * 2 ^ 59
def prefixEnd_1492242 : Nat := 4983230072969 + 3 ^ 40 * 1492242 * 2
def baseEnd_1492242 : Nat := 340549955034069257783249

theorem tailTrace_1492242 : CollatzResearch.WordTrace tailWord_1492242 prefixEnd_1492242 340549955034069257783249 := by
  unfold tailWord_1492242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606634264967390872173745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36284358039913042325796653 13606634264967390872173745)
  ·
    refine ⟨10204975698725543154130309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13606634264967390872173745 10204975698725543154130309)
    ·
      refine ⟨1913432943511039341399433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10204975698725543154130309 1913432943511039341399433)
      ·
        refine ⟨1435074707633279506049575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913432943511039341399433 1435074707633279506049575)
        ·
          refine ⟨2152612061449919259074363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435074707633279506049575 2152612061449919259074363)
          ·
            refine ⟨3228918092174878888611545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152612061449919259074363 3228918092174878888611545)
            ·
              refine ⟨2421688569131159166458659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228918092174878888611545 2421688569131159166458659)
              ·
                refine ⟨3632532853696738749687989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421688569131159166458659 3632532853696738749687989)
                ·
                  refine ⟨340549955034069257783249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3632532853696738749687989 340549955034069257783249)
                  ·
                    rfl

theorem cell21_1492242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1492242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492242 prefixEnd_1492242 := by exact prefixLift 1492242
  have htrace : WordTrace (prefixWord ++ tailWord_1492242) baseStart_1492242 baseEnd_1492242 := by
    simpa [prefixWord, tailWord_1492242, baseEnd_1492242] using wordTrace_append hprefix tailTrace_1492242
  have hstable : (prefixWord ++ tailWord_1492242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492242).length < 2 ^ (prefixWord ++ tailWord_1492242).sum := by decide
  have hdescent : baseEnd_1492242 < baseStart_1492242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492256 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_1492256 : Nat := 118140960795 + 1492256 * 2 ^ 59
def prefixEnd_1492256 : Nat := 4983230072969 + 3 ^ 40 * 1492256 * 2
def baseEnd_1492256 : Nat := 340553150024808344549887

theorem tailTrace_1492256 : CollatzResearch.WordTrace tailWord_1492256 prefixEnd_1492256 340553150024808344549887 := by
  unfold tailWord_1492256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27213523840909421939852311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36284698454545895919803081 27213523840909421939852311)
  ·
    refine ⟨40820285761364132909778467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27213523840909421939852311 40820285761364132909778467)
    ·
      refine ⟨61230428642046199364667701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40820285761364132909778467 61230428642046199364667701)
      ·
        refine ⟨5740352685191831190437597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61230428642046199364667701 5740352685191831190437597)
        ·
          refine ⟨2152632256946936696414099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5740352685191831190437597 2152632256946936696414099)
          ·
            refine ⟨3228948385420405044621149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152632256946936696414099 3228948385420405044621149)
            ·
              refine ⟨1210855644532651891732931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3228948385420405044621149 1210855644532651891732931)
              ·
                refine ⟨1816283466798977837599397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210855644532651891732931 1816283466798977837599397)
                ·
                  refine ⟨340553150024808344549887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816283466798977837599397 340553150024808344549887)
                  ·
                    rfl

theorem cell21_1492256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_1492256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492256 prefixEnd_1492256 := by exact prefixLift 1492256
  have htrace : WordTrace (prefixWord ++ tailWord_1492256) baseStart_1492256 baseEnd_1492256 := by
    simpa [prefixWord, tailWord_1492256, baseEnd_1492256] using wordTrace_append hprefix tailTrace_1492256
  have hstable : (prefixWord ++ tailWord_1492256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492256).length < 2 ^ (prefixWord ++ tailWord_1492256).sum := by decide
  have hdescent : baseEnd_1492256 < baseStart_1492256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492312 : List Nat := [2, 1, 2, 2, 1, 1, 6, 6]
def baseStart_1492312 : Nat := 118140960795 + 1492312 * 2 ^ 59
def prefixEnd_1492312 : Nat := 4983230072969 + 3 ^ 40 * 1492312 * 2
def baseEnd_1492312 : Nat := 113521976662588230538813

theorem tailTrace_1492312 : CollatzResearch.WordTrace tailWord_1492312 prefixEnd_1492312 113521976662588230538813 := by
  unfold tailWord_1492312
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214545084807982721871595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36286060113077310295828793 27214545084807982721871595)
  ·
    refine ⟨40821817627211974082807393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27214545084807982721871595 40821817627211974082807393)
    ·
      refine ⟨30616363220408980562105545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40821817627211974082807393 30616363220408980562105545)
      ·
        refine ⟨22962272415306735421579159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30616363220408980562105545 22962272415306735421579159)
        ·
          refine ⟨34443408622960103132368739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22962272415306735421579159 34443408622960103132368739)
          ·
            refine ⟨51665112934440154698553109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34443408622960103132368739 51665112934440154698553109)
            ·
              refine ⟨2421802168801882251494677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51665112934440154698553109 2421802168801882251494677)
              ·
                refine ⟨113521976662588230538813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2421802168801882251494677 113521976662588230538813)
                ·
                  rfl

theorem cell21_1492312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_1492312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492312 prefixEnd_1492312 := by exact prefixLift 1492312
  have htrace : WordTrace (prefixWord ++ tailWord_1492312) baseStart_1492312 baseEnd_1492312 := by
    simpa [prefixWord, tailWord_1492312, baseEnd_1492312] using wordTrace_append hprefix tailTrace_1492312
  have hstable : (prefixWord ++ tailWord_1492312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492312).length < 2 ^ (prefixWord ++ tailWord_1492312).sum := by decide
  have hdescent : baseEnd_1492312 < baseStart_1492312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492357 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1492357 : Nat := 118140960795 + 1492357 * 2 ^ 59
def prefixEnd_1492357 : Nat := 4983230072969 + 3 ^ 40 * 1492357 * 2
def baseEnd_1492357 : Nat := 340576199600854613366347

theorem tailTrace_1492357 : CollatzResearch.WordTrace tailWord_1492357 prefixEnd_1492357 340576199600854613366347 := by
  unfold tailWord_1492357
  simp only [CollatzResearch.WordTrace]
  refine ⟨54430731454452938129131325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36287154302968625419420883 54430731454452938129131325)
  ·
    refine ⟨20411524295419851798424247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54430731454452938129131325 20411524295419851798424247)
    ·
      refine ⟨30617286443129777697636371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20411524295419851798424247 30617286443129777697636371)
      ·
        refine ⟨45925929664694666546454557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30617286443129777697636371 45925929664694666546454557)
        ·
          refine ⟨17222223624260499954920459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45925929664694666546454557 17222223624260499954920459)
          ·
            refine ⟨25833335436390749932380689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17222223624260499954920459 25833335436390749932380689)
            ·
              refine ⟨19375001577293062449285517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25833335436390749932380689 19375001577293062449285517)
              ·
                refine ⟨7265625591484898418482069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19375001577293062449285517 7265625591484898418482069)
                ·
                  refine ⟨340576199600854613366347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7265625591484898418482069 340576199600854613366347)
                  ·
                    rfl

theorem cell21_1492357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1492357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492357 prefixEnd_1492357 := by exact prefixLift 1492357
  have htrace : WordTrace (prefixWord ++ tailWord_1492357) baseStart_1492357 baseEnd_1492357 := by
    simpa [prefixWord, tailWord_1492357, baseEnd_1492357] using wordTrace_append hprefix tailTrace_1492357
  have hstable : (prefixWord ++ tailWord_1492357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492357).length < 2 ^ (prefixWord ++ tailWord_1492357).sum := by decide
  have hdescent : baseEnd_1492357 < baseStart_1492357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492453 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1492453 : Nat := 118140960795 + 1492453 * 2 ^ 59
def prefixEnd_1492453 : Nat := 4983230072969 + 3 ^ 40 * 1492453 * 2
def baseEnd_1492453 : Nat := 340598108108779779766151

theorem tailTrace_1492453 : CollatzResearch.WordTrace tailWord_1492453 prefixEnd_1492453 340598108108779779766151 := by
  unfold tailWord_1492453
  simp only [CollatzResearch.WordTrace]
  refine ⟨54434232862105146524626013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36289488574736764349750675 54434232862105146524626013)
  ·
    refine ⟨20412837323289429946734755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54434232862105146524626013 20412837323289429946734755)
    ·
      refine ⟨30619255984934144920102133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20412837323289429946734755 30619255984934144920102133)
      ·
        refine ⟨2870555248587576086259575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30619255984934144920102133 2870555248587576086259575)
        ·
          refine ⟨4305832872881364129389363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870555248587576086259575 4305832872881364129389363)
          ·
            refine ⟨6458749309322046194084045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305832872881364129389363 6458749309322046194084045)
            ·
              refine ⟨2422030990995767322781517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6458749309322046194084045 2422030990995767322781517)
              ·
                refine ⟨908261621623412746043069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2422030990995767322781517 908261621623412746043069)
                ·
                  refine ⟨340598108108779779766151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908261621623412746043069 340598108108779779766151)
                  ·
                    rfl

theorem cell21_1492453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1492453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492453 prefixEnd_1492453 := by exact prefixLift 1492453
  have htrace : WordTrace (prefixWord ++ tailWord_1492453) baseStart_1492453 baseEnd_1492453 := by
    simpa [prefixWord, tailWord_1492453, baseEnd_1492453] using wordTrace_append hprefix tailTrace_1492453
  have hstable : (prefixWord ++ tailWord_1492453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492453).length < 2 ^ (prefixWord ++ tailWord_1492453).sum := by decide
  have hdescent : baseEnd_1492453 < baseStart_1492453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492464 : List Nat := [2, 1, 1, 1, 3, 6, 7]
def baseStart_1492464 : Nat := 118140960795 + 1492464 * 2 ^ 59
def prefixEnd_1492464 : Nat := 4983230072969 + 3 ^ 40 * 1492464 * 2
def baseEnd_1492464 : Nat := 37844513162071800564755

theorem tailTrace_1492464 : CollatzResearch.WordTrace tailWord_1492464 prefixEnd_1492464 37844513162071800564755 := by
  unfold tailWord_1492464
  simp only [CollatzResearch.WordTrace]
  refine ⟨27217317032532647701638223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36289756043376863602184297 27217317032532647701638223)
  ·
    refine ⟨40825975548798971552457335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27217317032532647701638223 40825975548798971552457335)
    ·
      refine ⟨61238963323198457328686003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40825975548798971552457335 61238963323198457328686003)
      ·
        refine ⟨91858444984797685993029005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61238963323198457328686003 91858444984797685993029005)
        ·
          refine ⟨34446916869299132247385877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91858444984797685993029005 34446916869299132247385877)
          ·
            refine ⟨1614699228248396824096213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34446916869299132247385877 1614699228248396824096213)
            ·
              refine ⟨37844513162071800564755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1614699228248396824096213 37844513162071800564755)
              ·
                rfl

theorem cell21_1492464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 7].length) (baseStart_1492464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492464 prefixEnd_1492464 := by exact prefixLift 1492464
  have htrace : WordTrace (prefixWord ++ tailWord_1492464) baseStart_1492464 baseEnd_1492464 := by
    simpa [prefixWord, tailWord_1492464, baseEnd_1492464] using wordTrace_append hprefix tailTrace_1492464
  have hstable : (prefixWord ++ tailWord_1492464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492464).length < 2 ^ (prefixWord ++ tailWord_1492464).sum := by decide
  have hdescent : baseEnd_1492464 < baseStart_1492464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492470 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1492470 : Nat := 118140960795 + 1492470 * 2 ^ 59
def prefixEnd_1492470 : Nat := 4983230072969 + 3 ^ 40 * 1492470 * 2
def baseEnd_1492470 : Nat := 340601987740391527982783

theorem tailTrace_1492470 : CollatzResearch.WordTrace tailWord_1492470 prefixEnd_1492470 340601987740391527982783 := by
  unfold tailWord_1492470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402178306440222401749679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36289901935362372285329909 3402178306440222401749679)
  ·
    refine ⟨5103267459660333602624519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402178306440222401749679 5103267459660333602624519)
    ·
      refine ⟨7654901189490500403936779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103267459660333602624519 7654901189490500403936779)
      ·
        refine ⟨11482351784235750605905169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7654901189490500403936779 11482351784235750605905169)
        ·
          refine ⟨8611763838176812954428877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11482351784235750605905169 8611763838176812954428877)
          ·
            refine ⟨3229411439316304857910829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8611763838176812954428877 3229411439316304857910829)
            ·
              refine ⟨1211029289743614321716561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229411439316304857910829 1211029289743614321716561)
              ·
                refine ⟨908271967307710741287421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211029289743614321716561 908271967307710741287421)
                ·
                  refine ⟨340601987740391527982783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908271967307710741287421 340601987740391527982783)
                  ·
                    rfl

theorem cell21_1492470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1492470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492470 prefixEnd_1492470 := by exact prefixLift 1492470
  have htrace : WordTrace (prefixWord ++ tailWord_1492470) baseStart_1492470 baseEnd_1492470 := by
    simpa [prefixWord, tailWord_1492470, baseEnd_1492470] using wordTrace_append hprefix tailTrace_1492470
  have hstable : (prefixWord ++ tailWord_1492470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492470).length < 2 ^ (prefixWord ++ tailWord_1492470).sum := by decide
  have hdescent : baseEnd_1492470 < baseStart_1492470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492481 : List Nat := [1, 2, 4, 1, 4, 1, 2, 6]
def baseStart_1492481 : Nat := 118140960795 + 1492481 * 2 ^ 59
def prefixEnd_1492481 : Nat := 4983230072969 + 3 ^ 40 * 1492481 * 2
def baseEnd_1492481 : Nat := 113534832696752651099809

theorem tailTrace_1492481 : CollatzResearch.WordTrace tailWord_1492481 prefixEnd_1492481 113534832696752651099809 := by
  unfold tailWord_1492481
  simp only [CollatzResearch.WordTrace]
  refine ⟨54435254106003707306645297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36290169404002471537763531 54435254106003707306645297)
  ·
    refine ⟨40826440579502780479983973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54435254106003707306645297 40826440579502780479983973)
    ·
      refine ⟨7654957608656771339996995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40826440579502780479983973 7654957608656771339996995)
      ·
        refine ⟨11482436412985157009995493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7654957608656771339996995 11482436412985157009995493)
        ·
          refine ⟨2152956827434716939374155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11482436412985157009995493 2152956827434716939374155)
          ·
            refine ⟨3229435241152075409061233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152956827434716939374155 3229435241152075409061233)
            ·
              refine ⟨2422076430864056556795925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229435241152075409061233 2422076430864056556795925)
              ·
                refine ⟨113534832696752651099809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422076430864056556795925 113534832696752651099809)
                ·
                  rfl

theorem cell21_1492481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_1492481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492481 prefixEnd_1492481 := by exact prefixLift 1492481
  have htrace : WordTrace (prefixWord ++ tailWord_1492481) baseStart_1492481 baseEnd_1492481 := by
    simpa [prefixWord, tailWord_1492481, baseEnd_1492481] using wordTrace_append hprefix tailTrace_1492481
  have hstable : (prefixWord ++ tailWord_1492481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492481).length < 2 ^ (prefixWord ++ tailWord_1492481).sum := by decide
  have hdescent : baseEnd_1492481 < baseStart_1492481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492599 : List Nat := [1, 1, 3, 1, 1, 3, 1, 10]
def baseStart_1492599 : Nat := 118140960795 + 1492599 * 2 ^ 59
def prefixEnd_1492599 : Nat := 4983230072969 + 3 ^ 40 * 1492599 * 2
def baseEnd_1492599 : Nat := 113543809099305323444173

theorem tailTrace_1492599 : CollatzResearch.WordTrace tailWord_1492599 prefixEnd_1492599 113543809099305323444173 := by
  unfold tailWord_1492599
  simp only [CollatzResearch.WordTrace]
  refine ⟨54439557919576213459440851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36293038613050808972960567 54439557919576213459440851)
  ·
    refine ⟨81659336879364320189161277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54439557919576213459440851 81659336879364320189161277)
    ·
      refine ⟨30622251329761620070935479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81659336879364320189161277 30622251329761620070935479)
      ·
        refine ⟨45933376994642430106403219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30622251329761620070935479 45933376994642430106403219)
        ·
          refine ⟨68900065491963645159604829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45933376994642430106403219 68900065491963645159604829)
          ·
            refine ⟨25837524559486366934851811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68900065491963645159604829 25837524559486366934851811)
            ·
              refine ⟨38756286839229550402277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25837524559486366934851811 38756286839229550402277717)
              ·
                refine ⟨113543809099305323444173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38756286839229550402277717 113543809099305323444173)
                ·
                  rfl

theorem cell21_1492599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_1492599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492599 prefixEnd_1492599 := by exact prefixLift 1492599
  have htrace : WordTrace (prefixWord ++ tailWord_1492599) baseStart_1492599 baseEnd_1492599 := by
    simpa [prefixWord, tailWord_1492599, baseEnd_1492599] using wordTrace_append hprefix tailTrace_1492599
  have hstable : (prefixWord ++ tailWord_1492599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492599).length < 2 ^ (prefixWord ++ tailWord_1492599).sum := by decide
  have hdescent : baseEnd_1492599 < baseStart_1492599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492692 : List Nat := [2, 4, 1, 3, 1, 10]
def baseStart_1492692 : Nat := 118140960795 + 1492692 * 2 ^ 59
def prefixEnd_1492692 : Nat := 4983230072969 + 3 ^ 40 * 1492692 * 2
def baseEnd_1492692 : Nat := 12616764857961795380827

theorem tailTrace_1492692 : CollatzResearch.WordTrace tailWord_1492692 prefixEnd_1492692 12616764857961795380827 := by
  unfold tailWord_1492692
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221474954119645171288165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36295299938826193561717553 27221474954119645171288165)
  ·
    refine ⟨5104026553897433469616531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27221474954119645171288165 5104026553897433469616531)
    ·
      refine ⟨7656039830846150204424797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104026553897433469616531 7656039830846150204424797)
      ·
        refine ⟨2871014936567306326659299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7656039830846150204424797 2871014936567306326659299)
        ·
          refine ⟨4306522404850959489988949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871014936567306326659299 4306522404850959489988949)
          ·
            refine ⟨12616764857961795380827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4306522404850959489988949 12616764857961795380827)
            ·
              rfl

theorem cell21_1492692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 10].length) (baseStart_1492692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492692 prefixEnd_1492692 := by exact prefixLift 1492692
  have htrace : WordTrace (prefixWord ++ tailWord_1492692) baseStart_1492692 baseEnd_1492692 := by
    simpa [prefixWord, tailWord_1492692, baseEnd_1492692] using wordTrace_append hprefix tailTrace_1492692
  have hstable : (prefixWord ++ tailWord_1492692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492692).length < 2 ^ (prefixWord ++ tailWord_1492692).sum := by decide
  have hdescent : baseEnd_1492692 < baseStart_1492692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492740 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1492740 : Nat := 118140960795 + 1492740 * 2 ^ 59
def prefixEnd_1492740 : Nat := 4983230072969 + 3 ^ 40 * 1492740 * 2
def baseEnd_1492740 : Nat := 340663605418931058482231

theorem tailTrace_1492740 : CollatzResearch.WordTrace tailWord_1492740 prefixEnd_1492740 340663605418931058482231 := by
  unfold tailWord_1492740
  simp only [CollatzResearch.WordTrace]
  refine ⟨27222350306032697270161837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36296467074710263026882449 27222350306032697270161837)
  ·
    refine ⟨10208381364762261476310689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27222350306032697270161837 10208381364762261476310689)
    ·
      refine ⟨7656286023571696107233017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10208381364762261476310689 7656286023571696107233017)
      ·
        refine ⟨5742214517678772080424763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7656286023571696107233017 5742214517678772080424763)
        ·
          refine ⟨8613321776518158120637145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742214517678772080424763 8613321776518158120637145)
          ·
            refine ⟨6459991332388618590477859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8613321776518158120637145 6459991332388618590477859)
            ·
              refine ⟨9689986998582927885716789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459991332388618590477859 9689986998582927885716789)
              ·
                refine ⟨908436281117149489285949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9689986998582927885716789 908436281117149489285949)
                ·
                  refine ⟨340663605418931058482231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908436281117149489285949 340663605418931058482231)
                  ·
                    rfl

theorem cell21_1492740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1492740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492740 prefixEnd_1492740 := by exact prefixLift 1492740
  have htrace : WordTrace (prefixWord ++ tailWord_1492740) baseStart_1492740 baseEnd_1492740 := by
    simpa [prefixWord, tailWord_1492740, baseEnd_1492740] using wordTrace_append hprefix tailTrace_1492740
  have hstable : (prefixWord ++ tailWord_1492740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492740).length < 2 ^ (prefixWord ++ tailWord_1492740).sum := by decide
  have hdescent : baseEnd_1492740 < baseStart_1492740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492785 : List Nat := [1, 2, 2, 3, 2, 4, 2, 5]
def baseStart_1492785 : Nat := 118140960795 + 1492785 * 2 ^ 59
def prefixEnd_1492785 : Nat := 4983230072969 + 3 ^ 40 * 1492785 * 2
def baseEnd_1492785 : Nat := 113557958344006993410713

theorem tailTrace_1492785 : CollatzResearch.WordTrace tailWord_1492785 prefixEnd_1492785 113557958344006993410713 := by
  unfold tailWord_1492785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54446341896902367225711809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36297561264601578150474539 54446341896902367225711809)
  ·
    refine ⟨40834756422676775419283857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54446341896902367225711809 40834756422676775419283857)
    ·
      refine ⟨30626067317007581564462893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40834756422676775419283857 30626067317007581564462893)
      ·
        refine ⟨11484775243877843086673585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30626067317007581564462893 11484775243877843086673585)
        ·
          refine ⟨8613581432908382315005189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11484775243877843086673585 8613581432908382315005189)
          ·
            refine ⟨1615046518670321684063473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8613581432908382315005189 1615046518670321684063473)
            ·
              refine ⟨1211284889002741263047605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615046518670321684063473 1211284889002741263047605)
              ·
                refine ⟨113557958344006993410713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1211284889002741263047605 113557958344006993410713)
                ·
                  rfl

theorem cell21_1492785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].length) (baseStart_1492785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492785 prefixEnd_1492785 := by exact prefixLift 1492785
  have htrace : WordTrace (prefixWord ++ tailWord_1492785) baseStart_1492785 baseEnd_1492785 := by
    simpa [prefixWord, tailWord_1492785, baseEnd_1492785] using wordTrace_append hprefix tailTrace_1492785
  have hstable : (prefixWord ++ tailWord_1492785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492785).length < 2 ^ (prefixWord ++ tailWord_1492785).sum := by decide
  have hdescent : baseEnd_1492785 < baseStart_1492785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492878 : List Nat := [4, 1, 1, 5, 1, 2, 1, 6]
def baseStart_1492878 : Nat := 118140960795 + 1492878 * 2 ^ 59
def prefixEnd_1492878 : Nat := 4983230072969 + 3 ^ 40 * 1492878 * 2
def baseEnd_1492878 : Nat := 113565032966357828393983

theorem tailTrace_1492878 : CollatzResearch.WordTrace tailWord_1492878 prefixEnd_1492878 113565032966357828393983 := by
  unfold tailWord_1492878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806216735695680513605911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36299822590376962739231525 6806216735695680513605911)
  ·
    refine ⟨10209325103543520770408867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806216735695680513605911 10209325103543520770408867)
    ·
      refine ⟨15313987655315281155613301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209325103543520770408867 15313987655315281155613301)
      ·
        refine ⟨1435686342685807608338747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15313987655315281155613301 1435686342685807608338747)
        ·
          refine ⟨2153529514028711412508121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435686342685807608338747 2153529514028711412508121)
          ·
            refine ⟨1615147135521533559381091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153529514028711412508121 1615147135521533559381091)
            ·
              refine ⟨2422720703282300339071637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615147135521533559381091 2422720703282300339071637)
              ·
                refine ⟨113565032966357828393983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422720703282300339071637 113565032966357828393983)
                ·
                  rfl

theorem cell21_1492878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_1492878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492878 prefixEnd_1492878 := by exact prefixLift 1492878
  have htrace : WordTrace (prefixWord ++ tailWord_1492878) baseStart_1492878 baseEnd_1492878 := by
    simpa [prefixWord, tailWord_1492878, baseEnd_1492878] using wordTrace_append hprefix tailTrace_1492878
  have hstable : (prefixWord ++ tailWord_1492878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492878).length < 2 ^ (prefixWord ++ tailWord_1492878).sum := by decide
  have hdescent : baseEnd_1492878 < baseStart_1492878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492889 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_1492889 : Nat := 118140960795 + 1492889 * 2 ^ 59
def prefixEnd_1492889 : Nat := 4983230072969 + 3 ^ 40 * 1492889 * 2
def baseEnd_1492889 : Nat := 340697609248939910498593

theorem tailTrace_1492889 : CollatzResearch.WordTrace tailWord_1492889 prefixEnd_1492889 340697609248939910498593 := by
  unfold tailWord_1492889
  simp only [CollatzResearch.WordTrace]
  refine ⟨54450135088525592987497721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36300090059017061991665147 54450135088525592987497721)
  ·
    refine ⟨40837601316394194740623291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54450135088525592987497721 40837601316394194740623291)
    ·
      refine ⟨61256401974591292110934937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40837601316394194740623291 61256401974591292110934937)
      ·
        refine ⟨45942301480943469083201203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61256401974591292110934937 45942301480943469083201203)
        ·
          refine ⟨68913452221415203624801805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45942301480943469083201203 68913452221415203624801805)
          ·
            refine ⟨25842544583030701359300677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68913452221415203624801805 25842544583030701359300677)
            ·
              refine ⟨4845477109318256504868877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25842544583030701359300677 4845477109318256504868877)
              ·
                refine ⟨1817053915994346189325829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4845477109318256504868877 1817053915994346189325829)
                ·
                  refine ⟨340697609248939910498593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817053915994346189325829 340697609248939910498593)
                  ·
                    rfl

theorem cell21_1492889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_1492889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492889 prefixEnd_1492889 := by exact prefixLift 1492889
  have htrace : WordTrace (prefixWord ++ tailWord_1492889) baseStart_1492889 baseEnd_1492889 := by
    simpa [prefixWord, tailWord_1492889, baseEnd_1492889] using wordTrace_append hprefix tailTrace_1492889
  have hstable : (prefixWord ++ tailWord_1492889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492889).length < 2 ^ (prefixWord ++ tailWord_1492889).sum := by decide
  have hdescent : baseEnd_1492889 < baseStart_1492889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492954 : List Nat := [3, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1492954 : Nat := 118140960795 + 1492954 * 2 ^ 59
def prefixEnd_1492954 : Nat := 4983230072969 + 3 ^ 40 * 1492954 * 2
def baseEnd_1492954 : Nat := 113570814378171413971709

theorem tailTrace_1492954 : CollatzResearch.WordTrace tailWord_1492954 prefixEnd_1492954 113570814378171413971709 := by
  unfold tailWord_1492954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613126458322527272153479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36301670555526739392409277 13613126458322527272153479)
  ·
    refine ⟨20419689687483790908230219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13613126458322527272153479 20419689687483790908230219)
    ·
      refine ⟨30629534531225686362345329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20419689687483790908230219 30629534531225686362345329)
      ·
        refine ⟨22972150898419264771758997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30629534531225686362345329 22972150898419264771758997)
        ·
          refine ⟨1076819573363403036176203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22972150898419264771758997 1076819573363403036176203)
          ·
            refine ⟨1615229360045104554264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076819573363403036176203 1615229360045104554264305)
            ·
              refine ⟨1211422020033828415698229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615229360045104554264305 1211422020033828415698229)
              ·
                refine ⟨113570814378171413971709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1211422020033828415698229 113570814378171413971709)
                ·
                  rfl

theorem cell21_1492954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1492954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492954 prefixEnd_1492954 := by exact prefixLift 1492954
  have htrace : WordTrace (prefixWord ++ tailWord_1492954) baseStart_1492954 baseEnd_1492954 := by
    simpa [prefixWord, tailWord_1492954, baseEnd_1492954] using wordTrace_append hprefix tailTrace_1492954
  have hstable : (prefixWord ++ tailWord_1492954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492954).length < 2 ^ (prefixWord ++ tailWord_1492954).sum := by decide
  have hdescent : baseEnd_1492954 < baseStart_1492954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492999 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 4]
def baseStart_1492999 : Nat := 118140960795 + 1492999 * 2 ^ 59
def prefixEnd_1492999 : Nat := 4983230072969 + 3 ^ 40 * 1492999 * 2
def baseEnd_1492999 : Nat := 340722712747604163665035

theorem tailTrace_1492999 : CollatzResearch.WordTrace tailWord_1492999 prefixEnd_1492999 340722712747604163665035 := by
  unfold tailWord_1492999
  simp only [CollatzResearch.WordTrace]
  refine ⟨54454147118127081774002051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36302764745418054516001367 54454147118127081774002051)
  ·
    refine ⟨81681220677190622661003077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54454147118127081774002051 81681220677190622661003077)
    ·
      refine ⟨15315228876973241748938077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81681220677190622661003077 15315228876973241748938077)
      ·
        refine ⟨5743210828864965655851779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15315228876973241748938077 5743210828864965655851779)
        ·
          refine ⟨8614816243297448483777669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743210828864965655851779 8614816243297448483777669)
          ·
            refine ⟨1615278045618271590708313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8614816243297448483777669 1615278045618271590708313)
            ·
              refine ⟨1211458534213703693031235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615278045618271590708313 1211458534213703693031235)
              ·
                refine ⟨1817187801320555539546853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211458534213703693031235 1817187801320555539546853)
                ·
                  refine ⟨340722712747604163665035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817187801320555539546853 340722712747604163665035)
                  ·
                    rfl

theorem cell21_1492999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_1492999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1492999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1492999 prefixEnd_1492999 := by exact prefixLift 1492999
  have htrace : WordTrace (prefixWord ++ tailWord_1492999) baseStart_1492999 baseEnd_1492999 := by
    simpa [prefixWord, tailWord_1492999, baseEnd_1492999] using wordTrace_append hprefix tailTrace_1492999
  have hstable : (prefixWord ++ tailWord_1492999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492999).length < 2 ^ (prefixWord ++ tailWord_1492999).sum := by decide
  have hdescent : baseEnd_1492999 < baseStart_1492999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493027 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 3]
def baseStart_1493027 : Nat := 118140960795 + 1493027 * 2 ^ 59
def prefixEnd_1493027 : Nat := 4983230072969 + 3 ^ 40 * 1493027 * 2
def baseEnd_1493027 : Nat := 340729102729082337198311

theorem tailTrace_1493027 : CollatzResearch.WordTrace tailWord_1493027 prefixEnd_1493027 340729102729082337198311 := by
  unfold tailWord_1493027
  simp only [CollatzResearch.WordTrace]
  refine ⟨54455168362025642556021335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36303445574683761704014223 54455168362025642556021335)
  ·
    refine ⟨81682752543038463834032003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54455168362025642556021335 81682752543038463834032003)
    ·
      refine ⟨122524128814557695751048005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81682752543038463834032003 122524128814557695751048005)
      ·
        refine ⟨22973274152729567953321501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122524128814557695751048005 22973274152729567953321501)
        ·
          refine ⟨8614977807273587982495563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22973274152729567953321501 8614977807273587982495563)
          ·
            refine ⟨12922466710910381973743345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614977807273587982495563 12922466710910381973743345)
            ·
              refine ⟨9691850033182786480307509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922466710910381973743345 9691850033182786480307509)
              ·
                refine ⟨908610940610886232528829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9691850033182786480307509 908610940610886232528829)
                ·
                  refine ⟨340729102729082337198311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908610940610886232528829 340729102729082337198311)
                  ·
                    rfl

theorem cell21_1493027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 3].length) (baseStart_1493027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493027 prefixEnd_1493027 := by exact prefixLift 1493027
  have htrace : WordTrace (prefixWord ++ tailWord_1493027) baseStart_1493027 baseEnd_1493027 := by
    simpa [prefixWord, tailWord_1493027, baseEnd_1493027] using wordTrace_append hprefix tailTrace_1493027
  have hstable : (prefixWord ++ tailWord_1493027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493027).length < 2 ^ (prefixWord ++ tailWord_1493027).sum := by decide
  have hdescent : baseEnd_1493027 < baseStart_1493027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493041 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_1493041 : Nat := 118140960795 + 1493041 * 2 ^ 59
def prefixEnd_1493041 : Nat := 4983230072969 + 3 ^ 40 * 1493041 * 2
def baseEnd_1493041 : Nat := 340732297719821423964949

theorem tailTrace_1493041 : CollatzResearch.WordTrace tailWord_1493041 prefixEnd_1493041 340732297719821423964949 := by
  unfold tailWord_1493041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54455678983974922947030977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36303785989316615298020651 54455678983974922947030977)
  ·
    refine ⟨40841759237981192210273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54455678983974922947030977 40841759237981192210273233)
    ·
      refine ⟨30631319428485894157704925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40841759237981192210273233 30631319428485894157704925)
      ·
        refine ⟨11486744785682210309139347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30631319428485894157704925 11486744785682210309139347)
        ·
          refine ⟨17230117178523315463709021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486744785682210309139347 17230117178523315463709021)
          ·
            refine ⟨6461293941946243298890883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17230117178523315463709021 6461293941946243298890883)
            ·
              refine ⟨9691940912919364948336325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461293941946243298890883 9691940912919364948336325)
              ·
                refine ⟨1817238921172380927813061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9691940912919364948336325 1817238921172380927813061)
                ·
                  refine ⟨340732297719821423964949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817238921172380927813061 340732297719821423964949)
                  ·
                    rfl

theorem cell21_1493041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_1493041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493041 prefixEnd_1493041 := by exact prefixLift 1493041
  have htrace : WordTrace (prefixWord ++ tailWord_1493041) baseStart_1493041 baseEnd_1493041 := by
    simpa [prefixWord, tailWord_1493041, baseEnd_1493041] using wordTrace_append hprefix tailTrace_1493041
  have hstable : (prefixWord ++ tailWord_1493041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493041).length < 2 ^ (prefixWord ++ tailWord_1493041).sum := by decide
  have hdescent : baseEnd_1493041 < baseStart_1493041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493055 : List Nat := [1, 1, 2, 2, 3, 1, 5, 6]
def baseStart_1493055 : Nat := 118140960795 + 1493055 * 2 ^ 59
def prefixEnd_1493055 : Nat := 4983230072969 + 3 ^ 40 * 1493055 * 2
def baseEnd_1493055 : Nat := 113578497570186836910529

theorem tailTrace_1493055 : CollatzResearch.WordTrace tailWord_1493055 prefixEnd_1493055 113578497570186836910529 := by
  unfold tailWord_1493055
  simp only [CollatzResearch.WordTrace]
  refine ⟨54456189605924203338040619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36304126403949468892027079 54456189605924203338040619)
  ·
    refine ⟨81684284408886305007060929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54456189605924203338040619 81684284408886305007060929)
    ·
      refine ⟨61263213306664728755295697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81684284408886305007060929 61263213306664728755295697)
      ·
        refine ⟨45947409979998546566471773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61263213306664728755295697 45947409979998546566471773)
        ·
          refine ⟨17230278742499454962426915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45947409979998546566471773 17230278742499454962426915)
          ·
            refine ⟨25845418113749182443640373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17230278742499454962426915 25845418113749182443640373)
            ·
              refine ⟨2423007948163985854091285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25845418113749182443640373 2423007948163985854091285)
              ·
                refine ⟨113578497570186836910529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2423007948163985854091285 113578497570186836910529)
                ·
                  rfl

theorem cell21_1493055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_1493055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493055 prefixEnd_1493055 := by exact prefixLift 1493055
  have htrace : WordTrace (prefixWord ++ tailWord_1493055) baseStart_1493055 baseEnd_1493055 := by
    simpa [prefixWord, tailWord_1493055, baseEnd_1493055] using wordTrace_append hprefix tailTrace_1493055
  have hstable : (prefixWord ++ tailWord_1493055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493055).length < 2 ^ (prefixWord ++ tailWord_1493055).sum := by decide
  have hdescent : baseEnd_1493055 < baseStart_1493055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493078 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1493078 : Nat := 118140960795 + 1493078 * 2 ^ 59
def prefixEnd_1493078 : Nat := 4983230072969 + 3 ^ 40 * 1493078 * 2
def baseEnd_1493078 : Nat := 340740741623917581848207

theorem tailTrace_1493078 : CollatzResearch.WordTrace tailWord_1493078 prefixEnd_1493078 340740741623917581848207 := by
  unfold tailWord_1493078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403564280302554891632993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36304685656560585510751925 3403564280302554891632993)
  ·
    refine ⟨2552673210226916168724745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3403564280302554891632993 2552673210226916168724745)
    ·
      refine ⟨1914504907670187126543559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552673210226916168724745 1914504907670187126543559)
      ·
        refine ⟨2871757361505280689815339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914504907670187126543559 2871757361505280689815339)
        ·
          refine ⟨4307636042257921034723009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871757361505280689815339 4307636042257921034723009)
          ·
            refine ⟨3230727031693440776042257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4307636042257921034723009 3230727031693440776042257)
            ·
              refine ⟨2423045273770080582031693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230727031693440776042257 2423045273770080582031693)
              ·
                refine ⟨908641977663780218261885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423045273770080582031693 908641977663780218261885)
                ·
                  refine ⟨340740741623917581848207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908641977663780218261885 340740741623917581848207)
                  ·
                    rfl

theorem cell21_1493078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1493078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493078 prefixEnd_1493078 := by exact prefixLift 1493078
  have htrace : WordTrace (prefixWord ++ tailWord_1493078) baseStart_1493078 baseEnd_1493078 := by
    simpa [prefixWord, tailWord_1493078, baseEnd_1493078] using wordTrace_append hprefix tailTrace_1493078
  have hstable : (prefixWord ++ tailWord_1493078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493078).length < 2 ^ (prefixWord ++ tailWord_1493078).sum := by decide
  have hdescent : baseEnd_1493078 < baseStart_1493078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493103 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 3]
def baseStart_1493103 : Nat := 118140960795 + 1493103 * 2 ^ 59
def prefixEnd_1493103 : Nat := 4983230072969 + 3 ^ 40 * 1493103 * 2
def baseEnd_1493103 : Nat := 340746446964523093931489

theorem tailTrace_1493103 : CollatzResearch.WordTrace tailWord_1493103 prefixEnd_1493103 340746446964523093931489 := by
  unfold tailWord_1493103
  simp only [CollatzResearch.WordTrace]
  refine ⟨54457940309750307535787963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36305293539833538357191975 54457940309750307535787963)
  ·
    refine ⟨81686910464625461303681945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54457940309750307535787963 81686910464625461303681945)
    ·
      refine ⟨61265182848469095977761459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81686910464625461303681945 61265182848469095977761459)
      ·
        refine ⟨91897774272703643966642189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61265182848469095977761459 91897774272703643966642189)
        ·
          refine ⟨34461665352263866487490821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91897774272703643966642189 34461665352263866487490821)
          ·
            refine ⟨6461562253549474966404529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34461665352263866487490821 6461562253549474966404529)
            ·
              refine ⟨4846171690162106224803397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6461562253549474966404529 4846171690162106224803397)
              ·
                refine ⟨908657191905394917150637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4846171690162106224803397 908657191905394917150637)
                ·
                  refine ⟨340746446964523093931489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908657191905394917150637 340746446964523093931489)
                  ·
                    rfl

theorem cell21_1493103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].length) (baseStart_1493103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493103 prefixEnd_1493103 := by exact prefixLift 1493103
  have htrace : WordTrace (prefixWord ++ tailWord_1493103) baseStart_1493103 baseEnd_1493103 := by
    simpa [prefixWord, tailWord_1493103, baseEnd_1493103] using wordTrace_append hprefix tailTrace_1493103
  have hstable : (prefixWord ++ tailWord_1493103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493103).length < 2 ^ (prefixWord ++ tailWord_1493103).sum := by decide
  have hdescent : baseEnd_1493103 < baseStart_1493103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493145 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1493145 : Nat := 118140960795 + 1493145 * 2 ^ 59
def prefixEnd_1493145 : Nat := 4983230072969 + 3 ^ 40 * 1493145 * 2
def baseEnd_1493145 : Nat := 340756031936740354231403

theorem tailTrace_1493145 : CollatzResearch.WordTrace tailWord_1493145 prefixEnd_1493145 340756031936740354231403 := by
  unfold tailWord_1493145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54459472175598148708816889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36306314783732099139211259 54459472175598148708816889)
  ·
    refine ⟨40844604131698611531612667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54459472175598148708816889 40844604131698611531612667)
    ·
      refine ⟨61266906197547917297419001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40844604131698611531612667 61266906197547917297419001)
      ·
        refine ⟨45950179648160937973064251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61266906197547917297419001 45950179648160937973064251)
        ·
          refine ⟨68925269472241406959596377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45950179648160937973064251 68925269472241406959596377)
          ·
            refine ⟨51693952104181055219697283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68925269472241406959596377 51693952104181055219697283)
            ·
              refine ⟨77540928156271582829545925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51693952104181055219697283 77540928156271582829545925)
              ·
                refine ⟨14538924029300921780539861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77540928156271582829545925 14538924029300921780539861)
                ·
                  refine ⟨340756031936740354231403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14538924029300921780539861 340756031936740354231403)
                  ·
                    rfl

theorem cell21_1493145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1493145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493145 prefixEnd_1493145 := by exact prefixLift 1493145
  have htrace : WordTrace (prefixWord ++ tailWord_1493145) baseStart_1493145 baseEnd_1493145 := by
    simpa [prefixWord, tailWord_1493145, baseEnd_1493145] using wordTrace_append hprefix tailTrace_1493145
  have hstable : (prefixWord ++ tailWord_1493145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493145).length < 2 ^ (prefixWord ++ tailWord_1493145).sum := by decide
  have hdescent : baseEnd_1493145 < baseStart_1493145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493213 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1493213 : Nat := 118140960795 + 1493213 * 2 ^ 59
def prefixEnd_1493213 : Nat := 4983230072969 + 3 ^ 40 * 1493213 * 2
def baseEnd_1493213 : Nat := 340771550463187347097931

theorem tailTrace_1493213 : CollatzResearch.WordTrace tailWord_1493213 prefixEnd_1493213 340771550463187347097931 := by
  unfold tailWord_1493213
  simp only [CollatzResearch.WordTrace]
  refine ⟨54461952339351796322292293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36307968226234530881528195 54461952339351796322292293)
  ·
    refine ⟨10211616063628461810429805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54461952339351796322292293 10211616063628461810429805)
    ·
      refine ⟨3829356023860673178911177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10211616063628461810429805 3829356023860673178911177)
      ·
        refine ⟨2872017017895504884183383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3829356023860673178911177 2872017017895504884183383)
        ·
          refine ⟨4308025526843257326275075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872017017895504884183383 4308025526843257326275075)
          ·
            refine ⟨6462038290264885989412613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308025526843257326275075 6462038290264885989412613)
            ·
              refine ⟨1211632179424666123014865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6462038290264885989412613 1211632179424666123014865)
              ·
                refine ⟨908724134568499592261149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211632179424666123014865 908724134568499592261149)
                ·
                  refine ⟨340771550463187347097931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908724134568499592261149 340771550463187347097931)
                  ·
                    rfl

theorem cell21_1493213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1493213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493213 prefixEnd_1493213 := by exact prefixLift 1493213
  have htrace : WordTrace (prefixWord ++ tailWord_1493213) baseStart_1493213 baseEnd_1493213 := by
    simpa [prefixWord, tailWord_1493213, baseEnd_1493213] using wordTrace_append hprefix tailTrace_1493213
  have hstable : (prefixWord ++ tailWord_1493213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493213).length < 2 ^ (prefixWord ++ tailWord_1493213).sum := by decide
  have hdescent : baseEnd_1493213 < baseStart_1493213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493224 : List Nat := [2, 1, 4, 1, 2, 4, 1, 6]
def baseStart_1493224 : Nat := 118140960795 + 1493224 * 2 ^ 59
def prefixEnd_1493224 : Nat := 4983230072969 + 3 ^ 40 * 1493224 * 2
def baseEnd_1493224 : Nat := 113591353604351257471525

theorem tailTrace_1493224 : CollatzResearch.WordTrace tailWord_1493224 prefixEnd_1493224 113591353604351257471525 := by
  unfold tailWord_1493224
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231176771155972600471363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36308235694874630133961817 27231176771155972600471363)
  ·
    refine ⟨40846765156733958900707045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27231176771155972600471363 40846765156733958900707045)
    ·
      refine ⟨7658768466887617293882571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40846765156733958900707045 7658768466887617293882571)
      ·
        refine ⟨11488152700331425940823857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658768466887617293882571 11488152700331425940823857)
        ·
          refine ⟨8616114525248569455617893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11488152700331425940823857 8616114525248569455617893)
          ·
            refine ⟨1615521473484106772928355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8616114525248569455617893 1615521473484106772928355)
            ·
              refine ⟨2423282210226160159392533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615521473484106772928355 2423282210226160159392533)
              ·
                refine ⟨113591353604351257471525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2423282210226160159392533 113591353604351257471525)
                ·
                  rfl

theorem cell21_1493224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_1493224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493224 prefixEnd_1493224 := by exact prefixLift 1493224
  have htrace : WordTrace (prefixWord ++ tailWord_1493224) baseStart_1493224 baseEnd_1493224 := by
    simpa [prefixWord, tailWord_1493224, baseEnd_1493224] using wordTrace_append hprefix tailTrace_1493224
  have hstable : (prefixWord ++ tailWord_1493224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493224).length < 2 ^ (prefixWord ++ tailWord_1493224).sum := by decide
  have hdescent : baseEnd_1493224 < baseStart_1493224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493238 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1493238 : Nat := 118140960795 + 1493238 * 2 ^ 59
def prefixEnd_1493238 : Nat := 4983230072969 + 3 ^ 40 * 1493238 * 2
def baseEnd_1493238 : Nat := 340777255803792859181213

theorem tailTrace_1493238 : CollatzResearch.WordTrace tailWord_1493238 prefixEnd_1493238 340777255803792859181213 := by
  unfold tailWord_1493238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403929010266326599497023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36308576109507483727968245 3403929010266326599497023)
  ·
    refine ⟨5105893515399489899245535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403929010266326599497023 5105893515399489899245535)
    ·
      refine ⟨7658840273099234848868303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105893515399489899245535 7658840273099234848868303)
      ·
        refine ⟨11488260409648852273302455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658840273099234848868303 11488260409648852273302455)
        ·
          refine ⟨17232390614473278409953683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11488260409648852273302455 17232390614473278409953683)
          ·
            refine ⟨25848585921709917614930525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17232390614473278409953683 25848585921709917614930525)
            ·
              refine ⟨9693219720641219105598947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25848585921709917614930525 9693219720641219105598947)
              ·
                refine ⟨14539829580961828658398421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693219720641219105598947 14539829580961828658398421)
                ·
                  refine ⟨340777255803792859181213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14539829580961828658398421 340777255803792859181213)
                  ·
                    rfl

theorem cell21_1493238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1493238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493238 prefixEnd_1493238 := by exact prefixLift 1493238
  have htrace : WordTrace (prefixWord ++ tailWord_1493238) baseStart_1493238 baseEnd_1493238 := by
    simpa [prefixWord, tailWord_1493238, baseEnd_1493238] using wordTrace_append hprefix tailTrace_1493238
  have hstable : (prefixWord ++ tailWord_1493238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493238).length < 2 ^ (prefixWord ++ tailWord_1493238).sum := by decide
  have hdescent : baseEnd_1493238 < baseStart_1493238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493269 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1493269 : Nat := 118140960795 + 1493269 * 2 ^ 59
def prefixEnd_1493269 : Nat := 4983230072969 + 3 ^ 40 * 1493269 * 2
def baseEnd_1493269 : Nat := 340784330426143694164483

theorem tailTrace_1493269 : CollatzResearch.WordTrace tailWord_1493269 prefixEnd_1493269 340784330426143694164483 := by
  unfold tailWord_1493269
  simp only [CollatzResearch.WordTrace]
  refine ⟨54463994827148917886330861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36309329884765945257553907 54463994827148917886330861)
  ·
    refine ⟨20423998060180844207374073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54463994827148917886330861 20423998060180844207374073)
    ·
      refine ⟨15317998545135633155530555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20423998060180844207374073 15317998545135633155530555)
      ·
        refine ⟨22976997817703449733295833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15317998545135633155530555 22976997817703449733295833)
        ·
          refine ⟨17232748363277587299971875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22976997817703449733295833 17232748363277587299971875)
          ·
            refine ⟨25849122544916380949957813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17232748363277587299971875 25849122544916380949957813)
            ·
              refine ⟨2423355238585910714058545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25849122544916380949957813 2423355238585910714058545)
              ·
                refine ⟨1817516428939433035543909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423355238585910714058545 1817516428939433035543909)
                ·
                  refine ⟨340784330426143694164483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817516428939433035543909 340784330426143694164483)
                  ·
                    rfl

theorem cell21_1493269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1493269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493269 prefixEnd_1493269 := by exact prefixLift 1493269
  have htrace : WordTrace (prefixWord ++ tailWord_1493269) baseStart_1493269 baseEnd_1493269 := by
    simpa [prefixWord, tailWord_1493269, baseEnd_1493269] using wordTrace_append hprefix tailTrace_1493269
  have hstable : (prefixWord ++ tailWord_1493269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493269).length < 2 ^ (prefixWord ++ tailWord_1493269).sum := by decide
  have hdescent : baseEnd_1493269 < baseStart_1493269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493300 : List Nat := [2, 5, 1, 1, 1, 3, 1, 7]
def baseStart_1493300 : Nat := 118140960795 + 1493300 * 2 ^ 59
def prefixEnd_1493300 : Nat := 4983230072969 + 3 ^ 40 * 1493300 * 2
def baseEnd_1493300 : Nat := 113597135016164843049251

theorem tailTrace_1493300 : CollatzResearch.WordTrace tailWord_1493300 prefixEnd_1493300 113597135016164843049251 := by
  unfold tailWord_1493300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27232562745018305090354677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36310083660024406787139569 27232562745018305090354677)
  ·
    refine ⟨2553052757345466102220751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27232562745018305090354677 2553052757345466102220751)
    ·
      refine ⟨3829579136018199153331127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553052757345466102220751 3829579136018199153331127)
      ·
        refine ⟨5744368704027298729996691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829579136018199153331127 5744368704027298729996691)
        ·
          refine ⟨8616553056040948094995037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744368704027298729996691 8616553056040948094995037)
          ·
            refine ⟨3231207396015355535623139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8616553056040948094995037 3231207396015355535623139)
            ·
              refine ⟨4846811094023033303434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231207396015355535623139 4846811094023033303434709)
              ·
                refine ⟨113597135016164843049251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4846811094023033303434709 113597135016164843049251)
                ·
                  rfl

theorem cell21_1493300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_1493300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493300 prefixEnd_1493300 := by exact prefixLift 1493300
  have htrace : WordTrace (prefixWord ++ tailWord_1493300) baseStart_1493300 baseEnd_1493300 := by
    simpa [prefixWord, tailWord_1493300, baseEnd_1493300] using wordTrace_append hprefix tailTrace_1493300
  have hstable : (prefixWord ++ tailWord_1493300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493300).length < 2 ^ (prefixWord ++ tailWord_1493300).sum := by decide
  have hdescent : baseEnd_1493300 < baseStart_1493300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493328 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1493328 : Nat := 118140960795 + 1493328 * 2 ^ 59
def prefixEnd_1493328 : Nat := 4983230072969 + 3 ^ 40 * 1493328 * 2
def baseEnd_1493328 : Nat := 340797795029972702681029

theorem tailTrace_1493328 : CollatzResearch.WordTrace tailWord_1493328 prefixEnd_1493328 340797795029972702681029 := by
  unfold tailWord_1493328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27233073366967585481364319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36310764489290113975152425 27233073366967585481364319)
  ·
    refine ⟨40849610050451378222046479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27233073366967585481364319 40849610050451378222046479)
    ·
      refine ⟨61274415075677067333069719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40849610050451378222046479 61274415075677067333069719)
      ·
        refine ⟨91911622613515600999604579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61274415075677067333069719 91911622613515600999604579)
        ·
          refine ⟨137867433920273401499406869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91911622613515600999604579 137867433920273401499406869)
          ·
            refine ⟨6462535965012815695284697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137867433920273401499406869 6462535965012815695284697)
            ·
              refine ⟨4846901973759611771463523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462535965012815695284697 4846901973759611771463523)
              ·
                refine ⟨7270352960639417657195285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846901973759611771463523 7270352960639417657195285)
                ·
                  refine ⟨340797795029972702681029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7270352960639417657195285 340797795029972702681029)
                  ·
                    rfl

theorem cell21_1493328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1493328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493328 prefixEnd_1493328 := by exact prefixLift 1493328
  have htrace : WordTrace (prefixWord ++ tailWord_1493328) baseStart_1493328 baseEnd_1493328 := by
    simpa [prefixWord, tailWord_1493328, baseEnd_1493328] using wordTrace_append hprefix tailTrace_1493328
  have hstable : (prefixWord ++ tailWord_1493328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493328).length < 2 ^ (prefixWord ++ tailWord_1493328).sum := by decide
  have hdescent : baseEnd_1493328 < baseStart_1493328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493441 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 5]
def baseStart_1493441 : Nat := 118140960795 + 1493441 * 2 ^ 59
def prefixEnd_1493441 : Nat := 4983230072969 + 3 ^ 40 * 1493441 * 2
def baseEnd_1493441 : Nat := 340823583169509617297465

theorem tailTrace_1493441 : CollatzResearch.WordTrace tailWord_1493441 prefixEnd_1493441 340823583169509617297465 := by
  unfold tailWord_1493441
  simp only [CollatzResearch.WordTrace]
  refine ⟨54470268182525791261592177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36313512121683860841061451 54470268182525791261592177)
  ·
    refine ⟨40852701136894343446194133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54470268182525791261592177 40852701136894343446194133)
    ·
      refine ⟨957485182895961174520175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40852701136894343446194133 957485182895961174520175)
      ·
        refine ⟨1436227774343941761780263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957485182895961174520175 1436227774343941761780263)
        ·
          refine ⟨2154341661515912642670395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436227774343941761780263 2154341661515912642670395)
          ·
            refine ⟨3231512492273868964005593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154341661515912642670395 3231512492273868964005593)
            ·
              refine ⟨2423634369205401723004195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231512492273868964005593 2423634369205401723004195)
              ·
                refine ⟨3635451553808102584506293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423634369205401723004195 3635451553808102584506293)
                ·
                  refine ⟨340823583169509617297465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635451553808102584506293 340823583169509617297465)
                  ·
                    rfl

theorem cell21_1493441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_1493441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493441 prefixEnd_1493441 := by exact prefixLift 1493441
  have htrace : WordTrace (prefixWord ++ tailWord_1493441) baseStart_1493441 baseEnd_1493441 := by
    simpa [prefixWord, tailWord_1493441, baseEnd_1493441] using wordTrace_append hprefix tailTrace_1493441
  have hstable : (prefixWord ++ tailWord_1493441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493441).length < 2 ^ (prefixWord ++ tailWord_1493441).sum := by decide
  have hdescent : baseEnd_1493441 < baseStart_1493441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493449 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_1493449 : Nat := 118140960795 + 1493449 * 2 ^ 59
def prefixEnd_1493449 : Nat := 4983230072969 + 3 ^ 40 * 1493449 * 2
def baseEnd_1493449 : Nat := 340825408878503381164115

theorem tailTrace_1493449 : CollatzResearch.WordTrace tailWord_1493449 prefixEnd_1493449 340825408878503381164115 := by
  unfold tailWord_1493449
  simp only [CollatzResearch.WordTrace]
  refine ⟨54470559966496808627883401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36313706644331205751922267 54470559966496808627883401)
  ·
    refine ⟨40852919974872606470912551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54470559966496808627883401 40852919974872606470912551)
    ·
      refine ⟨61279379962308909706368827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40852919974872606470912551 61279379962308909706368827)
      ·
        refine ⟨91919069943463364559553241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61279379962308909706368827 91919069943463364559553241)
        ·
          refine ⟨68939302457597523419664931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91919069943463364559553241 68939302457597523419664931)
          ·
            refine ⟨103408953686396285129497397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68939302457597523419664931 103408953686396285129497397)
            ·
              refine ⟨9694589408099651730890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103408953686396285129497397 9694589408099651730890381)
              ·
                refine ⟨3635471028037369399083893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9694589408099651730890381 3635471028037369399083893)
                ·
                  refine ⟨340825408878503381164115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635471028037369399083893 340825408878503381164115)
                  ·
                    rfl

theorem cell21_1493449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_1493449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493449 prefixEnd_1493449 := by exact prefixLift 1493449
  have htrace : WordTrace (prefixWord ++ tailWord_1493449) baseStart_1493449 baseEnd_1493449 := by
    simpa [prefixWord, tailWord_1493449, baseEnd_1493449] using wordTrace_append hprefix tailTrace_1493449
  have hstable : (prefixWord ++ tailWord_1493449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493449).length < 2 ^ (prefixWord ++ tailWord_1493449).sum := by decide
  have hdescent : baseEnd_1493449 < baseStart_1493449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493480 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_1493480 : Nat := 118140960795 + 1493480 * 2 ^ 59
def prefixEnd_1493480 : Nat := 4983230072969 + 3 ^ 40 * 1493480 * 2
def baseEnd_1493480 : Nat := 340832483500854216147385

theorem tailTrace_1493480 : CollatzResearch.WordTrace tailWord_1493480 prefixEnd_1493480 340832483500854216147385 := by
  unfold tailWord_1493480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235845314692250461130947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36314460419589667281507929 27235845314692250461130947)
  ·
    refine ⟨40853767972038375691696421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27235845314692250461130947 40853767972038375691696421)
    ·
      refine ⟨7660081494757195442193079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40853767972038375691696421 7660081494757195442193079)
      ·
        refine ⟨11490122242135793163289619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660081494757195442193079 11490122242135793163289619)
        ·
          refine ⟨17235183363203689744934429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490122242135793163289619 17235183363203689744934429)
          ·
            refine ⟨6463193761201383654350411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17235183363203689744934429 6463193761201383654350411)
            ·
              refine ⟨9694790641802075481525617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463193761201383654350411 9694790641802075481525617)
              ·
                refine ⟨7271092981351556611144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9694790641802075481525617 7271092981351556611144213)
                ·
                  refine ⟨340832483500854216147385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7271092981351556611144213 340832483500854216147385)
                  ·
                    rfl

theorem cell21_1493480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_1493480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493480 prefixEnd_1493480 := by exact prefixLift 1493480
  have htrace : WordTrace (prefixWord ++ tailWord_1493480) baseStart_1493480 baseEnd_1493480 := by
    simpa [prefixWord, tailWord_1493480, baseEnd_1493480] using wordTrace_append hprefix tailTrace_1493480
  have hstable : (prefixWord ++ tailWord_1493480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493480).length < 2 ^ (prefixWord ++ tailWord_1493480).sum := by decide
  have hdescent : baseEnd_1493480 < baseStart_1493480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493525 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1493525 : Nat := 118140960795 + 1493525 * 2 ^ 59
def prefixEnd_1493525 : Nat := 4983230072969 + 3 ^ 40 * 1493525 * 2
def baseEnd_1493525 : Nat := 340842753113944137897293

theorem tailTrace_1493525 : CollatzResearch.WordTrace tailWord_1493525 prefixEnd_1493525 340842753113944137897293 := by
  unfold tailWord_1493525
  simp only [CollatzResearch.WordTrace]
  refine ⟨54473331914221473607650029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36315554609480982405100019 54473331914221473607650029)
  ·
    refine ⟨20427499467833052602868761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54473331914221473607650029 20427499467833052602868761)
    ·
      refine ⟨15320624600874789452151571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20427499467833052602868761 15320624600874789452151571)
      ·
        refine ⟨22980936901312184178227357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15320624600874789452151571 22980936901312184178227357)
        ·
          refine ⟨8617851337992069066835259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22980936901312184178227357 8617851337992069066835259)
          ·
            refine ⟨12926777006988103600252889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617851337992069066835259 12926777006988103600252889)
            ·
              refine ⟨9695082755241077700189667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12926777006988103600252889 9695082755241077700189667)
              ·
                refine ⟨14542624132861616550284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695082755241077700189667 14542624132861616550284501)
                ·
                  refine ⟨340842753113944137897293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14542624132861616550284501 340842753113944137897293)
                  ·
                    rfl

theorem cell21_1493525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1493525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493525 prefixEnd_1493525 := by exact prefixLift 1493525
  have htrace : WordTrace (prefixWord ++ tailWord_1493525) baseStart_1493525 baseEnd_1493525 := by
    simpa [prefixWord, tailWord_1493525, baseEnd_1493525] using wordTrace_append hprefix tailTrace_1493525
  have hstable : (prefixWord ++ tailWord_1493525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493525).length < 2 ^ (prefixWord ++ tailWord_1493525).sum := by decide
  have hdescent : baseEnd_1493525 < baseStart_1493525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493652 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1493652 : Nat := 118140960795 + 1493652 * 2 ^ 59
def prefixEnd_1493652 : Nat := 4983230072969 + 3 ^ 40 * 1493652 * 2
def baseEnd_1493652 : Nat := 340871736244220139280367

theorem tailTrace_1493652 : CollatzResearch.WordTrace tailWord_1493652 prefixEnd_1493652 340871736244220139280367 := by
  unfold tailWord_1493652
  simp only [CollatzResearch.WordTrace]
  refine ⟨27238981992380687148761605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36318642656507582865015473 27238981992380687148761605)
  ·
    refine ⟨5107309123571378840392801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27238981992380687148761605 5107309123571378840392801)
    ·
      refine ⟨3830481842678534130294601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5107309123571378840392801 3830481842678534130294601)
      ·
        refine ⟨2872861382008900597720951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3830481842678534130294601 2872861382008900597720951)
        ·
          refine ⟨4309292073013350896581427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872861382008900597720951 4309292073013350896581427)
          ·
            refine ⟨6463938109520026344872141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309292073013350896581427 6463938109520026344872141)
            ·
              refine ⟨2423976791070009879327053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6463938109520026344872141 2423976791070009879327053)
              ·
                refine ⟨908991296651253704747645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423976791070009879327053 908991296651253704747645)
                ·
                  refine ⟨340871736244220139280367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908991296651253704747645 340871736244220139280367)
                  ·
                    rfl

theorem cell21_1493652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1493652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493652 prefixEnd_1493652 := by exact prefixLift 1493652
  have htrace : WordTrace (prefixWord ++ tailWord_1493652) baseStart_1493652 baseEnd_1493652 := by
    simpa [prefixWord, tailWord_1493652, baseEnd_1493652] using wordTrace_append hprefix tailTrace_1493652
  have hstable : (prefixWord ++ tailWord_1493652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493652).length < 2 ^ (prefixWord ++ tailWord_1493652).sum := by decide
  have hdescent : baseEnd_1493652 < baseStart_1493652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493821 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1493821 : Nat := 118140960795 + 1493821 * 2 ^ 59
def prefixEnd_1493821 : Nat := 4983230072969 + 3 ^ 40 * 1493821 * 2
def baseEnd_1493821 : Nat := 340910304346713400963355

theorem tailTrace_1493821 : CollatzResearch.WordTrace tailWord_1493821 prefixEnd_1493821 340910304346713400963355 := by
  unfold tailWord_1493821
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484127921149116160425317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36322751947432744106950211 54484127921149116160425317)
  ·
    refine ⟨10215773985215459280079747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54484127921149116160425317 10215773985215459280079747)
    ·
      refine ⟨15323660977823188920119621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215773985215459280079747 15323660977823188920119621)
      ·
        refine ⟨2873186433341847922522429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15323660977823188920119621 2873186433341847922522429)
        ·
          refine ⟨1077444912503192970945911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2873186433341847922522429 1077444912503192970945911)
          ·
            refine ⟨1616167368754789456418867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077444912503192970945911 1616167368754789456418867)
            ·
              refine ⟨2424251053132184184628301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616167368754789456418867 2424251053132184184628301)
              ·
                refine ⟨909094144924569069235613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424251053132184184628301 909094144924569069235613)
                ·
                  refine ⟨340910304346713400963355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909094144924569069235613 340910304346713400963355)
                  ·
                    rfl

theorem cell21_1493821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1493821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493821 prefixEnd_1493821 := by exact prefixLift 1493821
  have htrace : WordTrace (prefixWord ++ tailWord_1493821) baseStart_1493821 baseEnd_1493821 := by
    simpa [prefixWord, tailWord_1493821, baseEnd_1493821] using wordTrace_append hprefix tailTrace_1493821
  have hstable : (prefixWord ++ tailWord_1493821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493821).length < 2 ^ (prefixWord ++ tailWord_1493821).sum := by decide
  have hdescent : baseEnd_1493821 < baseStart_1493821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493874 : List Nat := [3, 2, 1, 2, 1, 1, 4, 7]
def baseStart_1493874 : Nat := 118140960795 + 1493874 * 2 ^ 59
def prefixEnd_1493874 : Nat := 4983230072969 + 3 ^ 40 * 1493874 * 2
def baseEnd_1493874 : Nat := 113640799889599028859971

theorem tailTrace_1493874 : CollatzResearch.WordTrace tailWord_1493874 prefixEnd_1493874 113640799889599028859971 := by
  unfold tailWord_1493874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621515247489276553026169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36324040659971404141403117 13621515247489276553026169)
  ·
    refine ⟨10216136435616957414769627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13621515247489276553026169 10216136435616957414769627)
    ·
      refine ⟨15324204653425436122154441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10216136435616957414769627 15324204653425436122154441)
      ·
        refine ⟨11493153490069077091615831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15324204653425436122154441 11493153490069077091615831)
        ·
          refine ⟨17239730235103615637423747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11493153490069077091615831 17239730235103615637423747)
          ·
            refine ⟨25859595352655423456135621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17239730235103615637423747 25859595352655423456135621)
            ·
              refine ⟨4848674128622891898025429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25859595352655423456135621 4848674128622891898025429)
              ·
                refine ⟨113640799889599028859971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4848674128622891898025429 113640799889599028859971)
                ·
                  rfl

theorem cell21_1493874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_1493874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493874 prefixEnd_1493874 := by exact prefixLift 1493874
  have htrace : WordTrace (prefixWord ++ tailWord_1493874) baseStart_1493874 baseEnd_1493874 := by
    simpa [prefixWord, tailWord_1493874, baseEnd_1493874] using wordTrace_append hprefix tailTrace_1493874
  have hstable : (prefixWord ++ tailWord_1493874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493874).length < 2 ^ (prefixWord ++ tailWord_1493874).sum := by decide
  have hdescent : baseEnd_1493874 < baseStart_1493874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493888 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_1493888 : Nat := 118140960795 + 1493888 * 2 ^ 59
def prefixEnd_1493888 : Nat := 4983230072969 + 3 ^ 40 * 1493888 * 2
def baseEnd_1493888 : Nat := 340925594659536173346551

theorem tailTrace_1493888 : CollatzResearch.WordTrace tailWord_1493888 prefixEnd_1493888 340925594659536173346551 := by
  unfold tailWord_1493888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27243285805953193301557159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36324381074604257735409545 27243285805953193301557159)
  ·
    refine ⟨40864928708929789952335739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27243285805953193301557159 40864928708929789952335739)
    ·
      refine ⟨61297393063394684928503609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40864928708929789952335739 61297393063394684928503609)
      ·
        refine ⟨45973044797546013696377707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61297393063394684928503609 45973044797546013696377707)
        ·
          refine ⟨68959567196319020544566561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45973044797546013696377707 68959567196319020544566561)
          ·
            refine ⟨51719675397239265408424921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68959567196319020544566561 51719675397239265408424921)
            ·
              refine ⟨38789756547929449056318691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51719675397239265408424921 38789756547929449056318691)
              ·
                refine ⟨58184634821894173584478037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38789756547929449056318691 58184634821894173584478037)
                ·
                  refine ⟨340925594659536173346551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58184634821894173584478037 340925594659536173346551)
                  ·
                    rfl

theorem cell21_1493888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_1493888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493888 prefixEnd_1493888 := by exact prefixLift 1493888
  have htrace : WordTrace (prefixWord ++ tailWord_1493888) baseStart_1493888 baseEnd_1493888 := by
    simpa [prefixWord, tailWord_1493888, baseEnd_1493888] using wordTrace_append hprefix tailTrace_1493888
  have hstable : (prefixWord ++ tailWord_1493888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493888).length < 2 ^ (prefixWord ++ tailWord_1493888).sum := by decide
  have hdescent : baseEnd_1493888 < baseStart_1493888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493922 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1493922 : Nat := 118140960795 + 1493922 * 2 ^ 59
def prefixEnd_1493922 : Nat := 4983230072969 + 3 ^ 40 * 1493922 * 2
def baseEnd_1493922 : Nat := 340933353922759669779815

theorem tailTrace_1493922 : CollatzResearch.WordTrace tailWord_1493922 prefixEnd_1493922 340933353922759669779815 := by
  unfold tailWord_1493922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621952923445802602463005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36325207795855473606568013 13621952923445802602463005)
  ·
    refine ⟨5108232346292175975923627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13621952923445802602463005 5108232346292175975923627)
    ·
      refine ⟨7662348519438263963885441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108232346292175975923627 7662348519438263963885441)
      ·
        refine ⟨5746761389578697972914081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7662348519438263963885441 5746761389578697972914081)
        ·
          refine ⟨4310071042184023479685561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5746761389578697972914081 4310071042184023479685561)
          ·
            refine ⟨3232553281638017609764171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310071042184023479685561 3232553281638017609764171)
            ·
              refine ⟨4848829922457026414646257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232553281638017609764171 4848829922457026414646257)
              ·
                refine ⟨3636622441842769810984693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848829922457026414646257 3636622441842769810984693)
                ·
                  refine ⟨340933353922759669779815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3636622441842769810984693 340933353922759669779815)
                  ·
                    rfl

theorem cell21_1493922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1493922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493922 prefixEnd_1493922 := by exact prefixLift 1493922
  have htrace : WordTrace (prefixWord ++ tailWord_1493922) baseStart_1493922 baseEnd_1493922 := by
    simpa [prefixWord, tailWord_1493922, baseEnd_1493922] using wordTrace_append hprefix tailTrace_1493922
  have hstable : (prefixWord ++ tailWord_1493922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493922).length < 2 ^ (prefixWord ++ tailWord_1493922).sum := by decide
  have hdescent : baseEnd_1493922 < baseStart_1493922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493950 : List Nat := [4, 2, 1, 1, 1, 2, 10]
def baseStart_1493950 : Nat := 118140960795 + 1493950 * 2 ^ 59
def prefixEnd_1493950 : Nat := 4983230072969 + 3 ^ 40 * 1493950 * 2
def baseEnd_1493950 : Nat := 37882193767137538145899

theorem tailTrace_1493950 : CollatzResearch.WordTrace tailWord_1493950 prefixEnd_1493950 37882193767137538145899 := by
  unfold tailWord_1493950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811104117210221398983913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36325888625121180794580869 6811104117210221398983913)
  ·
    refine ⟨5108328087907666049237935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6811104117210221398983913 5108328087907666049237935)
    ·
      refine ⟨7662492131861499073856903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108328087907666049237935 7662492131861499073856903)
      ·
        refine ⟨11493738197792248610785355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7662492131861499073856903 11493738197792248610785355)
        ·
          refine ⟨17240607296688372916178033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11493738197792248610785355 17240607296688372916178033)
          ·
            refine ⟨12930455472516279687133525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17240607296688372916178033 12930455472516279687133525)
            ·
              refine ⟨37882193767137538145899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12930455472516279687133525 37882193767137538145899)
              ·
                rfl

theorem cell21_1493950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 10].length) (baseStart_1493950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493950 prefixEnd_1493950 := by exact prefixLift 1493950
  have htrace : WordTrace (prefixWord ++ tailWord_1493950) baseStart_1493950 baseEnd_1493950 := by
    simpa [prefixWord, tailWord_1493950, baseEnd_1493950] using wordTrace_append hprefix tailTrace_1493950
  have hstable : (prefixWord ++ tailWord_1493950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493950).length < 2 ^ (prefixWord ++ tailWord_1493950).sum := by decide
  have hdescent : baseEnd_1493950 < baseStart_1493950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493970 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1493970 : Nat := 118140960795 + 1493970 * 2 ^ 59
def prefixEnd_1493970 : Nat := 4983230072969 + 3 ^ 40 * 1493970 * 2
def baseEnd_1493970 : Nat := 340944308176722252979717

theorem tailTrace_1493970 : CollatzResearch.WordTrace tailWord_1493970 prefixEnd_1493970 340944308176722252979717 := by
  unfold tailWord_1493970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13622390599402328651899841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36326374931739543071732909 13622390599402328651899841)
  ·
    refine ⟨10216792949551746488924881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13622390599402328651899841 10216792949551746488924881)
    ·
      refine ⟨7662594712163809866693661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10216792949551746488924881 7662594712163809866693661)
      ·
        refine ⟨2873473017061428700010123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7662594712163809866693661 2873473017061428700010123)
        ·
          refine ⟨4310209525592143050015185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873473017061428700010123 4310209525592143050015185)
          ·
            refine ⟨3232657144194107287511389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310209525592143050015185 3232657144194107287511389)
            ·
              refine ⟨1212246429072790232816771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3232657144194107287511389 1212246429072790232816771)
              ·
                refine ⟨1818369643609185349225157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212246429072790232816771 1818369643609185349225157)
                ·
                  refine ⟨340944308176722252979717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1818369643609185349225157 340944308176722252979717)
                  ·
                    rfl

theorem cell21_1493970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1493970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1493970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1493970 prefixEnd_1493970 := by exact prefixLift 1493970
  have htrace : WordTrace (prefixWord ++ tailWord_1493970) baseStart_1493970 baseEnd_1493970 := by
    simpa [prefixWord, tailWord_1493970, baseEnd_1493970] using wordTrace_append hprefix tailTrace_1493970
  have hstable : (prefixWord ++ tailWord_1493970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493970).length < 2 ^ (prefixWord ++ tailWord_1493970).sum := by decide
  have hdescent : baseEnd_1493970 < baseStart_1493970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494026 : List Nat := [3, 1, 2, 2, 3, 1, 1, 8]
def baseStart_1494026 : Nat := 118140960795 + 1494026 * 2 ^ 59
def prefixEnd_1494026 : Nat := 4983230072969 + 3 ^ 40 * 1494026 * 2
def baseEnd_1494026 : Nat := 113652362713226200015423

theorem tailTrace_1494026 : CollatzResearch.WordTrace tailWord_1494026 prefixEnd_1494026 113652362713226200015423 := by
  unfold tailWord_1494026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13622901221351609042909483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36327736590270957447758621 13622901221351609042909483)
  ·
    refine ⟨20434351832027413564364225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13622901221351609042909483 20434351832027413564364225)
    ·
      refine ⟨15325763874020560173273169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20434351832027413564364225 15325763874020560173273169)
      ·
        refine ⟨11494322905515420129954877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15325763874020560173273169 11494322905515420129954877)
        ·
          refine ⟨4310371089568282548733079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11494322905515420129954877 4310371089568282548733079)
          ·
            refine ⟨6465556634352423823099619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310371089568282548733079 6465556634352423823099619)
            ·
              refine ⟨9698334951528635734649429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465556634352423823099619 9698334951528635734649429)
              ·
                refine ⟨113652362713226200015423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9698334951528635734649429 113652362713226200015423)
                ·
                  rfl

theorem cell21_1494026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_1494026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494026 prefixEnd_1494026 := by exact prefixLift 1494026
  have htrace : WordTrace (prefixWord ++ tailWord_1494026) baseStart_1494026 baseEnd_1494026 := by
    simpa [prefixWord, tailWord_1494026, baseEnd_1494026] using wordTrace_append hprefix tailTrace_1494026
  have hstable : (prefixWord ++ tailWord_1494026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494026).length < 2 ^ (prefixWord ++ tailWord_1494026).sum := by decide
  have hdescent : baseEnd_1494026 < baseStart_1494026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494116 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1494116 : Nat := 118140960795 + 1494116 * 2 ^ 59
def prefixEnd_1494116 : Nat := 4983230072969 + 3 ^ 40 * 1494116 * 2
def baseEnd_1494116 : Nat := 340977627365858443546085

theorem tailTrace_1494116 : CollatzResearch.WordTrace tailWord_1494116 prefixEnd_1494116 340977627365858443546085 := by
  unfold tailWord_1494116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247443727540190771207101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36329924970053587694942801 27247443727540190771207101)
  ·
    refine ⟨10217791397827571539202663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27247443727540190771207101 10217791397827571539202663)
    ·
      refine ⟨15326687096741357308803995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217791397827571539202663 15326687096741357308803995)
      ·
        refine ⟨22990030645112035963205993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15326687096741357308803995 22990030645112035963205993)
        ·
          refine ⟨17242522983834026972404495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22990030645112035963205993 17242522983834026972404495)
          ·
            refine ⟨25863784475751040458606743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17242522983834026972404495 25863784475751040458606743)
            ·
              refine ⟨38795676713626560687910115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25863784475751040458606743 38795676713626560687910115)
              ·
                refine ⟨58193515070439841031865173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38795676713626560687910115 58193515070439841031865173)
                ·
                  refine ⟨340977627365858443546085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58193515070439841031865173 340977627365858443546085)
                  ·
                    rfl

theorem cell21_1494116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1494116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494116 prefixEnd_1494116 := by exact prefixLift 1494116
  have htrace : WordTrace (prefixWord ++ tailWord_1494116) baseStart_1494116 baseEnd_1494116 := by
    simpa [prefixWord, tailWord_1494116, baseEnd_1494116] using wordTrace_append hprefix tailTrace_1494116
  have hstable : (prefixWord ++ tailWord_1494116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494116).length < 2 ^ (prefixWord ++ tailWord_1494116).sum := by decide
  have hdescent : baseEnd_1494116 < baseStart_1494116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494167 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 3]
def baseStart_1494167 : Nat := 118140960795 + 1494167 * 2 ^ 59
def prefixEnd_1494167 : Nat := 4983230072969 + 3 ^ 40 * 1494167 * 2
def baseEnd_1494167 : Nat := 340989266260693688195981

theorem tailTrace_1494167 : CollatzResearch.WordTrace tailWord_1494167 prefixEnd_1494167 340989266260693688195981 := by
  unfold tailWord_1494167
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496747577895617252520755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36331165051930411501680503 54496747577895617252520755)
  ·
    refine ⟨81745121366843425878781133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54496747577895617252520755 81745121366843425878781133)
    ·
      refine ⟨30654420512566284704542925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81745121366843425878781133 30654420512566284704542925)
      ·
        refine ⟨11495407692212356764203597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30654420512566284704542925 11495407692212356764203597)
        ·
          refine ⟨4310777884579633786576349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11495407692212356764203597 4310777884579633786576349)
          ·
            refine ⟨1616541706717362669966131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4310777884579633786576349 1616541706717362669966131)
            ·
              refine ⟨2424812560076044004949197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616541706717362669966131 2424812560076044004949197)
              ·
                refine ⟨909304710028516501855949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424812560076044004949197 909304710028516501855949)
                ·
                  refine ⟨340989266260693688195981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909304710028516501855949 340989266260693688195981)
                  ·
                    rfl

theorem cell21_1494167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].length) (baseStart_1494167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494167 prefixEnd_1494167 := by exact prefixLift 1494167
  have htrace : WordTrace (prefixWord ++ tailWord_1494167) baseStart_1494167 baseEnd_1494167 := by
    simpa [prefixWord, tailWord_1494167, baseEnd_1494167] using wordTrace_append hprefix tailTrace_1494167
  have hstable : (prefixWord ++ tailWord_1494167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494167).length < 2 ^ (prefixWord ++ tailWord_1494167).sum := by decide
  have hdescent : baseEnd_1494167 < baseStart_1494167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494226 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1494226 : Nat := 118140960795 + 1494226 * 2 ^ 59
def prefixEnd_1494226 : Nat := 4983230072969 + 3 ^ 40 * 1494226 * 2
def baseEnd_1494226 : Nat := 341002730864522696712527

theorem tailTrace_1494226 : CollatzResearch.WordTrace tailWord_1494226 prefixEnd_1494226 341002730864522696712527 := by
  unfold tailWord_1494226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624724871170467582229633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36332599656454580219279021 13624724871170467582229633)
  ·
    refine ⟨10218543653377850686672225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13624724871170467582229633 10218543653377850686672225)
    ·
      refine ⟨7663907740033388015004169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10218543653377850686672225 7663907740033388015004169)
      ·
        refine ⟨5747930805025041011253127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663907740033388015004169 5747930805025041011253127)
        ·
          refine ⟨8621896207537561516879691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747930805025041011253127 8621896207537561516879691)
          ·
            refine ⟨12932844311306342275319537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621896207537561516879691 12932844311306342275319537)
            ·
              refine ⟨9699633233479756706489653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12932844311306342275319537 9699633233479756706489653)
              ·
                refine ⟨909340615638727191233405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9699633233479756706489653 909340615638727191233405)
                ·
                  refine ⟨341002730864522696712527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909340615638727191233405 341002730864522696712527)
                  ·
                    rfl

theorem cell21_1494226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1494226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494226 prefixEnd_1494226 := by exact prefixLift 1494226
  have htrace : WordTrace (prefixWord ++ tailWord_1494226) baseStart_1494226 baseEnd_1494226 := by
    simpa [prefixWord, tailWord_1494226, baseEnd_1494226] using wordTrace_append hprefix tailTrace_1494226
  have hstable : (prefixWord ++ tailWord_1494226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494226).length < 2 ^ (prefixWord ++ tailWord_1494226).sum := by decide
  have hdescent : baseEnd_1494226 < baseStart_1494226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494240 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1494240 : Nat := 118140960795 + 1494240 * 2 ^ 59
def prefixEnd_1494240 : Nat := 4983230072969 + 3 ^ 40 * 1494240 * 2
def baseEnd_1494240 : Nat := 341005925855261783479165

theorem tailTrace_1494240 : CollatzResearch.WordTrace tailWord_1494240 prefixEnd_1494240 341005925855261783479165 := by
  unfold tailWord_1494240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249705053315575359964087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36332940071087433813285449 27249705053315575359964087)
  ·
    refine ⟨40874557579973363039946131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27249705053315575359964087 40874557579973363039946131)
    ·
      refine ⟨61311836369960044559919197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40874557579973363039946131 61311836369960044559919197)
      ·
        refine ⟨22991938638735016709969699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61311836369960044559919197 22991938638735016709969699)
        ·
          refine ⟨34487907958102525064954549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22991938638735016709969699 34487907958102525064954549)
          ·
            refine ⟨3233241371072111724839489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34487907958102525064954549 3233241371072111724839489)
            ·
              refine ⟨2424931028304083793629617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233241371072111724839489 2424931028304083793629617)
              ·
                refine ⟨1818698271228062845222213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424931028304083793629617 1818698271228062845222213)
                ·
                  refine ⟨341005925855261783479165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1818698271228062845222213 341005925855261783479165)
                  ·
                    rfl

theorem cell21_1494240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1494240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494240 prefixEnd_1494240 := by exact prefixLift 1494240
  have htrace : WordTrace (prefixWord ++ tailWord_1494240) baseStart_1494240 baseEnd_1494240 := by
    simpa [prefixWord, tailWord_1494240, baseEnd_1494240] using wordTrace_append hprefix tailTrace_1494240
  have hstable : (prefixWord ++ tailWord_1494240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494240).length < 2 ^ (prefixWord ++ tailWord_1494240).sum := by decide
  have hdescent : baseEnd_1494240 < baseStart_1494240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494254 : List Nat := [4, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1494254 : Nat := 118140960795 + 1494254 * 2 ^ 59
def prefixEnd_1494254 : Nat := 4983230072969 + 3 ^ 40 * 1494254 * 2
def baseEnd_1494254 : Nat := 113669706948666956748601

theorem tailTrace_1494254 : CollatzResearch.WordTrace tailWord_1494254 prefixEnd_1494254 113669706948666956748601 := by
  unfold tailWord_1494254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812490091072553888867227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36333280485720287407291877 6812490091072553888867227)
  ·
    refine ⟨10218735136608830833300841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6812490091072553888867227 10218735136608830833300841)
    ·
      refine ⟨7664051352456623124975631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10218735136608830833300841 7664051352456623124975631)
      ·
        refine ⟨11496077028684934687463447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664051352456623124975631 11496077028684934687463447)
        ·
          refine ⟨17244115543027402031195171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496077028684934687463447 17244115543027402031195171)
          ·
            refine ⟨25866173314541103046792757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244115543027402031195171 25866173314541103046792757)
            ·
              refine ⟨2424953748238228410636821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25866173314541103046792757 2424953748238228410636821)
              ·
                refine ⟨113669706948666956748601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2424953748238228410636821 113669706948666956748601)
                ·
                  rfl

theorem cell21_1494254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1494254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494254 prefixEnd_1494254 := by exact prefixLift 1494254
  have htrace : WordTrace (prefixWord ++ tailWord_1494254) baseStart_1494254 baseEnd_1494254 := by
    simpa [prefixWord, tailWord_1494254, baseEnd_1494254] using wordTrace_append hprefix tailTrace_1494254
  have hstable : (prefixWord ++ tailWord_1494254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494254).length < 2 ^ (prefixWord ++ tailWord_1494254).sum := by decide
  have hdescent : baseEnd_1494254 < baseStart_1494254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494260 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1494260 : Nat := 118140960795 + 1494260 * 2 ^ 59
def prefixEnd_1494260 : Nat := 4983230072969 + 3 ^ 40 * 1494260 * 2
def baseEnd_1494260 : Nat := 341010490127746193145791

theorem tailTrace_1494260 : CollatzResearch.WordTrace tailWord_1494260 prefixEnd_1494260 341010490127746193145791 := by
  unfold tailWord_1494260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27250069783279347067828117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36333426377705796090437489 27250069783279347067828117)
  ·
    refine ⟨1277347021091219393804443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27250069783279347067828117 1277347021091219393804443)
    ·
      refine ⟨1916020531636829090706665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277347021091219393804443 1916020531636829090706665)
      ·
        refine ⟨1437015398727621818029999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1916020531636829090706665 1437015398727621818029999)
        ·
          refine ⟨2155523098091432727044999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437015398727621818029999 2155523098091432727044999)
          ·
            refine ⟨3233284647137149090567499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155523098091432727044999 3233284647137149090567499)
            ·
              refine ⟨4849926970705723635851249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233284647137149090567499 4849926970705723635851249)
              ·
                refine ⟨3637445228029292726888437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849926970705723635851249 3637445228029292726888437)
                ·
                  refine ⟨341010490127746193145791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637445228029292726888437 341010490127746193145791)
                  ·
                    rfl

theorem cell21_1494260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1494260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494260 prefixEnd_1494260 := by exact prefixLift 1494260
  have htrace : WordTrace (prefixWord ++ tailWord_1494260) baseStart_1494260 baseEnd_1494260 := by
    simpa [prefixWord, tailWord_1494260, baseEnd_1494260] using wordTrace_append hprefix tailTrace_1494260
  have hstable : (prefixWord ++ tailWord_1494260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494260).length < 2 ^ (prefixWord ++ tailWord_1494260).sum := by decide
  have hdescent : baseEnd_1494260 < baseStart_1494260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494361 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 3]
def baseStart_1494361 : Nat := 118140960795 + 1494361 * 2 ^ 59
def prefixEnd_1494361 : Nat := 4983230072969 + 3 ^ 40 * 1494361 * 2
def baseEnd_1494361 : Nat := 341033539703792461962251

theorem tailTrace_1494361 : CollatzResearch.WordTrace tailWord_1494361 prefixEnd_1494361 341033539703792461962251 := by
  unfold tailWord_1494361
  simp only [CollatzResearch.WordTrace]
  refine ⟨54503823339192788385082937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36335882226128525590055291 54503823339192788385082937)
  ·
    refine ⟨40877867504394591288812203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54503823339192788385082937 40877867504394591288812203)
    ·
      refine ⟨61316801256591886933218305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40877867504394591288812203 61316801256591886933218305)
      ·
        refine ⟨45987600942443915199913729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61316801256591886933218305 45987600942443915199913729)
        ·
          refine ⟨34490700706832936399935297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45987600942443915199913729 34490700706832936399935297)
          ·
            refine ⟨25868025530124702299951473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34490700706832936399935297 25868025530124702299951473)
            ·
              refine ⟨19401019147593526724963605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25868025530124702299951473 19401019147593526724963605)
              ·
                refine ⟨909422772543446565232669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19401019147593526724963605 909422772543446565232669)
                ·
                  refine ⟨341033539703792461962251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909422772543446565232669 341033539703792461962251)
                  ·
                    rfl

theorem cell21_1494361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_1494361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494361 prefixEnd_1494361 := by exact prefixLift 1494361
  have htrace : WordTrace (prefixWord ++ tailWord_1494361) baseStart_1494361 baseEnd_1494361 := by
    simpa [prefixWord, tailWord_1494361, baseEnd_1494361] using wordTrace_append hprefix tailTrace_1494361
  have hstable : (prefixWord ++ tailWord_1494361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494361).length < 2 ^ (prefixWord ++ tailWord_1494361).sum := by decide
  have hdescent : baseEnd_1494361 < baseStart_1494361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494440 : List Nat := [2, 1, 6, 1, 2, 1, 3, 5]
def baseStart_1494440 : Nat := 118140960795 + 1494440 * 2 ^ 59
def prefixEnd_1494440 : Nat := 4983230072969 + 3 ^ 40 * 1494440 * 2
def baseEnd_1494440 : Nat := 113683856193368626715141

theorem tailTrace_1494440 : CollatzResearch.WordTrace tailWord_1494440 prefixEnd_1494440 113683856193368626715141 := by
  unfold tailWord_1494440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27253352352953292438604387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36337803137271056584805849 27253352352953292438604387)
  ·
    refine ⟨40880028529429938657906581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27253352352953292438604387 40880028529429938657906581)
    ·
      refine ⟨1916251337317028374589371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40880028529429938657906581 1916251337317028374589371)
      ·
        refine ⟨2874377005975542561884057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916251337317028374589371 2874377005975542561884057)
        ·
          refine ⟨2155782754481656921413043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874377005975542561884057 2155782754481656921413043)
          ·
            refine ⟨3233674131722485382119565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155782754481656921413043 3233674131722485382119565)
            ·
              refine ⟨1212627799395932018294837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233674131722485382119565 1212627799395932018294837)
              ·
                refine ⟨113683856193368626715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1212627799395932018294837 113683856193368626715141)
                ·
                  rfl

theorem cell21_1494440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_1494440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494440 prefixEnd_1494440 := by exact prefixLift 1494440
  have htrace : WordTrace (prefixWord ++ tailWord_1494440) baseStart_1494440 baseEnd_1494440 := by
    simpa [prefixWord, tailWord_1494440, baseEnd_1494440] using wordTrace_append hprefix tailTrace_1494440
  have hstable : (prefixWord ++ tailWord_1494440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494440).length < 2 ^ (prefixWord ++ tailWord_1494440).sum := by decide
  have hdescent : baseEnd_1494440 < baseStart_1494440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494468 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1494468 : Nat := 118140960795 + 1494468 * 2 ^ 59
def prefixEnd_1494468 : Nat := 4983230072969 + 3 ^ 40 * 1494468 * 2
def baseEnd_1494468 : Nat := 341057958561584053678699

theorem tailTrace_1494468 : CollatzResearch.WordTrace tailWord_1494468 prefixEnd_1494468 341057958561584053678699 := by
  unfold tailWord_1494468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27253862974902572829614029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36338483966536763772818705 27253862974902572829614029)
  ·
    refine ⟨10220198615588464811105261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27253862974902572829614029 10220198615588464811105261)
    ·
      refine ⟨3832574480845674304164473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10220198615588464811105261 3832574480845674304164473)
      ·
        refine ⟨2874430860634255728123355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832574480845674304164473 2874430860634255728123355)
        ·
          refine ⟨4311646290951383592185033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874430860634255728123355 4311646290951383592185033)
          ·
            refine ⟨3233734718213537694138775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311646290951383592185033 3233734718213537694138775)
            ·
              refine ⟨4850602077320306541208163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233734718213537694138775 4850602077320306541208163)
              ·
                refine ⟨7275903115980459811812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850602077320306541208163 7275903115980459811812245)
                ·
                  refine ⟨341057958561584053678699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7275903115980459811812245 341057958561584053678699)
                  ·
                    rfl

theorem cell21_1494468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1494468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494468 prefixEnd_1494468 := by exact prefixLift 1494468
  have htrace : WordTrace (prefixWord ++ tailWord_1494468) baseStart_1494468 baseEnd_1494468 := by
    simpa [prefixWord, tailWord_1494468, baseEnd_1494468] using wordTrace_append hprefix tailTrace_1494468
  have hstable : (prefixWord ++ tailWord_1494468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494468).length < 2 ^ (prefixWord ++ tailWord_1494468).sum := by decide
  have hdescent : baseEnd_1494468 < baseStart_1494468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494499 : List Nat := [1, 1, 1, 6, 2, 3, 2, 5]
def baseStart_1494499 : Nat := 118140960795 + 1494499 * 2 ^ 59
def prefixEnd_1494499 : Nat := 4983230072969 + 3 ^ 40 * 1494499 * 2
def baseEnd_1494499 : Nat := 113688344394644962887323

theorem tailTrace_1494499 : CollatzResearch.WordTrace tailWord_1494499 prefixEnd_1494499 113688344394644962887323 := by
  unfold tailWord_1494499
  simp only [CollatzResearch.WordTrace]
  refine ⟨54508856612692837953606551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36339237741795225302404367 54508856612692837953606551)
  ·
    refine ⟨81763284919039256930409827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54508856612692837953606551 81763284919039256930409827)
    ·
      refine ⟨122644927378558885395614741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81763284919039256930409827 122644927378558885395614741)
      ·
        refine ⟨5748980970869947752919441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122644927378558885395614741 5748980970869947752919441)
        ·
          refine ⟨4311735728152460814689581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5748980970869947752919441 4311735728152460814689581)
          ·
            refine ⟨1616900898057172805508593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4311735728152460814689581 1616900898057172805508593)
            ·
              refine ⟨1212675673542879604131445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616900898057172805508593 1212675673542879604131445)
              ·
                refine ⟨113688344394644962887323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1212675673542879604131445 113688344394644962887323)
                ·
                  rfl

theorem cell21_1494499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].length) (baseStart_1494499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494499 prefixEnd_1494499 := by exact prefixLift 1494499
  have htrace : WordTrace (prefixWord ++ tailWord_1494499) baseStart_1494499 baseEnd_1494499 := by
    simpa [prefixWord, tailWord_1494499, baseEnd_1494499] using wordTrace_append hprefix tailTrace_1494499
  have hstable : (prefixWord ++ tailWord_1494499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494499).length < 2 ^ (prefixWord ++ tailWord_1494499).sum := by decide
  have hdescent : baseEnd_1494499 < baseStart_1494499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494530 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1494530 : Nat := 118140960795 + 1494530 * 2 ^ 59
def prefixEnd_1494530 : Nat := 4983230072969 + 3 ^ 40 * 1494530 * 2
def baseEnd_1494530 : Nat := 341072107806285723645239

theorem tailTrace_1494530 : CollatzResearch.WordTrace tailWord_1494530 prefixEnd_1494530 341072107806285723645239 := by
  unfold tailWord_1494530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627496818895132561996261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36339991517053686831990029 13627496818895132561996261)
  ·
    refine ⟨2555155653542837355374299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13627496818895132561996261 2555155653542837355374299)
    ·
      refine ⟨3832733480314256033061449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2555155653542837355374299 3832733480314256033061449)
      ·
        refine ⟨2874550110235692024796087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832733480314256033061449 2874550110235692024796087)
        ·
          refine ⟨4311825165353538037194131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874550110235692024796087 4311825165353538037194131)
          ·
            refine ⟨6467737748030307055791197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311825165353538037194131 6467737748030307055791197)
            ·
              refine ⟨2425401655511365145921699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6467737748030307055791197 2425401655511365145921699)
              ·
                refine ⟨3638102483267047718882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425401655511365145921699 3638102483267047718882549)
                ·
                  refine ⟨341072107806285723645239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3638102483267047718882549 341072107806285723645239)
                  ·
                    rfl

theorem cell21_1494530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1494530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494530 prefixEnd_1494530 := by exact prefixLift 1494530
  have htrace : WordTrace (prefixWord ++ tailWord_1494530) baseStart_1494530 baseEnd_1494530 := by
    simpa [prefixWord, tailWord_1494530, baseEnd_1494530] using wordTrace_append hprefix tailTrace_1494530
  have hstable : (prefixWord ++ tailWord_1494530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494530).length < 2 ^ (prefixWord ++ tailWord_1494530).sum := by decide
  have hdescent : baseEnd_1494530 < baseStart_1494530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494637 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1494637 : Nat := 118140960795 + 1494637 * 2 ^ 59
def prefixEnd_1494637 : Nat := 4983230072969 + 3 ^ 40 * 1494637 * 2
def baseEnd_1494637 : Nat := 341096526664077315361687

theorem tailTrace_1494637 : CollatzResearch.WordTrace tailWord_1494637 prefixEnd_1494637 341096526664077315361687 := by
  unfold tailWord_1494637
  simp only [CollatzResearch.WordTrace]
  refine ⟨54513889886192887522130165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36342593257461925014753443 54513889886192887522130165)
  ·
    refine ⟨5110677176830583205199703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54513889886192887522130165 5110677176830583205199703)
    ·
      refine ⟨7666015765245874807799555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5110677176830583205199703 7666015765245874807799555)
      ·
        refine ⟨11499023647868812211699333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666015765245874807799555 11499023647868812211699333)
        ·
          refine ⟨2156066933975402289693625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11499023647868812211699333 2156066933975402289693625)
          ·
            refine ⟨1617050200481551717270219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156066933975402289693625 1617050200481551717270219)
            ·
              refine ⟨2425575300722327575905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617050200481551717270219 2425575300722327575905329)
              ·
                refine ⟨1819181475541745681928997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425575300722327575905329 1819181475541745681928997)
                ·
                  refine ⟨341096526664077315361687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819181475541745681928997 341096526664077315361687)
                  ·
                    rfl

theorem cell21_1494637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1494637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494637 prefixEnd_1494637 := by exact prefixLift 1494637
  have htrace : WordTrace (prefixWord ++ tailWord_1494637) baseStart_1494637 baseEnd_1494637 := by
    simpa [prefixWord, tailWord_1494637, baseEnd_1494637] using wordTrace_append hprefix tailTrace_1494637
  have hstable : (prefixWord ++ tailWord_1494637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494637).length < 2 ^ (prefixWord ++ tailWord_1494637).sum := by decide
  have hdescent : baseEnd_1494637 < baseStart_1494637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494724 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1494724 : Nat := 118140960795 + 1494724 * 2 ^ 59
def prefixEnd_1494724 : Nat := 4983230072969 + 3 ^ 40 * 1494724 * 2
def baseEnd_1494724 : Nat := 341116381249384497411509

theorem tailTrace_1494724 : CollatzResearch.WordTrace tailWord_1494724 prefixEnd_1494724 341116381249384497411509 := by
  unfold tailWord_1494724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258531518438850690273613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36344708691251800920364817 27258531518438850690273613)
  ·
    refine ⟨10221949319414569008852605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27258531518438850690273613 10221949319414569008852605)
    ·
      refine ⟨3833230994780463378319727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10221949319414569008852605 3833230994780463378319727)
      ·
        refine ⟨5749846492170695067479591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3833230994780463378319727 5749846492170695067479591)
        ·
          refine ⟨8624769738256042601219387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749846492170695067479591 8624769738256042601219387)
          ·
            refine ⟨12937154607384063901829081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624769738256042601219387 12937154607384063901829081)
            ·
              refine ⟨9702865955538047926371811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12937154607384063901829081 9702865955538047926371811)
              ·
                refine ⟨14554298933307071889557717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702865955538047926371811 14554298933307071889557717)
                ·
                  refine ⟨341116381249384497411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14554298933307071889557717 341116381249384497411509)
                  ·
                    rfl

theorem cell21_1494724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1494724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494724 prefixEnd_1494724 := by exact prefixLift 1494724
  have htrace : WordTrace (prefixWord ++ tailWord_1494724) baseStart_1494724 baseEnd_1494724 := by
    simpa [prefixWord, tailWord_1494724, baseEnd_1494724] using wordTrace_append hprefix tailTrace_1494724
  have hstable : (prefixWord ++ tailWord_1494724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494724).length < 2 ^ (prefixWord ++ tailWord_1494724).sum := by decide
  have hdescent : baseEnd_1494724 < baseStart_1494724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494769 : List Nat := [1, 2, 2, 2, 2, 3, 3, 6]
def baseStart_1494769 : Nat := 118140960795 + 1494769 * 2 ^ 59
def prefixEnd_1494769 : Nat := 4983230072969 + 3 ^ 40 * 1494769 * 2
def baseEnd_1494769 : Nat := 113708883620824806387139

theorem tailTrace_1494769 : CollatzResearch.WordTrace tailWord_1494769 prefixEnd_1494769 113708883620824806387139 := by
  unfold tailWord_1494769
  simp only [CollatzResearch.WordTrace]
  refine ⟨54518704321714674065935361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36345802881143116043956907 54518704321714674065935361)
  ·
    refine ⟨40889028241286005549451521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54518704321714674065935361 40889028241286005549451521)
    ·
      refine ⟨30666771180964504162088641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40889028241286005549451521 30666771180964504162088641)
      ·
        refine ⟨23000078385723378121566481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30666771180964504162088641 23000078385723378121566481)
        ·
          refine ⟨17250058789292533591174861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23000078385723378121566481 17250058789292533591174861)
          ·
            refine ⟨6468772045984700096690573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17250058789292533591174861 6468772045984700096690573)
            ·
              refine ⟨2425789517244262536258965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6468772045984700096690573 2425789517244262536258965)
              ·
                refine ⟨113708883620824806387139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2425789517244262536258965 113708883620824806387139)
                ·
                  rfl

theorem cell21_1494769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_1494769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494769 prefixEnd_1494769 := by exact prefixLift 1494769
  have htrace : WordTrace (prefixWord ++ tailWord_1494769) baseStart_1494769 baseEnd_1494769 := by
    simpa [prefixWord, tailWord_1494769, baseEnd_1494769] using wordTrace_append hprefix tailTrace_1494769
  have hstable : (prefixWord ++ tailWord_1494769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494769).length < 2 ^ (prefixWord ++ tailWord_1494769).sum := by decide
  have hdescent : baseEnd_1494769 < baseStart_1494769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494783 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_1494783 : Nat := 118140960795 + 1494783 * 2 ^ 59
def prefixEnd_1494783 : Nat := 4983230072969 + 3 ^ 40 * 1494783 * 2
def baseEnd_1494783 : Nat := 341129845853213505928055

theorem tailTrace_1494783 : CollatzResearch.WordTrace tailWord_1494783 prefixEnd_1494783 341129845853213505928055 := by
  unfold tailWord_1494783
  simp only [CollatzResearch.WordTrace]
  refine ⟨54519214943663954456945003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346143295775969637963335 54519214943663954456945003)
  ·
    refine ⟨81778822415495931685417505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54519214943663954456945003 81778822415495931685417505)
    ·
      refine ⟨61334116811621948764063129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81778822415495931685417505 61334116811621948764063129)
      ·
        refine ⟨46000587608716461573047347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61334116811621948764063129 46000587608716461573047347)
        ·
          refine ⟨69000881413074692359571021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46000587608716461573047347 69000881413074692359571021)
          ·
            refine ⟨25875330529903009634839133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69000881413074692359571021 25875330529903009634839133)
            ·
              refine ⟨9703248948713628613064675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25875330529903009634839133 9703248948713628613064675)
              ·
                refine ⟨14554873423070442919597013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703248948713628613064675 14554873423070442919597013)
                ·
                  refine ⟨341129845853213505928055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14554873423070442919597013 341129845853213505928055)
                  ·
                    rfl

theorem cell21_1494783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_1494783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494783 prefixEnd_1494783 := by exact prefixLift 1494783
  have htrace : WordTrace (prefixWord ++ tailWord_1494783) baseStart_1494783 baseEnd_1494783 := by
    simpa [prefixWord, tailWord_1494783, baseEnd_1494783] using wordTrace_append hprefix tailTrace_1494783
  have hstable : (prefixWord ++ tailWord_1494783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494783).length < 2 ^ (prefixWord ++ tailWord_1494783).sum := by decide
  have hdescent : baseEnd_1494783 < baseStart_1494783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494817 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 3]
def baseStart_1494817 : Nat := 118140960795 + 1494817 * 2 ^ 59
def prefixEnd_1494817 : Nat := 4983230072969 + 3 ^ 40 * 1494817 * 2
def baseEnd_1494817 : Nat := 341137605116437002361319

theorem tailTrace_1494817 : CollatzResearch.WordTrace tailWord_1494817 prefixEnd_1494817 341137605116437002361319 := by
  unfold tailWord_1494817
  simp only [CollatzResearch.WordTrace]
  refine ⟨54520455025540778263682705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346970017027185509121803 54520455025540778263682705)
  ·
    refine ⟨40890341269155583697762029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54520455025540778263682705 40890341269155583697762029)
    ·
      refine ⟨15333877975933343886660761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40890341269155583697762029 15333877975933343886660761)
      ·
        refine ⟨11500408481950007914995571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15333877975933343886660761 11500408481950007914995571)
        ·
          refine ⟨17250612722925011872493357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11500408481950007914995571 17250612722925011872493357)
          ·
            refine ⟨6468979771096879452185009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17250612722925011872493357 6468979771096879452185009)
            ·
              refine ⟨4851734828322659589138757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6468979771096879452185009 4851734828322659589138757)
              ·
                refine ⟨909700280310498672963517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4851734828322659589138757 909700280310498672963517)
                ·
                  refine ⟨341137605116437002361319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909700280310498672963517 341137605116437002361319)
                  ·
                    rfl

theorem cell21_1494817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_1494817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494817 prefixEnd_1494817 := by exact prefixLift 1494817
  have htrace : WordTrace (prefixWord ++ tailWord_1494817) baseStart_1494817 baseEnd_1494817 := by
    simpa [prefixWord, tailWord_1494817, baseEnd_1494817] using wordTrace_append hprefix tailTrace_1494817
  have hstable : (prefixWord ++ tailWord_1494817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494817).length < 2 ^ (prefixWord ++ tailWord_1494817).sum := by decide
  have hdescent : baseEnd_1494817 < baseStart_1494817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494938 : List Nat := [3, 1, 1, 4, 2, 3, 1, 6]
def baseStart_1494938 : Nat := 118140960795 + 1494938 * 2 ^ 59
def prefixEnd_1494938 : Nat := 4983230072969 + 3 ^ 40 * 1494938 * 2
def baseEnd_1494938 : Nat := 113721739654989226948135

theorem tailTrace_1494938 : CollatzResearch.WordTrace tailWord_1494938 prefixEnd_1494938 113721739654989226948135 := by
  unfold tailWord_1494938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631217064525603982209367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36349912172068277285891645 13631217064525603982209367)
  ·
    refine ⟨20446825596788405973314051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13631217064525603982209367 20446825596788405973314051)
    ·
      refine ⟨30670238395182608959971077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20446825596788405973314051 30670238395182608959971077)
      ·
        refine ⟨5750669699096739179994577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30670238395182608959971077 5750669699096739179994577)
        ·
          refine ⟨4313002274322554384995933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750669699096739179994577 4313002274322554384995933)
          ·
            refine ⟨1617375852870957894373475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4313002274322554384995933 1617375852870957894373475)
            ·
              refine ⟨2426063779306436841560213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617375852870957894373475 2426063779306436841560213)
              ·
                refine ⟨113721739654989226948135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2426063779306436841560213 113721739654989226948135)
                ·
                  rfl

theorem cell21_1494938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_1494938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494938 prefixEnd_1494938 := by exact prefixLift 1494938
  have htrace : WordTrace (prefixWord ++ tailWord_1494938) baseStart_1494938 baseEnd_1494938 := by
    simpa [prefixWord, tailWord_1494938, baseEnd_1494938] using wordTrace_append hprefix tailTrace_1494938
  have hstable : (prefixWord ++ tailWord_1494938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494938).length < 2 ^ (prefixWord ++ tailWord_1494938).sum := by decide
  have hdescent : baseEnd_1494938 < baseStart_1494938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494969 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 3]
def baseStart_1494969 : Nat := 118140960795 + 1494969 * 2 ^ 59
def prefixEnd_1494969 : Nat := 4983230072969 + 3 ^ 40 * 1494969 * 2
def baseEnd_1494969 : Nat := 341172293587318515827675

theorem tailTrace_1494969 : CollatzResearch.WordTrace tailWord_1494969 prefixEnd_1494969 341172293587318515827675 := by
  unfold tailWord_1494969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54525998920990108223215961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36350665947326738815477307 54525998920990108223215961)
  ·
    refine ⟨40894499190742581167411971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54525998920990108223215961 40894499190742581167411971)
    ·
      refine ⟨61341748786113871751117957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40894499190742581167411971 61341748786113871751117957)
      ·
        refine ⟨11501577897396350953334617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61341748786113871751117957 11501577897396350953334617)
        ·
          refine ⟨8626183423047263215000963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11501577897396350953334617 8626183423047263215000963)
          ·
            refine ⟨12939275134570894822501445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8626183423047263215000963 12939275134570894822501445)
            ·
              refine ⟨2426114087732042779219021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12939275134570894822501445 2426114087732042779219021)
              ·
                refine ⟨909792782899516042207133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426114087732042779219021 909792782899516042207133)
                ·
                  refine ⟨341172293587318515827675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909792782899516042207133 341172293587318515827675)
                  ·
                    rfl

theorem cell21_1494969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_1494969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1494969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1494969 prefixEnd_1494969 := by exact prefixLift 1494969
  have htrace : WordTrace (prefixWord ++ tailWord_1494969) baseStart_1494969 baseEnd_1494969 := by
    simpa [prefixWord, tailWord_1494969, baseEnd_1494969] using wordTrace_append hprefix tailTrace_1494969
  have hstable : (prefixWord ++ tailWord_1494969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494969).length < 2 ^ (prefixWord ++ tailWord_1494969).sum := by decide
  have hdescent : baseEnd_1494969 < baseStart_1494969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495059 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 4]
def baseStart_1495059 : Nat := 118140960795 + 1495059 * 2 ^ 59
def prefixEnd_1495059 : Nat := 4983230072969 + 3 ^ 40 * 1495059 * 2
def baseEnd_1495059 : Nat := 341192832813498359327491

theorem tailTrace_1495059 : CollatzResearch.WordTrace tailWord_1495059 prefixEnd_1495059 341192832813498359327491 := by
  unfold tailWord_1495059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54529281490664053593992231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36352854327109369062661487 54529281490664053593992231)
  ·
    refine ⟨81793922235996080390988347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54529281490664053593992231 81793922235996080390988347)
    ·
      refine ⟨122690883353994120586482521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81793922235996080390988347 122690883353994120586482521)
      ·
        refine ⟨92018162515495590439861891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122690883353994120586482521 92018162515495590439861891)
        ·
          refine ⟨138027243773243385659792837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92018162515495590439861891 138027243773243385659792837)
          ·
            refine ⟨25880108207483134811211157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138027243773243385659792837 25880108207483134811211157)
            ·
              refine ⟨1213130072225771944275523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25880108207483134811211157 1213130072225771944275523)
              ·
                refine ⟨1819695108338657916413285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213130072225771944275523 1819695108338657916413285)
                ·
                  refine ⟨341192832813498359327491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819695108338657916413285 341192832813498359327491)
                  ·
                    rfl

theorem cell21_1495059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_1495059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495059 prefixEnd_1495059 := by exact prefixLift 1495059
  have htrace : WordTrace (prefixWord ++ tailWord_1495059) baseStart_1495059 baseEnd_1495059 := by
    simpa [prefixWord, tailWord_1495059, baseEnd_1495059] using wordTrace_append hprefix tailTrace_1495059
  have hstable : (prefixWord ++ tailWord_1495059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495059).length < 2 ^ (prefixWord ++ tailWord_1495059).sum := by decide
  have hdescent : baseEnd_1495059 < baseStart_1495059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495197 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1495197 : Nat := 118140960795 + 1495197 * 2 ^ 59
def prefixEnd_1495197 : Nat := 4983230072969 + 3 ^ 40 * 1495197 * 2
def baseEnd_1495197 : Nat := 341224326293640786027209

theorem tailTrace_1495197 : CollatzResearch.WordTrace tailWord_1495197 prefixEnd_1495197 341224326293640786027209 := by
  unfold tailWord_1495197
  simp only [CollatzResearch.WordTrace]
  refine ⟨54534314764164103162515845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36356209842776068775010563 54534314764164103162515845)
  ·
    refine ⟨10225184018280769342971721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54534314764164103162515845 10225184018280769342971721)
    ·
      refine ⟨7668888013710577007228791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10225184018280769342971721 7668888013710577007228791)
      ·
        refine ⟨11503332020565865510843187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668888013710577007228791 11503332020565865510843187)
        ·
          refine ⟨17254998030848798266264781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11503332020565865510843187 17254998030848798266264781)
          ·
            refine ⟨6470624261568299349849293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17254998030848798266264781 6470624261568299349849293)
            ·
              refine ⟨2426484098088112256193485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6470624261568299349849293 2426484098088112256193485)
              ·
                refine ⟨909931536783042096072557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426484098088112256193485 909931536783042096072557)
                ·
                  refine ⟨341224326293640786027209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909931536783042096072557 341224326293640786027209)
                  ·
                    rfl

theorem cell21_1495197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1495197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495197 prefixEnd_1495197 := by exact prefixLift 1495197
  have htrace : WordTrace (prefixWord ++ tailWord_1495197) baseStart_1495197 baseEnd_1495197 := by
    simpa [prefixWord, tailWord_1495197, baseEnd_1495197] using wordTrace_append hprefix tailTrace_1495197
  have hstable : (prefixWord ++ tailWord_1495197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495197).length < 2 ^ (prefixWord ++ tailWord_1495197).sum := by decide
  have hdescent : baseEnd_1495197 < baseStart_1495197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495220 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1495220 : Nat := 118140960795 + 1495220 * 2 ^ 59
def prefixEnd_1495220 : Nat := 4983230072969 + 3 ^ 40 * 1495220 * 2
def baseEnd_1495220 : Nat := 341229575206997857143829

theorem tailTrace_1495220 : CollatzResearch.WordTrace tailWord_1495220 prefixEnd_1495220 341229575206997857143829 := by
  unfold tailWord_1495220
  simp only [CollatzResearch.WordTrace]
  refine ⟨27267576821540389045301557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36356769095387185393735409 27267576821540389045301557)
  ·
    refine ⟨2556335327019411472997021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27267576821540389045301557 2556335327019411472997021)
    ·
      refine ⟨958625747632279302373883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2556335327019411472997021 958625747632279302373883)
      ·
        refine ⟨1437938621448418953560825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958625747632279302373883 1437938621448418953560825)
        ·
          refine ⟨1078453966086314215170619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437938621448418953560825 1078453966086314215170619)
          ·
            refine ⟨1617680949129471322755929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078453966086314215170619 1617680949129471322755929)
            ·
              refine ⟨1213260711847103492066947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617680949129471322755929 1213260711847103492066947)
              ·
                refine ⟨1819891067770655238100421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213260711847103492066947 1819891067770655238100421)
                ·
                  refine ⟨341229575206997857143829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819891067770655238100421 341229575206997857143829)
                  ·
                    rfl

theorem cell21_1495220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1495220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495220 prefixEnd_1495220 := by exact prefixLift 1495220
  have htrace : WordTrace (prefixWord ++ tailWord_1495220) baseStart_1495220 baseEnd_1495220 := by
    simpa [prefixWord, tailWord_1495220, baseEnd_1495220] using wordTrace_append hprefix tailTrace_1495220
  have hstable : (prefixWord ++ tailWord_1495220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495220).length < 2 ^ (prefixWord ++ tailWord_1495220).sum := by decide
  have hdescent : baseEnd_1495220 < baseStart_1495220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495332 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1495332 : Nat := 118140960795 + 1495332 * 2 ^ 59
def prefixEnd_1495332 : Nat := 4983230072969 + 3 ^ 40 * 1495332 * 2
def baseEnd_1495332 : Nat := 341255135132910551276933

theorem tailTrace_1495332 : CollatzResearch.WordTrace tailWord_1495332 prefixEnd_1495332 341255135132910551276933 := by
  unfold tailWord_1495332
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269619309337510609340125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36359492412450014145786833 27269619309337510609340125)
  ·
    refine ⟨10226107241001566478502547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27269619309337510609340125 10226107241001566478502547)
    ·
      refine ⟨15339160861502349717753821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226107241001566478502547 15339160861502349717753821)
      ·
        refine ⟨5752185323063381144157683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15339160861502349717753821 5752185323063381144157683)
        ·
          refine ⟨8628277984595071716236525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752185323063381144157683 8628277984595071716236525)
          ·
            refine ⟨3235604244223151893588697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8628277984595071716236525 3235604244223151893588697)
            ·
              refine ⟨2426703183167363920191523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235604244223151893588697 2426703183167363920191523)
              ·
                refine ⟨3640054774751045880287285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426703183167363920191523 3640054774751045880287285)
                ·
                  refine ⟨341255135132910551276933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3640054774751045880287285 341255135132910551276933)
                  ·
                    rfl

theorem cell21_1495332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1495332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495332 prefixEnd_1495332 := by exact prefixLift 1495332
  have htrace : WordTrace (prefixWord ++ tailWord_1495332) baseStart_1495332 baseEnd_1495332 := by
    simpa [prefixWord, tailWord_1495332, baseEnd_1495332] using wordTrace_append hprefix tailTrace_1495332
  have hstable : (prefixWord ++ tailWord_1495332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495332).length < 2 ^ (prefixWord ++ tailWord_1495332).sum := by decide
  have hdescent : baseEnd_1495332 < baseStart_1495332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495391 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_1495391 : Nat := 118140960795 + 1495391 * 2 ^ 59
def prefixEnd_1495391 : Nat := 4983230072969 + 3 ^ 40 * 1495391 * 2
def baseEnd_1495391 : Nat := 341268599736739559793479

theorem tailTrace_1495391 : CollatzResearch.WordTrace tailWord_1495391 prefixEnd_1495391 341268599736739559793479 := by
  unfold tailWord_1495391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54541390525461274295078027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36360927016974182863385351 54541390525461274295078027)
  ·
    refine ⟨81812085788191911442617041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54541390525461274295078027 81812085788191911442617041)
    ·
      refine ⟨61359064341143933581962781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81812085788191911442617041 61359064341143933581962781)
      ·
        refine ⟨23009649127928975093236043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61359064341143933581962781 23009649127928975093236043)
        ·
          refine ⟨34514473691893462639854065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23009649127928975093236043 34514473691893462639854065)
          ·
            refine ⟨25885855268920096979890549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34514473691893462639854065 25885855268920096979890549)
            ·
              refine ⟨2426798931461259091864739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25885855268920096979890549 2426798931461259091864739)
              ·
                refine ⟨3640198397191888637797109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426798931461259091864739 3640198397191888637797109)
                ·
                  refine ⟨341268599736739559793479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3640198397191888637797109 341268599736739559793479)
                  ·
                    rfl

theorem cell21_1495391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_1495391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495391 prefixEnd_1495391 := by exact prefixLift 1495391
  have htrace : WordTrace (prefixWord ++ tailWord_1495391) baseStart_1495391 baseEnd_1495391 := by
    simpa [prefixWord, tailWord_1495391, baseEnd_1495391] using wordTrace_append hprefix tailTrace_1495391
  have hstable : (prefixWord ++ tailWord_1495391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495391).length < 2 ^ (prefixWord ++ tailWord_1495391).sum := by decide
  have hdescent : baseEnd_1495391 < baseStart_1495391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495557 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1495557 : Nat := 118140960795 + 1495557 * 2 ^ 59
def prefixEnd_1495557 : Nat := 4983230072969 + 3 ^ 40 * 1495557 * 2
def baseEnd_1495557 : Nat := 341306483198360160026473

theorem tailTrace_1495557 : CollatzResearch.WordTrace tailWord_1495557 prefixEnd_1495557 341306483198360160026473 := by
  unfold tailWord_1495557
  simp only [CollatzResearch.WordTrace]
  refine ⟨54547445042859884645620925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36364963361906589763747283 54547445042859884645620925)
  ·
    refine ⟨20455291891072456742107847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54547445042859884645620925 20455291891072456742107847)
    ·
      refine ⟨30682937836608685113161771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455291891072456742107847 30682937836608685113161771)
      ·
        refine ⟨46024406754913027669742657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30682937836608685113161771 46024406754913027669742657)
        ·
          refine ⟨34518305066184770752306993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46024406754913027669742657 34518305066184770752306993)
          ·
            refine ⟨25888728799638578064230245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34518305066184770752306993 25888728799638578064230245)
            ·
              refine ⟨4854136649932233387043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25888728799638578064230245 4854136649932233387043171)
              ·
                refine ⟨7281204974898350080564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854136649932233387043171 7281204974898350080564757)
                ·
                  refine ⟨341306483198360160026473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7281204974898350080564757 341306483198360160026473)
                  ·
                    rfl

theorem cell21_1495557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1495557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495557 prefixEnd_1495557 := by exact prefixLift 1495557
  have htrace : WordTrace (prefixWord ++ tailWord_1495557) baseStart_1495557 baseEnd_1495557 := by
    simpa [prefixWord, tailWord_1495557, baseEnd_1495557] using wordTrace_append hprefix tailTrace_1495557
  have hstable : (prefixWord ++ tailWord_1495557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495557).length < 2 ^ (prefixWord ++ tailWord_1495557).sum := by decide
  have hdescent : baseEnd_1495557 < baseStart_1495557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495622 : List Nat := [6, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1495622 : Nat := 118140960795 + 1495622 * 2 ^ 59
def prefixEnd_1495622 : Nat := 4983230072969 + 3 ^ 40 * 1495622 * 2
def baseEnd_1495622 : Nat := 113773772361311497147669

theorem tailTrace_1495622 : CollatzResearch.WordTrace tailWord_1495622 prefixEnd_1495622 113773772361311497147669 := by
  unfold tailWord_1495622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704681743363262523335535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36366543858416267164491413 1704681743363262523335535)
  ·
    refine ⟨2557022615044893785003303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704681743363262523335535 2557022615044893785003303)
    ·
      refine ⟨3835533922567340677504955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557022615044893785003303 3835533922567340677504955)
      ·
        refine ⟨5753300883851011016257433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835533922567340677504955 5753300883851011016257433)
        ·
          refine ⟨4314975662888258262193075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5753300883851011016257433 4314975662888258262193075)
          ·
            refine ⟨6472463494332387393289613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314975662888258262193075 6472463494332387393289613)
            ·
              refine ⟨2427173810374645272483605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6472463494332387393289613 2427173810374645272483605)
              ·
                refine ⟨113773772361311497147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2427173810374645272483605 113773772361311497147669)
                ·
                  rfl

theorem cell21_1495622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1495622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495622 prefixEnd_1495622 := by exact prefixLift 1495622
  have htrace : WordTrace (prefixWord ++ tailWord_1495622) baseStart_1495622 baseEnd_1495622 := by
    simpa [prefixWord, tailWord_1495622, baseEnd_1495622] using wordTrace_append hprefix tailTrace_1495622
  have hstable : (prefixWord ++ tailWord_1495622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495622).length < 2 ^ (prefixWord ++ tailWord_1495622).sum := by decide
  have hdescent : baseEnd_1495622 < baseStart_1495622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495647 : List Nat := [1, 1, 2, 3, 1, 1, 1, 11]
def baseStart_1495647 : Nat := 118140960795 + 1495647 * 2 ^ 59
def prefixEnd_1495647 : Nat := 4983230072969 + 3 ^ 40 * 1495647 * 2
def baseEnd_1495647 : Nat := 113775674141513334508763

theorem tailTrace_1495647 : CollatzResearch.WordTrace tailWord_1495647 prefixEnd_1495647 113775674141513334508763 := by
  unfold tailWord_1495647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550727612533830016397195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36367151741689220010931463 54550727612533830016397195)
  ·
    refine ⟨81826091418800745024595793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54550727612533830016397195 81826091418800745024595793)
    ·
      refine ⟨61369568564100558768446845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81826091418800745024595793 61369568564100558768446845)
      ·
        refine ⟨23013588211537709538167567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61369568564100558768446845 23013588211537709538167567)
        ·
          refine ⟨34520382317306564307251351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013588211537709538167567 34520382317306564307251351)
          ·
            refine ⟨51780573475959846460877027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34520382317306564307251351 51780573475959846460877027)
            ·
              refine ⟨77670860213939769691315541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51780573475959846460877027 77670860213939769691315541)
              ·
                refine ⟨113775674141513334508763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77670860213939769691315541 113775674141513334508763)
                ·
                  rfl

theorem cell21_1495647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_1495647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495647 prefixEnd_1495647 := by exact prefixLift 1495647
  have htrace : WordTrace (prefixWord ++ tailWord_1495647) baseStart_1495647 baseEnd_1495647 := by
    simpa [prefixWord, tailWord_1495647, baseEnd_1495647] using wordTrace_append hprefix tailTrace_1495647
  have hstable : (prefixWord ++ tailWord_1495647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495647).length < 2 ^ (prefixWord ++ tailWord_1495647).sum := by decide
  have hdescent : baseEnd_1495647 < baseStart_1495647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495653 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 3]
def baseStart_1495653 : Nat := 118140960795 + 1495653 * 2 ^ 59
def prefixEnd_1495653 : Nat := 4983230072969 + 3 ^ 40 * 1495653 * 2
def baseEnd_1495653 : Nat := 341328391706285326426277

theorem tailTrace_1495653 : CollatzResearch.WordTrace tailWord_1495653 prefixEnd_1495653 341328391706285326426277 := by
  unfold tailWord_1495653
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550946450512093041115613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36367297633674728694077075 54550946450512093041115613)
  ·
    refine ⟨20456604918942034890418355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54550946450512093041115613 20456604918942034890418355)
    ·
      refine ⟨30684907378413052335627533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20456604918942034890418355 30684907378413052335627533)
      ·
        refine ⟨11506840266904894625860325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30684907378413052335627533 11506840266904894625860325)
        ·
          refine ⟨2157532550044667742348811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11506840266904894625860325 2157532550044667742348811)
          ·
            refine ⟨3236298825067001613523217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157532550044667742348811 3236298825067001613523217)
            ·
              refine ⟨2427224118800251210142413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236298825067001613523217 2427224118800251210142413)
              ·
                refine ⟨910209044550094203803405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427224118800251210142413 910209044550094203803405)
                ·
                  refine ⟨341328391706285326426277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910209044550094203803405 341328391706285326426277)
                  ·
                    rfl

theorem cell21_1495653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_1495653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495653 prefixEnd_1495653 := by exact prefixLift 1495653
  have htrace : WordTrace (prefixWord ++ tailWord_1495653) baseStart_1495653 baseEnd_1495653 := by
    simpa [prefixWord, tailWord_1495653, baseEnd_1495653] using wordTrace_append hprefix tailTrace_1495653
  have hstable : (prefixWord ++ tailWord_1495653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495653).length < 2 ^ (prefixWord ++ tailWord_1495653).sum := by decide
  have hdescent : baseEnd_1495653 < baseStart_1495653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495664 : List Nat := [2, 1, 1, 1, 7, 1, 8]
def baseStart_1495664 : Nat := 118140960795 + 1495664 * 2 ^ 59
def prefixEnd_1495664 : Nat := 4983230072969 + 3 ^ 40 * 1495664 * 2
def baseEnd_1495664 : Nat := 37925655784016861304769

theorem tailTrace_1495664 : CollatzResearch.WordTrace tailWord_1495664 prefixEnd_1495664 37925655784016861304769 := by
  unfold tailWord_1495664
  simp only [CollatzResearch.WordTrace]
  refine ⟨27275673826736120959883023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36367565102314827946510697 27275673826736120959883023)
  ·
    refine ⟨40913510740104181439824535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27275673826736120959883023 40913510740104181439824535)
    ·
      refine ⟨61370266110156272159736803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40913510740104181439824535 61370266110156272159736803)
      ·
        refine ⟨92055399165234408239605205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61370266110156272159736803 92055399165234408239605205)
        ·
          refine ⟨2157548417935181443115747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92055399165234408239605205 2157548417935181443115747)
          ·
            refine ⟨3236322626902772164673621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157548417935181443115747 3236322626902772164673621)
            ·
              refine ⟨37925655784016861304769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3236322626902772164673621 37925655784016861304769)
              ·
                rfl

theorem cell21_1495664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 8].length) (baseStart_1495664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495664 prefixEnd_1495664 := by exact prefixLift 1495664
  have htrace : WordTrace (prefixWord ++ tailWord_1495664) baseStart_1495664 baseEnd_1495664 := by
    simpa [prefixWord, tailWord_1495664, baseEnd_1495664] using wordTrace_append hprefix tailTrace_1495664
  have hstable : (prefixWord ++ tailWord_1495664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495664).length < 2 ^ (prefixWord ++ tailWord_1495664).sum := by decide
  have hdescent : baseEnd_1495664 < baseStart_1495664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495698 : List Nat := [3, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1495698 : Nat := 118140960795 + 1495698 * 2 ^ 59
def prefixEnd_1495698 : Nat := 4983230072969 + 3 ^ 40 * 1495698 * 2
def baseEnd_1495698 : Nat := 113779553773125082725395

theorem tailTrace_1495698 : CollatzResearch.WordTrace tailWord_1495698 prefixEnd_1495698 113779553773125082725395 := by
  unfold tailWord_1495698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638146933837266431625937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36368391823566043817669165 13638146933837266431625937)
  ·
    refine ⟨10228610200377949823719453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13638146933837266431625937 10228610200377949823719453)
    ·
      refine ⟨3835728825141731183894795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10228610200377949823719453 3835728825141731183894795)
      ·
        refine ⟨5753593237712596775842193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835728825141731183894795 5753593237712596775842193)
        ·
          refine ⟨4315194928284447581881645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5753593237712596775842193 4315194928284447581881645)
          ·
            refine ⟨1618198098106667843205617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4315194928284447581881645 1618198098106667843205617)
            ·
              refine ⟨1213648573580000882404213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618198098106667843205617 1213648573580000882404213)
              ·
                refine ⟨113779553773125082725395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1213648573580000882404213 113779553773125082725395)
                ·
                  rfl

theorem cell21_1495698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1495698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495698 prefixEnd_1495698 := by exact prefixLift 1495698
  have htrace : WordTrace (prefixWord ++ tailWord_1495698) baseStart_1495698 baseEnd_1495698 := by
    simpa [prefixWord, tailWord_1495698, baseEnd_1495698] using wordTrace_append hprefix tailTrace_1495698
  have hstable : (prefixWord ++ tailWord_1495698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495698).length < 2 ^ (prefixWord ++ tailWord_1495698).sum := by decide
  have hdescent : baseEnd_1495698 < baseStart_1495698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495709 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1495709 : Nat := 118140960795 + 1495709 * 2 ^ 59
def prefixEnd_1495709 : Nat := 4983230072969 + 3 ^ 40 * 1495709 * 2
def baseEnd_1495709 : Nat := 341341171669241673492829

theorem tailTrace_1495709 : CollatzResearch.WordTrace tailWord_1495709 prefixEnd_1495709 341341171669241673492829 := by
  unfold tailWord_1495709
  simp only [CollatzResearch.WordTrace]
  refine ⟨54552988938309214605154181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36368659292206143070102787 54552988938309214605154181)
  ·
    refine ⟨10228685425932977738466409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54552988938309214605154181 10228685425932977738466409)
    ·
      refine ⟨7671514069449733303849807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10228685425932977738466409 7671514069449733303849807)
      ·
        refine ⟨11507271104174599955774711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671514069449733303849807 11507271104174599955774711)
        ·
          refine ⟨17260906656261899933662067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507271104174599955774711 17260906656261899933662067)
          ·
            refine ⟨25891359984392849900493101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260906656261899933662067 25891359984392849900493101)
            ·
              refine ⟨9709259994147318712684913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25891359984392849900493101 9709259994147318712684913)
              ·
                refine ⟨7281944995610489034513685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9709259994147318712684913 7281944995610489034513685)
                ·
                  refine ⟨341341171669241673492829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7281944995610489034513685 341341171669241673492829)
                  ·
                    rfl

theorem cell21_1495709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1495709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495709 prefixEnd_1495709 := by exact prefixLift 1495709
  have htrace : WordTrace (prefixWord ++ tailWord_1495709) baseStart_1495709 baseEnd_1495709 := by
    simpa [prefixWord, tailWord_1495709, baseEnd_1495709] using wordTrace_append hprefix tailTrace_1495709
  have hstable : (prefixWord ++ tailWord_1495709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495709).length < 2 ^ (prefixWord ++ tailWord_1495709).sum := by decide
  have hdescent : baseEnd_1495709 < baseStart_1495709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495729 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_1495729 : Nat := 118140960795 + 1495729 * 2 ^ 59
def prefixEnd_1495729 : Nat := 4983230072969 + 3 ^ 40 * 1495729 * 2
def baseEnd_1495729 : Nat := 341345735941726083159455

theorem tailTrace_1495729 : CollatzResearch.WordTrace tailWord_1495729 prefixEnd_1495729 341345735941726083159455 := by
  unfold tailWord_1495729
  simp only [CollatzResearch.WordTrace]
  refine ⟨54553718398236758020882241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36369145598824505347254827 54553718398236758020882241)
  ·
    refine ⟨40915288798677568515661681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54553718398236758020882241 40915288798677568515661681)
    ·
      refine ⟨30686466599008176386746261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40915288798677568515661681 30686466599008176386746261)
      ·
        refine ⟨1438428121828508268128731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30686466599008176386746261 1438428121828508268128731)
        ·
          refine ⟨2157642182742762402193097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438428121828508268128731 2157642182742762402193097)
          ·
            refine ⟨1618231637057071801644823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157642182742762402193097 1618231637057071801644823)
            ·
              refine ⟨2427347455585607702467235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618231637057071801644823 2427347455585607702467235)
              ·
                refine ⟨3641021183378411553700853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427347455585607702467235 3641021183378411553700853)
                ·
                  refine ⟨341345735941726083159455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641021183378411553700853 341345735941726083159455)
                  ·
                    rfl

theorem cell21_1495729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_1495729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495729 prefixEnd_1495729 := by exact prefixLift 1495729
  have htrace : WordTrace (prefixWord ++ tailWord_1495729) baseStart_1495729 baseEnd_1495729 := by
    simpa [prefixWord, tailWord_1495729, baseEnd_1495729] using wordTrace_append hprefix tailTrace_1495729
  have hstable : (prefixWord ++ tailWord_1495729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495729).length < 2 ^ (prefixWord ++ tailWord_1495729).sum := by decide
  have hdescent : baseEnd_1495729 < baseStart_1495729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495740 : List Nat := [2, 2, 2, 3, 1, 1, 4, 6]
def baseStart_1495740 : Nat := 118140960795 + 1495740 * 2 ^ 59
def prefixEnd_1495740 : Nat := 4983230072969 + 3 ^ 40 * 1495740 * 2
def baseEnd_1495740 : Nat := 113782748763864169492033

theorem tailTrace_1495740 : CollatzResearch.WordTrace tailWord_1495740 prefixEnd_1495740 113782748763864169492033 := by
  unfold tailWord_1495740
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277059800598453449766337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36369413067464604599688449 27277059800598453449766337)
  ·
    refine ⟨20457794850448840087324753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27277059800598453449766337 20457794850448840087324753)
    ·
      refine ⟨15343346137836630065493565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20457794850448840087324753 15343346137836630065493565)
      ·
        refine ⟨5753754801688736274560087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15343346137836630065493565 5753754801688736274560087)
        ·
          refine ⟨8630632202533104411840131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753754801688736274560087 8630632202533104411840131)
          ·
            refine ⟨12945948303799656617760197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630632202533104411840131 12945948303799656617760197)
            ·
              refine ⟨2427365306962435615830037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12945948303799656617760197 2427365306962435615830037)
              ·
                refine ⟨113782748763864169492033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2427365306962435615830037 113782748763864169492033)
                ·
                  rfl

theorem cell21_1495740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_1495740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495740 prefixEnd_1495740 := by exact prefixLift 1495740
  have htrace : WordTrace (prefixWord ++ tailWord_1495740) baseStart_1495740 baseEnd_1495740 := by
    simpa [prefixWord, tailWord_1495740, baseEnd_1495740] using wordTrace_append hprefix tailTrace_1495740
  have hstable : (prefixWord ++ tailWord_1495740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495740).length < 2 ^ (prefixWord ++ tailWord_1495740).sum := by decide
  have hdescent : baseEnd_1495740 < baseStart_1495740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495743 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 4]
def baseStart_1495743 : Nat := 118140960795 + 1495743 * 2 ^ 59
def prefixEnd_1495743 : Nat := 4983230072969 + 3 ^ 40 * 1495743 * 2
def baseEnd_1495743 : Nat := 341348930932465169926093

theorem tailTrace_1495743 : CollatzResearch.WordTrace tailWord_1495743 prefixEnd_1495743 341348930932465169926093 := by
  unfold tailWord_1495743
  simp only [CollatzResearch.WordTrace]
  refine ⟨54554229020186038411891883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36369486013457358941261255 54554229020186038411891883)
  ·
    refine ⟨81831343530279057617837825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54554229020186038411891883 81831343530279057617837825)
    ·
      refine ⟨61373507647709293213378369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81831343530279057617837825 61373507647709293213378369)
      ·
        refine ⟨46030130735781969910033777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61373507647709293213378369 46030130735781969910033777)
        ·
          refine ⟨34522598051836477432525333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46030130735781969910033777 34522598051836477432525333)
          ·
            refine ⟨1618246783679834879649625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34522598051836477432525333 1618246783679834879649625)
            ·
              refine ⟨1213685087759876159737219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618246783679834879649625 1213685087759876159737219)
              ·
                refine ⟨1820527631639814239605829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213685087759876159737219 1820527631639814239605829)
                ·
                  refine ⟨341348930932465169926093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820527631639814239605829 341348930932465169926093)
                  ·
                    rfl

theorem cell21_1495743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_1495743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495743 prefixEnd_1495743 := by exact prefixLift 1495743
  have htrace : WordTrace (prefixWord ++ tailWord_1495743) baseStart_1495743 baseEnd_1495743 := by
    simpa [prefixWord, tailWord_1495743, baseEnd_1495743] using wordTrace_append hprefix tailTrace_1495743
  have hstable : (prefixWord ++ tailWord_1495743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495743).length < 2 ^ (prefixWord ++ tailWord_1495743).sum := by decide
  have hdescent : baseEnd_1495743 < baseStart_1495743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495785 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1495785 : Nat := 118140960795 + 1495785 * 2 ^ 59
def prefixEnd_1495785 : Nat := 4983230072969 + 3 ^ 40 * 1495785 * 2
def baseEnd_1495785 : Nat := 341358515904682430226007

theorem tailTrace_1495785 : CollatzResearch.WordTrace tailWord_1495785 prefixEnd_1495785 341358515904682430226007 := by
  unfold tailWord_1495785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54555760886033879584920809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36370507257355919723280539 54555760886033879584920809)
  ·
    refine ⟨40916820664525409688690607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54555760886033879584920809 40916820664525409688690607)
    ·
      refine ⟨61375230996788114533035911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40916820664525409688690607 61375230996788114533035911)
      ·
        refine ⟨92062846495182171799553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61375230996788114533035911 92062846495182171799553867)
        ·
          refine ⟨138094269742773257699330801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92062846495182171799553867 138094269742773257699330801)
          ·
            refine ⟨103570702307079943274498101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138094269742773257699330801 103570702307079943274498101)
            ·
              refine ⟨9709753341288744681984197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103570702307079943274498101 9709753341288744681984197)
              ·
                refine ⟨1820578751491639627872037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9709753341288744681984197 1820578751491639627872037)
                ·
                  refine ⟨341358515904682430226007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820578751491639627872037 341358515904682430226007)
                  ·
                    rfl

theorem cell21_1495785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1495785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495785 prefixEnd_1495785 := by exact prefixLift 1495785
  have htrace : WordTrace (prefixWord ++ tailWord_1495785) baseStart_1495785 baseEnd_1495785 := by
    simpa [prefixWord, tailWord_1495785, baseEnd_1495785] using wordTrace_append hprefix tailTrace_1495785
  have hstable : (prefixWord ++ tailWord_1495785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495785).length < 2 ^ (prefixWord ++ tailWord_1495785).sum := by decide
  have hdescent : baseEnd_1495785 < baseStart_1495785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495853 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1495853 : Nat := 118140960795 + 1495853 * 2 ^ 59
def prefixEnd_1495853 : Nat := 4983230072969 + 3 ^ 40 * 1495853 * 2
def baseEnd_1495853 : Nat := 341374034431129423092535

theorem tailTrace_1495853 : CollatzResearch.WordTrace tailWord_1495853 prefixEnd_1495853 341374034431129423092535 := by
  unfold tailWord_1495853
  simp only [CollatzResearch.WordTrace]
  refine ⟨54558241049787527198396213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36372160699858351465597475 54558241049787527198396213)
  ·
    refine ⟨5114835098417580674849645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54558241049787527198396213 5114835098417580674849645)
    ·
      refine ⟨1918063161906592753068617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5114835098417580674849645 1918063161906592753068617)
      ·
        refine ⟨1438547371429944564801463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1918063161906592753068617 1438547371429944564801463)
        ·
          refine ⟨2157821057144916847202195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438547371429944564801463 2157821057144916847202195)
          ·
            refine ⟨3236731585717375270803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157821057144916847202195 3236731585717375270803293)
            ·
              refine ⟨1213774344644015726551235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236731585717375270803293 1213774344644015726551235)
              ·
                refine ⟨1820661516966023589826853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213774344644015726551235 1820661516966023589826853)
                ·
                  refine ⟨341374034431129423092535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820661516966023589826853 341374034431129423092535)
                  ·
                    rfl

theorem cell21_1495853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1495853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495853 prefixEnd_1495853 := by exact prefixLift 1495853
  have htrace : WordTrace (prefixWord ++ tailWord_1495853) baseStart_1495853 baseEnd_1495853 := by
    simpa [prefixWord, tailWord_1495853, baseEnd_1495853] using wordTrace_append hprefix tailTrace_1495853
  have hstable : (prefixWord ++ tailWord_1495853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495853).length < 2 ^ (prefixWord ++ tailWord_1495853).sum := by decide
  have hdescent : baseEnd_1495853 < baseStart_1495853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495875 : List Nat := [1, 1, 1, 3, 1, 4, 3, 7]
def baseStart_1495875 : Nat := 118140960795 + 1495875 * 2 ^ 59
def prefixEnd_1495875 : Nat := 4983230072969 + 3 ^ 40 * 1495875 * 2
def baseEnd_1495875 : Nat := 113793018376954091241941

theorem tailTrace_1495875 : CollatzResearch.WordTrace tailWord_1495875 prefixEnd_1495875 113793018376954091241941 := by
  unfold tailWord_1495875
  simp only [CollatzResearch.WordTrace]
  refine ⟨54559043455707824955697079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36372695637138549970464719 54559043455707824955697079)
  ·
    refine ⟨81838565183561737433545619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54559043455707824955697079 81838565183561737433545619)
    ·
      refine ⟨122757847775342606150318429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81838565183561737433545619 122757847775342606150318429)
      ·
        refine ⟨46034192915753477306369411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122757847775342606150318429 46034192915753477306369411)
        ·
          refine ⟨69051289373630215959554117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46034192915753477306369411 69051289373630215959554117)
          ·
            refine ⟨12947116757555665492416397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69051289373630215959554117 12947116757555665492416397)
            ·
              refine ⟨4855168784083374559656149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12947116757555665492416397 4855168784083374559656149)
              ·
                refine ⟨113793018376954091241941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4855168784083374559656149 113793018376954091241941)
                ·
                  rfl

theorem cell21_1495875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_1495875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495875 prefixEnd_1495875 := by exact prefixLift 1495875
  have htrace : WordTrace (prefixWord ++ tailWord_1495875) baseStart_1495875 baseEnd_1495875 := by
    simpa [prefixWord, tailWord_1495875, baseEnd_1495875] using wordTrace_append hprefix tailTrace_1495875
  have hstable : (prefixWord ++ tailWord_1495875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495875).length < 2 ^ (prefixWord ++ tailWord_1495875).sum := by decide
  have hdescent : baseEnd_1495875 < baseStart_1495875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495957 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1495957 : Nat := 118140960795 + 1495957 * 2 ^ 59
def prefixEnd_1495957 : Nat := 4983230072969 + 3 ^ 40 * 1495957 * 2
def baseEnd_1495957 : Nat := 341397768648048353358989

theorem tailTrace_1495957 : CollatzResearch.WordTrace tailWord_1495957 prefixEnd_1495957 341397768648048353358989 := by
  unfold tailWord_1495957
  simp only [CollatzResearch.WordTrace]
  refine ⟨54562034241410752960182125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36374689494273835306788083 54562034241410752960182125)
  ·
    refine ⟨20460762840529032360068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54562034241410752960182125 20460762840529032360068297)
    ·
      refine ⟨15345572130396774270051223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20460762840529032360068297 15345572130396774270051223)
      ·
        refine ⟨23018358195595161405076835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345572130396774270051223 23018358195595161405076835)
        ·
          refine ⟨34527537293392742107615253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23018358195595161405076835 34527537293392742107615253)
          ·
            refine ⟨1618478310627784786294465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34527537293392742107615253 1618478310627784786294465)
            ·
              refine ⟨1213858732970838589720849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618478310627784786294465 1213858732970838589720849)
              ·
                refine ⟨910394049728128942290637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213858732970838589720849 910394049728128942290637)
                ·
                  refine ⟨341397768648048353358989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910394049728128942290637 341397768648048353358989)
                  ·
                    rfl

theorem cell21_1495957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1495957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495957 prefixEnd_1495957 := by exact prefixLift 1495957
  have htrace : WordTrace (prefixWord ++ tailWord_1495957) baseStart_1495957 baseEnd_1495957 := by
    simpa [prefixWord, tailWord_1495957, baseEnd_1495957] using wordTrace_append hprefix tailTrace_1495957
  have hstable : (prefixWord ++ tailWord_1495957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495957).length < 2 ^ (prefixWord ++ tailWord_1495957).sum := by decide
  have hdescent : baseEnd_1495957 < baseStart_1495957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495985 : List Nat := [1, 2, 2, 4, 3, 1, 3, 5]
def baseStart_1495985 : Nat := 118140960795 + 1495985 * 2 ^ 59
def prefixEnd_1495985 : Nat := 4983230072969 + 3 ^ 40 * 1495985 * 2
def baseEnd_1495985 : Nat := 113801386209842175630755

theorem tailTrace_1495985 : CollatzResearch.WordTrace tailWord_1495985 prefixEnd_1495985 113801386209842175630755 := by
  unfold tailWord_1495985
  simp only [CollatzResearch.WordTrace]
  refine ⟨54563055485309313742201409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36375370323539542494800939 54563055485309313742201409)
  ·
    refine ⟨40922291613981985306651057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54563055485309313742201409 40922291613981985306651057)
    ·
      refine ⟨30691718710486488979988293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40922291613981985306651057 30691718710486488979988293)
      ·
        refine ⟨5754697258216216683747805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30691718710486488979988293 5754697258216216683747805)
        ·
          refine ⟨2158011471831081256405427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5754697258216216683747805 2158011471831081256405427)
          ·
            refine ⟨3237017207746621884608141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158011471831081256405427 3237017207746621884608141)
            ·
              refine ⟨1213881452904983206728053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3237017207746621884608141 1213881452904983206728053)
              ·
                refine ⟨113801386209842175630755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1213881452904983206728053 113801386209842175630755)
                ·
                  rfl

theorem cell21_1495985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].length) (baseStart_1495985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1495985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1495985 prefixEnd_1495985 := by exact prefixLift 1495985
  have htrace : WordTrace (prefixWord ++ tailWord_1495985) baseStart_1495985 baseEnd_1495985 := by
    simpa [prefixWord, tailWord_1495985, baseEnd_1495985] using wordTrace_append hprefix tailTrace_1495985
  have hstable : (prefixWord ++ tailWord_1495985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495985).length < 2 ^ (prefixWord ++ tailWord_1495985).sum := by decide
  have hdescent : baseEnd_1495985 < baseStart_1495985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496050 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1496050 : Nat := 118140960795 + 1496050 * 2 ^ 59
def prefixEnd_1496050 : Nat := 4983230072969 + 3 ^ 40 * 1496050 * 2
def baseEnd_1496050 : Nat := 341418992515100858308799

theorem tailTrace_1496050 : CollatzResearch.WordTrace tailWord_1496050 prefixEnd_1496050 341418992515100858308799 := by
  unfold tailWord_1496050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641356557518457460829401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36376950820049219895545069 13641356557518457460829401)
  ·
    refine ⟨10231017418138843095622051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641356557518457460829401 10231017418138843095622051)
    ·
      refine ⟨15346526127208264643433077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10231017418138843095622051 15346526127208264643433077)
      ·
        refine ⟨1438736824425774810321851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15346526127208264643433077 1438736824425774810321851)
        ·
          refine ⟨2158105236638662215482777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438736824425774810321851 2158105236638662215482777)
          ·
            refine ⟨1618578927478996661612083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158105236638662215482777 1618578927478996661612083)
            ·
              refine ⟨2427868391218494992418125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618578927478996661612083 2427868391218494992418125)
              ·
                refine ⟨910450646706935622156797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427868391218494992418125 910450646706935622156797)
                ·
                  refine ⟨341418992515100858308799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910450646706935622156797 341418992515100858308799)
                  ·
                    rfl

theorem cell21_1496050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1496050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496050 prefixEnd_1496050 := by exact prefixLift 1496050
  have htrace : WordTrace (prefixWord ++ tailWord_1496050) baseStart_1496050 baseEnd_1496050 := by
    simpa [prefixWord, tailWord_1496050, baseEnd_1496050] using wordTrace_append hprefix tailTrace_1496050
  have hstable : (prefixWord ++ tailWord_1496050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496050).length < 2 ^ (prefixWord ++ tailWord_1496050).sum := by decide
  have hdescent : baseEnd_1496050 < baseStart_1496050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496075 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_1496075 : Nat := 118140960795 + 1496075 * 2 ^ 59
def prefixEnd_1496075 : Nat := 4983230072969 + 3 ^ 40 * 1496075 * 2
def baseEnd_1496075 : Nat := 341424697855706370392081

theorem tailTrace_1496075 : CollatzResearch.WordTrace tailWord_1496075 prefixEnd_1496075 341424697855706370392081 := by
  unfold tailWord_1496075
  simp only [CollatzResearch.WordTrace]
  refine ⟨54566338054983259112977679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36377558703322172741985119 54566338054983259112977679)
  ·
    refine ⟨81849507082474888669466519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54566338054983259112977679 81849507082474888669466519)
    ·
      refine ⟨122774260623712333004199779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81849507082474888669466519 122774260623712333004199779)
      ·
        refine ⟨184161390935568499506299669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122774260623712333004199779 184161390935568499506299669)
        ·
          refine ⟨8632565200104773414357797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184161390935568499506299669 8632565200104773414357797)
          ·
            refine ⟨1618605975019645015192087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8632565200104773414357797 1618605975019645015192087)
            ·
              refine ⟨2427908962529467522788131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618605975019645015192087 2427908962529467522788131)
              ·
                refine ⟨3641863443794201284182197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427908962529467522788131 3641863443794201284182197)
                ·
                  refine ⟨341424697855706370392081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641863443794201284182197 341424697855706370392081)
                  ·
                    rfl

theorem cell21_1496075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_1496075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496075 prefixEnd_1496075 := by exact prefixLift 1496075
  have htrace : WordTrace (prefixWord ++ tailWord_1496075) baseStart_1496075 baseEnd_1496075 := by
    simpa [prefixWord, tailWord_1496075, baseEnd_1496075] using wordTrace_append hprefix tailTrace_1496075
  have hstable : (prefixWord ++ tailWord_1496075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496075).length < 2 ^ (prefixWord ++ tailWord_1496075).sum := by decide
  have hdescent : baseEnd_1496075 < baseStart_1496075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496126 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1496126 : Nat := 118140960795 + 1496126 * 2 ^ 59
def prefixEnd_1496126 : Nat := 4983230072969 + 3 ^ 40 * 1496126 * 2
def baseEnd_1496126 : Nat := 341436336750541615041977

theorem tailTrace_1496126 : CollatzResearch.WordTrace tailWord_1496126 prefixEnd_1496126 341436336750541615041977 := by
  unfold tailWord_1496126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821024772224811852885529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36378798785198996548722821 6821024772224811852885529)
  ·
    refine ⟨5115768579168608889664147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6821024772224811852885529 5115768579168608889664147)
    ·
      refine ⟨7673652868752913334496221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5115768579168608889664147 7673652868752913334496221)
      ·
        refine ⟨2877619825782342500436083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7673652868752913334496221 2877619825782342500436083)
        ·
          refine ⟨4316429738673513750654125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877619825782342500436083 4316429738673513750654125)
          ·
            refine ⟨1618661152002567656495297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316429738673513750654125 1618661152002567656495297)
            ·
              refine ⟨1213995864001925742371473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618661152002567656495297 1213995864001925742371473)
              ·
                refine ⟨910496898001444306778605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213995864001925742371473 910496898001444306778605)
                ·
                  refine ⟨341436336750541615041977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910496898001444306778605 341436336750541615041977)
                  ·
                    rfl

theorem cell21_1496126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1496126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496126 prefixEnd_1496126 := by exact prefixLift 1496126
  have htrace : WordTrace (prefixWord ++ tailWord_1496126) baseStart_1496126 baseEnd_1496126 := by
    simpa [prefixWord, tailWord_1496126, baseEnd_1496126] using wordTrace_append hprefix tailTrace_1496126
  have hstable : (prefixWord ++ tailWord_1496126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496126).length < 2 ^ (prefixWord ++ tailWord_1496126).sum := by decide
  have hdescent : baseEnd_1496126 < baseStart_1496126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496224 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_1496224 : Nat := 118140960795 + 1496224 * 2 ^ 59
def prefixEnd_1496224 : Nat := 4983230072969 + 3 ^ 40 * 1496224 * 2
def baseEnd_1496224 : Nat := 341458701685715222408443

theorem tailTrace_1496224 : CollatzResearch.WordTrace tailWord_1496224 prefixEnd_1496224 341458701685715222408443 := by
  unfold tailWord_1496224
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285886265721728780075863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36381181687628971706767817 27285886265721728780075863)
  ·
    refine ⟨40928829398582593170113795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27285886265721728780075863 40928829398582593170113795)
    ·
      refine ⟨61393244097873889755170693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40928829398582593170113795 61393244097873889755170693)
      ·
        refine ⟨11511233268351354329094505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61393244097873889755170693 11511233268351354329094505)
        ·
          refine ⟨8633424951263515746820879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11511233268351354329094505 8633424951263515746820879)
          ·
            refine ⟨12950137426895273620231319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8633424951263515746820879 12950137426895273620231319)
            ·
              refine ⟨19425206140342910430346979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12950137426895273620231319 19425206140342910430346979)
              ·
                refine ⟨29137809210514365645520469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19425206140342910430346979 29137809210514365645520469)
                ·
                  refine ⟨341458701685715222408443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29137809210514365645520469 341458701685715222408443)
                  ·
                    rfl

theorem cell21_1496224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_1496224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496224 prefixEnd_1496224 := by exact prefixLift 1496224
  have htrace : WordTrace (prefixWord ++ tailWord_1496224) baseStart_1496224 baseEnd_1496224 := by
    simpa [prefixWord, tailWord_1496224, baseEnd_1496224] using wordTrace_append hprefix tailTrace_1496224
  have hstable : (prefixWord ++ tailWord_1496224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496224).length < 2 ^ (prefixWord ++ tailWord_1496224).sum := by decide
  have hdescent : baseEnd_1496224 < baseStart_1496224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496241 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1496241 : Nat := 118140960795 + 1496241 * 2 ^ 59
def prefixEnd_1496241 : Nat := 4983230072969 + 3 ^ 40 * 1496241 * 2
def baseEnd_1496241 : Nat := 341462581317326970625075

theorem tailTrace_1496241 : CollatzResearch.WordTrace tailWord_1496241 prefixEnd_1496241 341462581317326970625075 := by
  unfold tailWord_1496241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54572392572381869463520577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36381595048254579642347051 54572392572381869463520577)
  ·
    refine ⟨40929294429286402097640433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54572392572381869463520577 40929294429286402097640433)
    ·
      refine ⟨30696970821964801573230325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40929294429286402097640433 30696970821964801573230325)
      ·
        refine ⟨2877841014559200147490343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30696970821964801573230325 2877841014559200147490343)
        ·
          refine ⟨4316761521838800221235515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877841014559200147490343 4316761521838800221235515)
          ·
            refine ⟨6475142282758200331853273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316761521838800221235515 6475142282758200331853273)
            ·
              refine ⟨4856356712068650248889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475142282758200331853273 4856356712068650248889955)
              ·
                refine ⟨7284535068102975373334933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856356712068650248889955 7284535068102975373334933)
                ·
                  refine ⟨341462581317326970625075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7284535068102975373334933 341462581317326970625075)
                  ·
                    rfl

theorem cell21_1496241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1496241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496241 prefixEnd_1496241 := by exact prefixLift 1496241
  have htrace : WordTrace (prefixWord ++ tailWord_1496241) baseStart_1496241 baseEnd_1496241 := by
    simpa [prefixWord, tailWord_1496241, baseEnd_1496241] using wordTrace_append hprefix tailTrace_1496241
  have hstable : (prefixWord ++ tailWord_1496241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496241).length < 2 ^ (prefixWord ++ tailWord_1496241).sum := by decide
  have hdescent : baseEnd_1496241 < baseStart_1496241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496351 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 4]
def baseStart_1496351 : Nat := 118140960795 + 1496351 * 2 ^ 59
def prefixEnd_1496351 : Nat := 4983230072969 + 3 ^ 40 * 1496351 * 2
def baseEnd_1496351 : Nat := 341487684815991223791517

theorem tailTrace_1496351 : CollatzResearch.WordTrace tailWord_1496351 prefixEnd_1496351 341487684815991223791517 := by
  unfold tailWord_1496351
  simp only [CollatzResearch.WordTrace]
  refine ⟨54576404601983358250024907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36384269734655572166683271 54576404601983358250024907)
  ·
    refine ⟨81864606902975037375037361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54576404601983358250024907 81864606902975037375037361)
    ·
      refine ⟨61398455177231278031278021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81864606902975037375037361 61398455177231278031278021)
      ·
        refine ⟨11512210345730864630864629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61398455177231278031278021 11512210345730864630864629)
        ·
          refine ⟨1079269719912268559143559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11512210345730864630864629 1079269719912268559143559)
          ·
            refine ⟨1618904579868402838715339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079269719912268559143559 1618904579868402838715339)
            ·
              refine ⟨2428356869802604258073009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618904579868402838715339 2428356869802604258073009)
              ·
                refine ⟨1821267652351953193554757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428356869802604258073009 1821267652351953193554757)
                ·
                  refine ⟨341487684815991223791517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821267652351953193554757 341487684815991223791517)
                  ·
                    rfl

theorem cell21_1496351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].length) (baseStart_1496351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496351 prefixEnd_1496351 := by exact prefixLift 1496351
  have htrace : WordTrace (prefixWord ++ tailWord_1496351) baseStart_1496351 baseEnd_1496351 := by
    simpa [prefixWord, tailWord_1496351, baseEnd_1496351] using wordTrace_append hprefix tailTrace_1496351
  have hstable : (prefixWord ++ tailWord_1496351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496351).length < 2 ^ (prefixWord ++ tailWord_1496351).sum := by decide
  have hdescent : baseEnd_1496351 < baseStart_1496351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496396 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_1496396 : Nat := 118140960795 + 1496396 * 2 ^ 59
def prefixEnd_1496396 : Nat := 4983230072969 + 3 ^ 40 * 1496396 * 2
def baseEnd_1496396 : Nat := 341497954429081145541425

theorem tailTrace_1496396 : CollatzResearch.WordTrace tailWord_1496396 prefixEnd_1496396 341497954429081145541425 := by
  unfold tailWord_1496396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27289022943410165467706521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36385363924546887290275361 27289022943410165467706521)
  ·
    refine ⟨20466767207557624100779891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27289022943410165467706521 20466767207557624100779891)
    ·
      refine ⟨30700150811336436151169837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20466767207557624100779891 30700150811336436151169837)
      ·
        refine ⟨11512556554251163556688689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30700150811336436151169837 11512556554251163556688689)
        ·
          refine ⟨8634417415688372667516517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11512556554251163556688689 8634417415688372667516517)
          ·
            refine ⟨1618953265441569875159347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8634417415688372667516517 1618953265441569875159347)
            ·
              refine ⟨2428429898162354812739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618953265441569875159347 2428429898162354812739021)
              ·
                refine ⟨910661211810883054777133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428429898162354812739021 910661211810883054777133)
                ·
                  refine ⟨341497954429081145541425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910661211810883054777133 341497954429081145541425)
                  ·
                    rfl

theorem cell21_1496396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_1496396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496396 prefixEnd_1496396 := by exact prefixLift 1496396
  have htrace : WordTrace (prefixWord ++ tailWord_1496396) baseStart_1496396 baseEnd_1496396 := by
    simpa [prefixWord, tailWord_1496396, baseEnd_1496396] using wordTrace_append hprefix tailTrace_1496396
  have hstable : (prefixWord ++ tailWord_1496396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496396).length < 2 ^ (prefixWord ++ tailWord_1496396).sum := by decide
  have hdescent : baseEnd_1496396 < baseStart_1496396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496407 : List Nat := [1, 1, 3, 2, 3, 4, 7]
def baseStart_1496407 : Nat := 118140960795 + 1496407 * 2 ^ 59
def prefixEnd_1496407 : Nat := 4983230072969 + 3 ^ 40 * 1496407 * 2
def baseEnd_1496407 : Nat := 37944496086549730095341

theorem tailTrace_1496407 : CollatzResearch.WordTrace tailWord_1496407 prefixEnd_1496407 37944496086549730095341 := by
  unfold tailWord_1496407
  simp only [CollatzResearch.WordTrace]
  refine ⟨54578447089780479814063475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36385631393186986542708983 54578447089780479814063475)
  ·
    refine ⟨81867670634670719721095213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54578447089780479814063475 81867670634670719721095213)
    ·
      refine ⟨30700376488001519895410705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81867670634670719721095213 30700376488001519895410705)
      ·
        refine ⟨23025282366001139921558029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30700376488001519895410705 23025282366001139921558029)
        ·
          refine ⟨8634480887250427470584261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23025282366001139921558029 8634480887250427470584261)
          ·
            refine ⟨1618965166359455150734549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8634480887250427470584261 1618965166359455150734549)
            ·
              refine ⟨37944496086549730095341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1618965166359455150734549 37944496086549730095341)
              ·
                rfl

theorem cell21_1496407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 7].length) (baseStart_1496407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496407 prefixEnd_1496407 := by exact prefixLift 1496407
  have htrace : WordTrace (prefixWord ++ tailWord_1496407) baseStart_1496407 baseEnd_1496407 := by
    simpa [prefixWord, tailWord_1496407, baseEnd_1496407] using wordTrace_append hprefix tailTrace_1496407
  have hstable : (prefixWord ++ tailWord_1496407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496407).length < 2 ^ (prefixWord ++ tailWord_1496407).sum := by decide
  have hdescent : baseEnd_1496407 < baseStart_1496407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496424 : List Nat := [2, 1, 4, 2, 3, 1, 2, 6]
def baseStart_1496424 : Nat := 118140960795 + 1496424 * 2 ^ 59
def prefixEnd_1496424 : Nat := 4983230072969 + 3 ^ 40 * 1496424 * 2
def baseEnd_1496424 : Nat := 113834781470186439691567

theorem tailTrace_1496424 : CollatzResearch.WordTrace tailWord_1496424 prefixEnd_1496424 113834781470186439691567 := by
  unfold tailWord_1496424
  simp only [CollatzResearch.WordTrace]
  refine ⟨27289533565359445858716163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36386044753812594478288217 27289533565359445858716163)
  ·
    refine ⟨40934300348039168788074245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27289533565359445858716163 40934300348039168788074245)
    ·
      refine ⟨7675181315257344147763921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40934300348039168788074245 7675181315257344147763921)
      ·
        refine ⟨5756385986443008110822941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7675181315257344147763921 5756385986443008110822941)
        ·
          refine ⟨2158644744916128041558603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5756385986443008110822941 2158644744916128041558603)
          ·
            refine ⟨3237967117374192062337905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158644744916128041558603 3237967117374192062337905)
            ·
              refine ⟨2428475338030644046753429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237967117374192062337905 2428475338030644046753429)
              ·
                refine ⟨113834781470186439691567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2428475338030644046753429 113834781470186439691567)
                ·
                  rfl

theorem cell21_1496424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_1496424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496424 prefixEnd_1496424 := by exact prefixLift 1496424
  have htrace : WordTrace (prefixWord ++ tailWord_1496424) baseStart_1496424 baseEnd_1496424 := by
    simpa [prefixWord, tailWord_1496424, baseEnd_1496424] using wordTrace_append hprefix tailTrace_1496424
  have hstable : (prefixWord ++ tailWord_1496424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496424).length < 2 ^ (prefixWord ++ tailWord_1496424).sum := by decide
  have hdescent : baseEnd_1496424 < baseStart_1496424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496472 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_1496472 : Nat := 118140960795 + 1496472 * 2 ^ 59
def prefixEnd_1496472 : Nat := 4983230072969 + 3 ^ 40 * 1496472 * 2
def baseEnd_1496472 : Nat := 341515298664521902274603

theorem tailTrace_1496472 : CollatzResearch.WordTrace tailWord_1496472 prefixEnd_1496472 341515298664521902274603 := by
  unfold tailWord_1496472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27290408917272497957589835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36387211889696663943453113 27290408917272497957589835)
  ·
    refine ⟨40935613375908746936384753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27290408917272497957589835 40935613375908746936384753)
    ·
      refine ⟨30701710031931560202288565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40935613375908746936384753 30701710031931560202288565)
      ·
        refine ⟨2878285315493583768964553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30701710031931560202288565 2878285315493583768964553)
        ·
          refine ⟨2158713986620187826723415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878285315493583768964553 2158713986620187826723415)
          ·
            refine ⟨3238070979930281740085123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158713986620187826723415 3238070979930281740085123)
            ·
              refine ⟨4857106469895422610127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238070979930281740085123 4857106469895422610127685)
              ·
                refine ⟨910707463105391739398941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4857106469895422610127685 910707463105391739398941)
                ·
                  refine ⟨341515298664521902274603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910707463105391739398941 341515298664521902274603)
                  ·
                    rfl

theorem cell21_1496472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_1496472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496472 prefixEnd_1496472 := by exact prefixLift 1496472
  have htrace : WordTrace (prefixWord ++ tailWord_1496472) baseStart_1496472 baseEnd_1496472 := by
    simpa [prefixWord, tailWord_1496472, baseEnd_1496472] using wordTrace_append hprefix tailTrace_1496472
  have hstable : (prefixWord ++ tailWord_1496472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496472).length < 2 ^ (prefixWord ++ tailWord_1496472).sum := by decide
  have hdescent : baseEnd_1496472 < baseStart_1496472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496559 : List Nat := [1, 1, 2, 1, 4, 1, 6, 5]
def baseStart_1496559 : Nat := 118140960795 + 1496559 * 2 ^ 59
def prefixEnd_1496559 : Nat := 4983230072969 + 3 ^ 40 * 1496559 * 2
def baseEnd_1496559 : Nat := 113845051083276361441475

theorem tailTrace_1496559 : CollatzResearch.WordTrace tailWord_1496559 prefixEnd_1496559 113845051083276361441475 := by
  unfold tailWord_1496559
  simp only [CollatzResearch.WordTrace]
  refine ⟨54583990985229809773596731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36389327323486539849064487 54583990985229809773596731)
  ·
    refine ⟨81875986477844714660395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54583990985229809773596731 81875986477844714660395097)
    ·
      refine ⟨61406989858383535995296323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81875986477844714660395097 61406989858383535995296323)
      ·
        refine ⟨92110484787575303992944485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61406989858383535995296323 92110484787575303992944485)
        ·
          refine ⟨17270715897670369498677091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92110484787575303992944485 17270715897670369498677091)
          ·
            refine ⟨25906073846505554248015637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17270715897670369498677091 25906073846505554248015637)
            ·
              refine ⟨1214347211554947855375733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25906073846505554248015637 1214347211554947855375733)
              ·
                refine ⟨113845051083276361441475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1214347211554947855375733 113845051083276361441475)
                ·
                  rfl

theorem cell21_1496559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].length) (baseStart_1496559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496559 prefixEnd_1496559 := by exact prefixLift 1496559
  have htrace : WordTrace (prefixWord ++ tailWord_1496559) baseStart_1496559 baseEnd_1496559 := by
    simpa [prefixWord, tailWord_1496559, baseEnd_1496559] using wordTrace_append hprefix tailTrace_1496559
  have hstable : (prefixWord ++ tailWord_1496559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496559).length < 2 ^ (prefixWord ++ tailWord_1496559).sum := by decide
  have hdescent : baseEnd_1496559 < baseStart_1496559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496565 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1496565 : Nat := 118140960795 + 1496565 * 2 ^ 59
def prefixEnd_1496565 : Nat := 4983230072969 + 3 ^ 40 * 1496565 * 2
def baseEnd_1496565 : Nat := 341536522531574407224413

theorem tailTrace_1496565 : CollatzResearch.WordTrace tailWord_1496565 prefixEnd_1496565 341536522531574407224413 := by
  unfold tailWord_1496565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54584209823208072798315149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36389473215472048532210099 54584209823208072798315149)
  ·
    refine ⟨20469078683703027299368181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54584209823208072798315149 20469078683703027299368181)
    ·
      refine ⟨1918976126597158809315767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20469078683703027299368181 1918976126597158809315767)
      ·
        refine ⟨2878464189895738213973651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918976126597158809315767 2878464189895738213973651)
        ·
          refine ⟨4317696284843607320960477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878464189895738213973651 4317696284843607320960477)
          ·
            refine ⟨1619136106816352745360179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4317696284843607320960477 1619136106816352745360179)
            ·
              refine ⟨2428704160224529118040269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619136106816352745360179 2428704160224529118040269)
              ·
                refine ⟨910764060084198419265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428704160224529118040269 910764060084198419265101)
                ·
                  refine ⟨341536522531574407224413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910764060084198419265101 341536522531574407224413)
                  ·
                    rfl

theorem cell21_1496565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1496565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496565 prefixEnd_1496565 := by exact prefixLift 1496565
  have htrace : WordTrace (prefixWord ++ tailWord_1496565) baseStart_1496565 baseEnd_1496565 := by
    simpa [prefixWord, tailWord_1496565, baseEnd_1496565] using wordTrace_append hprefix tailTrace_1496565
  have hstable : (prefixWord ++ tailWord_1496565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496565).length < 2 ^ (prefixWord ++ tailWord_1496565).sum := by decide
  have hdescent : baseEnd_1496565 < baseStart_1496565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496582 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1496582 : Nat := 118140960795 + 1496582 * 2 ^ 59
def prefixEnd_1496582 : Nat := 4983230072969 + 3 ^ 40 * 1496582 * 2
def baseEnd_1496582 : Nat := 341540402163186155441045

theorem tailTrace_1496582 : CollatzResearch.WordTrace tailWord_1496582 prefixEnd_1496582 341540402163186155441045 := by
  unfold tailWord_1496582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705775933254577646927625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36389886576097656467789333 1705775933254577646927625)
  ·
    refine ⟨1279331949940933235195719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1705775933254577646927625 1279331949940933235195719)
    ·
      refine ⟨1918997924911399852793579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279331949940933235195719 1918997924911399852793579)
      ·
        refine ⟨2878496887367099779190369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918997924911399852793579 2878496887367099779190369)
        ·
          refine ⟨2158872665525324834392777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878496887367099779190369 2158872665525324834392777)
          ·
            refine ⟨1619154499143993625794583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158872665525324834392777 1619154499143993625794583)
            ·
              refine ⟨2428731748715990438691875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619154499143993625794583 2428731748715990438691875)
              ·
                refine ⟨3643097623073985658037813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428731748715990438691875 3643097623073985658037813)
                ·
                  refine ⟨341540402163186155441045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643097623073985658037813 341540402163186155441045)
                  ·
                    rfl

theorem cell21_1496582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1496582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496582 prefixEnd_1496582 := by exact prefixLift 1496582
  have htrace : WordTrace (prefixWord ++ tailWord_1496582) baseStart_1496582 baseEnd_1496582 := by
    simpa [prefixWord, tailWord_1496582, baseEnd_1496582] using wordTrace_append hprefix tailTrace_1496582
  have hstable : (prefixWord ++ tailWord_1496582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496582).length < 2 ^ (prefixWord ++ tailWord_1496582).sum := by decide
  have hdescent : baseEnd_1496582 < baseStart_1496582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496596 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1496596 : Nat := 118140960795 + 1496596 * 2 ^ 59
def prefixEnd_1496596 : Nat := 4983230072969 + 3 ^ 40 * 1496596 * 2
def baseEnd_1496596 : Nat := 341543597153925242207683

theorem tailTrace_1496596 : CollatzResearch.WordTrace tailWord_1496596 prefixEnd_1496596 341543597153925242207683 := by
  unfold tailWord_1496596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27292670243047882546346821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36390226990730510061795761 27292670243047882546346821)
  ·
    refine ⟨5117375670571477977440029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27292670243047882546346821 5117375670571477977440029)
    ·
      refine ⟨1919015876464304241540011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5117375670571477977440029 1919015876464304241540011)
      ·
        refine ⟨2878523814696456362310017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919015876464304241540011 2878523814696456362310017)
        ·
          refine ⟨2158892861022342271732513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878523814696456362310017 2158892861022342271732513)
          ·
            refine ⟨1619169645766756703799385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158892861022342271732513 1619169645766756703799385)
            ·
              refine ⟨1214377234325067527849539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619169645766756703799385 1214377234325067527849539)
              ·
                refine ⟨1821565851487601291774309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214377234325067527849539 1821565851487601291774309)
                ·
                  refine ⟨341543597153925242207683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821565851487601291774309 341543597153925242207683)
                  ·
                    rfl

theorem cell21_1496596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1496596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496596 prefixEnd_1496596 := by exact prefixLift 1496596
  have htrace : WordTrace (prefixWord ++ tailWord_1496596) baseStart_1496596 baseEnd_1496596 := by
    simpa [prefixWord, tailWord_1496596, baseEnd_1496596] using wordTrace_append hprefix tailTrace_1496596
  have hstable : (prefixWord ++ tailWord_1496596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496596).length < 2 ^ (prefixWord ++ tailWord_1496596).sum := by decide
  have hdescent : baseEnd_1496596 < baseStart_1496596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496714 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1496714 : Nat := 118140960795 + 1496714 * 2 ^ 59
def prefixEnd_1496714 : Nat := 4983230072969 + 3 ^ 40 * 1496714 * 2
def baseEnd_1496714 : Nat := 341570526361583259240775

theorem tailTrace_1496714 : CollatzResearch.WordTrace tailWord_1496714 prefixEnd_1496714 341570526361583259240775 := by
  unfold tailWord_1496714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647411074917067811372299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36393096199778847496992797 13647411074917067811372299)
  ·
    refine ⟨20471116612375601717058449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647411074917067811372299 20471116612375601717058449)
    ·
      refine ⟨15353337459281701287793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20471116612375601717058449 15353337459281701287793837)
      ·
        refine ⟨5757501547230637982922689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15353337459281701287793837 5757501547230637982922689)
        ·
          refine ⟨4318126160422978487192017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757501547230637982922689 4318126160422978487192017)
          ·
            refine ⟨3238594620317233865394013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318126160422978487192017 3238594620317233865394013)
            ·
              refine ⟨1214472982618962699522755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3238594620317233865394013 1214472982618962699522755)
              ·
                refine ⟨1821709473928444049284133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214472982618962699522755 1821709473928444049284133)
                ·
                  refine ⟨341570526361583259240775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821709473928444049284133 341570526361583259240775)
                  ·
                    rfl

theorem cell21_1496714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1496714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496714 prefixEnd_1496714 := by exact prefixLift 1496714
  have htrace : WordTrace (prefixWord ++ tailWord_1496714) baseStart_1496714 baseEnd_1496714 := by
    simpa [prefixWord, tailWord_1496714, baseEnd_1496714] using wordTrace_append hprefix tailTrace_1496714
  have hstable : (prefixWord ++ tailWord_1496714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496714).length < 2 ^ (prefixWord ++ tailWord_1496714).sum := by decide
  have hdescent : baseEnd_1496714 < baseStart_1496714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496728 : List Nat := [2, 1, 2, 4, 1, 4, 2, 5]
def baseStart_1496728 : Nat := 118140960795 + 1496728 * 2 ^ 59
def prefixEnd_1496728 : Nat := 4983230072969 + 3 ^ 40 * 1496728 * 2
def baseEnd_1496728 : Nat := 113857907117440782002471

theorem tailTrace_1496728 : CollatzResearch.WordTrace tailWord_1496728 prefixEnd_1496728 113857907117440782002471 := by
  unfold tailWord_1496728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27295077460808775818249419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36393436614411701090999225 27295077460808775818249419)
  ·
    refine ⟨40942616191213163727374129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27295077460808775818249419 40942616191213163727374129)
    ·
      refine ⟨30706962143409872795530597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40942616191213163727374129 30706962143409872795530597)
      ·
        refine ⟨5757555401889351149161987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30706962143409872795530597 5757555401889351149161987)
        ·
          refine ⟨8636333102834026723742981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757555401889351149161987 8636333102834026723742981)
          ·
            refine ⟨1619312456781380010701809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8636333102834026723742981 1619312456781380010701809)
            ·
              refine ⟨1214484342586035008026357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619312456781380010701809 1214484342586035008026357)
              ·
                refine ⟨113857907117440782002471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1214484342586035008026357 113857907117440782002471)
                ·
                  rfl

theorem cell21_1496728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_1496728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496728 prefixEnd_1496728 := by exact prefixLift 1496728
  have htrace : WordTrace (prefixWord ++ tailWord_1496728) baseStart_1496728 baseEnd_1496728 := by
    simpa [prefixWord, tailWord_1496728, baseEnd_1496728] using wordTrace_append hprefix tailTrace_1496728
  have hstable : (prefixWord ++ tailWord_1496728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496728).length < 2 ^ (prefixWord ++ tailWord_1496728).sum := by decide
  have hdescent : baseEnd_1496728 < baseStart_1496728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496739 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_1496739 : Nat := 118140960795 + 1496739 * 2 ^ 59
def prefixEnd_1496739 : Nat := 4983230072969 + 3 ^ 40 * 1496739 * 2
def baseEnd_1496739 : Nat := 341576231702188771324057

theorem tailTrace_1496739 : CollatzResearch.WordTrace tailWord_1496739 prefixEnd_1496739 341576231702188771324057 := by
  unfold tailWord_1496739
  simp only [CollatzResearch.WordTrace]
  refine ⟨54590556124577700515149271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36393704083051800343432847 54590556124577700515149271)
  ·
    refine ⟨81885834186866550772723907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54590556124577700515149271 81885834186866550772723907)
    ·
      refine ⟨122828751280299826159085861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81885834186866550772723907 122828751280299826159085861)
      ·
        refine ⟨23030390865056217404828599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122828751280299826159085861 23030390865056217404828599)
        ·
          refine ⟨34545586297584326107242899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23030390865056217404828599 34545586297584326107242899)
          ·
            refine ⟨51818379446376489160864349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34545586297584326107242899 51818379446376489160864349)
            ·
              refine ⟨19431892292391183435324131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51818379446376489160864349 19431892292391183435324131)
              ·
                refine ⟨29147838438586775152986197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19431892292391183435324131 29147838438586775152986197)
                ·
                  refine ⟨341576231702188771324057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29147838438586775152986197 341576231702188771324057)
                  ·
                    rfl

theorem cell21_1496739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_1496739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496739 prefixEnd_1496739 := by exact prefixLift 1496739
  have htrace : WordTrace (prefixWord ++ tailWord_1496739) baseStart_1496739 baseEnd_1496739 := by
    simpa [prefixWord, tailWord_1496739, baseEnd_1496739] using wordTrace_append hprefix tailTrace_1496739
  have hstable : (prefixWord ++ tailWord_1496739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496739).length < 2 ^ (prefixWord ++ tailWord_1496739).sum := by decide
  have hdescent : baseEnd_1496739 < baseStart_1496739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496846 : List Nat := [4, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1496846 : Nat := 118140960795 + 1496846 * 2 ^ 59
def prefixEnd_1496846 : Nat := 4983230072969 + 3 ^ 40 * 1496846 * 2
def baseEnd_1496846 : Nat := 113866883519993454346835

theorem tailTrace_1496846 : CollatzResearch.WordTrace tailWord_1496846 prefixEnd_1496846 113866883519993454346835 := by
  unfold tailWord_1496846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824307341898757223661799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36396305823460038526196261 6824307341898757223661799)
  ·
    refine ⟨10236461012848135835492699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6824307341898757223661799 10236461012848135835492699)
    ·
      refine ⟨15354691519272203753239049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236461012848135835492699 15354691519272203753239049)
      ·
        refine ⟨11516018639454152814929287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15354691519272203753239049 11516018639454152814929287)
        ·
          refine ⟨17274027959181229222393931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516018639454152814929287 17274027959181229222393931)
          ·
            refine ⟨25911041938771843833590897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274027959181229222393931 25911041938771843833590897)
            ·
              refine ⟨19433281454078882875193173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25911041938771843833590897 19433281454078882875193173)
              ·
                refine ⟨113866883519993454346835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19433281454078882875193173 113866883519993454346835)
                ·
                  rfl

theorem cell21_1496846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1496846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496846 prefixEnd_1496846 := by exact prefixLift 1496846
  have htrace : WordTrace (prefixWord ++ tailWord_1496846) baseStart_1496846 baseEnd_1496846 := by
    simpa [prefixWord, tailWord_1496846, baseEnd_1496846] using wordTrace_append hprefix tailTrace_1496846
  have hstable : (prefixWord ++ tailWord_1496846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496846).length < 2 ^ (prefixWord ++ tailWord_1496846).sum := by decide
  have hdescent : baseEnd_1496846 < baseStart_1496846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496894 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1496894 : Nat := 118140960795 + 1496894 * 2 ^ 59
def prefixEnd_1496894 : Nat := 4983230072969 + 3 ^ 40 * 1496894 * 2
def baseEnd_1496894 : Nat := 341611604813942946240407

theorem tailTrace_1496894 : CollatzResearch.WordTrace tailWord_1496894 prefixEnd_1496894 341611604813942946240407 := by
  unfold tailWord_1496894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824526179877020248380217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36397472959344107991361157 6824526179877020248380217)
  ·
    refine ⟨5118394634907765186285163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6824526179877020248380217 5118394634907765186285163)
    ·
      refine ⟨7677591952361647779427745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118394634907765186285163 7677591952361647779427745)
      ·
        refine ⟨5758193964271235834570809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7677591952361647779427745 5758193964271235834570809)
        ·
          refine ⟨4318645473203426875928107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758193964271235834570809 4318645473203426875928107)
          ·
            refine ⟨6477968209805140313892161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318645473203426875928107 6477968209805140313892161)
            ·
              refine ⟨4858476157353855235419121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6477968209805140313892161 4858476157353855235419121)
              ·
                refine ⟨3643857118015391426564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858476157353855235419121 3643857118015391426564341)
                ·
                  refine ⟨341611604813942946240407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643857118015391426564341 341611604813942946240407)
                  ·
                    rfl

theorem cell21_1496894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1496894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496894 prefixEnd_1496894 := by exact prefixLift 1496894
  have htrace : WordTrace (prefixWord ++ tailWord_1496894) baseStart_1496894 baseEnd_1496894 := by
    simpa [prefixWord, tailWord_1496894, baseEnd_1496894] using wordTrace_append hprefix tailTrace_1496894
  have hstable : (prefixWord ++ tailWord_1496894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496894).length < 2 ^ (prefixWord ++ tailWord_1496894).sum := by decide
  have hdescent : baseEnd_1496894 < baseStart_1496894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496942 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1496942 : Nat := 118140960795 + 1496942 * 2 ^ 59
def prefixEnd_1496942 : Nat := 4983230072969 + 3 ^ 40 * 1496942 * 2
def baseEnd_1496942 : Nat := 341622559067905529440309

theorem tailTrace_1496942 : CollatzResearch.WordTrace tailWord_1496942 prefixEnd_1496942 341622559067905529440309 := by
  unfold tailWord_1496942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824745017855283273098635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36398640095228177456526053 6824745017855283273098635)
  ·
    refine ⟨10237117526782924909647953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6824745017855283273098635 10237117526782924909647953)
    ·
      refine ⟨7677838145087193682235965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10237117526782924909647953 7677838145087193682235965)
      ·
        refine ⟨2879189304407697630838487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7677838145087193682235965 2879189304407697630838487)
        ·
          refine ⟨4318783956611546446257731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879189304407697630838487 4318783956611546446257731)
          ·
            refine ⟨6478175934917319669386597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318783956611546446257731 6478175934917319669386597)
            ·
              refine ⟨1214657987796997438009987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6478175934917319669386597 1214657987796997438009987)
              ·
                refine ⟨1821986981695496157014981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214657987796997438009987 1821986981695496157014981)
                ·
                  refine ⟨341622559067905529440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821986981695496157014981 341622559067905529440309)
                  ·
                    rfl

theorem cell21_1496942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1496942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496942 prefixEnd_1496942 := by exact prefixLift 1496942
  have htrace : WordTrace (prefixWord ++ tailWord_1496942) baseStart_1496942 baseEnd_1496942 := by
    simpa [prefixWord, tailWord_1496942, baseEnd_1496942] using wordTrace_append hprefix tailTrace_1496942
  have hstable : (prefixWord ++ tailWord_1496942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496942).length < 2 ^ (prefixWord ++ tailWord_1496942).sum := by decide
  have hdescent : baseEnd_1496942 < baseStart_1496942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496990 : List Nat := [4, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1496990 : Nat := 118140960795 + 1496990 * 2 ^ 59
def prefixEnd_1496990 : Nat := 4983230072969 + 3 ^ 40 * 1496990 * 2
def baseEnd_1496990 : Nat := 113877837773956037546737

theorem tailTrace_1496990 : CollatzResearch.WordTrace tailWord_1496990 prefixEnd_1496990 113877837773956037546737 := by
  unfold tailWord_1496990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824963855833546297817053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36399807231112246921690949 6824963855833546297817053)
  ·
    refine ⟨2559361445937579861681395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6824963855833546297817053 2559361445937579861681395)
    ·
      refine ⟨3839042168906369792522093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559361445937579861681395 3839042168906369792522093)
      ·
        refine ⟨1439640813339888672195785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3839042168906369792522093 1439640813339888672195785)
        ·
          refine ⟨1079730610004916504146839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439640813339888672195785 1079730610004916504146839)
          ·
            refine ⟨1619595915007374756220259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079730610004916504146839 1619595915007374756220259)
            ·
              refine ⟨2429393872511062134330389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619595915007374756220259 2429393872511062134330389)
              ·
                refine ⟨113877837773956037546737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2429393872511062134330389 113877837773956037546737)
                ·
                  rfl

theorem cell21_1496990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1496990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1496990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1496990 prefixEnd_1496990 := by exact prefixLift 1496990
  have htrace : WordTrace (prefixWord ++ tailWord_1496990) baseStart_1496990 baseEnd_1496990 := by
    simpa [prefixWord, tailWord_1496990, baseEnd_1496990] using wordTrace_append hprefix tailTrace_1496990
  have hstable : (prefixWord ++ tailWord_1496990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496990).length < 2 ^ (prefixWord ++ tailWord_1496990).sum := by decide
  have hdescent : baseEnd_1496990 < baseStart_1496990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497052 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1497052 : Nat := 118140960795 + 1497052 * 2 ^ 59
def prefixEnd_1497052 : Nat := 4983230072969 + 3 ^ 40 * 1497052 * 2
def baseEnd_1497052 : Nat := 341647662566569782606751

theorem tailTrace_1497052 : CollatzResearch.WordTrace tailWord_1497052 prefixEnd_1497052 341647662566569782606751 := by
  unfold tailWord_1497052
  simp only [CollatzResearch.WordTrace]
  refine ⟨27300986086221877485646705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36401314781629169980862273 27300986086221877485646705)
  ·
    refine ⟨20475739564666408114235029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27300986086221877485646705 20475739564666408114235029)
    ·
      refine ⟨959800292093737880354767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20475739564666408114235029 959800292093737880354767)
      ·
        refine ⟨1439700438140606820532151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959800292093737880354767 1439700438140606820532151)
        ·
          refine ⟨2159550657210910230798227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439700438140606820532151 2159550657210910230798227)
          ·
            refine ⟨3239325985816365346197341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159550657210910230798227 3239325985816365346197341)
            ·
              refine ⟨1214747244681137004824003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3239325985816365346197341 1214747244681137004824003)
              ·
                refine ⟨1822120867021705507236005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214747244681137004824003 1822120867021705507236005)
                ·
                  refine ⟨341647662566569782606751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822120867021705507236005 341647662566569782606751)
                  ·
                    rfl

theorem cell21_1497052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1497052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497052 prefixEnd_1497052 := by exact prefixLift 1497052
  have htrace : WordTrace (prefixWord ++ tailWord_1497052) baseStart_1497052 baseEnd_1497052 := by
    simpa [prefixWord, tailWord_1497052, baseEnd_1497052] using wordTrace_append hprefix tailTrace_1497052
  have hstable : (prefixWord ++ tailWord_1497052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497052).length < 2 ^ (prefixWord ++ tailWord_1497052).sum := by decide
  have hdescent : baseEnd_1497052 < baseStart_1497052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497111 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 4]
def baseStart_1497111 : Nat := 118140960795 + 1497111 * 2 ^ 59
def prefixEnd_1497111 : Nat := 4983230072969 + 3 ^ 40 * 1497111 * 2
def baseEnd_1497111 : Nat := 341661127170398791123297

theorem tailTrace_1497111 : CollatzResearch.WordTrace tailWord_1497111 prefixEnd_1497111 341661127170398791123297 := by
  unfold tailWord_1497111
  simp only [CollatzResearch.WordTrace]
  refine ⟨54604124079230008047691187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36402749386153338698460791 54604124079230008047691187)
  ·
    refine ⟨81906186118845012071536781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54604124079230008047691187 81906186118845012071536781)
    ·
      refine ⟨30714819794566879526826293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81906186118845012071536781 30714819794566879526826293)
      ·
        refine ⟨2879514355740644955639965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30714819794566879526826293 2879514355740644955639965)
        ·
          refine ⟨1079817883402741858364987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2879514355740644955639965 1079817883402741858364987)
          ·
            refine ⟨1619726825104112787547481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079817883402741858364987 1619726825104112787547481)
            ·
              refine ⟨1214795118828084590660611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619726825104112787547481 1214795118828084590660611)
              ·
                refine ⟨1822192678242126885990917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214795118828084590660611 1822192678242126885990917)
                ·
                  refine ⟨341661127170398791123297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822192678242126885990917 341661127170398791123297)
                  ·
                    rfl

theorem cell21_1497111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].length) (baseStart_1497111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497111 prefixEnd_1497111 := by exact prefixLift 1497111
  have htrace : WordTrace (prefixWord ++ tailWord_1497111) baseStart_1497111 baseEnd_1497111 := by
    simpa [prefixWord, tailWord_1497111, baseEnd_1497111] using wordTrace_append hprefix tailTrace_1497111
  have hstable : (prefixWord ++ tailWord_1497111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497111).length < 2 ^ (prefixWord ++ tailWord_1497111).sum := by decide
  have hdescent : baseEnd_1497111 < baseStart_1497111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497150 : List Nat := [4, 2, 1, 3, 11]
def baseStart_1497150 : Nat := 118140960795 + 1497150 * 2 ^ 59
def prefixEnd_1497150 : Nat := 4983230072969 + 3 ^ 40 * 1497150 * 2
def baseEnd_1497150 : Nat := 4218148487675844320657

theorem tailTrace_1497150 : CollatzResearch.WordTrace tailWord_1497150 prefixEnd_1497150 4218148487675844320657 := by
  unfold tailWord_1497150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825693315761089713545113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36403697684059145138907269 6825693315761089713545113)
  ·
    refine ⟨5119269986820817285158835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6825693315761089713545113 5119269986820817285158835)
    ·
      refine ⟨7678904980231225927738253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119269986820817285158835 7678904980231225927738253)
      ·
        refine ⟨2879589367586709722901845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7678904980231225927738253 2879589367586709722901845)
        ·
          refine ⟨4218148487675844320657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2879589367586709722901845 4218148487675844320657)
          ·
            rfl

theorem cell21_1497150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 11].length) (baseStart_1497150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497150 prefixEnd_1497150 := by exact prefixLift 1497150
  have htrace : WordTrace (prefixWord ++ tailWord_1497150) baseStart_1497150 baseEnd_1497150 := by
    simpa [prefixWord, tailWord_1497150, baseEnd_1497150] using wordTrace_append hprefix tailTrace_1497150
  have hstable : (prefixWord ++ tailWord_1497150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497150).length < 2 ^ (prefixWord ++ tailWord_1497150).sum := by decide
  have hdescent : baseEnd_1497150 < baseStart_1497150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497153 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1497153 : Nat := 118140960795 + 1497153 * 2 ^ 59
def prefixEnd_1497153 : Nat := 4983230072969 + 3 ^ 40 * 1497153 * 2
def baseEnd_1497153 : Nat := 341670712142616051423211

theorem tailTrace_1497153 : CollatzResearch.WordTrace tailWord_1497153 prefixEnd_1497153 341670712142616051423211 := by
  unfold tailWord_1497153
  simp only [CollatzResearch.WordTrace]
  refine ⟨54605655945077849220720113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36403770630051899480480075 54605655945077849220720113)
  ·
    refine ⟨40954241958808386915540085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54605655945077849220720113 40954241958808386915540085)
    ·
      refine ⟨3839460183638286273331883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40954241958808386915540085 3839460183638286273331883)
      ·
        refine ⟨5759190275457429409997825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839460183638286273331883 5759190275457429409997825)
        ·
          refine ⟨4319392706593072057498369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5759190275457429409997825 4319392706593072057498369)
          ·
            refine ⟨3239544529944804043123777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4319392706593072057498369 3239544529944804043123777)
            ·
              refine ⟨2429658397458603032342833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239544529944804043123777 2429658397458603032342833)
              ·
                refine ⟨1822243798093952274257125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429658397458603032342833 1822243798093952274257125)
                ·
                  refine ⟨341670712142616051423211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822243798093952274257125 341670712142616051423211)
                  ·
                    rfl

theorem cell21_1497153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1497153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497153 prefixEnd_1497153 := by exact prefixLift 1497153
  have htrace : WordTrace (prefixWord ++ tailWord_1497153) baseStart_1497153 baseEnd_1497153 := by
    simpa [prefixWord, tailWord_1497153, baseEnd_1497153] using wordTrace_append hprefix tailTrace_1497153
  have hstable : (prefixWord ++ tailWord_1497153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497153).length < 2 ^ (prefixWord ++ tailWord_1497153).sum := by decide
  have hdescent : baseEnd_1497153 < baseStart_1497153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497212 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1497212 : Nat := 118140960795 + 1497212 * 2 ^ 59
def prefixEnd_1497212 : Nat := 4983230072969 + 3 ^ 40 * 1497212 * 2
def baseEnd_1497212 : Nat := 341684176746445059939757

theorem tailTrace_1497212 : CollatzResearch.WordTrace tailWord_1497212 prefixEnd_1497212 341684176746445059939757 := by
  unfold tailWord_1497212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303903925932051148558945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36405205234576068198078593 27303903925932051148558945)
  ·
    refine ⟨20477927944449038361419209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27303903925932051148558945 20477927944449038361419209)
    ·
      refine ⟨15358445958336778771064407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20477927944449038361419209 15358445958336778771064407)
      ·
        refine ⟨23037668937505168156596611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358445958336778771064407 23037668937505168156596611)
        ·
          refine ⟨34556503406257752234894917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23037668937505168156596611 34556503406257752234894917)
          ·
            refine ⟨6479344388673328544042797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34556503406257752234894917 6479344388673328544042797)
            ·
              refine ⟨2429754145752498204016049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6479344388673328544042797 2429754145752498204016049)
              ·
                refine ⟨1822315609314373653012037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429754145752498204016049 1822315609314373653012037)
                ·
                  refine ⟨341684176746445059939757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822315609314373653012037 341684176746445059939757)
                  ·
                    rfl

theorem cell21_1497212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1497212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497212 prefixEnd_1497212 := by exact prefixLift 1497212
  have htrace : WordTrace (prefixWord ++ tailWord_1497212) baseStart_1497212 baseEnd_1497212 := by
    simpa [prefixWord, tailWord_1497212, baseEnd_1497212] using wordTrace_append hprefix tailTrace_1497212
  have hstable : (prefixWord ++ tailWord_1497212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497212).length < 2 ^ (prefixWord ++ tailWord_1497212).sum := by decide
  have hdescent : baseEnd_1497212 < baseStart_1497212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497271 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_1497271 : Nat := 118140960795 + 1497271 * 2 ^ 59
def prefixEnd_1497271 : Nat := 4983230072969 + 3 ^ 40 * 1497271 * 2
def baseEnd_1497271 : Nat := 341697641350274068456303

theorem tailTrace_1497271 : CollatzResearch.WordTrace tailWord_1497271 prefixEnd_1497271 341697641350274068456303 := by
  unfold tailWord_1497271
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609959758650355373515667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36406639839100236915677111 54609959758650355373515667)
  ·
    refine ⟨81914939637975533060273501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54609959758650355373515667 81914939637975533060273501)
    ·
      refine ⟨30718102364240824897602563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81914939637975533060273501 30718102364240824897602563)
      ·
        refine ⟨46077153546361237346403845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30718102364240824897602563 46077153546361237346403845)
        ·
          refine ⟨8639466289942732002450721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46077153546361237346403845 8639466289942732002450721)
          ·
            refine ⟨6479599717457049001838041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8639466289942732002450721 6479599717457049001838041)
            ·
              refine ⟨4859699788092786751378531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479599717457049001838041 4859699788092786751378531)
              ·
                refine ⟨7289549682139180127067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859699788092786751378531 7289549682139180127067797)
                ·
                  refine ⟨341697641350274068456303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7289549682139180127067797 341697641350274068456303)
                  ·
                    rfl

theorem cell21_1497271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_1497271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497271 prefixEnd_1497271 := by exact prefixLift 1497271
  have htrace : WordTrace (prefixWord ++ tailWord_1497271) baseStart_1497271 baseEnd_1497271 := by
    simpa [prefixWord, tailWord_1497271, baseEnd_1497271] using wordTrace_append hprefix tailTrace_1497271
  have hstable : (prefixWord ++ tailWord_1497271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497271).length < 2 ^ (prefixWord ++ tailWord_1497271).sum := by decide
  have hdescent : baseEnd_1497271 < baseStart_1497271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497285 : List Nat := [1, 3, 1, 1, 1, 1, 5, 8]
def baseStart_1497285 : Nat := 118140960795 + 1497285 * 2 ^ 59
def prefixEnd_1497285 : Nat := 4983230072969 + 3 ^ 40 * 1497285 * 2
def baseEnd_1497285 : Nat := 113900278780337718407647

theorem tailTrace_1497285 : CollatzResearch.WordTrace tailWord_1497285 prefixEnd_1497285 113900278780337718407647 := by
  unfold tailWord_1497285
  simp only [CollatzResearch.WordTrace]
  refine ⟨54610470380599635764525309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36406980253733090509683539 54610470380599635764525309)
  ·
    refine ⟨20478926392724863411696991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54610470380599635764525309 20478926392724863411696991)
    ·
      refine ⟨30718389589087295117545487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20478926392724863411696991 30718389589087295117545487)
      ·
        refine ⟨46077584383630942676318231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30718389589087295117545487 46077584383630942676318231)
        ·
          refine ⟨69116376575446414014477347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46077584383630942676318231 69116376575446414014477347)
          ·
            refine ⟨103674564863169621021716021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69116376575446414014477347 103674564863169621021716021)
            ·
              refine ⟨9719490455922151970785877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103674564863169621021716021 9719490455922151970785877)
              ·
                refine ⟨113900278780337718407647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9719490455922151970785877 113900278780337718407647)
                ·
                  rfl

theorem cell21_1497285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_1497285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497285 prefixEnd_1497285 := by exact prefixLift 1497285
  have htrace : WordTrace (prefixWord ++ tailWord_1497285) baseStart_1497285 baseEnd_1497285 := by
    simpa [prefixWord, tailWord_1497285, baseEnd_1497285] using wordTrace_append hprefix tailTrace_1497285
  have hstable : (prefixWord ++ tailWord_1497285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497285).length < 2 ^ (prefixWord ++ tailWord_1497285).sum := by decide
  have hdescent : baseEnd_1497285 < baseStart_1497285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497325 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1497325 : Nat := 118140960795 + 1497325 * 2 ^ 59
def prefixEnd_1497325 : Nat := 4983230072969 + 3 ^ 40 * 1497325 * 2
def baseEnd_1497325 : Nat := 341709964885981974556193

theorem tailTrace_1497325 : CollatzResearch.WordTrace tailWord_1497325 prefixEnd_1497325 341709964885981974556193 := by
  unfold tailWord_1497325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54611929300454722595981429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36407952866969815063987619 54611929300454722595981429)
  ·
    refine ⟨5119868371917630243373259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54611929300454722595981429 5119868371917630243373259)
    ·
      refine ⟨7679802557876445365059889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119868371917630243373259 7679802557876445365059889)
      ·
        refine ⟨5759851918407334023794917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7679802557876445365059889 5759851918407334023794917)
        ·
          refine ⟨1079972234701375129461547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5759851918407334023794917 1079972234701375129461547)
          ·
            refine ⟨1619958352052062694192321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079972234701375129461547 1619958352052062694192321)
            ·
              refine ⟨1214968764039047020644241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619958352052062694192321 1214968764039047020644241)
              ·
                refine ⟨911226573029285265483181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214968764039047020644241 911226573029285265483181)
                ·
                  refine ⟨341709964885981974556193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911226573029285265483181 341709964885981974556193)
                  ·
                    rfl

theorem cell21_1497325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1497325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497325 prefixEnd_1497325 := by exact prefixLift 1497325
  have htrace : WordTrace (prefixWord ++ tailWord_1497325) baseStart_1497325 baseEnd_1497325 := by
    simpa [prefixWord, tailWord_1497325, baseEnd_1497325] using wordTrace_append hprefix tailTrace_1497325
  have hstable : (prefixWord ++ tailWord_1497325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497325).length < 2 ^ (prefixWord ++ tailWord_1497325).sum := by decide
  have hdescent : baseEnd_1497325 < baseStart_1497325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497347 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_1497347 : Nat := 118140960795 + 1497347 * 2 ^ 59
def prefixEnd_1497347 : Nat := 4983230072969 + 3 ^ 40 * 1497347 * 2
def baseEnd_1497347 : Nat := 341714985585714825189481

theorem tailTrace_1497347 : CollatzResearch.WordTrace tailWord_1497347 prefixEnd_1497347 341714985585714825189481 := by
  unfold tailWord_1497347
  simp only [CollatzResearch.WordTrace]
  refine ⟨54612731706375020353282295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36408487804250013568854863 54612731706375020353282295)
  ·
    refine ⟨81919097559562530529923443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54612731706375020353282295 81919097559562530529923443)
    ·
      refine ⟨122878646339343795794885165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81919097559562530529923443 122878646339343795794885165)
      ·
        refine ⟨46079492377253923423081937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122878646339343795794885165 46079492377253923423081937)
        ·
          refine ⟨34559619282940442567311453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46079492377253923423081937 34559619282940442567311453)
          ·
            refine ⟨12959857231102665962741795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34559619282940442567311453 12959857231102665962741795)
            ·
              refine ⟨19439785846653998944112693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12959857231102665962741795 19439785846653998944112693)
              ·
                refine ⟨1822479923123812401010565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19439785846653998944112693 1822479923123812401010565)
                ·
                  refine ⟨341714985585714825189481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822479923123812401010565 341714985585714825189481)
                  ·
                    rfl

theorem cell21_1497347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_1497347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497347 prefixEnd_1497347 := by exact prefixLift 1497347
  have htrace : WordTrace (prefixWord ++ tailWord_1497347) baseStart_1497347 baseEnd_1497347 := by
    simpa [prefixWord, tailWord_1497347, baseEnd_1497347] using wordTrace_append hprefix tailTrace_1497347
  have hstable : (prefixWord ++ tailWord_1497347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497347).length < 2 ^ (prefixWord ++ tailWord_1497347).sum := by decide
  have hdescent : baseEnd_1497347 < baseStart_1497347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497378 : List Nat := [3, 3, 1, 1, 3, 2, 8]
def baseStart_1497378 : Nat := 118140960795 + 1497378 * 2 ^ 59
def prefixEnd_1497378 : Nat := 4983230072969 + 3 ^ 40 * 1497378 * 2
def baseEnd_1497378 : Nat := 37969117800896184463639

theorem tailTrace_1497378 : CollatzResearch.WordTrace tailWord_1497378 prefixEnd_1497378 37969117800896184463639 := by
  unfold tailWord_1497378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653465592315678161915197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36409241579508475098440525 13653465592315678161915197)
  ·
    refine ⟨5120049597118379310718199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13653465592315678161915197 5120049597118379310718199)
    ·
      refine ⟨7680074395677568966077299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120049597118379310718199 7680074395677568966077299)
      ·
        refine ⟨11520111593516353449115949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680074395677568966077299 11520111593516353449115949)
        ·
          refine ⟨4320041847568632543418481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11520111593516353449115949 4320041847568632543418481)
          ·
            refine ⟨3240031385676474407563861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4320041847568632543418481 3240031385676474407563861)
            ·
              refine ⟨37969117800896184463639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3240031385676474407563861 37969117800896184463639)
              ·
                rfl

theorem cell21_1497378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 8].length) (baseStart_1497378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497378 prefixEnd_1497378 := by exact prefixLift 1497378
  have htrace : WordTrace (prefixWord ++ tailWord_1497378) baseStart_1497378 baseEnd_1497378 := by
    simpa [prefixWord, tailWord_1497378, baseEnd_1497378] using wordTrace_append hprefix tailTrace_1497378
  have hstable : (prefixWord ++ tailWord_1497378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497378).length < 2 ^ (prefixWord ++ tailWord_1497378).sum := by decide
  have hdescent : baseEnd_1497378 < baseStart_1497378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497381 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1497381 : Nat := 118140960795 + 1497381 * 2 ^ 59
def prefixEnd_1497381 : Nat := 4983230072969 + 3 ^ 40 * 1497381 * 2
def baseEnd_1497381 : Nat := 341722744848938321622745

theorem tailTrace_1497381 : CollatzResearch.WordTrace tailWord_1497381 prefixEnd_1497381 341722744848938321622745 := by
  unfold tailWord_1497381
  simp only [CollatzResearch.WordTrace]
  refine ⟨54613971788251844160019997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36409314525501229440013331 54613971788251844160019997)
  ·
    refine ⟨20480239420594441560007499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54613971788251844160019997 20480239420594441560007499)
    ·
      refine ⟨30720359130891662340011249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20480239420594441560007499 30720359130891662340011249)
      ·
        refine ⟨23040269348168746755008437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30720359130891662340011249 23040269348168746755008437)
        ·
          refine ⟨2160025251390820008282041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23040269348168746755008437 2160025251390820008282041)
          ·
            refine ⟨1620018938543115006211531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160025251390820008282041 1620018938543115006211531)
            ·
              refine ⟨2430028407814672509317297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620018938543115006211531 2430028407814672509317297)
              ·
                refine ⟨1822521305861004381987973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430028407814672509317297 1822521305861004381987973)
                ·
                  refine ⟨341722744848938321622745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822521305861004381987973 341722744848938321622745)
                  ·
                    rfl

theorem cell21_1497381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1497381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497381 prefixEnd_1497381 := by exact prefixLift 1497381
  have htrace : WordTrace (prefixWord ++ tailWord_1497381) baseStart_1497381 baseEnd_1497381 := by
    simpa [prefixWord, tailWord_1497381, baseEnd_1497381] using wordTrace_append hprefix tailTrace_1497381
  have hstable : (prefixWord ++ tailWord_1497381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497381).length < 2 ^ (prefixWord ++ tailWord_1497381).sum := by decide
  have hdescent : baseEnd_1497381 < baseStart_1497381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497426 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1497426 : Nat := 118140960795 + 1497426 * 2 ^ 59
def prefixEnd_1497426 : Nat := 4983230072969 + 3 ^ 40 * 1497426 * 2
def baseEnd_1497426 : Nat := 341733014462028243372653

theorem tailTrace_1497426 : CollatzResearch.WordTrace tailWord_1497426 prefixEnd_1497426 341733014462028243372653 := by
  unfold tailWord_1497426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653903268272204211352033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36410408715392544563605421 13653903268272204211352033)
  ·
    refine ⟨10240427451204153158514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13653903268272204211352033 10240427451204153158514025)
    ·
      refine ⟨7680320588403114868885519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10240427451204153158514025 7680320588403114868885519)
      ·
        refine ⟨11520480882604672303328279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680320588403114868885519 11520480882604672303328279)
        ·
          refine ⟨17280721323907008454992419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520480882604672303328279 17280721323907008454992419)
          ·
            refine ⟨25921081985860512682488629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280721323907008454992419 25921081985860512682488629)
            ·
              refine ⟨2430101436174423063983309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25921081985860512682488629 2430101436174423063983309)
              ·
                refine ⟨911288038565408648993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430101436174423063983309 911288038565408648993741)
                ·
                  refine ⟨341733014462028243372653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911288038565408648993741 341733014462028243372653)
                  ·
                    rfl

theorem cell21_1497426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1497426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497426 prefixEnd_1497426 := by exact prefixLift 1497426
  have htrace : WordTrace (prefixWord ++ tailWord_1497426) baseStart_1497426 baseEnd_1497426 := by
    simpa [prefixWord, tailWord_1497426, baseEnd_1497426] using wordTrace_append hprefix tailTrace_1497426
  have hstable : (prefixWord ++ tailWord_1497426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497426).length < 2 ^ (prefixWord ++ tailWord_1497426).sum := by decide
  have hdescent : baseEnd_1497426 < baseStart_1497426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497561 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 3]
def baseStart_1497561 : Nat := 118140960795 + 1497561 * 2 ^ 59
def prefixEnd_1497561 : Nat := 4983230072969 + 3 ^ 40 * 1497561 * 2
def baseEnd_1497561 : Nat := 341763823301298008622377

theorem tailTrace_1497561 : CollatzResearch.WordTrace tailWord_1497561 prefixEnd_1497561 341763823301298008622377 := by
  unfold tailWord_1497561
  simp only [CollatzResearch.WordTrace]
  refine ⟨54620536927599734901572537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36413691285066489934381691 54620536927599734901572537)
  ·
    refine ⟨40965402695699801176179403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54620536927599734901572537 40965402695699801176179403)
    ·
      refine ⟨61448104043549701764269105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40965402695699801176179403 61448104043549701764269105)
      ·
        refine ⟨46086078032662276323201829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61448104043549701764269105 46086078032662276323201829)
        ·
          refine ⟨8641139631124176810600343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46086078032662276323201829 8641139631124176810600343)
          ·
            refine ⟨12961709446686265215900515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641139631124176810600343 12961709446686265215900515)
            ·
              refine ⟨19442564170029397823850773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961709446686265215900515 19442564170029397823850773)
              ·
                refine ⟨911370195470128022993005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19442564170029397823850773 911370195470128022993005)
                ·
                  refine ⟨341763823301298008622377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911370195470128022993005 341763823301298008622377)
                  ·
                    rfl

theorem cell21_1497561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_1497561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497561 prefixEnd_1497561 := by exact prefixLift 1497561
  have htrace : WordTrace (prefixWord ++ tailWord_1497561) baseStart_1497561 baseEnd_1497561 := by
    simpa [prefixWord, tailWord_1497561, baseEnd_1497561] using wordTrace_append hprefix tailTrace_1497561
  have hstable : (prefixWord ++ tailWord_1497561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497561).length < 2 ^ (prefixWord ++ tailWord_1497561).sum := by decide
  have hdescent : baseEnd_1497561 < baseStart_1497561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497623 : List Nat := [1, 1, 3, 6, 1, 1, 2, 6]
def baseStart_1497623 : Nat := 118140960795 + 1497623 * 2 ^ 59
def prefixEnd_1497623 : Nat := 4983230072969 + 3 ^ 40 * 1497623 * 2
def baseEnd_1497623 : Nat := 113925990848666559529639

theorem tailTrace_1497623 : CollatzResearch.WordTrace tailWord_1497623 prefixEnd_1497623 113925990848666559529639 := by
  unfold tailWord_1497623
  simp only [CollatzResearch.WordTrace]
  refine ⟨54622798253375119490329523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36415198835583412993553015 54622798253375119490329523)
  ·
    refine ⟨81934197380062679235494285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54622798253375119490329523 81934197380062679235494285)
    ·
      refine ⟨30725324017523504713310357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81934197380062679235494285 30725324017523504713310357)
      ·
        refine ⟨1440249563321414283436423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30725324017523504713310357 1440249563321414283436423)
        ·
          refine ⟨2160374344982121425154635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440249563321414283436423 2160374344982121425154635)
          ·
            refine ⟨3240561517473182137731953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160374344982121425154635 3240561517473182137731953)
            ·
              refine ⟨2430421138104886603298965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240561517473182137731953 2430421138104886603298965)
              ·
                refine ⟨113925990848666559529639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2430421138104886603298965 113925990848666559529639)
                ·
                  rfl

theorem cell21_1497623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_1497623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497623 prefixEnd_1497623 := by exact prefixLift 1497623
  have htrace : WordTrace (prefixWord ++ tailWord_1497623) baseStart_1497623 baseEnd_1497623 := by
    simpa [prefixWord, tailWord_1497623, baseEnd_1497623] using wordTrace_append hprefix tailTrace_1497623
  have hstable : (prefixWord ++ tailWord_1497623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497623).length < 2 ^ (prefixWord ++ tailWord_1497623).sum := by decide
  have hdescent : baseEnd_1497623 < baseStart_1497623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
