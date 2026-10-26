import V185TrunkScan22Chunk366

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3273270 : List Nat := [5, 1, 2, 1, 2, 3, 2, 6]
def baseStart_3273270 : Nat := 118140960795 + 3273270 * 2 ^ 59
def prefixEnd_3273270 : Nat := 4983230072969 + 3 ^ 40 * 3273270 * 2
def baseEnd_3273270 : Nat := 124500801625371374057149

theorem tailTrace_3273270 : CollatzResearch.WordTrace tailWord_3273270 prefixEnd_3273270 124500801625371374057149 := by
  unfold tailWord_3273270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461622803219330928403579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79590643234339529902971509 7461622803219330928403579)
  ·
    refine ⟨11192434204828996392605369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461622803219330928403579 11192434204828996392605369)
    ·
      refine ⟨8394325653621747294454027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11192434204828996392605369 8394325653621747294454027)
      ·
        refine ⟨12591488480432620941681041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394325653621747294454027 12591488480432620941681041)
        ·
          refine ⟨9443616360324465706260781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12591488480432620941681041 9443616360324465706260781)
          ·
            refine ⟨3541356135121674639847793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9443616360324465706260781 3541356135121674639847793)
            ·
              refine ⟨2656017101341255979885845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541356135121674639847793 2656017101341255979885845)
              ·
                refine ⟨124500801625371374057149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656017101341255979885845 124500801625371374057149)
                ·
                  rfl

theorem cell22_3273270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_3273270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273270 prefixEnd_3273270 := by exact prefixLift 3273270
  have htrace : WordTrace (prefixWord ++ tailWord_3273270) baseStart_3273270 baseEnd_3273270 := by
    simpa [prefixWord, tailWord_3273270, baseEnd_3273270] using wordTrace_append hprefix tailTrace_3273270
  have hstable : (prefixWord ++ tailWord_3273270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273270).length < 2 ^ (prefixWord ++ tailWord_3273270).sum := by decide
  have hdescent : baseEnd_3273270 < baseStart_3273270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273281 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 7]
def baseStart_3273281 : Nat := 118140960795 + 3273281 * 2 ^ 59
def prefixEnd_3273281 : Nat := 4983230072969 + 3 ^ 40 * 3273281 * 2
def baseEnd_3273281 : Nat := 373503660051047334829769

theorem tailTrace_3273281 : CollatzResearch.WordTrace tailWord_3273281 prefixEnd_3273281 373503660051047334829769 := by
  unfold tailWord_3273281
  simp only [CollatzResearch.WordTrace]
  refine ⟨119386366054469443733107697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79590910702979629155405131 119386366054469443733107697)
  ·
    refine ⟨89539774540852082799830773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119386366054469443733107697 89539774540852082799830773)
    ·
      refine ⟨8394353863204882762484135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89539774540852082799830773 8394353863204882762484135)
      ·
        refine ⟨12591530794807324143726203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394353863204882762484135 12591530794807324143726203)
        ·
          refine ⟨18887296192210986215589305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591530794807324143726203 18887296192210986215589305)
          ·
            refine ⟨14165472144158239661691979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18887296192210986215589305 14165472144158239661691979)
            ·
              refine ⟨21248208216237359492537969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14165472144158239661691979 21248208216237359492537969)
              ·
                refine ⟨15936156162178019619403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21248208216237359492537969 15936156162178019619403477)
                ·
                  refine ⟨373503660051047334829769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15936156162178019619403477 373503660051047334829769)
                  ·
                    rfl

theorem cell22_3273281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_3273281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273281 prefixEnd_3273281 := by exact prefixLift 3273281
  have htrace : WordTrace (prefixWord ++ tailWord_3273281) baseStart_3273281 baseEnd_3273281 := by
    simpa [prefixWord, tailWord_3273281, baseEnd_3273281] using wordTrace_append hprefix tailTrace_3273281
  have hstable : (prefixWord ++ tailWord_3273281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273281).length < 2 ^ (prefixWord ++ tailWord_3273281).sum := by decide
  have hdescent : baseEnd_3273281 < baseStart_3273281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273285 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_3273285 : Nat := 118140960795 + 3273285 * 2 ^ 59
def prefixEnd_3273285 : Nat := 4983230072969 + 3 ^ 40 * 3273285 * 2
def baseEnd_3273285 : Nat := 1120512349434887327389295

theorem tailTrace_3273285 : CollatzResearch.WordTrace tailWord_3273285 prefixEnd_3273285 1120512349434887327389295 := by
  unfold tailWord_3273285
  simp only [CollatzResearch.WordTrace]
  refine ⟨119386511946454952416253309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79591007964303301610835539 119386511946454952416253309)
  ·
    refine ⟨44769941979920607156094991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119386511946454952416253309 44769941979920607156094991)
    ·
      refine ⟨67154912969880910734142487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44769941979920607156094991 67154912969880910734142487)
      ·
        refine ⟨100732369454821366101213731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67154912969880910734142487 100732369454821366101213731)
        ·
          refine ⟨151098554182232049151820597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100732369454821366101213731 151098554182232049151820597)
          ·
            refine ⟨14165489454584254607983181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151098554182232049151820597 14165489454584254607983181)
            ·
              refine ⟨5312058545469095477993693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14165489454584254607983181 5312058545469095477993693)
              ·
                refine ⟨1992021954550910804247635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5312058545469095477993693 1992021954550910804247635)
                ·
                  refine ⟨2988032931826366206371453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992021954550910804247635 2988032931826366206371453)
                  ·
                    refine ⟨1120512349434887327389295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988032931826366206371453 1120512349434887327389295)
                    ·
                      rfl

theorem cell22_3273285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_3273285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273285 prefixEnd_3273285 := by exact prefixLift 3273285
  have htrace : WordTrace (prefixWord ++ tailWord_3273285) baseStart_3273285 baseEnd_3273285 := by
    simpa [prefixWord, tailWord_3273285, baseEnd_3273285] using wordTrace_append hprefix tailTrace_3273285
  have hstable : (prefixWord ++ tailWord_3273285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273285).length < 2 ^ (prefixWord ++ tailWord_3273285).sum := by decide
  have hdescent : baseEnd_3273285 < baseStart_3273285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273328 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_3273328 : Nat := 118140960795 + 3273328 * 2 ^ 59
def prefixEnd_3273328 : Nat := 4983230072969 + 3 ^ 40 * 3273328 * 2
def baseEnd_3273328 : Nat := 1120527069213649548564163

theorem tailTrace_3273328 : CollatzResearch.WordTrace tailWord_3273328 prefixEnd_3273328 1120527069213649548564163 := by
  unfold tailWord_3273328
  simp only [CollatzResearch.WordTrace]
  refine ⟨59694040142649585380034319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79592053523532780506712425 59694040142649585380034319)
  ·
    refine ⟨89541060213974378070051479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59694040142649585380034319 89541060213974378070051479)
    ·
      refine ⟨134311590320961567105077219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89541060213974378070051479 134311590320961567105077219)
      ·
        refine ⟨201467385481442350657615829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134311590320961567105077219 201467385481442350657615829)
        ·
          refine ⟨4721891847221305093537871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 201467385481442350657615829 4721891847221305093537871)
          ·
            refine ⟨7082837770831957640306807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721891847221305093537871 7082837770831957640306807)
            ·
              refine ⟨10624256656247936460460211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082837770831957640306807 10624256656247936460460211)
              ·
                refine ⟨15936384984371904690690317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624256656247936460460211 15936384984371904690690317)
                ·
                  refine ⟨5976144369139464259008869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15936384984371904690690317 5976144369139464259008869)
                  ·
                    refine ⟨1120527069213649548564163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976144369139464259008869 1120527069213649548564163)
                    ·
                      rfl

theorem cell22_3273328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_3273328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273328 prefixEnd_3273328 := by exact prefixLift 3273328
  have htrace : WordTrace (prefixWord ++ tailWord_3273328) baseStart_3273328 baseEnd_3273328 := by
    simpa [prefixWord, tailWord_3273328, baseEnd_3273328] using wordTrace_append hprefix tailTrace_3273328
  have hstable : (prefixWord ++ tailWord_3273328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273328).length < 2 ^ (prefixWord ++ tailWord_3273328).sum := by decide
  have hdescent : baseEnd_3273328 < baseStart_3273328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273345 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3273345 : Nat := 118140960795 + 3273345 * 2 ^ 59
def prefixEnd_3273345 : Nat := 4983230072969 + 3 ^ 40 * 3273345 * 2
def baseEnd_3273345 : Nat := 1120532888661067170889111

theorem tailTrace_3273345 : CollatzResearch.WordTrace tailWord_3273345 prefixEnd_3273345 1120532888661067170889111 := by
  unfold tailWord_3273345
  simp only [CollatzResearch.WordTrace]
  refine ⟨119388700326237582663437489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79592466884158388442291659 119388700326237582663437489)
  ·
    refine ⟨89541525244678186997578117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119388700326237582663437489 89541525244678186997578117)
    ·
      refine ⟨16789035983377160062045897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89541525244678186997578117 16789035983377160062045897)
      ·
        refine ⟨12591776987532870046534423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16789035983377160062045897 12591776987532870046534423)
        ·
          refine ⟨18887665481299305069801635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591776987532870046534423 18887665481299305069801635)
          ·
            refine ⟨28331498221948957604702453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887665481299305069801635 28331498221948957604702453)
            ·
              refine ⟨2656077958307714775440855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28331498221948957604702453 2656077958307714775440855)
              ·
                refine ⟨3984116937461572163161283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656077958307714775440855 3984116937461572163161283)
                ·
                  refine ⟨5976175406192358244741925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984116937461572163161283 5976175406192358244741925)
                  ·
                    refine ⟨1120532888661067170889111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976175406192358244741925 1120532888661067170889111)
                    ·
                      rfl

theorem cell22_3273345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3273345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273345 prefixEnd_3273345 := by exact prefixLift 3273345
  have htrace : WordTrace (prefixWord ++ tailWord_3273345) baseStart_3273345 baseEnd_3273345 := by
    simpa [prefixWord, tailWord_3273345, baseEnd_3273345] using wordTrace_append hprefix tailTrace_3273345
  have hstable : (prefixWord ++ tailWord_3273345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273345).length < 2 ^ (prefixWord ++ tailWord_3273345).sum := by decide
  have hdescent : baseEnd_3273345 < baseStart_3273345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273356 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_3273356 : Nat := 118140960795 + 3273356 * 2 ^ 59
def prefixEnd_3273356 : Nat := 4983230072969 + 3 ^ 40 * 3273356 * 2
def baseEnd_3273356 : Nat := 1120536654185866808864077

theorem tailTrace_3273356 : CollatzResearch.WordTrace tailWord_3273356 prefixEnd_3273356 1120536654185866808864077 := by
  unfold tailWord_3273356
  simp only [CollatzResearch.WordTrace]
  refine ⟨59694550764598865771043961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79592734352798487694725281 59694550764598865771043961)
  ·
    refine ⟨44770913073449149328282971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59694550764598865771043961 44770913073449149328282971)
    ·
      refine ⟨67156369610173723992424457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44770913073449149328282971 67156369610173723992424457)
      ·
        refine ⟨50367277207630292994318343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67156369610173723992424457 50367277207630292994318343)
        ·
          refine ⟨75550915811445439491477515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50367277207630292994318343 75550915811445439491477515)
          ·
            refine ⟨113326373717168159237216273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75550915811445439491477515 113326373717168159237216273)
            ·
              refine ⟨84994780287876119427912205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113326373717168159237216273 84994780287876119427912205)
              ·
                refine ⟨31873042607953544785467077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84994780287876119427912205 31873042607953544785467077)
                ·
                  refine ⟨5976195488991289647275077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31873042607953544785467077 5976195488991289647275077)
                  ·
                    refine ⟨1120536654185866808864077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976195488991289647275077 1120536654185866808864077)
                    ·
                      rfl

theorem cell22_3273356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_3273356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273356 prefixEnd_3273356 := by exact prefixLift 3273356
  have htrace : WordTrace (prefixWord ++ tailWord_3273356) baseStart_3273356 baseEnd_3273356 := by
    simpa [prefixWord, tailWord_3273356, baseEnd_3273356] using wordTrace_append hprefix tailTrace_3273356
  have hstable : (prefixWord ++ tailWord_3273356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273356).length < 2 ^ (prefixWord ++ tailWord_3273356).sum := by decide
  have hdescent : baseEnd_3273356 < baseStart_3273356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273390 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3273390 : Nat := 118140960795 + 3273390 * 2 ^ 59
def prefixEnd_3273390 : Nat := 4983230072969 + 3 ^ 40 * 3273390 * 2
def baseEnd_3273390 : Nat := 1120548293080702053513973

theorem tailTrace_3273390 : CollatzResearch.WordTrace tailWord_3273390 prefixEnd_3273390 1120548293080702053513973 := by
  unfold tailWord_3273390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14923792701384319418603203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79593561074049703565883749 14923792701384319418603203)
  ·
    refine ⟨22385689052076479127904805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14923792701384319418603203 22385689052076479127904805)
    ·
      refine ⟨4197316697264339836482151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22385689052076479127904805 4197316697264339836482151)
      ·
        refine ⟨6295975045896509754723227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197316697264339836482151 6295975045896509754723227)
        ·
          refine ⟨9443962568844764632084841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295975045896509754723227 9443962568844764632084841)
          ·
            refine ⟨7082971926633573474063631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9443962568844764632084841 7082971926633573474063631)
            ·
              refine ⟨10624457889950360211095447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082971926633573474063631 10624457889950360211095447)
              ·
                refine ⟨15936686834925540316643171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624457889950360211095447 15936686834925540316643171)
                ·
                  refine ⟨23905030252388310474964757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15936686834925540316643171 23905030252388310474964757)
                  ·
                    refine ⟨1120548293080702053513973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23905030252388310474964757 1120548293080702053513973)
                    ·
                      rfl

theorem cell22_3273390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3273390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273390 prefixEnd_3273390 := by exact prefixLift 3273390
  have htrace : WordTrace (prefixWord ++ tailWord_3273390) baseStart_3273390 baseEnd_3273390 := by
    simpa [prefixWord, tailWord_3273390, baseEnd_3273390] using wordTrace_append hprefix tailTrace_3273390
  have hstable : (prefixWord ++ tailWord_3273390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273390).length < 2 ^ (prefixWord ++ tailWord_3273390).sum := by decide
  have hdescent : baseEnd_3273390 < baseStart_3273390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273420 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_3273420 : Nat := 118140960795 + 3273420 * 2 ^ 59
def prefixEnd_3273420 : Nat := 4983230072969 + 3 ^ 40 * 3273420 * 2
def baseEnd_3273420 : Nat := 1120558562693791975263881

theorem tailTrace_3273420 : CollatzResearch.WordTrace tailWord_3273420 prefixEnd_3273420 1120558562693791975263881 := by
  unfold tailWord_3273420
  simp only [CollatzResearch.WordTrace]
  refine ⟨59695717900482935236208857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79594290533977246981611809 59695717900482935236208857)
  ·
    refine ⟨44771788425362201427156643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59695717900482935236208857 44771788425362201427156643)
    ·
      refine ⟨67157682638043302140734965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44771788425362201427156643 67157682638043302140734965)
      ·
        refine ⟨6296032747316559575693903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67157682638043302140734965 6296032747316559575693903)
        ·
          refine ⟨9444049120974839363540855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296032747316559575693903 9444049120974839363540855)
          ·
            refine ⟨14166073681462259045311283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444049120974839363540855 14166073681462259045311283)
            ·
              refine ⟨21249110522193388567966925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166073681462259045311283 21249110522193388567966925)
              ·
                refine ⟨7968416445822520712987597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21249110522193388567966925 7968416445822520712987597)
                ·
                  refine ⟨2988156167183445267370349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7968416445822520712987597 2988156167183445267370349)
                  ·
                    refine ⟨1120558562693791975263881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988156167183445267370349 1120558562693791975263881)
                    ·
                      rfl

theorem cell22_3273420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_3273420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273420 prefixEnd_3273420 := by exact prefixLift 3273420
  have htrace : WordTrace (prefixWord ++ tailWord_3273420) baseStart_3273420 baseEnd_3273420 := by
    simpa [prefixWord, tailWord_3273420, baseEnd_3273420] using wordTrace_append hprefix tailTrace_3273420
  have hstable : (prefixWord ++ tailWord_3273420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273420).length < 2 ^ (prefixWord ++ tailWord_3273420).sum := by decide
  have hdescent : baseEnd_3273420 < baseStart_3273420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273454 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3273454 : Nat := 118140960795 + 3273454 * 2 ^ 59
def prefixEnd_3273454 : Nat := 4983230072969 + 3 ^ 40 * 3273454 * 2
def baseEnd_3273454 : Nat := 1120570201588627219913777

theorem tailTrace_3273454 : CollatzResearch.WordTrace tailWord_3273454 prefixEnd_3273454 1120570201588627219913777 := by
  unfold tailWord_3273454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14924084485355336784894427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79595117255228462852770277 14924084485355336784894427)
  ·
    refine ⟨22386126728033005177341641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14924084485355336784894427 22386126728033005177341641)
    ·
      refine ⟨16789595046024753883006231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22386126728033005177341641 16789595046024753883006231)
      ·
        refine ⟨25184392569037130824509347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16789595046024753883006231 25184392569037130824509347)
        ·
          refine ⟨37776588853555696236764021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25184392569037130824509347 37776588853555696236764021)
          ·
            refine ⟨3541555205020846522196627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37776588853555696236764021 3541555205020846522196627)
            ·
              refine ⟨5312332807531269783294941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541555205020846522196627 5312332807531269783294941)
              ·
                refine ⟨1992124802824226168735603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5312332807531269783294941 1992124802824226168735603)
                ·
                  refine ⟨2988187204236339253103405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992124802824226168735603 2988187204236339253103405)
                  ·
                    refine ⟨1120570201588627219913777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988187204236339253103405 1120570201588627219913777)
                    ·
                      rfl

theorem cell22_3273454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3273454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273454 prefixEnd_3273454 := by exact prefixLift 3273454
  have htrace : WordTrace (prefixWord ++ tailWord_3273454) baseStart_3273454 baseEnd_3273454 := by
    simpa [prefixWord, tailWord_3273454, baseEnd_3273454] using wordTrace_append hprefix tailTrace_3273454
  have hstable : (prefixWord ++ tailWord_3273454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273454).length < 2 ^ (prefixWord ++ tailWord_3273454).sum := by decide
  have hdescent : baseEnd_3273454 < baseStart_3273454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273493 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3273493 : Nat := 118140960795 + 3273493 * 2 ^ 59
def prefixEnd_3273493 : Nat := 4983230072969 + 3 ^ 40 * 3273493 * 2
def baseEnd_3273493 : Nat := 1120583552085644118188657

theorem tailTrace_3273493 : CollatzResearch.WordTrace tailWord_3273493 prefixEnd_3273493 1120583552085644118188657 := by
  unfold tailWord_3273493
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394098329701403939825133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596065553134269293216755 119394098329701403939825133)
  ·
    refine ⟨44772786873638026477434425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119394098329701403939825133 44772786873638026477434425)
    ·
      refine ⟨33579590155228519858075819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44772786873638026477434425 33579590155228519858075819)
      ·
        refine ⟨50369385232842779787113729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33579590155228519858075819 50369385232842779787113729)
        ·
          refine ⟨37777038924632084840335297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50369385232842779787113729 37777038924632084840335297)
          ·
            refine ⟨28332779193474063630251473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37777038924632084840335297 28332779193474063630251473)
            ·
              refine ⟨21249584395105547722688605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28332779193474063630251473 21249584395105547722688605)
              ·
                refine ⟨7968594148164580396008227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21249584395105547722688605 7968594148164580396008227)
                ·
                  refine ⟨11952891222246870594012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968594148164580396008227 11952891222246870594012341)
                  ·
                    refine ⟨1120583552085644118188657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11952891222246870594012341 1120583552085644118188657)
                    ·
                      rfl

theorem cell22_3273493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3273493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273493 prefixEnd_3273493 := by exact prefixLift 3273493
  have htrace : WordTrace (prefixWord ++ tailWord_3273493) baseStart_3273493 baseEnd_3273493 := by
    simpa [prefixWord, tailWord_3273493, baseEnd_3273493] using wordTrace_append hprefix tailTrace_3273493
  have hstable : (prefixWord ++ tailWord_3273493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273493).length < 2 ^ (prefixWord ++ tailWord_3273493).sum := by decide
  have hdescent : baseEnd_3273493 < baseStart_3273493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273525 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3273525 : Nat := 118140960795 + 3273525 * 2 ^ 59
def prefixEnd_3273525 : Nat := 4983230072969 + 3 ^ 40 * 3273525 * 2
def baseEnd_3273525 : Nat := 1120594506339606701388559

theorem tailTrace_3273525 : CollatzResearch.WordTrace tailWord_3273525 prefixEnd_3273525 1120594506339606701388559 := by
  unfold tailWord_3273525
  simp only [CollatzResearch.WordTrace]
  refine ⟨119395265465585473404990029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596843643723648936660019 119395265465585473404990029)
  ·
    refine ⟨44773224549594552526871261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119395265465585473404990029 44773224549594552526871261)
    ·
      refine ⟨16789959206097957197576723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44773224549594552526871261 16789959206097957197576723)
      ·
        refine ⟨25184938809146935796365085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16789959206097957197576723 25184938809146935796365085)
        ·
          refine ⟨9444352053430100923636907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25184938809146935796365085 9444352053430100923636907)
          ·
            refine ⟨14166528080145151385455361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444352053430100923636907 14166528080145151385455361)
            ·
              refine ⟨10624896060108863539091521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14166528080145151385455361 10624896060108863539091521)
              ·
                refine ⟨7968672045081647654318641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624896060108863539091521 7968672045081647654318641)
                ·
                  refine ⟨5976504033811235740738981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968672045081647654318641 5976504033811235740738981)
                  ·
                    refine ⟨1120594506339606701388559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976504033811235740738981 1120594506339606701388559)
                    ·
                      rfl

theorem cell22_3273525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3273525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273525 prefixEnd_3273525 := by exact prefixLift 3273525
  have htrace : WordTrace (prefixWord ++ tailWord_3273525) baseStart_3273525 baseEnd_3273525 := by
    simpa [prefixWord, tailWord_3273525, baseEnd_3273525] using wordTrace_append hprefix tailTrace_3273525
  have hstable : (prefixWord ++ tailWord_3273525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273525).length < 2 ^ (prefixWord ++ tailWord_3273525).sum := by decide
  have hdescent : baseEnd_3273525 < baseStart_3273525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273568 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_3273568 : Nat := 118140960795 + 3273568 * 2 ^ 59
def prefixEnd_3273568 : Nat := 4983230072969 + 3 ^ 40 * 3273568 * 2
def baseEnd_3273568 : Nat := 373536408706122974187809

theorem tailTrace_3273568 : CollatzResearch.WordTrace tailWord_3273568 prefixEnd_3273568 373536408706122974187809 := by
  unfold tailWord_3273568
  simp only [CollatzResearch.WordTrace]
  refine ⟨59698416902214845874402679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79597889202953127832536905 59698416902214845874402679)
  ·
    refine ⟨89547625353322268811604019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59698416902214845874402679 89547625353322268811604019)
    ·
      refine ⟨134321438029983403217406029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89547625353322268811604019 134321438029983403217406029)
      ·
        refine ⟨50370539261243776206527261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134321438029983403217406029 50370539261243776206527261)
        ·
          refine ⟨18888952222966416077447723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50370539261243776206527261 18888952222966416077447723)
          ·
            refine ⟨28333428334449624116171585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18888952222966416077447723 28333428334449624116171585)
            ·
              refine ⟨21250071250837218087128689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28333428334449624116171585 21250071250837218087128689)
              ·
                refine ⟨15937553438127913565346517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21250071250837218087128689 15937553438127913565346517)
                ·
                  refine ⟨373536408706122974187809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15937553438127913565346517 373536408706122974187809)
                  ·
                    rfl

theorem cell22_3273568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_3273568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273568 prefixEnd_3273568 := by exact prefixLift 3273568
  have htrace : WordTrace (prefixWord ++ tailWord_3273568) baseStart_3273568 baseEnd_3273568 := by
    simpa [prefixWord, tailWord_3273568, baseEnd_3273568] using wordTrace_append hprefix tailTrace_3273568
  have hstable : (prefixWord ++ tailWord_3273568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273568).length < 2 ^ (prefixWord ++ tailWord_3273568).sum := by decide
  have hdescent : baseEnd_3273568 < baseStart_3273568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273585 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 5]
def baseStart_3273585 : Nat := 118140960795 + 3273585 * 2 ^ 59
def prefixEnd_3273585 : Nat := 4983230072969 + 3 ^ 40 * 3273585 * 2
def baseEnd_3273585 : Nat := 373538348521928848296125

theorem tailTrace_3273585 : CollatzResearch.WordTrace tailWord_3273585 prefixEnd_3273585 373538348521928848296125 := by
  unfold tailWord_3273585
  simp only [CollatzResearch.WordTrace]
  refine ⟨119397453845368103652174209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79598302563578735768116139 119397453845368103652174209)
  ·
    refine ⟨89548090384026077739130657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119397453845368103652174209 89548090384026077739130657)
    ·
      refine ⟨67161067788019558304347993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89548090384026077739130657 67161067788019558304347993)
      ·
        refine ⟨50370800841014668728260995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67161067788019558304347993 50370800841014668728260995)
        ·
          refine ⟨75556201261522003092391493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50370800841014668728260995 75556201261522003092391493)
          ·
            refine ⟨14166787736535375579823405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75556201261522003092391493 14166787736535375579823405)
            ·
              refine ⟨5312545401200765842433777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14166787736535375579823405 5312545401200765842433777)
              ·
                refine ⟨3984409050900574381825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312545401200765842433777 3984409050900574381825333)
                ·
                  refine ⟨373538348521928848296125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3984409050900574381825333 373538348521928848296125)
                  ·
                    rfl

theorem cell22_3273585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_3273585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273585 prefixEnd_3273585 := by exact prefixLift 3273585
  have htrace : WordTrace (prefixWord ++ tailWord_3273585) baseStart_3273585 baseEnd_3273585 := by
    simpa [prefixWord, tailWord_3273585, baseEnd_3273585] using wordTrace_append hprefix tailTrace_3273585
  have hstable : (prefixWord ++ tailWord_3273585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273585).length < 2 ^ (prefixWord ++ tailWord_3273585).sum := by decide
  have hdescent : baseEnd_3273585 < baseStart_3273585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273589 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3273589 : Nat := 118140960795 + 3273589 * 2 ^ 59
def prefixEnd_3273589 : Nat := 4983230072969 + 3 ^ 40 * 3273589 * 2
def baseEnd_3273589 : Nat := 1120616414847531867788363

theorem tailTrace_3273589 : CollatzResearch.WordTrace tailWord_3273589 prefixEnd_3273589 1120616414847531867788363 := by
  unfold tailWord_3273589
  simp only [CollatzResearch.WordTrace]
  refine ⟨119397599737353612335319821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79598399824902408223546547 119397599737353612335319821)
  ·
    refine ⟨44774099901507604625744933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119397599737353612335319821 44774099901507604625744933)
    ·
      refine ⟨8395143731532675867327175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44774099901507604625744933 8395143731532675867327175)
      ·
        refine ⟨12592715597299013800990763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395143731532675867327175 12592715597299013800990763)
        ·
          refine ⟨18889073395948520701486145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12592715597299013800990763 18889073395948520701486145)
          ·
            refine ⟨14166805046961390526114609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18889073395948520701486145 14166805046961390526114609)
            ·
              refine ⟨10625103785221042894585957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14166805046961390526114609 10625103785221042894585957)
              ·
                refine ⟨1992206959728945542734867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10625103785221042894585957 1992206959728945542734867)
                ·
                  refine ⟨2988310439593418314102301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992206959728945542734867 2988310439593418314102301)
                  ·
                    refine ⟨1120616414847531867788363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988310439593418314102301 1120616414847531867788363)
                    ·
                      rfl

theorem cell22_3273589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3273589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273589 prefixEnd_3273589 := by exact prefixLift 3273589
  have htrace : WordTrace (prefixWord ++ tailWord_3273589) baseStart_3273589 baseEnd_3273589 := by
    simpa [prefixWord, tailWord_3273589, baseEnd_3273589] using wordTrace_append hprefix tailTrace_3273589
  have hstable : (prefixWord ++ tailWord_3273589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273589).length < 2 ^ (prefixWord ++ tailWord_3273589).sum := by decide
  have hdescent : baseEnd_3273589 < baseStart_3273589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273698 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3273698 : Nat := 118140960795 + 3273698 * 2 ^ 59
def prefixEnd_3273698 : Nat := 4983230072969 + 3 ^ 40 * 3273698 * 2
def baseEnd_3273698 : Nat := 373551242591697305604343

theorem tailTrace_3273698 : CollatzResearch.WordTrace tailWord_3273698 prefixEnd_3273698 373551242591697305604343 := by
  unfold tailWord_3273698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850393823489680987759437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79601050195972482634025165 29850393823489680987759437)
  ·
    refine ⟨11193897683808630370409789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29850393823489680987759437 11193897683808630370409789)
    ·
      refine ⟨4197711631428236388903671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11193897683808630370409789 4197711631428236388903671)
      ·
        refine ⟨6296567447142354583355507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197711631428236388903671 6296567447142354583355507)
        ·
          refine ⟨9444851170713531875033261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296567447142354583355507 9444851170713531875033261)
          ·
            refine ⟨3541819189017574453137473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9444851170713531875033261 3541819189017574453137473)
            ·
              refine ⟨2656364391763180839853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541819189017574453137473 2656364391763180839853105)
              ·
                refine ⟨1992273293822385629889829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656364391763180839853105 1992273293822385629889829)
                ·
                  refine ⟨373551242591697305604343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992273293822385629889829 373551242591697305604343)
                  ·
                    rfl

theorem cell22_3273698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3273698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273698 prefixEnd_3273698 := by exact prefixLift 3273698
  have htrace : WordTrace (prefixWord ++ tailWord_3273698) baseStart_3273698 baseEnd_3273698 := by
    simpa [prefixWord, tailWord_3273698, baseEnd_3273698] using wordTrace_append hprefix tailTrace_3273698
  have hstable : (prefixWord ++ tailWord_3273698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273698).length < 2 ^ (prefixWord ++ tailWord_3273698).sum := by decide
  have hdescent : baseEnd_3273698 < baseStart_3273698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273735 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3273735 : Nat := 118140960795 + 3273735 * 2 ^ 59
def prefixEnd_3273735 : Nat := 4983230072969 + 3 ^ 40 * 3273735 * 2
def baseEnd_3273735 : Nat := 1120666393631236153637915

theorem tailTrace_3273735 : CollatzResearch.WordTrace tailWord_3273735 prefixEnd_3273735 1120666393631236153637915 := by
  unfold tailWord_3273735
  simp only [CollatzResearch.WordTrace]
  refine ⟨119402924794824679270134659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79601949863216452846756439 119402924794824679270134659)
  ·
    refine ⟨179104387192237018905201989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119402924794824679270134659 179104387192237018905201989)
    ·
      refine ⟨33582072598544441044725373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179104387192237018905201989 33582072598544441044725373)
      ·
        refine ⟨12593277224454165391772015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33582072598544441044725373 12593277224454165391772015)
        ·
          refine ⟨18889915836681248087658023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593277224454165391772015 18889915836681248087658023)
          ·
            refine ⟨28334873755021872131487035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18889915836681248087658023 28334873755021872131487035)
            ·
              refine ⟨42502310632532808197230553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28334873755021872131487035 42502310632532808197230553)
              ·
                refine ⟨31876732974399606147922915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42502310632532808197230553 31876732974399606147922915)
                ·
                  refine ⟨47815099461599409221884373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31876732974399606147922915 47815099461599409221884373)
                  ·
                    refine ⟨1120666393631236153637915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47815099461599409221884373 1120666393631236153637915)
                    ·
                      rfl

theorem cell22_3273735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3273735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273735 prefixEnd_3273735 := by exact prefixLift 3273735
  have htrace : WordTrace (prefixWord ++ tailWord_3273735) baseStart_3273735 baseEnd_3273735 := by
    simpa [prefixWord, tailWord_3273735, baseEnd_3273735] using wordTrace_append hprefix tailTrace_3273735
  have hstable : (prefixWord ++ tailWord_3273735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273735).length < 2 ^ (prefixWord ++ tailWord_3273735).sum := by decide
  have hdescent : baseEnd_3273735 < baseStart_3273735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273784 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_3273784 : Nat := 118140960795 + 3273784 * 2 ^ 59
def prefixEnd_3273784 : Nat := 4983230072969 + 3 ^ 40 * 3273784 * 2
def baseEnd_3273784 : Nat := 1120683167332616359162765

theorem tailTrace_3273784 : CollatzResearch.WordTrace tailWord_3273784 prefixEnd_3273784 1120683167332616359162765 := by
  unfold tailWord_3273784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702355985823580319334203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79603141314431440425778937 59702355985823580319334203)
  ·
    refine ⟨89553533978735370479001305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59702355985823580319334203 89553533978735370479001305)
    ·
      refine ⟨67165150484051527859250979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89553533978735370479001305 67165150484051527859250979)
      ·
        refine ⟨100747725726077291788876469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67165150484051527859250979 100747725726077291788876469)
        ·
          refine ⟨9445099286819746105207169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100747725726077291788876469 9445099286819746105207169)
          ·
            refine ⟨7083824465114809578905377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9445099286819746105207169 7083824465114809578905377)
            ·
              refine ⟨5312868348836107184179033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083824465114809578905377 5312868348836107184179033)
              ·
                refine ⟨3984651261627080388134275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312868348836107184179033 3984651261627080388134275)
                ·
                  refine ⟨5976976892440620582201413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984651261627080388134275 5976976892440620582201413)
                  ·
                    refine ⟨1120683167332616359162765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976976892440620582201413 1120683167332616359162765)
                    ·
                      rfl

theorem cell22_3273784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_3273784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273784 prefixEnd_3273784 := by exact prefixLift 3273784
  have htrace : WordTrace (prefixWord ++ tailWord_3273784) baseStart_3273784 baseEnd_3273784 := by
    simpa [prefixWord, tailWord_3273784, baseEnd_3273784] using wordTrace_append hprefix tailTrace_3273784
  have hstable : (prefixWord ++ tailWord_3273784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273784).length < 2 ^ (prefixWord ++ tailWord_3273784).sum := by decide
  have hdescent : baseEnd_3273784 < baseStart_3273784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273795 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_3273795 : Nat := 118140960795 + 3273795 * 2 ^ 59
def prefixEnd_3273795 : Nat := 4983230072969 + 3 ^ 40 * 3273795 * 2
def baseEnd_3273795 : Nat := 1120686932857415997137731

theorem tailTrace_3273795 : CollatzResearch.WordTrace tailWord_3273795 prefixEnd_3273795 1120686932857415997137731 := by
  unfold tailWord_3273795
  simp only [CollatzResearch.WordTrace]
  refine ⟨119405113174607309517318839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79603408783071539678212559 119405113174607309517318839)
  ·
    refine ⟨179107669761910964275978259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119405113174607309517318839 179107669761910964275978259)
    ·
      refine ⟨268661504642866446413967389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179107669761910964275978259 268661504642866446413967389)
      ·
        refine ⟨100748064241074917405237771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268661504642866446413967389 100748064241074917405237771)
        ·
          refine ⟨151122096361612376107856657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100748064241074917405237771 151122096361612376107856657)
          ·
            refine ⟨113341572271209282080892493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151122096361612376107856657 113341572271209282080892493)
            ·
              refine ⟨42503089601703480780334685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113341572271209282080892493 42503089601703480780334685)
              ·
                refine ⟨15938658600638805292625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42503089601703480780334685 15938658600638805292625507)
                ·
                  refine ⟨23907987900958207938938261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15938658600638805292625507 23907987900958207938938261)
                  ·
                    refine ⟨1120686932857415997137731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23907987900958207938938261 1120686932857415997137731)
                    ·
                      rfl

theorem cell22_3273795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_3273795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273795 prefixEnd_3273795 := by exact prefixLift 3273795
  have htrace : WordTrace (prefixWord ++ tailWord_3273795) baseStart_3273795 baseEnd_3273795 := by
    simpa [prefixWord, tailWord_3273795, baseEnd_3273795] using wordTrace_append hprefix tailTrace_3273795
  have hstable : (prefixWord ++ tailWord_3273795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273795).length < 2 ^ (prefixWord ++ tailWord_3273795).sum := by decide
  have hdescent : baseEnd_3273795 < baseStart_3273795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273797 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_3273797 : Nat := 118140960795 + 3273797 * 2 ^ 59
def prefixEnd_3273797 : Nat := 4983230072969 + 3 ^ 40 * 3273797 * 2
def baseEnd_3273797 : Nat := 1120687617498288658587725

theorem tailTrace_3273797 : CollatzResearch.WordTrace tailWord_3273797 prefixEnd_3273797 1120687617498288658587725 := by
  unfold tailWord_3273797
  simp only [CollatzResearch.WordTrace]
  refine ⟨119405186120600063858891645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79603457413733375905927763 119405186120600063858891645)
  ·
    refine ⟨44776944795225023947084367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119405186120600063858891645 44776944795225023947084367)
    ·
      refine ⟨67165417192837535920626551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44776944795225023947084367 67165417192837535920626551)
      ·
        refine ⟨100748125789256303880939827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67165417192837535920626551 100748125789256303880939827)
        ·
          refine ⟨151122188683884455821409741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100748125789256303880939827 151122188683884455821409741)
          ·
            refine ⟨56670820756456670933028653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151122188683884455821409741 56670820756456670933028653)
            ·
              refine ⟨21251557783671251599885745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56670820756456670933028653 21251557783671251599885745)
              ·
                refine ⟨15938668337753438699914309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21251557783671251599885745 15938668337753438699914309)
                ·
                  refine ⟨2988500313328769756233933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15938668337753438699914309 2988500313328769756233933)
                  ·
                    refine ⟨1120687617498288658587725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988500313328769756233933 1120687617498288658587725)
                    ·
                      rfl

theorem cell22_3273797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_3273797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273797 prefixEnd_3273797 := by exact prefixLift 3273797
  have htrace : WordTrace (prefixWord ++ tailWord_3273797) baseStart_3273797 baseEnd_3273797 := by
    simpa [prefixWord, tailWord_3273797, baseEnd_3273797] using wordTrace_append hprefix tailTrace_3273797
  have hstable : (prefixWord ++ tailWord_3273797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273797).length < 2 ^ (prefixWord ++ tailWord_3273797).sum := by decide
  have hdescent : baseEnd_3273797 < baseStart_3273797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273799 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 4]
def baseStart_3273799 : Nat := 118140960795 + 3273799 * 2 ^ 59
def prefixEnd_3273799 : Nat := 4983230072969 + 3 ^ 40 * 3273799 * 2
def baseEnd_3273799 : Nat := 373562767379720440012573

theorem tailTrace_3273799 : CollatzResearch.WordTrace tailWord_3273799 prefixEnd_3273799 373562767379720440012573 := by
  unfold tailWord_3273799
  simp only [CollatzResearch.WordTrace]
  refine ⟨119405259066592818200464451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79603506044395212133642967 119405259066592818200464451)
  ·
    refine ⟨179107888599889227300696677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119405259066592818200464451 179107888599889227300696677)
    ·
      refine ⟨33582729112479230118880627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179107888599889227300696677 33582729112479230118880627)
      ·
        refine ⟨50374093668718845178320941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33582729112479230118880627 50374093668718845178320941)
        ·
          refine ⟨18890285125769566941870353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50374093668718845178320941 18890285125769566941870353)
          ·
            refine ⟨14167713844327175206402765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18890285125769566941870353 14167713844327175206402765)
            ·
              refine ⟨5312892691622690702401037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14167713844327175206402765 5312892691622690702401037)
              ·
                refine ⟨1992334759358509013400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5312892691622690702401037 1992334759358509013400389)
                ·
                  refine ⟨373562767379720440012573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992334759358509013400389 373562767379720440012573)
                  ·
                    rfl

theorem cell22_3273799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 4].length) (baseStart_3273799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273799 prefixEnd_3273799 := by exact prefixLift 3273799
  have htrace : WordTrace (prefixWord ++ tailWord_3273799) baseStart_3273799 baseEnd_3273799 := by
    simpa [prefixWord, tailWord_3273799, baseEnd_3273799] using wordTrace_append hprefix tailTrace_3273799
  have hstable : (prefixWord ++ tailWord_3273799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273799).length < 2 ^ (prefixWord ++ tailWord_3273799).sum := by decide
  have hdescent : baseEnd_3273799 < baseStart_3273799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273812 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3273812 : Nat := 118140960795 + 3273812 * 2 ^ 59
def prefixEnd_3273812 : Nat := 4983230072969 + 3 ^ 40 * 3273812 * 2
def baseEnd_3273812 : Nat := 1120692752304833619462679

theorem tailTrace_3273812 : CollatzResearch.WordTrace tailWord_3273812 prefixEnd_3273812 1120692752304833619462679 := by
  unfold tailWord_3273812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702866607772860710343845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79603822143697147613791793 59702866607772860710343845)
  ·
    refine ⟨11194287488957411383189471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59702866607772860710343845 11194287488957411383189471)
    ·
      refine ⟨16791431233436117074784207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194287488957411383189471 16791431233436117074784207)
      ·
        refine ⟨25187146850154175612176311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791431233436117074784207 25187146850154175612176311)
        ·
          refine ⟨37780720275231263418264467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25187146850154175612176311 37780720275231263418264467)
          ·
            refine ⟨56671080412846895127396701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37780720275231263418264467 56671080412846895127396701)
            ·
              refine ⟨21251655154817585672773763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56671080412846895127396701 21251655154817585672773763)
              ·
                refine ⟨31877482732226378509160645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21251655154817585672773763 31877482732226378509160645)
                ·
                  refine ⟨5977028012292445970467621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31877482732226378509160645 5977028012292445970467621)
                  ·
                    refine ⟨1120692752304833619462679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5977028012292445970467621 1120692752304833619462679)
                    ·
                      rfl

theorem cell22_3273812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3273812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273812 prefixEnd_3273812 := by exact prefixLift 3273812
  have htrace : WordTrace (prefixWord ++ tailWord_3273812) baseStart_3273812 baseEnd_3273812 := by
    simpa [prefixWord, tailWord_3273812, baseEnd_3273812] using wordTrace_append hprefix tailTrace_3273812
  have hstable : (prefixWord ++ tailWord_3273812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273812).length < 2 ^ (prefixWord ++ tailWord_3273812).sum := by decide
  have hdescent : baseEnd_3273812 < baseStart_3273812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273831 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3273831 : Nat := 118140960795 + 3273831 * 2 ^ 59
def prefixEnd_3273831 : Nat := 4983230072969 + 3 ^ 40 * 3273831 * 2
def baseEnd_3273831 : Nat := 1120699256393123903237621

theorem tailTrace_3273831 : CollatzResearch.WordTrace tailWord_3273831 prefixEnd_3273831 1120699256393123903237621 := by
  unfold tailWord_3273831
  simp only [CollatzResearch.WordTrace]
  refine ⟨119406426202476887665629347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79604284134984591777086231 119406426202476887665629347)
  ·
    refine ⟨179109639303715331498444021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119406426202476887665629347 179109639303715331498444021)
    ·
      refine ⟨16791528684723312327979127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179109639303715331498444021 16791528684723312327979127)
      ·
        refine ⟨25187293027084968491968691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791528684723312327979127 25187293027084968491968691)
        ·
          refine ⟨37780939540627452737953037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25187293027084968491968691 37780939540627452737953037)
          ·
            refine ⟨14167852327735294776732389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37780939540627452737953037 14167852327735294776732389)
            ·
              refine ⟨2656472311450367770637323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14167852327735294776732389 2656472311450367770637323)
              ·
                refine ⟨3984708467175551655955985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656472311450367770637323 3984708467175551655955985)
                ·
                  refine ⟨2988531350381663741966989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3984708467175551655955985 2988531350381663741966989)
                  ·
                    refine ⟨1120699256393123903237621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988531350381663741966989 1120699256393123903237621)
                    ·
                      rfl

theorem cell22_3273831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3273831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273831 prefixEnd_3273831 := by exact prefixLift 3273831
  have htrace : WordTrace (prefixWord ++ tailWord_3273831) baseStart_3273831 baseEnd_3273831 := by
    simpa [prefixWord, tailWord_3273831, baseEnd_3273831] using wordTrace_append hprefix tailTrace_3273831
  have hstable : (prefixWord ++ tailWord_3273831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273831).length < 2 ^ (prefixWord ++ tailWord_3273831).sum := by decide
  have hdescent : baseEnd_3273831 < baseStart_3273831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274069 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 8]
def baseStart_3274069 : Nat := 118140960795 + 3274069 * 2 ^ 59
def prefixEnd_3274069 : Nat := 4983230072969 + 3 ^ 40 * 3274069 * 2
def baseEnd_3274069 : Nat := 373593576218990205262297

theorem tailTrace_3274069 : CollatzResearch.WordTrace tailWord_3274069 prefixEnd_3274069 373593576218990205262297 := by
  unfold tailWord_3274069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119415106775614654312793261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79610071183743102875195507 119415106775614654312793261)
  ·
    refine ⟨44780665040855495367297473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119415106775614654312793261 44780665040855495367297473)
    ·
      refine ⟨33585498780641621525473105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44780665040855495367297473 33585498780641621525473105)
      ·
        refine ⟨25189124085481216144104829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33585498780641621525473105 25189124085481216144104829)
        ·
          refine ⟨9445921532055456054039311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25189124085481216144104829 9445921532055456054039311)
          ·
            refine ⟨14168882298083184081058967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445921532055456054039311 14168882298083184081058967)
            ·
              refine ⟨21253323447124776121588451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14168882298083184081058967 21253323447124776121588451)
              ·
                refine ⟨31879985170687164182382677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21253323447124776121588451 31879985170687164182382677)
                ·
                  refine ⟨373593576218990205262297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31879985170687164182382677 373593576218990205262297)
                  ·
                    rfl

theorem cell22_3274069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_3274069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274069 prefixEnd_3274069 := by exact prefixLift 3274069
  have htrace : WordTrace (prefixWord ++ tailWord_3274069) baseStart_3274069 baseEnd_3274069 := by
    simpa [prefixWord, tailWord_3274069, baseEnd_3274069] using wordTrace_append hprefix tailTrace_3274069
  have hstable : (prefixWord ++ tailWord_3274069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274069).length < 2 ^ (prefixWord ++ tailWord_3274069).sum := by decide
  have hdescent : baseEnd_3274069 < baseStart_3274069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274088 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3274088 : Nat := 118140960795 + 3274088 * 2 ^ 59
def prefixEnd_3274088 : Nat := 4983230072969 + 3 ^ 40 * 3274088 * 2
def baseEnd_3274088 : Nat := 1120787232745260899561833

theorem tailTrace_3274088 : CollatzResearch.WordTrace tailWord_3274088 prefixEnd_3274088 1120787232745260899561833 := by
  unfold tailWord_3274088
  simp only [CollatzResearch.WordTrace]
  refine ⟨59707899881272910278867459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79610533175030547038489945 59707899881272910278867459)
  ·
    refine ⟨89561849821909365418301189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59707899881272910278867459 89561849821909365418301189)
    ·
      refine ⟨16792846841608006015931473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89561849821909365418301189 16792846841608006015931473)
      ·
        refine ⟨12594635131206004511948605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16792846841608006015931473 12594635131206004511948605)
        ·
          refine ⟨4722988174202251691980727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12594635131206004511948605 4722988174202251691980727)
          ·
            refine ⟨7084482261303377537971091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722988174202251691980727 7084482261303377537971091)
            ·
              refine ⟨10626723391955066306956637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084482261303377537971091 10626723391955066306956637)
              ·
                refine ⟨3985021271983149865108739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10626723391955066306956637 3985021271983149865108739)
                ·
                  refine ⟨5977531907974724797663109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985021271983149865108739 5977531907974724797663109)
                  ·
                    refine ⟨1120787232745260899561833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5977531907974724797663109 1120787232745260899561833)
                    ·
                      rfl

theorem cell22_3274088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3274088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274088 prefixEnd_3274088 := by exact prefixLift 3274088
  have htrace : WordTrace (prefixWord ++ tailWord_3274088) baseStart_3274088 baseEnd_3274088 := by
    simpa [prefixWord, tailWord_3274088, baseEnd_3274088] using wordTrace_append hprefix tailTrace_3274088
  have hstable : (prefixWord ++ tailWord_3274088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274088).length < 2 ^ (prefixWord ++ tailWord_3274088).sum := by decide
  have hdescent : baseEnd_3274088 < baseStart_3274088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274163 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 1, 3]
def baseStart_3274163 : Nat := 118140960795 + 3274163 * 2 ^ 59
def prefixEnd_3274163 : Nat := 4983230072969 + 3 ^ 40 * 3274163 * 2
def baseEnd_3274163 : Nat := 1120812906777985703936603

theorem tailTrace_3274163 : CollatzResearch.WordTrace tailWord_3274163 prefixEnd_3274163 1120812906777985703936603 := by
  unfold tailWord_3274163
  simp only [CollatzResearch.WordTrace]
  refine ⟨119418535237274108366715143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79612356824849405577810095 119418535237274108366715143)
  ·
    refine ⟨179127802855911162550072715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119418535237274108366715143 179127802855911162550072715)
    ·
      refine ⟨268691704283866743825109073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179127802855911162550072715 268691704283866743825109073)
      ·
        refine ⟨201518778212900057868831805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268691704283866743825109073 201518778212900057868831805)
        ·
          refine ⟨75569541829837521700811927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201518778212900057868831805 75569541829837521700811927)
          ·
            refine ⟨113354312744756282551217891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75569541829837521700811927 113354312744756282551217891)
            ·
              refine ⟨170031469117134423826826837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113354312744756282551217891 170031469117134423826826837)
              ·
                refine ⟨1992556278716419029220627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 170031469117134423826826837 1992556278716419029220627)
                ·
                  refine ⟨2988834418074628543830941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992556278716419029220627 2988834418074628543830941)
                  ·
                    refine ⟨1120812906777985703936603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988834418074628543830941 1120812906777985703936603)
                    ·
                      rfl

theorem cell22_3274163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 3].length) (baseStart_3274163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274163 prefixEnd_3274163 := by exact prefixLift 3274163
  have htrace : WordTrace (prefixWord ++ tailWord_3274163) baseStart_3274163 baseEnd_3274163 := by
    simpa [prefixWord, tailWord_3274163, baseEnd_3274163] using wordTrace_append hprefix tailTrace_3274163
  have hstable : (prefixWord ++ tailWord_3274163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274163).length < 2 ^ (prefixWord ++ tailWord_3274163).sum := by decide
  have hdescent : baseEnd_3274163 < baseStart_3274163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274236 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3274236 : Nat := 118140960795 + 3274236 * 2 ^ 59
def prefixEnd_3274236 : Nat := 4983230072969 + 3 ^ 40 * 3274236 * 2
def baseEnd_3274236 : Nat := 1120837896169837846861379

theorem tailTrace_3274236 : CollatzResearch.WordTrace tailWord_3274236 prefixEnd_3274236 1120837896169837846861379 := by
  unfold tailWord_3274236
  simp only [CollatzResearch.WordTrace]
  refine ⟨59710598883004820917061281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79614131844006427889415041 59710598883004820917061281)
  ·
    refine ⟨44782949162253615687795961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59710598883004820917061281 44782949162253615687795961)
    ·
      refine ⟨33587211871690211765846971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44782949162253615687795961 33587211871690211765846971)
      ·
        refine ⟨50380817807535317648770457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33587211871690211765846971 50380817807535317648770457)
        ·
          refine ⟨37785613355651488236577843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50380817807535317648770457 37785613355651488236577843)
          ·
            refine ⟨56678420033477232354866765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37785613355651488236577843 56678420033477232354866765)
            ·
              refine ⟨21254407512553962133075037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56678420033477232354866765 21254407512553962133075037)
              ·
                refine ⟨7970402817207735799903139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21254407512553962133075037 7970402817207735799903139)
                ·
                  refine ⟨11955604225811603699854709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970402817207735799903139 11955604225811603699854709)
                  ·
                    refine ⟨1120837896169837846861379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11955604225811603699854709 1120837896169837846861379)
                    ·
                      rfl

theorem cell22_3274236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3274236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274236 prefixEnd_3274236 := by exact prefixLift 3274236
  have htrace : WordTrace (prefixWord ++ tailWord_3274236) baseStart_3274236 baseEnd_3274236 := by
    simpa [prefixWord, tailWord_3274236, baseEnd_3274236] using wordTrace_append hprefix tailTrace_3274236
  have hstable : (prefixWord ++ tailWord_3274236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274236).length < 2 ^ (prefixWord ++ tailWord_3274236).sum := by decide
  have hdescent : baseEnd_3274236 < baseStart_3274236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274298 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_3274298 : Nat := 118140960795 + 3274298 * 2 ^ 59
def prefixEnd_3274298 : Nat := 4983230072969 + 3 ^ 40 * 3274298 * 2
def baseEnd_3274298 : Nat := 1120859120036890351811189

theorem tailTrace_3274298 : CollatzResearch.WordTrace tailWord_3274298 prefixEnd_3274298 1120859120036890351811189 := by
  unfold tailWord_3274298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855864772946256605719887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79615639394523350948586365 29855864772946256605719887)
  ·
    refine ⟨44783797159419384908579831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29855864772946256605719887 44783797159419384908579831)
    ·
      refine ⟨67175695739129077362869747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44783797159419384908579831 67175695739129077362869747)
      ·
        refine ⟨100763543608693616044304621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67175695739129077362869747 100763543608693616044304621)
        ·
          refine ⟨37786328853260106016614233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100763543608693616044304621 37786328853260106016614233)
          ·
            refine ⟨28339746639945079512460675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37786328853260106016614233 28339746639945079512460675)
            ·
              refine ⟨42509619959917619268691013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28339746639945079512460675 42509619959917619268691013)
              ·
                refine ⟨7970553742484553612879565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42509619959917619268691013 7970553742484553612879565)
                ·
                  refine ⟨2988957653431707604829837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7970553742484553612879565 2988957653431707604829837)
                  ·
                    refine ⟨1120859120036890351811189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988957653431707604829837 1120859120036890351811189)
                    ·
                      rfl

theorem cell22_3274298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_3274298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274298 prefixEnd_3274298 := by exact prefixLift 3274298
  have htrace : WordTrace (prefixWord ++ tailWord_3274298) baseStart_3274298 baseEnd_3274298 := by
    simpa [prefixWord, tailWord_3274298, baseEnd_3274298] using wordTrace_append hprefix tailTrace_3274298
  have hstable : (prefixWord ++ tailWord_3274298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274298).length < 2 ^ (prefixWord ++ tailWord_3274298).sum := by decide
  have hdescent : baseEnd_3274298 < baseStart_3274298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274300 : List Nat := [2, 2, 2, 2, 4, 2, 2, 6]
def baseStart_3274300 : Nat := 118140960795 + 3274300 * 2 ^ 59
def prefixEnd_3274300 : Nat := 4983230072969 + 3 ^ 40 * 3274300 * 2
def baseEnd_3274300 : Nat := 124539978297529223695687

theorem tailTrace_3274300 : CollatzResearch.WordTrace tailWord_3274300 prefixEnd_3274300 124539978297529223695687 := by
  unfold tailWord_3274300
  simp only [CollatzResearch.WordTrace]
  refine ⟨59711766018888890382226177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79615688025185187176301569 59711766018888890382226177)
  ·
    refine ⟨44783824514166667786669633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59711766018888890382226177 44783824514166667786669633)
    ·
      refine ⟨33587868385625000840002225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44783824514166667786669633 33587868385625000840002225)
      ·
        refine ⟨25190901289218750630001669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33587868385625000840002225 25190901289218750630001669)
        ·
          refine ⟨4723293991728515743125313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25190901289218750630001669 4723293991728515743125313)
          ·
            refine ⟨3542470493796386807343985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723293991728515743125313 3542470493796386807343985)
            ·
              refine ⟨2656852870347290105507989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542470493796386807343985 2656852870347290105507989)
              ·
                refine ⟨124539978297529223695687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656852870347290105507989 124539978297529223695687)
                ·
                  rfl

theorem cell22_3274300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_3274300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274300 prefixEnd_3274300 := by exact prefixLift 3274300
  have htrace : WordTrace (prefixWord ++ tailWord_3274300) baseStart_3274300 baseEnd_3274300 := by
    simpa [prefixWord, tailWord_3274300, baseEnd_3274300] using wordTrace_append hprefix tailTrace_3274300
  have hstable : (prefixWord ++ tailWord_3274300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274300).length < 2 ^ (prefixWord ++ tailWord_3274300).sum := by decide
  have hdescent : baseEnd_3274300 < baseStart_3274300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274332 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3274332 : Nat := 118140960795 + 3274332 * 2 ^ 59
def prefixEnd_3274332 : Nat := 4983230072969 + 3 ^ 40 * 3274332 * 2
def baseEnd_3274332 : Nat := 1120870758931725596461085

theorem tailTrace_3274332 : CollatzResearch.WordTrace tailWord_3274332 prefixEnd_3274332 1120870758931725596461085 := by
  unfold tailWord_3274332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59712349586830925114808625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79616466115774566819744833 59712349586830925114808625)
  ·
    refine ⟨44784262190123193836106469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59712349586830925114808625 44784262190123193836106469)
    ·
      refine ⟨8397049160648098844269963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44784262190123193836106469 8397049160648098844269963)
      ·
        refine ⟨12595573740972148266404945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397049160648098844269963 12595573740972148266404945)
        ·
          refine ⟨9446680305729111199803709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595573740972148266404945 9446680305729111199803709)
          ·
            refine ⟨3542505114648416699926391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9446680305729111199803709 3542505114648416699926391)
            ·
              refine ⟨5313757671972625049889587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542505114648416699926391 5313757671972625049889587)
              ·
                refine ⟨7970636507958937574834381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313757671972625049889587 7970636507958937574834381)
                ·
                  refine ⟨2988988690484601590562893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7970636507958937574834381 2988988690484601590562893)
                  ·
                    refine ⟨1120870758931725596461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2988988690484601590562893 1120870758931725596461085)
                    ·
                      rfl

theorem cell22_3274332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3274332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274332 prefixEnd_3274332 := by exact prefixLift 3274332
  have htrace : WordTrace (prefixWord ++ tailWord_3274332) baseStart_3274332 baseEnd_3274332 := by
    simpa [prefixWord, tailWord_3274332, baseEnd_3274332] using wordTrace_append hprefix tailTrace_3274332
  have hstable : (prefixWord ++ tailWord_3274332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274332).length < 2 ^ (prefixWord ++ tailWord_3274332).sum := by decide
  have hdescent : baseEnd_3274332 < baseStart_3274332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274405 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_3274405 : Nat := 118140960795 + 3274405 * 2 ^ 59
def prefixEnd_3274405 : Nat := 4983230072969 + 3 ^ 40 * 3274405 * 2
def baseEnd_3274405 : Nat := 1120895748323577739385861

theorem tailTrace_3274405 : CollatzResearch.WordTrace tailWord_3274405 prefixEnd_3274405 1120895748323577739385861 := by
  unfold tailWord_3274405
  simp only [CollatzResearch.WordTrace]
  refine ⟨119427361702397383697024669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79618241134931589131349779 119427361702397383697024669)
  ·
    refine ⟨44785260638399018886384251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119427361702397383697024669 44785260638399018886384251)
    ·
      refine ⟨67177890957598528329576377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44785260638399018886384251 67177890957598528329576377)
      ·
        refine ⟨50383418218198896247182283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67177890957598528329576377 50383418218198896247182283)
        ·
          refine ⟨75575127327298344370773425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50383418218198896247182283 75575127327298344370773425)
          ·
            refine ⟨56681345495473758278080069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75575127327298344370773425 56681345495473758278080069)
            ·
              refine ⟨10627752280401329677140013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56681345495473758278080069 10627752280401329677140013)
              ·
                refine ⟨3985407105150498628927505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10627752280401329677140013 3985407105150498628927505)
                ·
                  refine ⟨2989055328862873971695629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985407105150498628927505 2989055328862873971695629)
                  ·
                    refine ⟨1120895748323577739385861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989055328862873971695629 1120895748323577739385861)
                    ·
                      rfl

theorem cell22_3274405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_3274405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274405 prefixEnd_3274405 := by exact prefixLift 3274405
  have htrace : WordTrace (prefixWord ++ tailWord_3274405) baseStart_3274405 baseEnd_3274405 := by
    simpa [prefixWord, tailWord_3274405, baseEnd_3274405] using wordTrace_append hprefix tailTrace_3274405
  have hstable : (prefixWord ++ tailWord_3274405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274405).length < 2 ^ (prefixWord ++ tailWord_3274405).sum := by decide
  have hdescent : baseEnd_3274405 < baseStart_3274405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274422 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3274422 : Nat := 118140960795 + 3274422 * 2 ^ 59
def prefixEnd_3274422 : Nat := 4983230072969 + 3 ^ 40 * 3274422 * 2
def baseEnd_3274422 : Nat := 1120901567770995361710809

theorem tailTrace_3274422 : CollatzResearch.WordTrace tailWord_3274422 prefixEnd_3274422 1120901567770995361710809 := by
  unfold tailWord_3274422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464248858958487225024595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79618654495557197066929013 7464248858958487225024595)
  ·
    refine ⟨11196373288437730837536893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464248858958487225024595 11196373288437730837536893)
    ·
      refine ⟨4198639983164149064076335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11196373288437730837536893 4198639983164149064076335)
      ·
        refine ⟨6297959974746223596114503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198639983164149064076335 6297959974746223596114503)
        ·
          refine ⟨9446939962119335394171755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297959974746223596114503 9446939962119335394171755)
          ·
            refine ⟨14170409943179003091257633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446939962119335394171755 14170409943179003091257633)
            ·
              refine ⟨10627807457384252318443225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14170409943179003091257633 10627807457384252318443225)
              ·
                refine ⟨7970855593038189238832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10627807457384252318443225 7970855593038189238832419)
                ·
                  refine ⟨11956283389557283858248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970855593038189238832419 11956283389557283858248629)
                  ·
                    refine ⟨1120901567770995361710809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11956283389557283858248629 1120901567770995361710809)
                    ·
                      rfl

theorem cell22_3274422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3274422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274422 prefixEnd_3274422 := by exact prefixLift 3274422
  have htrace : WordTrace (prefixWord ++ tailWord_3274422) baseStart_3274422 baseEnd_3274422 := by
    simpa [prefixWord, tailWord_3274422, baseEnd_3274422] using wordTrace_append hprefix tailTrace_3274422
  have hstable : (prefixWord ++ tailWord_3274422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274422).length < 2 ^ (prefixWord ++ tailWord_3274422).sum := by decide
  have hdescent : baseEnd_3274422 < baseStart_3274422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274514 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_3274514 : Nat := 118140960795 + 3274514 * 2 ^ 59
def prefixEnd_3274514 : Nat := 4983230072969 + 3 ^ 40 * 3274514 * 2
def baseEnd_3274514 : Nat := 373644353750379262803509

theorem tailTrace_3274514 : CollatzResearch.WordTrace tailWord_3274514 prefixEnd_3274514 373644353750379262803509 := by
  unfold tailWord_3274514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29857834314750623828185649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79620891506001663541828397 29857834314750623828185649)
  ·
    refine ⟨22393375736062967871139237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29857834314750623828185649 22393375736062967871139237)
    ·
      refine ⟨4198757950511806475838607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22393375736062967871139237 4198757950511806475838607)
      ·
        refine ⟨6298136925767709713757911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198757950511806475838607 6298136925767709713757911)
        ·
          refine ⟨9447205388651564570636867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298136925767709713757911 9447205388651564570636867)
          ·
            refine ⟨14170808082977346855955301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447205388651564570636867 14170808082977346855955301)
            ·
              refine ⟨2657026515558252535491619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14170808082977346855955301 2657026515558252535491619)
              ·
                refine ⟨3985539773337378803237429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657026515558252535491619 3985539773337378803237429)
                ·
                  refine ⟨373644353750379262803509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3985539773337378803237429 373644353750379262803509)
                  ·
                    rfl

theorem cell22_3274514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_3274514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274514 prefixEnd_3274514 := by exact prefixLift 3274514
  have htrace : WordTrace (prefixWord ++ tailWord_3274514) baseStart_3274514 baseEnd_3274514 := by
    simpa [prefixWord, tailWord_3274514, baseEnd_3274514] using wordTrace_append hprefix tailTrace_3274514
  have hstable : (prefixWord ++ tailWord_3274514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274514).length < 2 ^ (prefixWord ++ tailWord_3274514).sum := by decide
  have hdescent : baseEnd_3274514 < baseStart_3274514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274540 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3274540 : Nat := 118140960795 + 3274540 * 2 ^ 59
def prefixEnd_3274540 : Nat := 4983230072969 + 3 ^ 40 * 3274540 * 2
def baseEnd_3274540 : Nat := 1120941961582482387260447

theorem tailTrace_3274540 : CollatzResearch.WordTrace tailWord_3274540 prefixEnd_3274540 1120941961582482387260447 := by
  unfold tailWord_3274540
  simp only [CollatzResearch.WordTrace]
  refine ⟨59716142778454150876594537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79621523704605534502126049 59716142778454150876594537)
  ·
    refine ⟨44787107083840613157445903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59716142778454150876594537 44787107083840613157445903)
    ·
      refine ⟨67180660625760919736168855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44787107083840613157445903 67180660625760919736168855)
      ·
        refine ⟨100770990938641379604253283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67180660625760919736168855 100770990938641379604253283)
        ·
          refine ⟨151156486407962069406379925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100770990938641379604253283 151156486407962069406379925)
          ·
            refine ⟨7085460300373222003424059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151156486407962069406379925 7085460300373222003424059)
            ·
              refine ⟨10628190450559833005136089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085460300373222003424059 10628190450559833005136089)
              ·
                refine ⟨7971142837919874753852067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10628190450559833005136089 7971142837919874753852067)
                ·
                  refine ⟨11956714256879812130778101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971142837919874753852067 11956714256879812130778101)
                  ·
                    refine ⟨1120941961582482387260447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11956714256879812130778101 1120941961582482387260447)
                    ·
                      rfl

theorem cell22_3274540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3274540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274540 prefixEnd_3274540 := by exact prefixLift 3274540
  have htrace : WordTrace (prefixWord ++ tailWord_3274540) baseStart_3274540 baseEnd_3274540 := by
    simpa [prefixWord, tailWord_3274540, baseEnd_3274540] using wordTrace_append hprefix tailTrace_3274540
  have hstable : (prefixWord ++ tailWord_3274540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274540).length < 2 ^ (prefixWord ++ tailWord_3274540).sum := by decide
  have hdescent : baseEnd_3274540 < baseStart_3274540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274670 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3274670 : Nat := 118140960795 + 3274670 * 2 ^ 59
def prefixEnd_3274670 : Nat := 4983230072969 + 3 ^ 40 * 3274670 * 2
def baseEnd_3274670 : Nat := 1120986463239205381510049

theorem tailTrace_3274670 : CollatzResearch.WordTrace tailWord_3274670 prefixEnd_3274670 1120986463239205381510049 := by
  unfold tailWord_3274670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929628380804666744427683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79624684697624889303614309 14929628380804666744427683)
  ·
    refine ⟨22394442571207000116641525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14929628380804666744427683 22394442571207000116641525)
    ·
      refine ⟨2099478991050656260935143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22394442571207000116641525 2099478991050656260935143)
      ·
        refine ⟨3149218486575984391402715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099478991050656260935143 3149218486575984391402715)
        ·
          refine ⟨4723827729863976587104073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149218486575984391402715 4723827729863976587104073)
          ·
            refine ⟨3542870797397982440328055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723827729863976587104073 3542870797397982440328055)
            ·
              refine ⟨5314306196096973660492083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542870797397982440328055 5314306196096973660492083)
              ·
                refine ⟨7971459294145460490738125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314306196096973660492083 7971459294145460490738125)
                ·
                  refine ⟨2989297235304547684026797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7971459294145460490738125 2989297235304547684026797)
                  ·
                    refine ⟨1120986463239205381510049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989297235304547684026797 1120986463239205381510049)
                    ·
                      rfl

theorem cell22_3274670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3274670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274670 prefixEnd_3274670 := by exact prefixLift 3274670
  have htrace : WordTrace (prefixWord ++ tailWord_3274670) baseStart_3274670 baseEnd_3274670 := by
    simpa [prefixWord, tailWord_3274670, baseEnd_3274670] using wordTrace_append hprefix tailTrace_3274670
  have hstable : (prefixWord ++ tailWord_3274670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274670).length < 2 ^ (prefixWord ++ tailWord_3274670).sum := by decide
  have hdescent : baseEnd_3274670 < baseStart_3274670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274677 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3274677 : Nat := 118140960795 + 3274677 * 2 ^ 59
def prefixEnd_3274677 : Nat := 4983230072969 + 3 ^ 40 * 3274677 * 2
def baseEnd_3274677 : Nat := 373662953160753232195009

theorem tailTrace_3274677 : CollatzResearch.WordTrace tailWord_3274677 prefixEnd_3274677 373662953160753232195009 := by
  unfold tailWord_3274677
  simp only [CollatzResearch.WordTrace]
  refine ⟨119437282357411974150926285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79624854904941316100617523 119437282357411974150926285)
  ·
    refine ⟨44788980884029490306597357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119437282357411974150926285 44788980884029490306597357)
    ·
      refine ⟨16795867831511058864974009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44788980884029490306597357 16795867831511058864974009)
      ·
        refine ⟨12596900873633294148730507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16795867831511058864974009 12596900873633294148730507)
        ·
          refine ⟨18895351310449941223095761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12596900873633294148730507 18895351310449941223095761)
          ·
            refine ⟨14171513482837455917321821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18895351310449941223095761 14171513482837455917321821)
            ·
              refine ⟨5314317556064045968995683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14171513482837455917321821 5314317556064045968995683)
              ·
                refine ⟨7971476334096068953493525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314317556064045968995683 7971476334096068953493525)
                ·
                  refine ⟨373662953160753232195009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7971476334096068953493525 373662953160753232195009)
                  ·
                    rfl

theorem cell22_3274677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3274677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274677 prefixEnd_3274677 := by exact prefixLift 3274677
  have htrace : WordTrace (prefixWord ++ tailWord_3274677) baseStart_3274677 baseEnd_3274677 := by
    simpa [prefixWord, tailWord_3274677, baseEnd_3274677] using wordTrace_append hprefix tailTrace_3274677
  have hstable : (prefixWord ++ tailWord_3274677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274677).length < 2 ^ (prefixWord ++ tailWord_3274677).sum := by decide
  have hdescent : baseEnd_3274677 < baseStart_3274677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274722 : List Nat := [3, 3, 3, 1, 12]
def baseStart_3274722 : Nat := 118140960795 + 3274722 * 2 ^ 59
def prefixEnd_3274722 : Nat := 4983230072969 + 3 ^ 40 * 3274722 * 2
def baseEnd_3274722 : Nat := 4613186271201212260123

theorem tailTrace_3274722 : CollatzResearch.WordTrace tailWord_3274722 prefixEnd_3274722 4613186271201212260123 := by
  unfold tailWord_3274722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859730910562236709078605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79625949094832631224209613 29859730910562236709078605)
  ·
    refine ⟨11197399091460838765904477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29859730910562236709078605 11197399091460838765904477)
    ·
      refine ⟨4199024659297814537214179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11197399091460838765904477 4199024659297814537214179)
      ·
        refine ⟨6298536988946721805821269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199024659297814537214179 6298536988946721805821269)
        ·
          refine ⟨4613186271201212260123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6298536988946721805821269 4613186271201212260123)
          ·
            rfl

theorem cell22_3274722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 12].length) (baseStart_3274722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274722 prefixEnd_3274722 := by exact prefixLift 3274722
  have htrace : WordTrace (prefixWord ++ tailWord_3274722) baseStart_3274722 baseEnd_3274722 := by
    simpa [prefixWord, tailWord_3274722, baseEnd_3274722] using wordTrace_append hprefix tailTrace_3274722
  have hstable : (prefixWord ++ tailWord_3274722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274722).length < 2 ^ (prefixWord ++ tailWord_3274722).sum := by decide
  have hdescent : baseEnd_3274722 < baseStart_3274722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274735 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_3274735 : Nat := 118140960795 + 3274735 * 2 ^ 59
def prefixEnd_3274735 : Nat := 4983230072969 + 3 ^ 40 * 3274735 * 2
def baseEnd_3274735 : Nat := 1121008714067566878634849

theorem tailTrace_3274735 : CollatzResearch.WordTrace tailWord_3274735 prefixEnd_3274735 1121008714067566878634849 := by
  unfold tailWord_3274735
  simp only [CollatzResearch.WordTrace]
  refine ⟨119439397791201850056537659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79626265194134566704358439 119439397791201850056537659)
  ·
    refine ⟨179159096686802775084806489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119439397791201850056537659 179159096686802775084806489)
    ·
      refine ⟨134369322515102081313604867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179159096686802775084806489 134369322515102081313604867)
      ·
        refine ⟨201553983772653121970407301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134369322515102081313604867 201553983772653121970407301)
        ·
          refine ⟨37791371957372460369451369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201553983772653121970407301 37791371957372460369451369)
          ·
            refine ⟨28343528968029345277088527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37791371957372460369451369 28343528968029345277088527)
            ·
              refine ⟨42515293452044017915632791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28343528968029345277088527 42515293452044017915632791)
              ·
                refine ⟨63772940178066026873449187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42515293452044017915632791 63772940178066026873449187)
                ·
                  refine ⟨95659410267099040310173781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63772940178066026873449187 95659410267099040310173781)
                  ·
                    refine ⟨1121008714067566878634849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95659410267099040310173781 1121008714067566878634849)
                    ·
                      rfl

theorem cell22_3274735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_3274735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274735 prefixEnd_3274735 := by exact prefixLift 3274735
  have htrace : WordTrace (prefixWord ++ tailWord_3274735) baseStart_3274735 baseEnd_3274735 := by
    simpa [prefixWord, tailWord_3274735, baseEnd_3274735] using wordTrace_append hprefix tailTrace_3274735
  have hstable : (prefixWord ++ tailWord_3274735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274735).length < 2 ^ (prefixWord ++ tailWord_3274735).sum := by decide
  have hdescent : baseEnd_3274735 < baseStart_3274735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274756 : List Nat := [2, 3, 2, 4, 1, 1, 3, 6]
def baseStart_3274756 : Nat := 118140960795 + 3274756 * 2 ^ 59
def prefixEnd_3274756 : Nat := 4983230072969 + 3 ^ 40 * 3274756 * 2
def baseEnd_3274756 : Nat := 124557322532969980428865

theorem tailTrace_3274756 : CollatzResearch.WordTrace tailWord_3274756 prefixEnd_3274756 124557322532969980428865 := by
  unfold tailWord_3274756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59720081862062885321526061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79626775816083847095368081 59720081862062885321526061)
  ·
    refine ⟨22395030698273581995572273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59720081862062885321526061 22395030698273581995572273)
    ·
      refine ⟨16796273023705186496679205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22395030698273581995572273 16796273023705186496679205)
      ·
        refine ⟨3149301191944722468127351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16796273023705186496679205 3149301191944722468127351)
        ·
          refine ⟨4723951787917083702191027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149301191944722468127351 4723951787917083702191027)
          ·
            refine ⟨7085927681875625553286541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723951787917083702191027 7085927681875625553286541)
            ·
              refine ⟨2657222880703359582482453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085927681875625553286541 2657222880703359582482453)
              ·
                refine ⟨124557322532969980428865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2657222880703359582482453 124557322532969980428865)
                ·
                  rfl

theorem cell22_3274756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_3274756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274756 prefixEnd_3274756 := by exact prefixLift 3274756
  have htrace : WordTrace (prefixWord ++ tailWord_3274756) baseStart_3274756 baseEnd_3274756 := by
    simpa [prefixWord, tailWord_3274756, baseEnd_3274756] using wordTrace_append hprefix tailTrace_3274756
  have hstable : (prefixWord ++ tailWord_3274756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274756).length < 2 ^ (prefixWord ++ tailWord_3274756).sum := by decide
  have hdescent : baseEnd_3274756 < baseStart_3274756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274812 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_3274812 : Nat := 118140960795 + 3274812 * 2 ^ 59
def prefixEnd_3274812 : Nat := 4983230072969 + 3 ^ 40 * 3274812 * 2
def baseEnd_3274812 : Nat := 373678357580388114819871

theorem tailTrace_3274812 : CollatzResearch.WordTrace tailWord_3274812 prefixEnd_3274812 373678357580388114819871 := by
  unfold tailWord_3274812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59721103105961446103545345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79628137474615261471393793 59721103105961446103545345)
  ·
    refine ⟨44790827329471084577659009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59721103105961446103545345 44790827329471084577659009)
    ·
      refine ⟨33593120497103313433244257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44790827329471084577659009 33593120497103313433244257)
      ·
        refine ⟨25194840372827485074933193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33593120497103313433244257 25194840372827485074933193)
        ·
          refine ⟨18896130279620613806199895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25194840372827485074933193 18896130279620613806199895)
          ·
            refine ⟨28344195419430920709299843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896130279620613806199895 28344195419430920709299843)
            ·
              refine ⟨42516293129146381063949765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28344195419430920709299843 42516293129146381063949765)
              ·
                refine ⟨7971804961714946449490581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42516293129146381063949765 7971804961714946449490581)
                ·
                  refine ⟨373678357580388114819871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7971804961714946449490581 373678357580388114819871)
                  ·
                    rfl

theorem cell22_3274812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_3274812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274812 prefixEnd_3274812 := by exact prefixLift 3274812
  have htrace : WordTrace (prefixWord ++ tailWord_3274812) baseStart_3274812 baseEnd_3274812 := by
    simpa [prefixWord, tailWord_3274812, baseEnd_3274812] using wordTrace_append hprefix tailTrace_3274812
  have hstable : (prefixWord ++ tailWord_3274812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274812).length < 2 ^ (prefixWord ++ tailWord_3274812).sum := by decide
  have hdescent : baseEnd_3274812 < baseStart_3274812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274857 : List Nat := [1, 2, 1, 1, 1, 5, 4, 7]
def baseStart_3274857 : Nat := 118140960795 + 3274857 * 2 ^ 59
def prefixEnd_3274857 : Nat := 4983230072969 + 3 ^ 40 * 3274857 * 2
def baseEnd_3274857 : Nat := 124561164128977691898275

theorem tailTrace_3274857 : CollatzResearch.WordTrace tailWord_3274857 prefixEnd_3274857 124561164128977691898275 := by
  unfold tailWord_3274857
  simp only [CollatzResearch.WordTrace]
  refine ⟨119443847496759864892478825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79629231664506576594985883 119443847496759864892478825)
  ·
    refine ⟨89582885622569898669359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119443847496759864892478825 89582885622569898669359119)
    ·
      refine ⟨134374328433854848004038679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89582885622569898669359119 134374328433854848004038679)
      ·
        refine ⟨201561492650782272006058019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134374328433854848004038679 201561492650782272006058019)
        ·
          refine ⟨302342238976173408009087029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201561492650782272006058019 302342238976173408009087029)
          ·
            refine ⟨28344584904016257000851909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302342238976173408009087029 28344584904016257000851909)
            ·
              refine ⟨5314609669503048187659733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28344584904016257000851909 5314609669503048187659733)
              ·
                refine ⟨124561164128977691898275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5314609669503048187659733 124561164128977691898275)
                ·
                  rfl

theorem cell22_3274857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 7].length) (baseStart_3274857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274857 prefixEnd_3274857 := by exact prefixLift 3274857
  have htrace : WordTrace (prefixWord ++ tailWord_3274857) baseStart_3274857 baseEnd_3274857 := by
    simpa [prefixWord, tailWord_3274857, baseEnd_3274857] using wordTrace_append hprefix tailTrace_3274857
  have hstable : (prefixWord ++ tailWord_3274857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274857).length < 2 ^ (prefixWord ++ tailWord_3274857).sum := by decide
  have hdescent : baseEnd_3274857 < baseStart_3274857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274861 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3274861 : Nat := 118140960795 + 3274861 * 2 ^ 59
def prefixEnd_3274861 : Nat := 4983230072969 + 3 ^ 40 * 3274861 * 2
def baseEnd_3274861 : Nat := 1121051846442544549984463

theorem tailTrace_3274861 : CollatzResearch.WordTrace tailWord_3274861 prefixEnd_3274861 1121051846442544549984463 := by
  unfold tailWord_3274861
  simp only [CollatzResearch.WordTrace]
  refine ⟨119443993388745373575624437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79629328925830249050416291 119443993388745373575624437)
  ·
    refine ⟨11197874380194878772714791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119443993388745373575624437 11197874380194878772714791)
    ·
      refine ⟨16796811570292318159072187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197874380194878772714791 16796811570292318159072187)
      ·
        refine ⟨25195217355438477238608281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16796811570292318159072187 25195217355438477238608281)
        ·
          refine ⟨18896413016578857928956211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25195217355438477238608281 18896413016578857928956211)
          ·
            refine ⟨28344619524868286893434317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896413016578857928956211 28344619524868286893434317)
            ·
              refine ⟨10629232321825607585037869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28344619524868286893434317 10629232321825607585037869)
              ·
                refine ⟨3985962120684602844389201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10629232321825607585037869 3985962120684602844389201)
                ·
                  refine ⟨2989471590513452133291901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985962120684602844389201 2989471590513452133291901)
                  ·
                    refine ⟨1121051846442544549984463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989471590513452133291901 1121051846442544549984463)
                    ·
                      rfl

theorem cell22_3274861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3274861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274861 prefixEnd_3274861 := by exact prefixLift 3274861
  have htrace : WordTrace (prefixWord ++ tailWord_3274861) baseStart_3274861 baseEnd_3274861 := by
    simpa [prefixWord, tailWord_3274861, baseEnd_3274861] using wordTrace_append hprefix tailTrace_3274861
  have hstable : (prefixWord ++ tailWord_3274861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274861).length < 2 ^ (prefixWord ++ tailWord_3274861).sum := by decide
  have hdescent : baseEnd_3274861 < baseStart_3274861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274940 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3274940 : Nat := 118140960795 + 3274940 * 2 ^ 59
def prefixEnd_3274940 : Nat := 4983230072969 + 3 ^ 40 * 3274940 * 2
def baseEnd_3274940 : Nat := 1121078889757014677259221

theorem tailTrace_3274940 : CollatzResearch.WordTrace tailWord_3274940 prefixEnd_3274940 1121078889757014677259221 := by
  unfold tailWord_3274940
  simp only [CollatzResearch.WordTrace]
  refine ⟨59723437377729585033875137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79631249836972780045166849 59723437377729585033875137)
  ·
    refine ⟨44792578033297188775406353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59723437377729585033875137 44792578033297188775406353)
    ·
      refine ⟨33594433524972891581554765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44792578033297188775406353 33594433524972891581554765)
      ·
        refine ⟨12597912571864834343083037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33594433524972891581554765 12597912571864834343083037)
        ·
          refine ⟨4724217214449312878656139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12597912571864834343083037 4724217214449312878656139)
          ·
            refine ⟨7086325821673969317984209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724217214449312878656139 7086325821673969317984209)
            ·
              refine ⟨5314744366255476988488157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7086325821673969317984209 5314744366255476988488157)
              ·
                refine ⟨1993029137345803870683059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5314744366255476988488157 1993029137345803870683059)
                ·
                  refine ⟨2989543706018705806024589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993029137345803870683059 2989543706018705806024589)
                  ·
                    refine ⟨1121078889757014677259221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989543706018705806024589 1121078889757014677259221)
                    ·
                      rfl

theorem cell22_3274940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3274940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274940 prefixEnd_3274940 := by exact prefixLift 3274940
  have htrace : WordTrace (prefixWord ++ tailWord_3274940) baseStart_3274940 baseEnd_3274940 := by
    simpa [prefixWord, tailWord_3274940, baseEnd_3274940] using wordTrace_append hprefix tailTrace_3274940
  have hstable : (prefixWord ++ tailWord_3274940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274940).length < 2 ^ (prefixWord ++ tailWord_3274940).sum := by decide
  have hdescent : baseEnd_3274940 < baseStart_3274940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274983 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3274983 : Nat := 118140960795 + 3274983 * 2 ^ 59
def prefixEnd_3274983 : Nat := 4983230072969 + 3 ^ 40 * 3274983 * 2
def baseEnd_3274983 : Nat := 1121093609535776898434089

theorem tailTrace_3274983 : CollatzResearch.WordTrace tailWord_3274983 prefixEnd_3274983 1121093609535776898434089 := by
  unfold tailWord_3274983
  simp only [CollatzResearch.WordTrace]
  refine ⟨119448443094303388411565603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79632295396202258941043735 119448443094303388411565603)
  ·
    refine ⟨179172664641455082617348405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119448443094303388411565603 179172664641455082617348405)
    ·
      refine ⟨16797437310136413995376413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179172664641455082617348405 16797437310136413995376413)
      ·
        refine ⟨6299038991301155248266155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16797437310136413995376413 6299038991301155248266155)
        ·
          refine ⟨9448558486951732872399233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299038991301155248266155 9448558486951732872399233)
          ·
            refine ⟨7086418865213799654299425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9448558486951732872399233 7086418865213799654299425)
            ·
              refine ⟨5314814148910349740724569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7086418865213799654299425 5314814148910349740724569)
              ·
                refine ⟨3986110611682762305543427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314814148910349740724569 3986110611682762305543427)
                ·
                  refine ⟨5979165917524143458315141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986110611682762305543427 5979165917524143458315141)
                  ·
                    refine ⟨1121093609535776898434089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5979165917524143458315141 1121093609535776898434089)
                    ·
                      rfl

theorem cell22_3274983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3274983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274983 prefixEnd_3274983 := by exact prefixLift 3274983
  have htrace : WordTrace (prefixWord ++ tailWord_3274983) baseStart_3274983 baseEnd_3274983 := by
    simpa [prefixWord, tailWord_3274983, baseEnd_3274983] using wordTrace_append hprefix tailTrace_3274983
  have hstable : (prefixWord ++ tailWord_3274983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274983).length < 2 ^ (prefixWord ++ tailWord_3274983).sum := by decide
  have hdescent : baseEnd_3274983 < baseStart_3274983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274998 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_3274998 : Nat := 118140960795 + 3274998 * 2 ^ 59
def prefixEnd_3274998 : Nat := 4983230072969 + 3 ^ 40 * 3274998 * 2
def baseEnd_3274998 : Nat := 373699581447440619769681

theorem tailTrace_3274998 : CollatzResearch.WordTrace tailWord_3274998 prefixEnd_3274998 373699581447440619769681 := by
  unfold tailWord_3274998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465561886828065373335103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79632660126166030648907765 7465561886828065373335103)
  ·
    refine ⟨11198342830242098060002655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7465561886828065373335103 11198342830242098060002655)
    ·
      refine ⟨16797514245363147090003983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198342830242098060002655 16797514245363147090003983)
      ·
        refine ⟨25196271368044720635005975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16797514245363147090003983 25196271368044720635005975)
        ·
          refine ⟨37794407052067080952508963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25196271368044720635005975 37794407052067080952508963)
          ·
            refine ⟨56691610578100621428763445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37794407052067080952508963 56691610578100621428763445)
            ·
              refine ⟨5314838491696933258946573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56691610578100621428763445 5314838491696933258946573)
              ·
                refine ⟨1993064434386349972104965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5314838491696933258946573 1993064434386349972104965)
                ·
                  refine ⟨373699581447440619769681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993064434386349972104965 373699581447440619769681)
                  ·
                    rfl

theorem cell22_3274998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_3274998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3274998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3274998 prefixEnd_3274998 := by exact prefixLift 3274998
  have htrace : WordTrace (prefixWord ++ tailWord_3274998) baseStart_3274998 baseEnd_3274998 := by
    simpa [prefixWord, tailWord_3274998, baseEnd_3274998] using wordTrace_append hprefix tailTrace_3274998
  have hstable : (prefixWord ++ tailWord_3274998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274998).length < 2 ^ (prefixWord ++ tailWord_3274998).sum := by decide
  have hdescent : baseEnd_3274998 < baseStart_3274998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275015 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 6]
def baseStart_3275015 : Nat := 118140960795 + 3275015 * 2 ^ 59
def prefixEnd_3275015 : Nat := 4983230072969 + 3 ^ 40 * 3275015 * 2
def baseEnd_3275015 : Nat := 373701521263246493877997

theorem tailTrace_3275015 : CollatzResearch.WordTrace tailWord_3275015 prefixEnd_3275015 373701521263246493877997 := by
  unfold tailWord_3275015
  simp only [CollatzResearch.WordTrace]
  refine ⟨119449610230187457876730499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79633073486791638584486999 119449610230187457876730499)
  ·
    refine ⟨179174415345281186815095749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119449610230187457876730499 179174415345281186815095749)
    ·
      refine ⟨33595202877240222527830453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179174415345281186815095749 33595202877240222527830453)
      ·
        refine ⟨3149550269741270861984105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33595202877240222527830453 3149550269741270861984105)
        ·
          refine ⟨2362162702305953146488079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149550269741270861984105 2362162702305953146488079)
          ·
            refine ⟨3543244053458929719732119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362162702305953146488079 3543244053458929719732119)
            ·
              refine ⟨5314866080188394579598179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543244053458929719732119 5314866080188394579598179)
              ·
                refine ⟨7972299120282591869397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314866080188394579598179 7972299120282591869397269)
                ·
                  refine ⟨373701521263246493877997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7972299120282591869397269 373701521263246493877997)
                  ·
                    rfl

theorem cell22_3275015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 6].length) (baseStart_3275015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275015 prefixEnd_3275015 := by exact prefixLift 3275015
  have htrace : WordTrace (prefixWord ++ tailWord_3275015) baseStart_3275015 baseEnd_3275015 := by
    simpa [prefixWord, tailWord_3275015, baseEnd_3275015] using wordTrace_append hprefix tailTrace_3275015
  have hstable : (prefixWord ++ tailWord_3275015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275015).length < 2 ^ (prefixWord ++ tailWord_3275015).sum := by decide
  have hdescent : baseEnd_3275015 < baseStart_3275015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275041 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3275041 : Nat := 118140960795 + 3275041 * 2 ^ 59
def prefixEnd_3275041 : Nat := 4983230072969 + 3 ^ 40 * 3275041 * 2
def baseEnd_3275041 : Nat := 1121113464121084080483911

theorem tailTrace_3275041 : CollatzResearch.WordTrace tailWord_3275041 prefixEnd_3275041 1121113464121084080483911 := by
  unfold tailWord_3275041
  simp only [CollatzResearch.WordTrace]
  refine ⟨119450558528093264317176977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79633705685395509544784651 119450558528093264317176977)
  ·
    refine ⟨89587918896069948237882733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119450558528093264317176977 89587918896069948237882733)
    ·
      refine ⟨33595469586026230589206025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89587918896069948237882733 33595469586026230589206025)
      ·
        refine ⟨25196602189519672941904519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33595469586026230589206025 25196602189519672941904519)
        ·
          refine ⟨37794903284279509412856779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25196602189519672941904519 37794903284279509412856779)
          ·
            refine ⟨56692354926419264119285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37794903284279509412856779 56692354926419264119285169)
            ·
              refine ⟨42519266194814448089463877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56692354926419264119285169 42519266194814448089463877)
              ·
                refine ⟨7972362411527709016774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42519266194814448089463877 7972362411527709016774477)
                ·
                  refine ⟨2989635904322890881290429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7972362411527709016774477 2989635904322890881290429)
                  ·
                    refine ⟨1121113464121084080483911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989635904322890881290429 1121113464121084080483911)
                    ·
                      rfl

theorem cell22_3275041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3275041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275041 prefixEnd_3275041 := by exact prefixLift 3275041
  have htrace : WordTrace (prefixWord ++ tailWord_3275041) baseStart_3275041 baseEnd_3275041 := by
    simpa [prefixWord, tailWord_3275041, baseEnd_3275041] using wordTrace_append hprefix tailTrace_3275041
  have hstable : (prefixWord ++ tailWord_3275041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275041).length < 2 ^ (prefixWord ++ tailWord_3275041).sum := by decide
  have hdescent : baseEnd_3275041 < baseStart_3275041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275071 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 5]
def baseStart_3275071 : Nat := 118140960795 + 3275071 * 2 ^ 59
def prefixEnd_3275071 : Nat := 4983230072969 + 3 ^ 40 * 3275071 * 2
def baseEnd_3275071 : Nat := 373707911244724667411273

theorem tailTrace_3275071 : CollatzResearch.WordTrace tailWord_3275071 prefixEnd_3275071 373707911244724667411273 := by
  unfold tailWord_3275071
  simp only [CollatzResearch.WordTrace]
  refine ⟨119451652717984579440769067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79634435145323052960512711 119451652717984579440769067)
  ·
    refine ⟨179177479076976869161153601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119451652717984579440769067 179177479076976869161153601)
    ·
      refine ⟨134383109307732651870865201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179177479076976869161153601 134383109307732651870865201)
      ·
        refine ⟨100787331980799488903148901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134383109307732651870865201 100787331980799488903148901)
        ·
          refine ⟨18897624746399904169340419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100787331980799488903148901 18897624746399904169340419)
          ·
            refine ⟨28346437119599856254010629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18897624746399904169340419 28346437119599856254010629)
            ·
              refine ⟨5314956959924973047626993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28346437119599856254010629 5314956959924973047626993)
              ·
                refine ⟨3986217719943729785720245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314956959924973047626993 3986217719943729785720245)
                ·
                  refine ⟨373707911244724667411273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986217719943729785720245 373707911244724667411273)
                  ·
                    rfl

theorem cell22_3275071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].length) (baseStart_3275071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275071 prefixEnd_3275071 := by exact prefixLift 3275071
  have htrace : WordTrace (prefixWord ++ tailWord_3275071) baseStart_3275071 baseEnd_3275071 := by
    simpa [prefixWord, tailWord_3275071, baseEnd_3275071] using wordTrace_append hprefix tailTrace_3275071
  have hstable : (prefixWord ++ tailWord_3275071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275071).length < 2 ^ (prefixWord ++ tailWord_3275071).sum := by decide
  have hdescent : baseEnd_3275071 < baseStart_3275071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275075 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 1, 3]
def baseStart_3275075 : Nat := 118140960795 + 3275075 * 2 ^ 59
def prefixEnd_3275075 : Nat := 4983230072969 + 3 ^ 40 * 3275075 * 2
def baseEnd_3275075 : Nat := 1121125103015919325133807

theorem tailTrace_3275075 : CollatzResearch.WordTrace tailWord_3275075 prefixEnd_3275075 1121125103015919325133807 := by
  unfold tailWord_3275075
  simp only [CollatzResearch.WordTrace]
  refine ⟨119451798609970088123914679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79634532406646725415943119 119451798609970088123914679)
  ·
    refine ⟨179177697914955132185872019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119451798609970088123914679 179177697914955132185872019)
    ·
      refine ⟨268766546872432698278808029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179177697914955132185872019 268766546872432698278808029)
      ·
        refine ⟨100787455077162261854553011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268766546872432698278808029 100787455077162261854553011)
        ·
          refine ⟨151181182615743392781829517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100787455077162261854553011 151181182615743392781829517)
          ·
            refine ⟨56692943480903772293186069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151181182615743392781829517 56692943480903772293186069)
            ·
              refine ⟨2657481725667364326243097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56692943480903772293186069 2657481725667364326243097)
              ·
                refine ⟨1993111294250523244682323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657481725667364326243097 1993111294250523244682323)
                ·
                  refine ⟨2989666941375784867023485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993111294250523244682323 2989666941375784867023485)
                  ·
                    refine ⟨1121125103015919325133807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989666941375784867023485 1121125103015919325133807)
                    ·
                      rfl

theorem cell22_3275075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 3].length) (baseStart_3275075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275075 prefixEnd_3275075 := by exact prefixLift 3275075
  have htrace : WordTrace (prefixWord ++ tailWord_3275075) baseStart_3275075 baseEnd_3275075 := by
    simpa [prefixWord, tailWord_3275075, baseEnd_3275075] using wordTrace_append hprefix tailTrace_3275075
  have hstable : (prefixWord ++ tailWord_3275075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275075).length < 2 ^ (prefixWord ++ tailWord_3275075).sum := by decide
  have hdescent : baseEnd_3275075 < baseStart_3275075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275133 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3275133 : Nat := 118140960795 + 3275133 * 2 ^ 59
def prefixEnd_3275133 : Nat := 4983230072969 + 3 ^ 40 * 3275133 * 2
def baseEnd_3275133 : Nat := 373714985867075502394543

theorem tailTrace_3275133 : CollatzResearch.WordTrace tailWord_3275133 prefixEnd_3275133 373714985867075502394543 := by
  unfold tailWord_3275133
  simp only [CollatzResearch.WordTrace]
  refine ⟨119453914043759964029526053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79635942695839976019684035 119453914043759964029526053)
  ·
    refine ⟨22397608883204993255536135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119453914043759964029526053 22397608883204993255536135)
    ·
      refine ⟨33596413324807489883304203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22397608883204993255536135 33596413324807489883304203)
      ·
        refine ⟨50394619987211234824956305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33596413324807489883304203 50394619987211234824956305)
        ·
          refine ⟨37795964990408426118717229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50394619987211234824956305 37795964990408426118717229)
          ·
            refine ⟨14173486871403159794518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37795964990408426118717229 14173486871403159794518961)
            ·
              refine ⟨10630115153552369845889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14173486871403159794518961 10630115153552369845889221)
              ·
                refine ⟨1993146591291069346104229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10630115153552369845889221 1993146591291069346104229)
                ·
                  refine ⟨373714985867075502394543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993146591291069346104229 373714985867075502394543)
                  ·
                    rfl

theorem cell22_3275133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3275133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275133 prefixEnd_3275133 := by exact prefixLift 3275133
  have htrace : WordTrace (prefixWord ++ tailWord_3275133) baseStart_3275133 baseEnd_3275133 := by
    simpa [prefixWord, tailWord_3275133, baseEnd_3275133] using wordTrace_append hprefix tailTrace_3275133
  have hstable : (prefixWord ++ tailWord_3275133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275133).length < 2 ^ (prefixWord ++ tailWord_3275133).sum := by decide
  have hdescent : baseEnd_3275133 < baseStart_3275133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275148 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_3275148 : Nat := 118140960795 + 3275148 * 2 ^ 59
def prefixEnd_3275148 : Nat := 4983230072969 + 3 ^ 40 * 3275148 * 2
def baseEnd_3275148 : Nat := 1121150092407771468058583

theorem tailTrace_3275148 : CollatzResearch.WordTrace tailWord_3275148 prefixEnd_3275148 1121150092407771468058583 := by
  unfold tailWord_3275148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59727230569352810795661049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79636307425803747727548065 59727230569352810795661049)
  ·
    refine ⟨44795422927014608096745787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59727230569352810795661049 44795422927014608096745787)
    ·
      refine ⟨67193134390521912145118681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44795422927014608096745787 67193134390521912145118681)
      ·
        refine ⟨50394850792891434108839011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67193134390521912145118681 50394850792891434108839011)
        ·
          refine ⟨75592276189337151163258517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50394850792891434108839011 75592276189337151163258517)
          ·
            refine ⟨3543387946375178960777743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75592276189337151163258517 3543387946375178960777743)
            ·
              refine ⟨5315081919562768441166615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543387946375178960777743 5315081919562768441166615)
              ·
                refine ⟨7972622879344152661749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315081919562768441166615 7972622879344152661749923)
                ·
                  refine ⟨11958934319016228992624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972622879344152661749923 11958934319016228992624885)
                  ·
                    refine ⟨1121150092407771468058583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11958934319016228992624885 1121150092407771468058583)
                    ·
                      rfl

theorem cell22_3275148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_3275148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275148 prefixEnd_3275148 := by exact prefixLift 3275148
  have htrace : WordTrace (prefixWord ++ tailWord_3275148) baseStart_3275148 baseEnd_3275148 := by
    simpa [prefixWord, tailWord_3275148, baseEnd_3275148] using wordTrace_append hprefix tailTrace_3275148
  have hstable : (prefixWord ++ tailWord_3275148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275148).length < 2 ^ (prefixWord ++ tailWord_3275148).sum := by decide
  have hdescent : baseEnd_3275148 < baseStart_3275148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275251 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 6]
def baseStart_3275251 : Nat := 118140960795 + 3275251 * 2 ^ 59
def prefixEnd_3275251 : Nat := 4983230072969 + 3 ^ 40 * 3275251 * 2
def baseEnd_3275251 : Nat := 373728450470904510911089

theorem tailTrace_3275251 : CollatzResearch.WordTrace tailWord_3275251 prefixEnd_3275251 373728450470904510911089 := by
  unfold tailWord_3275251
  simp only [CollatzResearch.WordTrace]
  refine ⟨119458217857332470182321607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79638811904888313454881071 119458217857332470182321607)
  ·
    refine ⟨179187326785998705273482411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119458217857332470182321607 179187326785998705273482411)
    ·
      refine ⟨268780990178998057910223617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179187326785998705273482411 268780990178998057910223617)
      ·
        refine ⟨201585742634248543432667713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268780990178998057910223617 201585742634248543432667713)
        ·
          refine ⟨151189306975686407574500785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201585742634248543432667713 151189306975686407574500785)
          ·
            refine ⟨113391980231764805680875589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151189306975686407574500785 113391980231764805680875589)
            ·
              refine ⟨21260996293455901065164173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113391980231764805680875589 21260996293455901065164173)
              ·
                refine ⟨7972873610045962899436565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21260996293455901065164173 7972873610045962899436565)
                ·
                  refine ⟨373728450470904510911089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7972873610045962899436565 373728450470904510911089)
                  ·
                    rfl

theorem cell22_3275251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_3275251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275251 prefixEnd_3275251 := by exact prefixLift 3275251
  have htrace : WordTrace (prefixWord ++ tailWord_3275251) baseStart_3275251 baseEnd_3275251 := by
    simpa [prefixWord, tailWord_3275251, baseEnd_3275251] using wordTrace_append hprefix tailTrace_3275251
  have hstable : (prefixWord ++ tailWord_3275251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275251).length < 2 ^ (prefixWord ++ tailWord_3275251).sum := by decide
  have hdescent : baseEnd_3275251 < baseStart_3275251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275268 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3275268 : Nat := 118140960795 + 3275268 * 2 ^ 59
def prefixEnd_3275268 : Nat := 4983230072969 + 3 ^ 40 * 3275268 * 2
def baseEnd_3275268 : Nat := 373730390286710385019405

theorem tailTrace_3275268 : CollatzResearch.WordTrace tailWord_3275268 prefixEnd_3275268 373730390286710385019405 := by
  unfold tailWord_3275268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59729418949135441042845229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79639225265513921390460305 59729418949135441042845229)
  ·
    refine ⟨22398532105925790391066961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59729418949135441042845229 22398532105925790391066961)
    ·
      refine ⟨16798899079444342793300221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22398532105925790391066961 16798899079444342793300221)
      ·
        refine ⟨6299587154791628547487583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16798899079444342793300221 6299587154791628547487583)
        ·
          refine ⟨9449380732187442821231375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299587154791628547487583 9449380732187442821231375)
          ·
            refine ⟨14174071098281164231847063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449380732187442821231375 14174071098281164231847063)
            ·
              refine ⟨21261106647421746347770595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14174071098281164231847063 21261106647421746347770595)
              ·
                refine ⟨31891659971132619521655893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21261106647421746347770595 31891659971132619521655893)
                ·
                  refine ⟨373730390286710385019405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31891659971132619521655893 373730390286710385019405)
                  ·
                    rfl

theorem cell22_3275268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3275268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275268 prefixEnd_3275268 := by exact prefixLift 3275268
  have htrace : WordTrace (prefixWord ++ tailWord_3275268) baseStart_3275268 baseEnd_3275268 := by
    simpa [prefixWord, tailWord_3275268, baseEnd_3275268] using wordTrace_append hprefix tailTrace_3275268
  have hstable : (prefixWord ++ tailWord_3275268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275268).length < 2 ^ (prefixWord ++ tailWord_3275268).sum := by decide
  have hdescent : baseEnd_3275268 < baseStart_3275268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275283 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 4, 3]
def baseStart_3275283 : Nat := 118140960795 + 3275283 * 2 ^ 59
def prefixEnd_3275283 : Nat := 4983230072969 + 3 ^ 40 * 3275283 * 2
def baseEnd_3275283 : Nat := 1121196305666676115933169

theorem tailTrace_3275283 : CollatzResearch.WordTrace tailWord_3275283 prefixEnd_3275283 1121196305666676115933169 := by
  unfold tailWord_3275283
  simp only [CollatzResearch.WordTrace]
  refine ⟨119459384993216539647486503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79639589995477693098324335 119459384993216539647486503)
  ·
    refine ⟨179189077489824809471229755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119459384993216539647486503 179189077489824809471229755)
    ·
      refine ⟨268783616234737214206844633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179189077489824809471229755 268783616234737214206844633)
      ·
        refine ⟨201587712176052910655133475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268783616234737214206844633 201587712176052910655133475)
        ·
          refine ⟨302381568264079365982700213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201587712176052910655133475 302381568264079365982700213)
          ·
            refine ⟨28348272024757440560878145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302381568264079365982700213 28348272024757440560878145)
            ·
              refine ⟨21261204018568080420658609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28348272024757440560878145 21261204018568080420658609)
              ·
                refine ⟨15945903013926060315493957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21261204018568080420658609 15945903013926060315493957)
                ·
                  refine ⟨2989856815111136309155117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15945903013926060315493957 2989856815111136309155117)
                  ·
                    refine ⟨1121196305666676115933169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989856815111136309155117 1121196305666676115933169)
                    ·
                      rfl

theorem cell22_3275283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].length) (baseStart_3275283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275283 prefixEnd_3275283 := by exact prefixLift 3275283
  have htrace : WordTrace (prefixWord ++ tailWord_3275283) baseStart_3275283 baseEnd_3275283 := by
    simpa [prefixWord, tailWord_3275283, baseEnd_3275283] using wordTrace_append hprefix tailTrace_3275283
  have hstable : (prefixWord ++ tailWord_3275283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275283).length < 2 ^ (prefixWord ++ tailWord_3275283).sum := by decide
  have hdescent : baseEnd_3275283 < baseStart_3275283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275285 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 4]
def baseStart_3275285 : Nat := 118140960795 + 3275285 * 2 ^ 59
def prefixEnd_3275285 : Nat := 4983230072969 + 3 ^ 40 * 3275285 * 2
def baseEnd_3275285 : Nat := 373732330102516259127721

theorem tailTrace_3275285 : CollatzResearch.WordTrace tailWord_3275285 prefixEnd_3275285 373732330102516259127721 := by
  unfold tailWord_3275285
  simp only [CollatzResearch.WordTrace]
  refine ⟨119459457939209293989059309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79639638626139529326039539 119459457939209293989059309)
  ·
    refine ⟨44797296727203485245897241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119459457939209293989059309 44797296727203485245897241)
    ·
      refine ⟨33597972545402613934422931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44797296727203485245897241 33597972545402613934422931)
      ·
        refine ⟨50396958818103920901634397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33597972545402613934422931 50396958818103920901634397)
        ·
          refine ⟨18898859556788970338112899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50396958818103920901634397 18898859556788970338112899)
          ·
            refine ⟨28348289335183455507169349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18898859556788970338112899 28348289335183455507169349)
            ·
              refine ⟨5315304250346897907594253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28348289335183455507169349 5315304250346897907594253)
              ·
                refine ⟨1993239093880086715347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315304250346897907594253 1993239093880086715347845)
                ·
                  refine ⟨373732330102516259127721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993239093880086715347845 373732330102516259127721)
                  ·
                    rfl

theorem cell22_3275285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_3275285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275285 prefixEnd_3275285 := by exact prefixLift 3275285
  have htrace : WordTrace (prefixWord ++ tailWord_3275285) baseStart_3275285 baseEnd_3275285 := by
    simpa [prefixWord, tailWord_3275285, baseEnd_3275285] using wordTrace_append hprefix tailTrace_3275285
  have hstable : (prefixWord ++ tailWord_3275285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275285).length < 2 ^ (prefixWord ++ tailWord_3275285).sum := by decide
  have hdescent : baseEnd_3275285 < baseStart_3275285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275287 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 1, 4]
def baseStart_3275287 : Nat := 118140960795 + 3275287 * 2 ^ 59
def prefixEnd_3275287 : Nat := 4983230072969 + 3 ^ 40 * 3275287 * 2
def baseEnd_3275287 : Nat := 1121197674948421438833157

theorem tailTrace_3275287 : CollatzResearch.WordTrace tailWord_3275287 prefixEnd_3275287 1121197674948421438833157 := by
  unfold tailWord_3275287
  simp only [CollatzResearch.WordTrace]
  refine ⟨119459530885202048330632115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79639687256801365553754743 119459530885202048330632115)
  ·
    refine ⟨179189296327803072495948173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119459530885202048330632115 179189296327803072495948173)
    ·
      refine ⟨67195986122926152185980565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179189296327803072495948173 67195986122926152185980565)
      ·
        refine ⟨3149811849512163383717839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67195986122926152185980565 3149811849512163383717839)
        ·
          refine ⟨4724717774268245075576759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149811849512163383717839 4724717774268245075576759)
          ·
            refine ⟨7087076661402367613365139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724717774268245075576759 7087076661402367613365139)
            ·
              refine ⟨10630614992103551420047709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087076661402367613365139 10630614992103551420047709)
              ·
                refine ⟨3986480622038831782517891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10630614992103551420047709 3986480622038831782517891)
                ·
                  refine ⟨5979720933058247673776837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986480622038831782517891 5979720933058247673776837)
                  ·
                    refine ⟨1121197674948421438833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5979720933058247673776837 1121197674948421438833157)
                    ·
                      rfl

theorem cell22_3275287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_3275287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275287 prefixEnd_3275287 := by exact prefixLift 3275287
  have htrace : WordTrace (prefixWord ++ tailWord_3275287) baseStart_3275287 baseEnd_3275287 := by
    simpa [prefixWord, tailWord_3275287, baseEnd_3275287] using wordTrace_append hprefix tailTrace_3275287
  have hstable : (prefixWord ++ tailWord_3275287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275287).length < 2 ^ (prefixWord ++ tailWord_3275287).sum := by decide
  have hdescent : baseEnd_3275287 < baseStart_3275287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275298 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3275298 : Nat := 118140960795 + 3275298 * 2 ^ 59
def prefixEnd_3275298 : Nat := 4983230072969 + 3 ^ 40 * 3275298 * 2
def baseEnd_3275298 : Nat := 1121201440473221076808123

theorem tailTrace_3275298 : CollatzResearch.WordTrace tailWord_3275298 prefixEnd_3275298 1121201440473221076808123 := by
  unfold tailWord_3275298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29864983022040549302320637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79639954725441464806188365 29864983022040549302320637)
  ·
    refine ⟨11199368633265205988370239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29864983022040549302320637 11199368633265205988370239)
    ·
      refine ⟨16799052949897808982555359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11199368633265205988370239 16799052949897808982555359)
      ·
        refine ⟨25198579424846713473833039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16799052949897808982555359 25198579424846713473833039)
        ·
          refine ⟨37797869137270070210749559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25198579424846713473833039 37797869137270070210749559)
          ·
            refine ⟨56696803705905105316124339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37797869137270070210749559 56696803705905105316124339)
            ·
              refine ⟨85045205558857657974186509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56696803705905105316124339 85045205558857657974186509)
              ·
                refine ⟨31891952084571621740319941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85045205558857657974186509 31891952084571621740319941)
                ·
                  refine ⟨5979741015857179076309989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31891952084571621740319941 5979741015857179076309989)
                  ·
                    refine ⟨1121201440473221076808123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5979741015857179076309989 1121201440473221076808123)
                    ·
                      rfl

theorem cell22_3275298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3275298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275298 prefixEnd_3275298 := by exact prefixLift 3275298
  have htrace : WordTrace (prefixWord ++ tailWord_3275298) baseStart_3275298 baseEnd_3275298 := by
    simpa [prefixWord, tailWord_3275298, baseEnd_3275298] using wordTrace_append hprefix tailTrace_3275298
  have hstable : (prefixWord ++ tailWord_3275298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275298).length < 2 ^ (prefixWord ++ tailWord_3275298).sum := by decide
  have hdescent : baseEnd_3275298 < baseStart_3275298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275317 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3275317 : Nat := 118140960795 + 3275317 * 2 ^ 59
def prefixEnd_3275317 : Nat := 4983230072969 + 3 ^ 40 * 3275317 * 2
def baseEnd_3275317 : Nat := 1121207944561511360583065

theorem tailTrace_3275317 : CollatzResearch.WordTrace tailWord_3275317 prefixEnd_3275317 1121207944561511360583065 := by
  unfold tailWord_3275317
  simp only [CollatzResearch.WordTrace]
  refine ⟨119460625075093363454224205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79640416716728908969482803 119460625075093363454224205)
  ·
    refine ⟨44797734403160011295334077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119460625075093363454224205 44797734403160011295334077)
    ·
      refine ⟨16799150401185004235750279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44797734403160011295334077 16799150401185004235750279)
      ·
        refine ⟨25198725601777506353625419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16799150401185004235750279 25198725601777506353625419)
        ·
          refine ⟨37798088402666259530438129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25198725601777506353625419 37798088402666259530438129)
          ·
            refine ⟨28348566301999694647828597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37798088402666259530438129 28348566301999694647828597)
            ·
              refine ⟨2657678090812471373233931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28348566301999694647828597 2657678090812471373233931)
              ·
                refine ⟨3986517136218707059850897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657678090812471373233931 3986517136218707059850897)
                ·
                  refine ⟨2989887852164030294888173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986517136218707059850897 2989887852164030294888173)
                  ·
                    refine ⟨1121207944561511360583065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2989887852164030294888173 1121207944561511360583065)
                    ·
                      rfl

theorem cell22_3275317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3275317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275317 prefixEnd_3275317 := by exact prefixLift 3275317
  have htrace : WordTrace (prefixWord ++ tailWord_3275317) baseStart_3275317 baseEnd_3275317 := by
    simpa [prefixWord, tailWord_3275317, baseEnd_3275317] using wordTrace_append hprefix tailTrace_3275317
  have hstable : (prefixWord ++ tailWord_3275317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275317).length < 2 ^ (prefixWord ++ tailWord_3275317).sum := by decide
  have hdescent : baseEnd_3275317 < baseStart_3275317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275375 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 5]
def baseStart_3275375 : Nat := 118140960795 + 3275375 * 2 ^ 59
def prefixEnd_3275375 : Nat := 4983230072969 + 3 ^ 40 * 3275375 * 2
def baseEnd_3275375 : Nat := 373742599715606180877629

theorem tailTrace_3275375 : CollatzResearch.WordTrace tailWord_3275375 prefixEnd_3275375 373742599715606180877629 := by
  unfold tailWord_3275375
  simp only [CollatzResearch.WordTrace]
  refine ⟨119462740508883239359835579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79641827005922159573223719 119462740508883239359835579)
  ·
    refine ⟨179194110763324859039753369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119462740508883239359835579 179194110763324859039753369)
    ·
      refine ⟨134395583072493644279815027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179194110763324859039753369 134395583072493644279815027)
      ·
        refine ⟨201593374608740466419722541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134395583072493644279815027 201593374608740466419722541)
        ·
          refine ⟨75597515478277674907395953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201593374608740466419722541 75597515478277674907395953)
          ·
            refine ⟨56698136608708256180546965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75597515478277674907395953 56698136608708256180546965)
            ·
              refine ⟨2657725153533199508463139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56698136608708256180546965 2657725153533199508463139)
              ·
                refine ⟨3986587730299799262694709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657725153533199508463139 3986587730299799262694709)
                ·
                  refine ⟨373742599715606180877629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986587730299799262694709 373742599715606180877629)
                  ·
                    rfl

theorem cell22_3275375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 5].length) (baseStart_3275375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275375 prefixEnd_3275375 := by exact prefixLift 3275375
  have htrace : WordTrace (prefixWord ++ tailWord_3275375) baseStart_3275375 baseEnd_3275375 := by
    simpa [prefixWord, tailWord_3275375, baseEnd_3275375] using wordTrace_append hprefix tailTrace_3275375
  have hstable : (prefixWord ++ tailWord_3275375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275375).length < 2 ^ (prefixWord ++ tailWord_3275375).sum := by decide
  have hdescent : baseEnd_3275375 < baseStart_3275375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275433 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3275433 : Nat := 118140960795 + 3275433 * 2 ^ 59
def prefixEnd_3275433 : Nat := 4983230072969 + 3 ^ 40 * 3275433 * 2
def baseEnd_3275433 : Nat := 1121247653732125724682709

theorem tailTrace_3275433 : CollatzResearch.WordTrace tailWord_3275433 prefixEnd_3275433 1121247653732125724682709 := by
  unfold tailWord_3275433
  simp only [CollatzResearch.WordTrace]
  refine ⟨119464855942673115265446953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79643237295115410176964635 119464855942673115265446953)
  ·
    refine ⟨89598641957004836449085215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119464855942673115265446953 89598641957004836449085215)
    ·
      refine ⟨134397962935507254673627823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89598641957004836449085215 134397962935507254673627823)
      ·
        refine ⟨201596944403260882010441735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134397962935507254673627823 201596944403260882010441735)
        ·
          refine ⟨302395416604891323015662603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201596944403260882010441735 302395416604891323015662603)
          ·
            refine ⟨453593124907336984523493905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302395416604891323015662603 453593124907336984523493905)
            ·
              refine ⟨340194843680502738392620429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453593124907336984523493905 340194843680502738392620429)
              ·
                refine ⟨127573066380188526897232661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340194843680502738392620429 127573066380188526897232661)
                ·
                  refine ⟨5979987486571337198307781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127573066380188526897232661 5979987486571337198307781)
                  ·
                    refine ⟨1121247653732125724682709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5979987486571337198307781 1121247653732125724682709)
                    ·
                      rfl

theorem cell22_3275433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3275433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275433 prefixEnd_3275433 := by exact prefixLift 3275433
  have htrace : WordTrace (prefixWord ++ tailWord_3275433) baseStart_3275433 baseEnd_3275433 := by
    simpa [prefixWord, tailWord_3275433, baseEnd_3275433] using wordTrace_append hprefix tailTrace_3275433
  have hstable : (prefixWord ++ tailWord_3275433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275433).length < 2 ^ (prefixWord ++ tailWord_3275433).sum := by decide
  have hdescent : baseEnd_3275433 < baseStart_3275433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275510 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3275510 : Nat := 118140960795 + 3275510 * 2 ^ 59
def prefixEnd_3275510 : Nat := 4983230072969 + 3 ^ 40 * 3275510 * 2
def baseEnd_3275510 : Nat := 373758004135241063502491

theorem tailTrace_3275510 : CollatzResearch.WordTrace tailWord_3275510 prefixEnd_3275510 373758004135241063502491 := by
  unfold tailWord_3275510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466729022712134838499999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79645109575596104943999989 7466729022712134838499999)
  ·
    refine ⟨11200093534068202257749999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466729022712134838499999 11200093534068202257749999)
    ·
      refine ⟨16800140301102303386624999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200093534068202257749999 16800140301102303386624999)
      ·
        refine ⟨25200210451653455079937499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800140301102303386624999 25200210451653455079937499)
        ·
          refine ⟨37800315677480182619906249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200210451653455079937499 37800315677480182619906249)
          ·
            refine ⟨28350236758110136964929687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37800315677480182619906249 28350236758110136964929687)
            ·
              refine ⟨42525355137165205447394531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28350236758110136964929687 42525355137165205447394531)
              ·
                refine ⟨63788032705747808171091797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42525355137165205447394531 63788032705747808171091797)
                ·
                  refine ⟨373758004135241063502491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63788032705747808171091797 373758004135241063502491)
                  ·
                    rfl

theorem cell22_3275510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3275510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275510 prefixEnd_3275510 := by exact prefixLift 3275510
  have htrace : WordTrace (prefixWord ++ tailWord_3275510) baseStart_3275510 baseEnd_3275510 := by
    simpa [prefixWord, tailWord_3275510, baseEnd_3275510] using wordTrace_append hprefix tailTrace_3275510
  have hstable : (prefixWord ++ tailWord_3275510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275510).length < 2 ^ (prefixWord ++ tailWord_3275510).sum := by decide
  have hdescent : baseEnd_3275510 < baseStart_3275510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275514 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_3275514 : Nat := 118140960795 + 3275514 * 2 ^ 59
def prefixEnd_3275514 : Nat := 4983230072969 + 3 ^ 40 * 3275514 * 2
def baseEnd_3275514 : Nat := 1121275381687468513407461

theorem tailTrace_3275514 : CollatzResearch.WordTrace tailWord_3275514 prefixEnd_3275514 1121275381687468513407461 := by
  unfold tailWord_3275514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866952563844916524786399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79645206836919777399430397 29866952563844916524786399)
  ·
    refine ⟨44800428845767374787179599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29866952563844916524786399 44800428845767374787179599)
    ·
      refine ⟨67200643268651062180769399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44800428845767374787179599 67200643268651062180769399)
      ·
        refine ⟨100800964902976593271154099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67200643268651062180769399 100800964902976593271154099)
        ·
          refine ⟨151201447354464889906731149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100800964902976593271154099 151201447354464889906731149)
          ·
            refine ⟨56700542757924333715024181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151201447354464889906731149 56700542757924333715024181)
            ·
              refine ⟨5315675883555406285783517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56700542757924333715024181 5315675883555406285783517)
              ·
                refine ⟨1993378456333277357168819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315675883555406285783517 1993378456333277357168819)
                ·
                  refine ⟨2990067684499916035753229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993378456333277357168819 2990067684499916035753229)
                  ·
                    refine ⟨1121275381687468513407461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990067684499916035753229 1121275381687468513407461)
                    ·
                      rfl

theorem cell22_3275514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_3275514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275514 prefixEnd_3275514 := by exact prefixLift 3275514
  have htrace : WordTrace (prefixWord ++ tailWord_3275514) baseStart_3275514 baseEnd_3275514 := by
    simpa [prefixWord, tailWord_3275514, baseEnd_3275514] using wordTrace_append hprefix tailTrace_3275514
  have hstable : (prefixWord ++ tailWord_3275514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275514).length < 2 ^ (prefixWord ++ tailWord_3275514).sum := by decide
  have hdescent : baseEnd_3275514 < baseStart_3275514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275600 : List Nat := [2, 1, 1, 1, 1, 4, 5, 7]
def baseStart_3275600 : Nat := 118140960795 + 3275600 * 2 ^ 59
def prefixEnd_3275600 : Nat := 4983230072969 + 3 ^ 40 * 3275600 * 2
def baseEnd_3275600 : Nat := 124589424582776995084133

theorem tailTrace_3275600 : CollatzResearch.WordTrace tailWord_3275600 prefixEnd_3275600 124589424582776995084133 := by
  unfold tailWord_3275600
  simp only [CollatzResearch.WordTrace]
  refine ⟨59735473466534051393388127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79647297955378735191184169 59735473466534051393388127)
  ·
    refine ⟨89603210199801077090082191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59735473466534051393388127 89603210199801077090082191)
    ·
      refine ⟨134404815299701615635123287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89603210199801077090082191 134404815299701615635123287)
      ·
        refine ⟨201607222949552423452684931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134404815299701615635123287 201607222949552423452684931)
        ·
          refine ⟨302410834424328635179027397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201607222949552423452684931 302410834424328635179027397)
          ·
            refine ⟨56702031454561619096067637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302410834424328635179027397 56702031454561619096067637)
            ·
              refine ⟨5315815448865151790256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56702031454561619096067637 5315815448865151790256341)
              ·
                refine ⟨124589424582776995084133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5315815448865151790256341 124589424582776995084133)
                ·
                  rfl

theorem cell22_3275600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_3275600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275600 prefixEnd_3275600 := by exact prefixLift 3275600
  have htrace : WordTrace (prefixWord ++ tailWord_3275600) baseStart_3275600 baseEnd_3275600 := by
    simpa [prefixWord, tailWord_3275600, baseEnd_3275600] using wordTrace_append hprefix tailTrace_3275600
  have hstable : (prefixWord ++ tailWord_3275600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275600).length < 2 ^ (prefixWord ++ tailWord_3275600).sum := by decide
  have hdescent : baseEnd_3275600 < baseStart_3275600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275604 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3275604 : Nat := 118140960795 + 3275604 * 2 ^ 59
def prefixEnd_3275604 : Nat := 4983230072969 + 3 ^ 40 * 3275604 * 2
def baseEnd_3275604 : Nat := 1121306190526738278657185

theorem tailTrace_3275604 : CollatzResearch.WordTrace tailWord_3275604 prefixEnd_3275604 1121306190526738278657185 := by
  unfold tailWord_3275604
  simp only [CollatzResearch.WordTrace]
  refine ⟨59735546412526805734960933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79647395216702407646614577 59735546412526805734960933)
  ·
    refine ⟨11200414952348776075305175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59735546412526805734960933 11200414952348776075305175)
    ·
      refine ⟨16800622428523164112957763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200414952348776075305175 16800622428523164112957763)
      ·
        refine ⟨25200933642784746169436645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800622428523164112957763 25200933642784746169436645)
        ·
          refine ⟨4725175058022139906769371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25200933642784746169436645 4725175058022139906769371)
          ·
            refine ⟨7087762587033209860154057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725175058022139906769371 7087762587033209860154057)
            ·
              refine ⟨5315821940274907395115543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7087762587033209860154057 5315821940274907395115543)
              ·
                refine ⟨7973732910412361092673315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315821940274907395115543 7973732910412361092673315)
                ·
                  refine ⟨11960599365618541639009973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973732910412361092673315 11960599365618541639009973)
                  ·
                    refine ⟨1121306190526738278657185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11960599365618541639009973 1121306190526738278657185)
                    ·
                      rfl

theorem cell22_3275604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3275604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275604 prefixEnd_3275604 := by exact prefixLift 3275604
  have htrace : WordTrace (prefixWord ++ tailWord_3275604) baseStart_3275604 baseEnd_3275604 := by
    simpa [prefixWord, tailWord_3275604, baseEnd_3275604] using wordTrace_append hprefix tailTrace_3275604
  have hstable : (prefixWord ++ tailWord_3275604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275604).length < 2 ^ (prefixWord ++ tailWord_3275604).sum := by decide
  have hdescent : baseEnd_3275604 < baseStart_3275604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275619 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 2, 4]
def baseStart_3275619 : Nat := 118140960795 + 3275619 * 2 ^ 59
def prefixEnd_3275619 : Nat := 4983230072969 + 3 ^ 40 * 3275619 * 2
def baseEnd_3275619 : Nat := 1121311325333283239532139

theorem tailTrace_3275619 : CollatzResearch.WordTrace tailWord_3275619 prefixEnd_3275619 1121311325333283239532139 := by
  unfold tailWord_3275619
  simp only [CollatzResearch.WordTrace]
  refine ⟨119471639919999269031717911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79647759946666179354478607 119471639919999269031717911)
  ·
    refine ⟨179207459879998903547576867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119471639919999269031717911 179207459879998903547576867)
    ·
      refine ⟨268811189819998355321365301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179207459879998903547576867 268811189819998355321365301)
      ·
        refine ⟨25201049045624845811377997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268811189819998355321365301 25201049045624845811377997)
        ·
          refine ⟨9450393392109317179266749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25201049045624845811377997 9450393392109317179266749)
          ·
            refine ⟨3543897522040993942225031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9450393392109317179266749 3543897522040993942225031)
            ·
              refine ⟨5315846283061490913337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543897522040993942225031 5315846283061490913337547)
              ·
                refine ⟨7973769424592236370006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315846283061490913337547 7973769424592236370006321)
                ·
                  refine ⟨5980327068444177277504741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7973769424592236370006321 5980327068444177277504741)
                  ·
                    refine ⟨1121311325333283239532139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980327068444177277504741 1121311325333283239532139)
                    ·
                      rfl

theorem cell22_3275619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].length) (baseStart_3275619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275619 prefixEnd_3275619 := by exact prefixLift 3275619
  have htrace : WordTrace (prefixWord ++ tailWord_3275619) baseStart_3275619 baseEnd_3275619 := by
    simpa [prefixWord, tailWord_3275619, baseEnd_3275619] using wordTrace_append hprefix tailTrace_3275619
  have hstable : (prefixWord ++ tailWord_3275619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275619).length < 2 ^ (prefixWord ++ tailWord_3275619).sum := by decide
  have hdescent : baseEnd_3275619 < baseStart_3275619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275638 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3275638 : Nat := 118140960795 + 3275638 * 2 ^ 59
def prefixEnd_3275638 : Nat := 4983230072969 + 3 ^ 40 * 3275638 * 2
def baseEnd_3275638 : Nat := 1121317829421573523307081

theorem tailTrace_3275638 : CollatzResearch.WordTrace tailWord_3275638 prefixEnd_3275638 1121317829421573523307081 := by
  unfold tailWord_3275638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467020806683152204791223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79648221937953623517773045 7467020806683152204791223)
  ·
    refine ⟨11200531210024728307186835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7467020806683152204791223 11200531210024728307186835)
    ·
      refine ⟨16800796815037092460780253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200531210024728307186835 16800796815037092460780253)
      ·
        refine ⟨6300298805638909672792595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16800796815037092460780253 6300298805638909672792595)
        ·
          refine ⟨9450448208458364509188893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300298805638909672792595 9450448208458364509188893)
          ·
            refine ⟨3543918078171886690945835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9450448208458364509188893 3543918078171886690945835)
            ·
              refine ⟨5315877117257830036418753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543918078171886690945835 5315877117257830036418753)
              ·
                refine ⟨3986907837943372527314065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315877117257830036418753 3986907837943372527314065)
                ·
                  refine ⟨2990180878457529395485549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986907837943372527314065 2990180878457529395485549)
                  ·
                    refine ⟨1121317829421573523307081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990180878457529395485549 1121317829421573523307081)
                    ·
                      rfl

theorem cell22_3275638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3275638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275638 prefixEnd_3275638 := by exact prefixLift 3275638
  have htrace : WordTrace (prefixWord ++ tailWord_3275638) baseStart_3275638 baseEnd_3275638 := by
    simpa [prefixWord, tailWord_3275638, baseEnd_3275638] using wordTrace_append hprefix tailTrace_3275638
  have hstable : (prefixWord ++ tailWord_3275638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275638).length < 2 ^ (prefixWord ++ tailWord_3275638).sum := by decide
  have hdescent : baseEnd_3275638 < baseStart_3275638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275722 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_3275722 : Nat := 118140960795 + 3275722 * 2 ^ 59
def prefixEnd_3275722 : Nat := 4983230072969 + 3 ^ 40 * 3275722 * 2
def baseEnd_3275722 : Nat := 1121346584338225304206823

theorem tailTrace_3275722 : CollatzResearch.WordTrace tailWord_3275722 prefixEnd_3275722 1121346584338225304206823 := by
  unfold tailWord_3275722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29868849159656529405679355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79650264425750745081811613 29868849159656529405679355)
  ·
    refine ⟨44803273739484794108519033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29868849159656529405679355 44803273739484794108519033)
    ·
      refine ⟨33602455304613595581389275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44803273739484794108519033 33602455304613595581389275)
      ·
        refine ⟨50403682956920393372083913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33602455304613595581389275 50403682956920393372083913)
        ·
          refine ⟨37802762217690295029062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50403682956920393372083913 37802762217690295029062935)
          ·
            refine ⟨56704143326535442543594403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37802762217690295029062935 56704143326535442543594403)
            ·
              refine ⟨85056214989803163815391605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56704143326535442543594403 85056214989803163815391605)
              ·
                refine ⟨7974020155294046607692963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85056214989803163815391605 7974020155294046607692963)
                ·
                  refine ⟨11961030232941069911539445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974020155294046607692963 11961030232941069911539445)
                  ·
                    refine ⟨1121346584338225304206823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11961030232941069911539445 1121346584338225304206823)
                    ·
                      rfl

theorem cell22_3275722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_3275722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275722 prefixEnd_3275722 := by exact prefixLift 3275722
  have htrace : WordTrace (prefixWord ++ tailWord_3275722) baseStart_3275722 baseEnd_3275722 := by
    simpa [prefixWord, tailWord_3275722, baseEnd_3275722] using wordTrace_append hprefix tailTrace_3275722
  have hstable : (prefixWord ++ tailWord_3275722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275722).length < 2 ^ (prefixWord ++ tailWord_3275722).sum := by decide
  have hdescent : baseEnd_3275722 < baseStart_3275722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275726 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3275726 : Nat := 118140960795 + 3275726 * 2 ^ 59
def prefixEnd_3275726 : Nat := 4983230072969 + 3 ^ 40 * 3275726 * 2
def baseEnd_3275726 : Nat := 1121347953619970627106811

theorem tailTrace_3275726 : CollatzResearch.WordTrace tailWord_3275726 prefixEnd_3275726 1121347953619970627106811 := by
  unfold tailWord_3275726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14934442816326453288232879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79650361687074417537242021 14934442816326453288232879)
  ·
    refine ⟨22401664224489679932349319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14934442816326453288232879 22401664224489679932349319)
    ·
      refine ⟨33602496336734519898523979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22401664224489679932349319 33602496336734519898523979)
      ·
        refine ⟨50403744505101779847785969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33602496336734519898523979 50403744505101779847785969)
        ·
          refine ⟨37802808378826334885839477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50403744505101779847785969 37802808378826334885839477)
          ·
            refine ⟨3544013285514968895547451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37802808378826334885839477 3544013285514968895547451)
            ·
              refine ⟨5316019928272453343321177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544013285514968895547451 5316019928272453343321177)
              ·
                refine ⟨3987014946204340007490883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316019928272453343321177 3987014946204340007490883)
                ·
                  refine ⟨5980522419306510011236325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987014946204340007490883 5980522419306510011236325)
                  ·
                    refine ⟨1121347953619970627106811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980522419306510011236325 1121347953619970627106811)
                    ·
                      rfl

theorem cell22_3275726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3275726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275726 prefixEnd_3275726 := by exact prefixLift 3275726
  have htrace : WordTrace (prefixWord ++ tailWord_3275726) baseStart_3275726 baseEnd_3275726 := by
    simpa [prefixWord, tailWord_3275726, baseEnd_3275726] using wordTrace_append hprefix tailTrace_3275726
  have hstable : (prefixWord ++ tailWord_3275726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275726).length < 2 ^ (prefixWord ++ tailWord_3275726).sum := by decide
  have hdescent : baseEnd_3275726 < baseStart_3275726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275754 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3275754 : Nat := 118140960795 + 3275754 * 2 ^ 59
def prefixEnd_3275754 : Nat := 4983230072969 + 3 ^ 40 * 3275754 * 2
def baseEnd_3275754 : Nat := 1121357538592187887406725

theorem tailTrace_3275754 : CollatzResearch.WordTrace tailWord_3275754 prefixEnd_3275754 1121357538592187887406725 := by
  unfold tailWord_3275754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29869140943627546771970579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79651042516340124725254877 29869140943627546771970579)
  ·
    refine ⟨44803711415441320157955869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29869140943627546771970579 44803711415441320157955869)
    ·
      refine ⟨16801391780790495059233451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44803711415441320157955869 16801391780790495059233451)
      ·
        refine ⟨25202087671185742588850177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16801391780790495059233451 25202087671185742588850177)
        ·
          refine ⟨18901565753389306941637633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25202087671185742588850177 18901565753389306941637633)
          ·
            refine ⟨14176174315041980206228225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18901565753389306941637633 14176174315041980206228225)
            ·
              refine ⟨10632130736281485154671169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14176174315041980206228225 10632130736281485154671169)
              ·
                refine ⟨7974098052211113866003377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10632130736281485154671169 7974098052211113866003377)
                ·
                  refine ⟨5980573539158335399502533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7974098052211113866003377 5980573539158335399502533)
                  ·
                    refine ⟨1121357538592187887406725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980573539158335399502533 1121357538592187887406725)
                    ·
                      rfl

theorem cell22_3275754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3275754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275754 prefixEnd_3275754 := by exact prefixLift 3275754
  have htrace : WordTrace (prefixWord ++ tailWord_3275754) baseStart_3275754 baseEnd_3275754 := by
    simpa [prefixWord, tailWord_3275754, baseEnd_3275754] using wordTrace_append hprefix tailTrace_3275754
  have hstable : (prefixWord ++ tailWord_3275754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275754).length < 2 ^ (prefixWord ++ tailWord_3275754).sum := by decide
  have hdescent : baseEnd_3275754 < baseStart_3275754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275784 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3275784 : Nat := 118140960795 + 3275784 * 2 ^ 59
def prefixEnd_3275784 : Nat := 4983230072969 + 3 ^ 40 * 3275784 * 2
def baseEnd_3275784 : Nat := 1121367808205277809156633

theorem tailTrace_3275784 : CollatzResearch.WordTrace tailWord_3275784 prefixEnd_3275784 1121367808205277809156633 := by
  unfold tailWord_3275784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59738828982200751105737203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79651771976267668140982937 59738828982200751105737203)
  ·
    refine ⟨89608243473301126658605805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59738828982200751105737203 89608243473301126658605805)
    ·
      refine ⟨33603091302487922496977177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89608243473301126658605805 33603091302487922496977177)
      ·
        refine ⟨25202318476865941872732883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33603091302487922496977177 25202318476865941872732883)
        ·
          refine ⟨37803477715298912809099325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25202318476865941872732883 37803477715298912809099325)
          ·
            refine ⟨14176304143237092303412247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37803477715298912809099325 14176304143237092303412247)
            ·
              refine ⟨21264456214855638455118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14176304143237092303412247 21264456214855638455118371)
              ·
                refine ⟨31896684322283457682677557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21264456214855638455118371 31896684322283457682677557)
                ·
                  refine ⟨2990314155214074157751021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31896684322283457682677557 2990314155214074157751021)
                  ·
                    refine ⟨1121367808205277809156633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990314155214074157751021 1121367808205277809156633)
                    ·
                      rfl

theorem cell22_3275784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3275784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275784 prefixEnd_3275784 := by exact prefixLift 3275784
  have htrace : WordTrace (prefixWord ++ tailWord_3275784) baseStart_3275784 baseEnd_3275784 := by
    simpa [prefixWord, tailWord_3275784, baseEnd_3275784] using wordTrace_append hprefix tailTrace_3275784
  have hstable : (prefixWord ++ tailWord_3275784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275784).length < 2 ^ (prefixWord ++ tailWord_3275784).sum := by decide
  have hdescent : baseEnd_3275784 < baseStart_3275784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275794 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3275794 : Nat := 118140960795 + 3275794 * 2 ^ 59
def prefixEnd_3275794 : Nat := 4983230072969 + 3 ^ 40 * 3275794 * 2
def baseEnd_3275794 : Nat := 1121371231409641116406603

theorem tailTrace_3275794 : CollatzResearch.WordTrace tailWord_3275794 prefixEnd_3275794 1121371231409641116406603 := by
  unfold tailWord_3275794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29869505673591318479834609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79652015129576849279558957 29869505673591318479834609)
  ·
    refine ⟨22402129255193488859875957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29869505673591318479834609 22402129255193488859875957)
    ·
      refine ⟨2100199617674389580613371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22402129255193488859875957 2100199617674389580613371)
      ·
        refine ⟨3150299426511584370920057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100199617674389580613371 3150299426511584370920057)
        ·
          refine ⟨2362724569883688278190043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150299426511584370920057 2362724569883688278190043)
          ·
            refine ⟨3544086854825532417285065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362724569883688278190043 3544086854825532417285065)
            ·
              refine ⟨2658065141119149312963799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544086854825532417285065 2658065141119149312963799)
              ·
                refine ⟨3987097711678723969445699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658065141119149312963799 3987097711678723969445699)
                ·
                  refine ⟨5980646567518085954168549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987097711678723969445699 5980646567518085954168549)
                  ·
                    refine ⟨1121371231409641116406603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980646567518085954168549 1121371231409641116406603)
                    ·
                      rfl

theorem cell22_3275794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3275794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275794 prefixEnd_3275794 := by exact prefixLift 3275794
  have htrace : WordTrace (prefixWord ++ tailWord_3275794) baseStart_3275794 baseEnd_3275794 := by
    simpa [prefixWord, tailWord_3275794, baseEnd_3275794] using wordTrace_append hprefix tailTrace_3275794
  have hstable : (prefixWord ++ tailWord_3275794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275794).length < 2 ^ (prefixWord ++ tailWord_3275794).sum := by decide
  have hdescent : baseEnd_3275794 < baseStart_3275794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275801 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_3275801 : Nat := 118140960795 + 3275801 * 2 ^ 59
def prefixEnd_3275801 : Nat := 4983230072969 + 3 ^ 40 * 3275801 * 2
def baseEnd_3275801 : Nat := 1121373627652695431481581

theorem tailTrace_3275801 : CollatzResearch.WordTrace tailWord_3275801 prefixEnd_3275801 1121373627652695431481581 := by
  unfold tailWord_3275801
  simp only [CollatzResearch.WordTrace]
  refine ⟨119478278005339914114843257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79652185336893276076562171 119478278005339914114843257)
  ·
    refine ⟨89608708504004935586132443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119478278005339914114843257 89608708504004935586132443)
    ·
      refine ⟨134413062756007403379198665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89608708504004935586132443 134413062756007403379198665)
      ·
        refine ⟨100809797067005552534398999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134413062756007403379198665 100809797067005552534398999)
        ·
          refine ⟨151214695600508328801598499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100809797067005552534398999 151214695600508328801598499)
          ·
            refine ⟨226822043400762493202397749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151214695600508328801598499 226822043400762493202397749)
            ·
              refine ⟨21264566568821483737724789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226822043400762493202397749 21264566568821483737724789)
              ·
                refine ⟨1993553115827014100411699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21264566568821483737724789 1993553115827014100411699)
                ·
                  refine ⟨2990329673740521150617549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993553115827014100411699 2990329673740521150617549)
                  ·
                    refine ⟨1121373627652695431481581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990329673740521150617549 1121373627652695431481581)
                    ·
                      rfl

theorem cell22_3275801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_3275801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275801 prefixEnd_3275801 := by exact prefixLift 3275801
  have htrace : WordTrace (prefixWord ++ tailWord_3275801) baseStart_3275801 baseEnd_3275801 := by
    simpa [prefixWord, tailWord_3275801, baseEnd_3275801] using wordTrace_append hprefix tailTrace_3275801
  have hstable : (prefixWord ++ tailWord_3275801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275801).length < 2 ^ (prefixWord ++ tailWord_3275801).sum := by decide
  have hdescent : baseEnd_3275801 < baseStart_3275801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275818 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3275818 : Nat := 118140960795 + 3275818 * 2 ^ 59
def prefixEnd_3275818 : Nat := 4983230072969 + 3 ^ 40 * 3275818 * 2
def baseEnd_3275818 : Nat := 1121379447100113053806529

theorem tailTrace_3275818 : CollatzResearch.WordTrace tailWord_3275818 prefixEnd_3275818 1121379447100113053806529 := by
  unfold tailWord_3275818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29869724511569581504553027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79652598697518884012141405 29869724511569581504553027)
  ·
    refine ⟨44804586767354372256829541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29869724511569581504553027 44804586767354372256829541)
    ·
      refine ⟨8400860018878944798155539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44804586767354372256829541 8400860018878944798155539)
      ·
        refine ⟨12601290028318417197233309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8400860018878944798155539 12601290028318417197233309)
        ·
          refine ⟨4725483760619406448962491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12601290028318417197233309 4725483760619406448962491)
          ·
            refine ⟨7088225640929109673443737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725483760619406448962491 7088225640929109673443737)
            ·
              refine ⟨5316169230696832255082803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088225640929109673443737 5316169230696832255082803)
              ·
                refine ⟨7974253846045248382624205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316169230696832255082803 7974253846045248382624205)
                ·
                  refine ⟨2990345192266968143484077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7974253846045248382624205 2990345192266968143484077)
                  ·
                    refine ⟨1121379447100113053806529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990345192266968143484077 1121379447100113053806529)
                    ·
                      rfl

theorem cell22_3275818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3275818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275818 prefixEnd_3275818 := by exact prefixLift 3275818
  have htrace : WordTrace (prefixWord ++ tailWord_3275818) baseStart_3275818 baseEnd_3275818 := by
    simpa [prefixWord, tailWord_3275818, baseEnd_3275818] using wordTrace_append hprefix tailTrace_3275818
  have hstable : (prefixWord ++ tailWord_3275818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275818).length < 2 ^ (prefixWord ++ tailWord_3275818).sum := by decide
  have hdescent : baseEnd_3275818 < baseStart_3275818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275936 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_3275936 : Nat := 118140960795 + 3275936 * 2 ^ 59
def prefixEnd_3275936 : Nat := 4983230072969 + 3 ^ 40 * 3275936 * 2
def baseEnd_3275936 : Nat := 1121419840911600079356167

theorem tailTrace_3275936 : CollatzResearch.WordTrace tailWord_3275936 prefixEnd_3275936 1121419840911600079356167 := by
  unfold tailWord_3275936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59741600929925416085503831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79655467906567221447338441 59741600929925416085503831)
  ·
    refine ⟨89612401394888124128255747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59741600929925416085503831 89612401394888124128255747)
    ·
      refine ⟨134418602092332186192383621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89612401394888124128255747 134418602092332186192383621)
      ·
        refine ⟨25203487892312284911071929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134418602092332186192383621 25203487892312284911071929)
        ·
          refine ⟨18902615919234213683303947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25203487892312284911071929 18902615919234213683303947)
          ·
            refine ⟨28353923878851320524955921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18902615919234213683303947 28353923878851320524955921)
            ·
              refine ⟨21265442909138490393716941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28353923878851320524955921 21265442909138490393716941)
              ·
                refine ⟨7974541090926933897643853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21265442909138490393716941 7974541090926933897643853)
                ·
                  refine ⟨2990452909097600211616445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7974541090926933897643853 2990452909097600211616445)
                  ·
                    refine ⟨1121419840911600079356167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990452909097600211616445 1121419840911600079356167)
                    ·
                      rfl

theorem cell22_3275936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_3275936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275936 prefixEnd_3275936 := by exact prefixLift 3275936
  have htrace : WordTrace (prefixWord ++ tailWord_3275936) baseStart_3275936 baseEnd_3275936 := by
    simpa [prefixWord, tailWord_3275936, baseEnd_3275936] using wordTrace_append hprefix tailTrace_3275936
  have hstable : (prefixWord ++ tailWord_3275936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275936).length < 2 ^ (prefixWord ++ tailWord_3275936).sum := by decide
  have hdescent : baseEnd_3275936 < baseStart_3275936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275938 : List Nat := [3, 3, 1, 3, 2, 2, 1, 7]
def baseStart_3275938 : Nat := 118140960795 + 3275938 * 2 ^ 59
def prefixEnd_3275938 : Nat := 4983230072969 + 3 ^ 40 * 3275938 * 2
def baseEnd_3275938 : Nat := 124602280616941415645129

theorem tailTrace_3275938 : CollatzResearch.WordTrace tailWord_3275938 prefixEnd_3275938 124602280616941415645129 := by
  unfold tailWord_3275938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870818701460896628145117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79655516537229057675053645 29870818701460896628145117)
  ·
    refine ⟨11201557013047836235554419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29870818701460896628145117 11201557013047836235554419)
    ·
      refine ⟨16802335519571754353331629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11201557013047836235554419 16802335519571754353331629)
      ·
        refine ⟨6300875819839407882499361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16802335519571754353331629 6300875819839407882499361)
        ·
          refine ⟨4725656864879555911874521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6300875819839407882499361 4725656864879555911874521)
          ·
            refine ⟨3544242648659666933905891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4725656864879555911874521 3544242648659666933905891)
            ·
              refine ⟨5316363972989500400858837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544242648659666933905891 5316363972989500400858837)
              ·
                refine ⟨124602280616941415645129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5316363972989500400858837 124602280616941415645129)
                ·
                  rfl

theorem cell22_3275938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_3275938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275938 prefixEnd_3275938 := by exact prefixLift 3275938
  have htrace : WordTrace (prefixWord ++ tailWord_3275938) baseStart_3275938 baseEnd_3275938 := by
    simpa [prefixWord, tailWord_3275938, baseEnd_3275938] using wordTrace_append hprefix tailTrace_3275938
  have hstable : (prefixWord ++ tailWord_3275938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275938).length < 2 ^ (prefixWord ++ tailWord_3275938).sum := by decide
  have hdescent : baseEnd_3275938 < baseStart_3275938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275953 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_3275953 : Nat := 118140960795 + 3275953 * 2 ^ 59
def prefixEnd_3275953 : Nat := 4983230072969 + 3 ^ 40 * 3275953 * 2
def baseEnd_3275953 : Nat := 1121425660359017701681115

theorem tailTrace_3275953 : CollatzResearch.WordTrace tailWord_3275953 prefixEnd_3275953 1121425660359017701681115 := by
  unfold tailWord_3275953
  simp only [CollatzResearch.WordTrace]
  refine ⟨119483821900789244074376513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79655881267192829382917675 119483821900789244074376513)
  ·
    refine ⟨89612866425591933055782385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119483821900789244074376513 89612866425591933055782385)
    ·
      refine ⟨67209649819193949791836789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89612866425591933055782385 67209649819193949791836789)
      ·
        refine ⟨6300904670549432792984699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67209649819193949791836789 6300904670549432792984699)
        ·
          refine ⟨9451357005824149189477049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300904670549432792984699 9451357005824149189477049)
          ·
            refine ⟨7088517754368111892107787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9451357005824149189477049 7088517754368111892107787)
            ·
              refine ⟨10632776631552167838161681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088517754368111892107787 10632776631552167838161681)
              ·
                refine ⟨7974582473664125878621261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10632776631552167838161681 7974582473664125878621261)
                ·
                  refine ⟨2990468427624047204482973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7974582473664125878621261 2990468427624047204482973)
                  ·
                    refine ⟨1121425660359017701681115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990468427624047204482973 1121425660359017701681115)
                    ·
                      rfl

theorem cell22_3275953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_3275953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275953 prefixEnd_3275953 := by exact prefixLift 3275953
  have htrace : WordTrace (prefixWord ++ tailWord_3275953) baseStart_3275953 baseEnd_3275953 := by
    simpa [prefixWord, tailWord_3275953, baseEnd_3275953] using wordTrace_append hprefix tailTrace_3275953
  have hstable : (prefixWord ++ tailWord_3275953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275953).length < 2 ^ (prefixWord ++ tailWord_3275953).sum := by decide
  have hdescent : baseEnd_3275953 < baseStart_3275953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275979 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_3275979 : Nat := 118140960795 + 3275979 * 2 ^ 59
def prefixEnd_3275979 : Nat := 4983230072969 + 3 ^ 40 * 3275979 * 2
def baseEnd_3275979 : Nat := 1121434560690362300531035

theorem tailTrace_3275979 : CollatzResearch.WordTrace tailWord_3275979 prefixEnd_3275979 1121434560690362300531035 := by
  unfold tailWord_3275979
  simp only [CollatzResearch.WordTrace]
  refine ⟨119484770198695050514822991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79656513465796700343215327 119484770198695050514822991)
  ·
    refine ⟨179227155298042575772234487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119484770198695050514822991 179227155298042575772234487)
    ·
      refine ⟨268840732947063863658351731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179227155298042575772234487 268840732947063863658351731)
      ·
        refine ⟨403261099420595795487527597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268840732947063863658351731 403261099420595795487527597)
        ·
          refine ⟨151222912282723423307822849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403261099420595795487527597 151222912282723423307822849)
          ·
            refine ⟨113417184212042567480867137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151222912282723423307822849 113417184212042567480867137)
            ·
              refine ⟨85062888159031925610650353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113417184212042567480867137 85062888159031925610650353)
              ·
                refine ⟨63797166119273944207987765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85062888159031925610650353 63797166119273944207987765)
                ·
                  refine ⟨5980984323681932269498853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63797166119273944207987765 5980984323681932269498853)
                  ·
                    refine ⟨1121434560690362300531035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980984323681932269498853 1121434560690362300531035)
                    ·
                      rfl

theorem cell22_3275979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_3275979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3275979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3275979 prefixEnd_3275979 := by exact prefixLift 3275979
  have htrace : WordTrace (prefixWord ++ tailWord_3275979) baseStart_3275979 baseEnd_3275979 := by
    simpa [prefixWord, tailWord_3275979, baseEnd_3275979] using wordTrace_append hprefix tailTrace_3275979
  have hstable : (prefixWord ++ tailWord_3275979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275979).length < 2 ^ (prefixWord ++ tailWord_3275979).sum := by decide
  have hdescent : baseEnd_3275979 < baseStart_3275979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276013 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3276013 : Nat := 118140960795 + 3276013 * 2 ^ 59
def prefixEnd_3276013 : Nat := 4983230072969 + 3 ^ 40 * 3276013 * 2
def baseEnd_3276013 : Nat := 1121446199585197545180931

theorem tailTrace_3276013 : CollatzResearch.WordTrace tailWord_3276013 prefixEnd_3276013 1121446199585197545180931 := by
  unfold tailWord_3276013
  simp only [CollatzResearch.WordTrace]
  refine ⟨119486010280571874321560693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79657340187047916214373795 119486010280571874321560693)
  ·
    refine ⟨11201813463803613217646315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119486010280571874321560693 11201813463803613217646315)
    ·
      refine ⟨16802720195705419826469473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11201813463803613217646315 16802720195705419826469473)
      ·
        refine ⟨12602040146779064869852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16802720195705419826469473 12602040146779064869852105)
        ·
          refine ⟨9451530110084298652389079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12602040146779064869852105 9451530110084298652389079)
          ·
            refine ⟨14177295165126447978583619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451530110084298652389079 14177295165126447978583619)
            ·
              refine ⟨21265942747689671967875429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177295165126447978583619 21265942747689671967875429)
              ·
                refine ⟨3987364265191813493976643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21265942747689671967875429 3987364265191813493976643)
                ·
                  refine ⟨5981046397787720240964965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987364265191813493976643 5981046397787720240964965)
                  ·
                    refine ⟨1121446199585197545180931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981046397787720240964965 1121446199585197545180931)
                    ·
                      rfl

theorem cell22_3276013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3276013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276013 prefixEnd_3276013 := by exact prefixLift 3276013
  have htrace : WordTrace (prefixWord ++ tailWord_3276013) baseStart_3276013 baseEnd_3276013 := by
    simpa [prefixWord, tailWord_3276013, baseEnd_3276013] using wordTrace_append hprefix tailTrace_3276013
  have hstable : (prefixWord ++ tailWord_3276013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276013).length < 2 ^ (prefixWord ++ tailWord_3276013).sum := by decide
  have hdescent : baseEnd_3276013 < baseStart_3276013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276026 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_3276026 : Nat := 118140960795 + 3276026 * 2 ^ 59
def prefixEnd_3276026 : Nat := 4983230072969 + 3 ^ 40 * 3276026 * 2
def baseEnd_3276026 : Nat := 1121450649750869844605891

theorem tailTrace_3276026 : CollatzResearch.WordTrace tailWord_3276026 prefixEnd_3276026 1121450649750869844605891 := by
  unfold tailWord_3276026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29871621107381194385445983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79657656286349851694522621 29871621107381194385445983)
  ·
    refine ⟨44807431661071791578168975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29871621107381194385445983 44807431661071791578168975)
    ·
      refine ⟨67211147491607687367253463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44807431661071791578168975 67211147491607687367253463)
      ·
        refine ⟨100816721237411531050880195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67211147491607687367253463 100816721237411531050880195)
        ·
          refine ⟨151225081856117296576320293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100816721237411531050880195 151225081856117296576320293)
          ·
            refine ⟨28354702848021993108060055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151225081856117296576320293 28354702848021993108060055)
            ·
              refine ⟨42532054272032989662090083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28354702848021993108060055 42532054272032989662090083)
              ·
                refine ⟨63798081408049484493135125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42532054272032989662090083 63798081408049484493135125)
                ·
                  refine ⟨2990535066002319585615709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63798081408049484493135125 2990535066002319585615709)
                  ·
                    refine ⟨1121450649750869844605891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990535066002319585615709 1121450649750869844605891)
                    ·
                      rfl

theorem cell22_3276026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_3276026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276026 prefixEnd_3276026 := by exact prefixLift 3276026
  have htrace : WordTrace (prefixWord ++ tailWord_3276026) baseStart_3276026 baseEnd_3276026 := by
    simpa [prefixWord, tailWord_3276026, baseEnd_3276026] using wordTrace_append hprefix tailTrace_3276026
  have hstable : (prefixWord ++ tailWord_3276026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276026).length < 2 ^ (prefixWord ++ tailWord_3276026).sum := by decide
  have hdescent : baseEnd_3276026 < baseStart_3276026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276041 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_3276041 : Nat := 118140960795 + 3276041 * 2 ^ 59
def prefixEnd_3276041 : Nat := 4983230072969 + 3 ^ 40 * 3276041 * 2
def baseEnd_3276041 : Nat := 1121455784557414805480845

theorem tailTrace_3276041 : CollatzResearch.WordTrace tailWord_3276041 prefixEnd_3276041 1121455784557414805480845 := by
  unfold tailWord_3276041
  simp only [CollatzResearch.WordTrace]
  refine ⟨119487031524470435103579977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79658021016313623402386651 119487031524470435103579977)
  ·
    refine ⟨89615273643352826327684983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119487031524470435103579977 89615273643352826327684983)
    ·
      refine ⟨134422910465029239491527475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89615273643352826327684983 134422910465029239491527475)
      ·
        refine ⟨201634365697543859237291213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134422910465029239491527475 201634365697543859237291213)
        ·
          refine ⟨75612887136578947213984205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201634365697543859237291213 75612887136578947213984205)
          ·
            refine ⟨28354832676217105205244077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75612887136578947213984205 28354832676217105205244077)
            ·
              refine ⟨10633062253581414451966529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28354832676217105205244077 10633062253581414451966529)
              ·
                refine ⟨7974796690186060838974897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10633062253581414451966529 7974796690186060838974897)
                ·
                  refine ⟨5981097517639545629231173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7974796690186060838974897 5981097517639545629231173)
                  ·
                    refine ⟨1121455784557414805480845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981097517639545629231173 1121455784557414805480845)
                    ·
                      rfl

theorem cell22_3276041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_3276041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276041 prefixEnd_3276041 := by exact prefixLift 3276041
  have htrace : WordTrace (prefixWord ++ tailWord_3276041) baseStart_3276041 baseEnd_3276041 := by
    simpa [prefixWord, tailWord_3276041, baseEnd_3276041] using wordTrace_append hprefix tailTrace_3276041
  have hstable : (prefixWord ++ tailWord_3276041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276041).length < 2 ^ (prefixWord ++ tailWord_3276041).sum := by decide
  have hdescent : baseEnd_3276041 < baseStart_3276041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276056 : List Nat := [2, 1, 2, 3, 1, 4, 2, 7]
def baseStart_3276056 : Nat := 118140960795 + 3276056 * 2 ^ 59
def prefixEnd_3276056 : Nat := 4983230072969 + 3 ^ 40 * 3276056 * 2
def baseEnd_3276056 : Nat := 124606768818217751817311

theorem tailTrace_3276056 : CollatzResearch.WordTrace tailWord_3276056 prefixEnd_3276056 124606768818217751817311 := by
  unfold tailWord_3276056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743789309708046332688011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79658385746277395110250681 59743789309708046332688011)
  ·
    refine ⟨89615683964562069499032017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59743789309708046332688011 89615683964562069499032017)
    ·
      refine ⟨67211762973421552124274013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89615683964562069499032017 67211762973421552124274013)
      ·
        refine ⟨25204411115033082046602755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67211762973421552124274013 25204411115033082046602755)
        ·
          refine ⟨37806616672549623069904133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25204411115033082046602755 37806616672549623069904133)
          ·
            refine ⟨7088740626103054325607025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37806616672549623069904133 7088740626103054325607025)
            ·
              refine ⟨5316555469577290744205269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088740626103054325607025 5316555469577290744205269)
              ·
                refine ⟨124606768818217751817311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5316555469577290744205269 124606768818217751817311)
                ·
                  rfl

theorem cell22_3276056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_3276056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276056 prefixEnd_3276056 := by exact prefixLift 3276056
  have htrace : WordTrace (prefixWord ++ tailWord_3276056) baseStart_3276056 baseEnd_3276056 := by
    simpa [prefixWord, tailWord_3276056, baseEnd_3276056] using wordTrace_append hprefix tailTrace_3276056
  have hstable : (prefixWord ++ tailWord_3276056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276056).length < 2 ^ (prefixWord ++ tailWord_3276056).sum := by decide
  have hdescent : baseEnd_3276056 < baseStart_3276056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276060 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3276060 : Nat := 118140960795 + 3276060 * 2 ^ 59
def prefixEnd_3276060 : Nat := 4983230072969 + 3 ^ 40 * 3276060 * 2
def baseEnd_3276060 : Nat := 1121462288645705089255787

theorem tailTrace_3276060 : CollatzResearch.WordTrace tailWord_3276060 prefixEnd_3276060 1121462288645705089255787 := by
  unfold tailWord_3276060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743862255700800674260817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79658483007601067565681089 59743862255700800674260817)
  ·
    refine ⟨44807896691775600505695613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59743862255700800674260817 44807896691775600505695613)
    ·
      refine ⟨16802961259415850189635855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44807896691775600505695613 16802961259415850189635855)
      ·
        refine ⟨25204441889123775284453783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16802961259415850189635855 25204441889123775284453783)
        ·
          refine ⟨37806662833685662926680675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25204441889123775284453783 37806662833685662926680675)
          ·
            refine ⟨56709994250528494390021013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37806662833685662926680675 56709994250528494390021013)
            ·
              refine ⟨2658280980493523174532235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56709994250528494390021013 2658280980493523174532235)
              ·
                refine ⟨3987421470740284761798353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658280980493523174532235 3987421470740284761798353)
                ·
                  refine ⟨2990566103055213571348765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987421470740284761798353 2990566103055213571348765)
                  ·
                    refine ⟨1121462288645705089255787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990566103055213571348765 1121462288645705089255787)
                    ·
                      rfl

theorem cell22_3276060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3276060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276060 prefixEnd_3276060 := by exact prefixLift 3276060
  have htrace : WordTrace (prefixWord ++ tailWord_3276060) baseStart_3276060 baseEnd_3276060 := by
    simpa [prefixWord, tailWord_3276060, baseEnd_3276060] using wordTrace_append hprefix tailTrace_3276060
  have hstable : (prefixWord ++ tailWord_3276060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276060).length < 2 ^ (prefixWord ++ tailWord_3276060).sum := by decide
  have hdescent : baseEnd_3276060 < baseStart_3276060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276146 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_3276146 : Nat := 118140960795 + 3276146 * 2 ^ 59
def prefixEnd_3276146 : Nat := 4983230072969 + 3 ^ 40 * 3276146 * 2
def baseEnd_3276146 : Nat := 373830576067743177201841

theorem tailTrace_3276146 : CollatzResearch.WordTrace tailWord_3276146 prefixEnd_3276146 373830576067743177201841 := by
  unfold tailWord_3276146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29872715297272509509038073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79660574126060025357434861 29872715297272509509038073)
  ·
    refine ⟨22404536472954382131778555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29872715297272509509038073 22404536472954382131778555)
    ·
      refine ⟨33606804709431573197667833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22404536472954382131778555 33606804709431573197667833)
      ·
        refine ⟨25205103532073679898250875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33606804709431573197667833 25205103532073679898250875)
        ·
          refine ⟨37807655298110519847376313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25205103532073679898250875 37807655298110519847376313)
          ·
            refine ⟨28355741473582889885532235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37807655298110519847376313 28355741473582889885532235)
            ·
              refine ⟨42533612210374334828298353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28355741473582889885532235 42533612210374334828298353)
              ·
                refine ⟨31900209157780751121223765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42533612210374334828298353 31900209157780751121223765)
                ·
                  refine ⟨373830576067743177201841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31900209157780751121223765 373830576067743177201841)
                  ·
                    rfl

theorem cell22_3276146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_3276146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276146 prefixEnd_3276146 := by exact prefixLift 3276146
  have htrace : WordTrace (prefixWord ++ tailWord_3276146) baseStart_3276146 baseEnd_3276146 := by
    simpa [prefixWord, tailWord_3276146, baseEnd_3276146] using wordTrace_append hprefix tailTrace_3276146
  have hstable : (prefixWord ++ tailWord_3276146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276146).length < 2 ^ (prefixWord ++ tailWord_3276146).sum := by decide
  have hdescent : baseEnd_3276146 < baseStart_3276146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276163 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 6]
def baseStart_3276163 : Nat := 118140960795 + 3276163 * 2 ^ 59
def prefixEnd_3276163 : Nat := 4983230072969 + 3 ^ 40 * 3276163 * 2
def baseEnd_3276163 : Nat := 373832515883549051310157

theorem tailTrace_3276163 : CollatzResearch.WordTrace tailWord_3276163 prefixEnd_3276163 373832515883549051310157 := by
  unfold tailWord_3276163
  simp only [CollatzResearch.WordTrace]
  refine ⟨119491481230028449939521143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79660987486685633293014095 119491481230028449939521143)
  ·
    refine ⟨179237221845042674909281715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119491481230028449939521143 179237221845042674909281715)
    ·
      refine ⟨268855832767564012363922573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179237221845042674909281715 268855832767564012363922573)
      ·
        refine ⟨100820937287836504636470965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268855832767564012363922573 100820937287836504636470965)
        ·
          refine ⟨9451962870734672309669153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100820937287836504636470965 9451962870734672309669153)
          ·
            refine ⟨7088972153051004232251865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9451962870734672309669153 7088972153051004232251865)
            ·
              refine ⟨5316729114788253174188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088972153051004232251865 5316729114788253174188899)
              ·
                refine ⟨7975093672182379761283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316729114788253174188899 7975093672182379761283349)
                ·
                  refine ⟨373832515883549051310157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7975093672182379761283349 373832515883549051310157)
                  ·
                    rfl

theorem cell22_3276163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_3276163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276163 prefixEnd_3276163 := by exact prefixLift 3276163
  have htrace : WordTrace (prefixWord ++ tailWord_3276163) baseStart_3276163 baseEnd_3276163 := by
    simpa [prefixWord, tailWord_3276163, baseEnd_3276163] using wordTrace_append hprefix tailTrace_3276163
  have hstable : (prefixWord ++ tailWord_3276163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276163).length < 2 ^ (prefixWord ++ tailWord_3276163).sum := by decide
  have hdescent : baseEnd_3276163 < baseStart_3276163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276270 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_3276270 : Nat := 118140960795 + 3276270 * 2 ^ 59
def prefixEnd_3276270 : Nat := 4983230072969 + 3 ^ 40 * 3276270 * 2
def baseEnd_3276270 : Nat := 373844725312444847168381

theorem tailTrace_3276270 : CollatzResearch.WordTrace tailWord_3276270 prefixEnd_3276270 373844725312444847168381 := by
  unfold tailWord_3276270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14936922980080100901708283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79663589227093871475777509 14936922980080100901708283)
  ·
    refine ⟨22405384470120151352562425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14936922980080100901708283 22405384470120151352562425)
    ·
      refine ⟨16804038352590113514421819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22405384470120151352562425 16804038352590113514421819)
      ·
        refine ⟨25206057528885170271632729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16804038352590113514421819 25206057528885170271632729)
        ·
          refine ⟨18904543146663877703724547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25206057528885170271632729 18904543146663877703724547)
          ·
            refine ⟨28356814719995816555586821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18904543146663877703724547 28356814719995816555586821)
            ·
              refine ⟨5316902759999215604172529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28356814719995816555586821 5316902759999215604172529)
              ·
                refine ⟨3987677069999411703129397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316902759999215604172529 3987677069999411703129397)
                ·
                  refine ⟨373844725312444847168381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3987677069999411703129397 373844725312444847168381)
                  ·
                    rfl

theorem cell22_3276270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_3276270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276270 prefixEnd_3276270 := by exact prefixLift 3276270
  have htrace : WordTrace (prefixWord ++ tailWord_3276270) baseStart_3276270 baseEnd_3276270 := by
    simpa [prefixWord, tailWord_3276270, baseEnd_3276270] using wordTrace_append hprefix tailTrace_3276270
  have hstable : (prefixWord ++ tailWord_3276270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276270).length < 2 ^ (prefixWord ++ tailWord_3276270).sum := by decide
  have hdescent : baseEnd_3276270 < baseStart_3276270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276274 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3276274 : Nat := 118140960795 + 3276274 * 2 ^ 59
def prefixEnd_3276274 : Nat := 4983230072969 + 3 ^ 40 * 3276274 * 2
def baseEnd_3276274 : Nat := 1121535545219079864405131

theorem tailTrace_3276274 : CollatzResearch.WordTrace tailWord_3276274 prefixEnd_3276274 1121535545219079864405131 := by
  unfold tailWord_3276274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873882433156578974202969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79663686488417543931207917 29873882433156578974202969)
  ·
    refine ⟨22405411824867434230652227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873882433156578974202969 22405411824867434230652227)
    ·
      refine ⟨33608117737301151345978341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22405411824867434230652227 33608117737301151345978341)
      ·
        refine ⟨6301522075743965877370939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33608117737301151345978341 6301522075743965877370939)
        ·
          refine ⟨9452283113615948816056409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301522075743965877370939 9452283113615948816056409)
          ·
            refine ⟨7089212335211961612042307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9452283113615948816056409 7089212335211961612042307)
            ·
              refine ⟨10633818502817942418063461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089212335211961612042307 10633818502817942418063461)
              ·
                refine ⟨1993840969278364203386899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10633818502817942418063461 1993840969278364203386899)
                ·
                  refine ⟨2990761453917546305080349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993840969278364203386899 2990761453917546305080349)
                  ·
                    refine ⟨1121535545219079864405131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990761453917546305080349 1121535545219079864405131)
                    ·
                      rfl

theorem cell22_3276274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3276274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276274 prefixEnd_3276274 := by exact prefixLift 3276274
  have htrace : WordTrace (prefixWord ++ tailWord_3276274) baseStart_3276274 baseEnd_3276274 := by
    simpa [prefixWord, tailWord_3276274, baseEnd_3276274] using wordTrace_append hprefix tailTrace_3276274
  have hstable : (prefixWord ++ tailWord_3276274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276274).length < 2 ^ (prefixWord ++ tailWord_3276274).sum := by decide
  have hdescent : baseEnd_3276274 < baseStart_3276274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276298 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_3276298 : Nat := 118140960795 + 3276298 * 2 ^ 59
def prefixEnd_3276298 : Nat := 4983230072969 + 3 ^ 40 * 3276298 * 2
def baseEnd_3276298 : Nat := 373847920303183933935019

theorem tailTrace_3276298 : CollatzResearch.WordTrace tailWord_3276298 prefixEnd_3276298 373847920303183933935019 := by
  unfold tailWord_3276298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874101271134841998921387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79664270056359578663790365 29874101271134841998921387)
  ·
    refine ⟨44811151906702262998382081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29874101271134841998921387 44811151906702262998382081)
    ·
      refine ⟨33608363930026697248786561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44811151906702262998382081 33608363930026697248786561)
      ·
        refine ⟨25206272947520022936589921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33608363930026697248786561 25206272947520022936589921)
        ·
          refine ⟨18904704710640017202442441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25206272947520022936589921 18904704710640017202442441)
          ·
            refine ⟨14178528532980012901831831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18904704710640017202442441 14178528532980012901831831)
            ·
              refine ⟨21267792799470019352747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178528532980012901831831 21267792799470019352747747)
              ·
                refine ⟨31901689199205029029121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21267792799470019352747747 31901689199205029029121621)
                ·
                  refine ⟨373847920303183933935019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31901689199205029029121621 373847920303183933935019)
                  ·
                    rfl

theorem cell22_3276298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_3276298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276298 prefixEnd_3276298 := by exact prefixLift 3276298
  have htrace : WordTrace (prefixWord ++ tailWord_3276298) baseStart_3276298 baseEnd_3276298 := by
    simpa [prefixWord, tailWord_3276298, baseEnd_3276298] using wordTrace_append hprefix tailTrace_3276298
  have hstable : (prefixWord ++ tailWord_3276298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276298).length < 2 ^ (prefixWord ++ tailWord_3276298).sum := by decide
  have hdescent : baseEnd_3276298 < baseStart_3276298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276373 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3276373 : Nat := 118140960795 + 3276373 * 2 ^ 59
def prefixEnd_3276373 : Nat := 4983230072969 + 3 ^ 40 * 3276373 * 2
def baseEnd_3276373 : Nat := 1121569434942276606179827

theorem tailTrace_3276373 : CollatzResearch.WordTrace tailWord_3276373 prefixEnd_3276373 1121569434942276606179827 := by
  unfold tailWord_3276373
  simp only [CollatzResearch.WordTrace]
  refine ⟨119499140559267655804665773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79666093706178437203110515 119499140559267655804665773)
  ·
    refine ⟨44812177709725370926749665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119499140559267655804665773 44812177709725370926749665)
    ·
      refine ⟨33609133282294028195062249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44812177709725370926749665 33609133282294028195062249)
      ·
        refine ⟨25206849961720521146296687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33609133282294028195062249 25206849961720521146296687)
        ·
          refine ⟨37810274942580781719445031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25206849961720521146296687 37810274942580781719445031)
          ·
            refine ⟨56715412413871172579167547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37810274942580781719445031 56715412413871172579167547)
            ·
              refine ⟨85073118620806758868751321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56715412413871172579167547 85073118620806758868751321)
              ·
                refine ⟨63804838965605069151563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85073118620806758868751321 63804838965605069151563491)
                ·
                  refine ⟨95707258448407603727345237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63804838965605069151563491 95707258448407603727345237)
                  ·
                    refine ⟨1121569434942276606179827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95707258448407603727345237 1121569434942276606179827)
                    ·
                      rfl

theorem cell22_3276373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3276373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276373 prefixEnd_3276373 := by exact prefixLift 3276373
  have htrace : WordTrace (prefixWord ++ tailWord_3276373) baseStart_3276373 baseEnd_3276373 := by
    simpa [prefixWord, tailWord_3276373, baseEnd_3276373] using wordTrace_append hprefix tailTrace_3276373
  have hstable : (prefixWord ++ tailWord_3276373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276373).length < 2 ^ (prefixWord ++ tailWord_3276373).sum := by decide
  have hdescent : baseEnd_3276373 < baseStart_3276373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276398 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3276398 : Nat := 118140960795 + 3276398 * 2 ^ 59
def prefixEnd_3276398 : Nat := 4983230072969 + 3 ^ 40 * 3276398 * 2
def baseEnd_3276398 : Nat := 1121577992953184874304751

theorem tailTrace_3276398 : CollatzResearch.WordTrace tailWord_3276398 prefixEnd_3276398 1121577992953184874304751 := by
  unfold tailWord_3276398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937506548022135634290731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79666701589451390049550565 14937506548022135634290731)
  ·
    refine ⟨22406259822033203451436097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14937506548022135634290731 22406259822033203451436097)
    ·
      refine ⟨16804694866524902588577073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22406259822033203451436097 16804694866524902588577073)
      ·
        refine ⟨12603521149893676941432805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16804694866524902588577073 12603521149893676941432805)
        ·
          refine ⟨2363160215605064426518651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12603521149893676941432805 2363160215605064426518651)
          ·
            refine ⟨3544740323407596639777977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363160215605064426518651 3544740323407596639777977)
            ·
              refine ⟨2658555242555697479833483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544740323407596639777977 2658555242555697479833483)
              ·
                refine ⟨3987832863833546219750225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658555242555697479833483 3987832863833546219750225)
                ·
                  refine ⟨2990874647875159664812669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987832863833546219750225 2990874647875159664812669)
                  ·
                    refine ⟨1121577992953184874304751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990874647875159664812669 1121577992953184874304751)
                    ·
                      rfl

theorem cell22_3276398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3276398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276398 prefixEnd_3276398 := by exact prefixLift 3276398
  have htrace : WordTrace (prefixWord ++ tailWord_3276398) baseStart_3276398 baseEnd_3276398 := by
    simpa [prefixWord, tailWord_3276398, baseEnd_3276398] using wordTrace_append hprefix tailTrace_3276398
  have hstable : (prefixWord ++ tailWord_3276398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276398).length < 2 ^ (prefixWord ++ tailWord_3276398).sum := by decide
  have hdescent : baseEnd_3276398 < baseStart_3276398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276403 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_3276403 : Nat := 118140960795 + 3276403 * 2 ^ 59
def prefixEnd_3276403 : Nat := 4983230072969 + 3 ^ 40 * 3276403 * 2
def baseEnd_3276403 : Nat := 1121579704555366527929735

theorem tailTrace_3276403 : CollatzResearch.WordTrace tailWord_3276403 prefixEnd_3276403 1121579704555366527929735 := by
  unfold tailWord_3276403
  simp only [CollatzResearch.WordTrace]
  refine ⟨119500234749158970928257863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79666823166105980618838575 119500234749158970928257863)
  ·
    refine ⟨179250352123738456392386795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119500234749158970928257863 179250352123738456392386795)
    ·
      refine ⟨268875528185607684588580193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179250352123738456392386795 268875528185607684588580193)
      ·
        refine ⟨201656646139205763441435145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268875528185607684588580193 201656646139205763441435145)
        ·
          refine ⟨151242484604404322581076359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201656646139205763441435145 151242484604404322581076359)
          ·
            refine ⟨226863726906606483871614539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151242484604404322581076359 226863726906606483871614539)
            ·
              refine ⟨340295590359909725807421809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226863726906606483871614539 340295590359909725807421809)
              ·
                refine ⟨255221692769932294355566357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340295590359909725807421809 255221692769932294355566357)
                ·
                  refine ⟨11963516848590576297917173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255221692769932294355566357 11963516848590576297917173)
                  ·
                    refine ⟨1121579704555366527929735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11963516848590576297917173 1121579704555366527929735)
                    ·
                      rfl

theorem cell22_3276403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_3276403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276403 prefixEnd_3276403 := by exact prefixLift 3276403
  have htrace : WordTrace (prefixWord ++ tailWord_3276403) baseStart_3276403 baseEnd_3276403 := by
    simpa [prefixWord, tailWord_3276403, baseEnd_3276403] using wordTrace_append hprefix tailTrace_3276403
  have hstable : (prefixWord ++ tailWord_3276403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276403).length < 2 ^ (prefixWord ++ tailWord_3276403).sum := by decide
  have hdescent : baseEnd_3276403 < baseStart_3276403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276433 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 10]
def baseStart_3276433 : Nat := 118140960795 + 3276433 * 2 ^ 59
def prefixEnd_3276433 : Nat := 4983230072969 + 3 ^ 40 * 3276433 * 2
def baseEnd_3276433 : Nat := 373863324722818816559881

theorem tailTrace_3276433 : CollatzResearch.WordTrace tailWord_3276433 prefixEnd_3276433 373863324722818816559881 := by
  unfold tailWord_3276433
  simp only [CollatzResearch.WordTrace]
  refine ⟨119501328939050286051849953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79667552626033524034566635 119501328939050286051849953)
  ·
    refine ⟨89625996704287714538887465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119501328939050286051849953 89625996704287714538887465)
    ·
      refine ⟨67219497528215785904165599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89625996704287714538887465 67219497528215785904165599)
      ·
        refine ⟨100829246292323678856248399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67219497528215785904165599 100829246292323678856248399)
        ·
          refine ⟨151243869438485518284372599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100829246292323678856248399 151243869438485518284372599)
          ·
            refine ⟨226865804157728277426558899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151243869438485518284372599 226865804157728277426558899)
            ·
              refine ⟨340298706236592416139838349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226865804157728277426558899 340298706236592416139838349)
              ·
                refine ⟨127612014838722156052439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340298706236592416139838349 127612014838722156052439381)
                ·
                  refine ⟨373863324722818816559881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127612014838722156052439381 373863324722818816559881)
                  ·
                    rfl

theorem cell22_3276433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_3276433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276433 prefixEnd_3276433 := by exact prefixLift 3276433
  have htrace : WordTrace (prefixWord ++ tailWord_3276433) baseStart_3276433 baseEnd_3276433 := by
    simpa [prefixWord, tailWord_3276433, baseEnd_3276433] using wordTrace_append hprefix tailTrace_3276433
  have hstable : (prefixWord ++ tailWord_3276433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276433).length < 2 ^ (prefixWord ++ tailWord_3276433).sum := by decide
  have hdescent : baseEnd_3276433 < baseStart_3276433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276480 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_3276480 : Nat := 118140960795 + 3276480 * 2 ^ 59
def prefixEnd_3276480 : Nat := 4983230072969 + 3 ^ 40 * 3276480 * 2
def baseEnd_3276480 : Nat := 1121606063228963993754499

theorem tailTrace_3276480 : CollatzResearch.WordTrace tailWord_3276480 prefixEnd_3276480 1121606063228963993754499 := by
  unfold tailWord_3276480
  simp only [CollatzResearch.WordTrace]
  refine ⟨59751521584940006539405447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79668695446586675385873929 59751521584940006539405447)
  ·
    refine ⟨89627282377410009809108171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59751521584940006539405447 89627282377410009809108171)
    ·
      refine ⟨134440923566115014713662257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627282377410009809108171 134440923566115014713662257)
      ·
        refine ⟨100830692674586261035246693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134440923566115014713662257 100830692674586261035246693)
        ·
          refine ⟨18905754876484923944108755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100830692674586261035246693 18905754876484923944108755)
          ·
            refine ⟨28358632314727385916163133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18905754876484923944108755 28358632314727385916163133)
            ·
              refine ⟨10634487118022769718561175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28358632314727385916163133 10634487118022769718561175)
              ·
                refine ⟨15951730677034154577841763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634487118022769718561175 15951730677034154577841763)
                ·
                  refine ⟨23927596015551231866762645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15951730677034154577841763 23927596015551231866762645)
                  ·
                    refine ⟨1121606063228963993754499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23927596015551231866762645 1121606063228963993754499)
                    ·
                      rfl

theorem cell22_3276480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_3276480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276480 prefixEnd_3276480 := by exact prefixLift 3276480
  have htrace : WordTrace (prefixWord ++ tailWord_3276480) baseStart_3276480 baseEnd_3276480 := by
    simpa [prefixWord, tailWord_3276480, baseEnd_3276480] using wordTrace_append hprefix tailTrace_3276480
  have hstable : (prefixWord ++ tailWord_3276480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276480).length < 2 ^ (prefixWord ++ tailWord_3276480).sum := by decide
  have hdescent : baseEnd_3276480 < baseStart_3276480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276484 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3276484 : Nat := 118140960795 + 3276484 * 2 ^ 59
def prefixEnd_3276484 : Nat := 4983230072969 + 3 ^ 40 * 3276484 * 2
def baseEnd_3276484 : Nat := 373869144170236438884829

theorem tailTrace_3276484 : CollatzResearch.WordTrace tailWord_3276484 prefixEnd_3276484 373869144170236438884829 := by
  unfold tailWord_3276484
  simp only [CollatzResearch.WordTrace]
  refine ⟨59751594530932760880978253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79668792707910347841304337 59751594530932760880978253)
  ·
    refine ⟨22406847949099785330366845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59751594530932760880978253 22406847949099785330366845)
    ·
      refine ⟨8402567980912419498887567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22406847949099785330366845 8402567980912419498887567)
      ·
        refine ⟨12603851971368629248331351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8402567980912419498887567 12603851971368629248331351)
        ·
          refine ⟨18905777957052943872497027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12603851971368629248331351 18905777957052943872497027)
          ·
            refine ⟨28358666935579415808745541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18905777957052943872497027 28358666935579415808745541)
            ·
              refine ⟨5317250050421140464139789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28358666935579415808745541 5317250050421140464139789)
              ·
                refine ⟨1993968768907927674052421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317250050421140464139789 1993968768907927674052421)
                ·
                  refine ⟨373869144170236438884829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993968768907927674052421 373869144170236438884829)
                  ·
                    rfl

theorem cell22_3276484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3276484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276484 prefixEnd_3276484 := by exact prefixLift 3276484
  have htrace : WordTrace (prefixWord ++ tailWord_3276484) baseStart_3276484 baseEnd_3276484 := by
    simpa [prefixWord, tailWord_3276484, baseEnd_3276484] using wordTrace_append hprefix tailTrace_3276484
  have hstable : (prefixWord ++ tailWord_3276484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276484).length < 2 ^ (prefixWord ++ tailWord_3276484).sum := by decide
  have hdescent : baseEnd_3276484 < baseStart_3276484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276527 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 3, 3]
def baseStart_3276527 : Nat := 118140960795 + 3276527 * 2 ^ 59
def prefixEnd_3276527 : Nat := 4983230072969 + 3 ^ 40 * 3276527 * 2
def baseEnd_3276527 : Nat := 1121622152289471537829355

theorem tailTrace_3276527 : CollatzResearch.WordTrace tailWord_3276527 prefixEnd_3276527 1121622152289471537829355 := by
  unfold tailWord_3276527
  simp only [CollatzResearch.WordTrace]
  refine ⟨119504757400709740105771835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79669838267139826737181223 119504757400709740105771835)
  ·
    refine ⟨179257136101064610158657753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119504757400709740105771835 179257136101064610158657753)
    ·
      refine ⟨134442852075798457618993315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179257136101064610158657753 134442852075798457618993315)
      ·
        refine ⟨201664278113697686428489973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134442852075798457618993315 201664278113697686428489973)
        ·
          refine ⟨18906026073159158102670935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201664278113697686428489973 18906026073159158102670935)
          ·
            refine ⟨28359039109738737154006403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18906026073159158102670935 28359039109738737154006403)
            ·
              refine ⟨42538558664608105731009605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359039109738737154006403 42538558664608105731009605)
              ·
                refine ⟨7975979749614019824564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42538558664608105731009605 7975979749614019824564301)
                ·
                  refine ⟨2990992406105257434211613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7975979749614019824564301 2990992406105257434211613)
                  ·
                    refine ⟨1121622152289471537829355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2990992406105257434211613 1121622152289471537829355)
                    ·
                      rfl

theorem cell22_3276527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_3276527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276527 prefixEnd_3276527 := by exact prefixLift 3276527
  have htrace : WordTrace (prefixWord ++ tailWord_3276527) baseStart_3276527 baseEnd_3276527 := by
    simpa [prefixWord, tailWord_3276527, baseEnd_3276527] using wordTrace_append hprefix tailTrace_3276527
  have hstable : (prefixWord ++ tailWord_3276527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276527).length < 2 ^ (prefixWord ++ tailWord_3276527).sum := by decide
  have hdescent : baseEnd_3276527 < baseStart_3276527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276540 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3276540 : Nat := 118140960795 + 3276540 * 2 ^ 59
def prefixEnd_3276540 : Nat := 4983230072969 + 3 ^ 40 * 3276540 * 2
def baseEnd_3276540 : Nat := 373875534151714612418105

theorem tailTrace_3276540 : CollatzResearch.WordTrace tailWord_3276540 prefixEnd_3276540 373875534151714612418105 := by
  unfold tailWord_3276540
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752615774831321662997537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79670154366441762217330049 59752615774831321662997537)
  ·
    refine ⟨44814461831123491247248153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59752615774831321662997537 44814461831123491247248153)
    ·
      refine ⟨33610846373342618435436115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44814461831123491247248153 33610846373342618435436115)
      ·
        refine ⟨50416269560013927653154173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33610846373342618435436115 50416269560013927653154173)
        ·
          refine ⟨18906101085005222869932815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50416269560013927653154173 18906101085005222869932815)
          ·
            refine ⟨28359151627507834304899223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18906101085005222869932815 28359151627507834304899223)
            ·
              refine ⟨42538727441261751457348835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359151627507834304899223 42538727441261751457348835)
              ·
                refine ⟨63808091161892627186023253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42538727441261751457348835 63808091161892627186023253)
                ·
                  refine ⟨373875534151714612418105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63808091161892627186023253 373875534151714612418105)
                  ·
                    rfl

theorem cell22_3276540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3276540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276540 prefixEnd_3276540 := by exact prefixLift 3276540
  have htrace : WordTrace (prefixWord ++ tailWord_3276540) baseStart_3276540 baseEnd_3276540 := by
    simpa [prefixWord, tailWord_3276540, baseEnd_3276540] using wordTrace_append hprefix tailTrace_3276540
  have hstable : (prefixWord ++ tailWord_3276540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276540).length < 2 ^ (prefixWord ++ tailWord_3276540).sum := by decide
  have hdescent : baseEnd_3276540 < baseStart_3276540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276555 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_3276555 : Nat := 118140960795 + 3276555 * 2 ^ 59
def prefixEnd_3276555 : Nat := 4983230072969 + 3 ^ 40 * 3276555 * 2
def baseEnd_3276555 : Nat := 1121631737261688798129269

theorem tailTrace_3276555 : CollatzResearch.WordTrace tailWord_3276555 prefixEnd_3276555 1121631737261688798129269 := by
  unfold tailWord_3276555
  simp only [CollatzResearch.WordTrace]
  refine ⟨119505778644608300887791119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79670519096405533925194079 119505778644608300887791119)
  ·
    refine ⟨179258667966912451331686679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119505778644608300887791119 179258667966912451331686679)
    ·
      refine ⟨268888001950368676997530019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179258667966912451331686679 268888001950368676997530019)
      ·
        refine ⟨403332002925553015496295029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268888001950368676997530019 403332002925553015496295029)
        ·
          refine ⟨37812375274270595202777659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 403332002925553015496295029 37812375274270595202777659)
          ·
            refine ⟨56718562911405892804166489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37812375274270595202777659 56718562911405892804166489)
            ·
              refine ⟨42538922183554419603124867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56718562911405892804166489 42538922183554419603124867)
              ·
                refine ⟨63808383275331629404687301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42538922183554419603124867 63808383275331629404687301)
                ·
                  refine ⟨11964071864124680513378869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63808383275331629404687301 11964071864124680513378869)
                  ·
                    refine ⟨1121631737261688798129269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11964071864124680513378869 1121631737261688798129269)
                    ·
                      rfl

theorem cell22_3276555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_3276555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276555 prefixEnd_3276555 := by exact prefixLift 3276555
  have htrace : WordTrace (prefixWord ++ tailWord_3276555) baseStart_3276555 baseEnd_3276555 := by
    simpa [prefixWord, tailWord_3276555, baseEnd_3276555] using wordTrace_append hprefix tailTrace_3276555
  have hstable : (prefixWord ++ tailWord_3276555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276555).length < 2 ^ (prefixWord ++ tailWord_3276555).sum := by decide
  have hdescent : baseEnd_3276555 < baseStart_3276555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276634 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_3276634 : Nat := 118140960795 + 3276634 * 2 ^ 59
def prefixEnd_3276634 : Nat := 4983230072969 + 3 ^ 40 * 3276634 * 2
def baseEnd_3276634 : Nat := 1121658780576158925404027

theorem tailTrace_3276634 : CollatzResearch.WordTrace tailWord_3276634 prefixEnd_3276634 1121658780576158925404027 := by
  unfold tailWord_3276634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29877165002830524344979239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79672440007548064919944637 29877165002830524344979239)
  ·
    refine ⟨44815747504245786517468859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29877165002830524344979239 44815747504245786517468859)
    ·
      refine ⟨67223621256368679776203289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44815747504245786517468859 67223621256368679776203289)
      ·
        refine ⟨50417715942276509832152467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67223621256368679776203289 50417715942276509832152467)
        ·
          refine ⟨75626573913414764748228701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50417715942276509832152467 75626573913414764748228701)
          ·
            refine ⟨28359965217530536780585763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75626573913414764748228701 28359965217530536780585763)
            ·
              refine ⟨42539947826295805170878645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359965217530536780585763 42539947826295805170878645)
              ·
                refine ⟨3988120108715231734769873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42539947826295805170878645 3988120108715231734769873)
                ·
                  refine ⟨2991090081536423801077405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988120108715231734769873 2991090081536423801077405)
                  ·
                    refine ⟨1121658780576158925404027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991090081536423801077405 1121658780576158925404027)
                    ·
                      rfl

theorem cell22_3276634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_3276634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276634 prefixEnd_3276634 := by exact prefixLift 3276634
  have htrace : WordTrace (prefixWord ++ tailWord_3276634) baseStart_3276634 baseEnd_3276634 := by
    simpa [prefixWord, tailWord_3276634, baseEnd_3276634] using wordTrace_append hprefix tailTrace_3276634
  have hstable : (prefixWord ++ tailWord_3276634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276634).length < 2 ^ (prefixWord ++ tailWord_3276634).sum := by decide
  have hdescent : baseEnd_3276634 < baseStart_3276634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276769 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3276769 : Nat := 118140960795 + 3276769 * 2 ^ 59
def prefixEnd_3276769 : Nat := 4983230072969 + 3 ^ 40 * 3276769 * 2
def baseEnd_3276769 : Nat := 1121704993835063573278613

theorem tailTrace_3276769 : CollatzResearch.WordTrace tailWord_3276769 prefixEnd_3276769 1121704993835063573278613 := by
  unfold tailWord_3276769
  simp only [CollatzResearch.WordTrace]
  refine ⟨119513583865833015436081361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79675722577222010290720907 119513583865833015436081361)
  ·
    refine ⟨89635187899374761577061021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119513583865833015436081361 89635187899374761577061021)
    ·
      refine ⟨33613195462265535591397883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89635187899374761577061021 33613195462265535591397883)
      ·
        refine ⟨50419793193398303387096825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33613195462265535591397883 50419793193398303387096825)
        ·
          refine ⟨37814844895048727540322619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50419793193398303387096825 37814844895048727540322619)
          ·
            refine ⟨56722267342573091310483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37814844895048727540322619 56722267342573091310483929)
            ·
              refine ⟨42541700506929818482862947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56722267342573091310483929 42541700506929818482862947)
              ·
                refine ⟨63812550760394727724294421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42541700506929818482862947 63812550760394727724294421)
                ·
                  refine ⟨2991213316893502862076301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63812550760394727724294421 2991213316893502862076301)
                  ·
                    refine ⟨1121704993835063573278613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991213316893502862076301 1121704993835063573278613)
                    ·
                      rfl

theorem cell22_3276769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3276769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276769 prefixEnd_3276769 := by exact prefixLift 3276769
  have htrace : WordTrace (prefixWord ++ tailWord_3276769) baseStart_3276769 baseEnd_3276769 := by
    simpa [prefixWord, tailWord_3276769, baseEnd_3276769] using wordTrace_append hprefix tailTrace_3276769
  have hstable : (prefixWord ++ tailWord_3276769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276769).length < 2 ^ (prefixWord ++ tailWord_3276769).sum := by decide
  have hdescent : baseEnd_3276769 < baseStart_3276769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276784 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_3276784 : Nat := 118140960795 + 3276784 * 2 ^ 59
def prefixEnd_3276784 : Nat := 4983230072969 + 3 ^ 40 * 3276784 * 2
def baseEnd_3276784 : Nat := 1121710128641608534153567

theorem tailTrace_3276784 : CollatzResearch.WordTrace tailWord_3276784 prefixEnd_3276784 1121710128641608534153567 := by
  unfold tailWord_3276784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59757065480389336498938703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79676087307185781998584937 59757065480389336498938703)
  ·
    refine ⟨89635598220584004748408055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59757065480389336498938703 89635598220584004748408055)
    ·
      refine ⟨134453397330876007122612083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89635598220584004748408055 134453397330876007122612083)
      ·
        refine ⟨201680095996314010683918125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134453397330876007122612083 201680095996314010683918125)
        ·
          refine ⟨75630035998617754006469297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201680095996314010683918125 75630035998617754006469297)
          ·
            refine ⟨56722526998963315504851973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75630035998617754006469297 56722526998963315504851973)
            ·
              refine ⟨10635473812305621657159745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56722526998963315504851973 10635473812305621657159745)
              ·
                refine ⟨7976605359229216242869809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10635473812305621657159745 7976605359229216242869809)
                ·
                  refine ⟨5982454019421912182152357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976605359229216242869809 5982454019421912182152357)
                  ·
                    refine ⟨1121710128641608534153567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5982454019421912182152357 1121710128641608534153567)
                    ·
                      rfl

theorem cell22_3276784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_3276784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276784 prefixEnd_3276784 := by exact prefixLift 3276784
  have htrace : WordTrace (prefixWord ++ tailWord_3276784) baseStart_3276784 baseEnd_3276784 := by
    simpa [prefixWord, tailWord_3276784, baseEnd_3276784] using wordTrace_append hprefix tailTrace_3276784
  have hstable : (prefixWord ++ tailWord_3276784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276784).length < 2 ^ (prefixWord ++ tailWord_3276784).sum := by decide
  have hdescent : baseEnd_3276784 < baseStart_3276784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276844 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3276844 : Nat := 118140960795 + 3276844 * 2 ^ 59
def prefixEnd_3276844 : Nat := 4983230072969 + 3 ^ 40 * 3276844 * 2
def baseEnd_3276844 : Nat := 373910222622596125884461

theorem tailTrace_3276844 : CollatzResearch.WordTrace tailWord_3276844 prefixEnd_3276844 373910222622596125884461 := by
  unfold tailWord_3276844
  simp only [CollatzResearch.WordTrace]
  refine ⟨59758159670280651622530793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79677546227040868830041057 59758159670280651622530793)
  ·
    refine ⟨44818619752710488716898095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59758159670280651622530793 44818619752710488716898095)
    ·
      refine ⟨67227929629065733075347143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44818619752710488716898095 67227929629065733075347143)
      ·
        refine ⟨100841894443598599613020715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67227929629065733075347143 100841894443598599613020715)
        ·
          refine ⟨151262841665397899419531073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100841894443598599613020715 151262841665397899419531073)
          ·
            refine ⟨113447131249048424564648305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151262841665397899419531073 113447131249048424564648305)
            ·
              refine ⟨85085348436786318423486229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113447131249048424564648305 85085348436786318423486229)
              ·
                refine ⟨3988375707974358676100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85085348436786318423486229 3988375707974358676100917)
                ·
                  refine ⟨373910222622596125884461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3988375707974358676100917 373910222622596125884461)
                  ·
                    rfl

theorem cell22_3276844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3276844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276844 prefixEnd_3276844 := by exact prefixLift 3276844
  have htrace : WordTrace (prefixWord ++ tailWord_3276844) baseStart_3276844 baseEnd_3276844 := by
    simpa [prefixWord, tailWord_3276844, baseEnd_3276844] using wordTrace_append hprefix tailTrace_3276844
  have hstable : (prefixWord ++ tailWord_3276844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276844).length < 2 ^ (prefixWord ++ tailWord_3276844).sum := by decide
  have hdescent : baseEnd_3276844 < baseStart_3276844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276848 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_3276848 : Nat := 118140960795 + 3276848 * 2 ^ 59
def prefixEnd_3276848 : Nat := 4983230072969 + 3 ^ 40 * 3276848 * 2
def baseEnd_3276848 : Nat := 1121732037149533700553371

theorem tailTrace_3276848 : CollatzResearch.WordTrace tailWord_3276848 prefixEnd_3276848 1121732037149533700553371 := by
  unfold tailWord_3276848
  simp only [CollatzResearch.WordTrace]
  refine ⟨59758232616273405964103599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79677643488364541285471465 59758232616273405964103599)
  ·
    refine ⟨89637348924410108946155399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59758232616273405964103599 89637348924410108946155399)
    ·
      refine ⟨134456023386615163419233099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89637348924410108946155399 134456023386615163419233099)
      ·
        refine ⟨201684035079922745128849649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134456023386615163419233099 201684035079922745128849649)
        ·
          refine ⟨151263026309942058846637237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201684035079922745128849649 151263026309942058846637237)
          ·
            refine ⟨14180908716557068016872241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151263026309942058846637237 14180908716557068016872241)
            ·
              refine ⟨10635681537417801012654181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14180908716557068016872241 10635681537417801012654181)
              ·
                refine ⟨1994190288265837689872659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10635681537417801012654181 1994190288265837689872659)
                ·
                  refine ⟨2991285432398756534808989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994190288265837689872659 2991285432398756534808989)
                  ·
                    refine ⟨1121732037149533700553371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991285432398756534808989 1121732037149533700553371)
                    ·
                      rfl

theorem cell22_3276848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_3276848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276848 prefixEnd_3276848 := by exact prefixLift 3276848
  have htrace : WordTrace (prefixWord ++ tailWord_3276848) baseStart_3276848 baseEnd_3276848 := by
    simpa [prefixWord, tailWord_3276848, baseEnd_3276848] using wordTrace_append hprefix tailTrace_3276848
  have hstable : (prefixWord ++ tailWord_3276848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276848).length < 2 ^ (prefixWord ++ tailWord_3276848).sum := by decide
  have hdescent : baseEnd_3276848 < baseStart_3276848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276882 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_3276882 : Nat := 118140960795 + 3276882 * 2 ^ 59
def prefixEnd_3276882 : Nat := 4983230072969 + 3 ^ 40 * 3276882 * 2
def baseEnd_3276882 : Nat := 1121743676044368945203267

theorem tailTrace_3276882 : CollatzResearch.WordTrace tailWord_3276882 prefixEnd_3276882 1121743676044368945203267 := by
  unfold tailWord_3276882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29879426328605908933736225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79678470209615757156629933 29879426328605908933736225)
  ·
    refine ⟨22409569746454431700302169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29879426328605908933736225 22409569746454431700302169)
    ·
      refine ⟨16807177309840823775226627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22409569746454431700302169 16807177309840823775226627)
      ·
        refine ⟨25210765964761235662839941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16807177309840823775226627 25210765964761235662839941)
        ·
          refine ⟨4727018618392731686782489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25210765964761235662839941 4727018618392731686782489)
          ·
            refine ⟨3545263963794548765086867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727018618392731686782489 3545263963794548765086867)
            ·
              refine ⟨5317895945691823147630301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545263963794548765086867 5317895945691823147630301)
              ·
                refine ⟨1994210979634433680361363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317895945691823147630301 1994210979634433680361363)
                ·
                  refine ⟨2991316469451650520542045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994210979634433680361363 2991316469451650520542045)
                  ·
                    refine ⟨1121743676044368945203267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991316469451650520542045 1121743676044368945203267)
                    ·
                      rfl

theorem cell22_3276882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_3276882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276882 prefixEnd_3276882 := by exact prefixLift 3276882
  have htrace : WordTrace (prefixWord ++ tailWord_3276882) baseStart_3276882 baseEnd_3276882 := by
    simpa [prefixWord, tailWord_3276882, baseEnd_3276882] using wordTrace_append hprefix tailTrace_3276882
  have hstable : (prefixWord ++ tailWord_3276882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276882).length < 2 ^ (prefixWord ++ tailWord_3276882).sum := by decide
  have hdescent : baseEnd_3276882 < baseStart_3276882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276950 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3276950 : Nat := 118140960795 + 3276950 * 2 ^ 59
def prefixEnd_3276950 : Nat := 4983230072969 + 3 ^ 40 * 3276950 * 2
def baseEnd_3276950 : Nat := 1121766953834039434503059

theorem tailTrace_3276950 : CollatzResearch.WordTrace tailWord_3276950 prefixEnd_3276950 1121766953834039434503059 := by
  unfold tailWord_3276950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470011592386080209276269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79680123652118188898946869 7470011592386080209276269)
  ·
    refine ⟨2801254347144780078478601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7470011592386080209276269 2801254347144780078478601)
    ·
      refine ⟨2100940760358585058858951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2801254347144780078478601 2100940760358585058858951)
      ·
        refine ⟨3151411140537877588288427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100940760358585058858951 3151411140537877588288427)
        ·
          refine ⟨4727116710806816382432641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151411140537877588288427 4727116710806816382432641)
          ·
            refine ⟨3545337533105112286824481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727116710806816382432641 3545337533105112286824481)
            ·
              refine ⟨2659003149828834215118361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545337533105112286824481 2659003149828834215118361)
              ·
                refine ⟨1994252362371625661338771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659003149828834215118361 1994252362371625661338771)
                ·
                  refine ⟨2991378543557438492008157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994252362371625661338771 2991378543557438492008157)
                  ·
                    refine ⟨1121766953834039434503059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991378543557438492008157 1121766953834039434503059)
                    ·
                      rfl

theorem cell22_3276950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3276950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276950 prefixEnd_3276950 := by exact prefixLift 3276950
  have htrace : WordTrace (prefixWord ++ tailWord_3276950) baseStart_3276950 baseEnd_3276950 := by
    simpa [prefixWord, tailWord_3276950, baseEnd_3276950] using wordTrace_append hprefix tailTrace_3276950
  have hstable : (prefixWord ++ tailWord_3276950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276950).length < 2 ^ (prefixWord ++ tailWord_3276950).sum := by decide
  have hdescent : baseEnd_3276950 < baseStart_3276950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276951 : List Nat := [1, 1, 3, 3, 5, 9]
def baseStart_3276951 : Nat := 118140960795 + 3276951 * 2 ^ 59
def prefixEnd_3276951 : Nat := 4983230072969 + 3 ^ 40 * 3276951 * 2
def baseEnd_3276951 : Nat := 13848978964870071175655

theorem tailTrace_3276951 : CollatzResearch.WordTrace tailWord_3276951 prefixEnd_3276951 13848978964870071175655 := by
  unfold tailWord_3276951
  simp only [CollatzResearch.WordTrace]
  refine ⟨119520221951173660519206707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79680147967449107012804471 119520221951173660519206707)
  ·
    refine ⟨179280332926760490778810061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119520221951173660519206707 179280332926760490778810061)
    ·
      refine ⟨67230124847535184042053773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179280332926760490778810061 67230124847535184042053773)
      ·
        refine ⟨25211296817825694015770165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67230124847535184042053773 25211296817825694015770165)
        ·
          refine ⟨2363559076671158813978453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25211296817825694015770165 2363559076671158813978453)
          ·
            refine ⟨13848978964870071175655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2363559076671158813978453 13848978964870071175655)
            ·
              rfl

theorem cell22_3276951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 9].length) (baseStart_3276951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276951 prefixEnd_3276951 := by exact prefixLift 3276951
  have htrace : WordTrace (prefixWord ++ tailWord_3276951) baseStart_3276951 baseEnd_3276951 := by
    simpa [prefixWord, tailWord_3276951, baseEnd_3276951] using wordTrace_append hprefix tailTrace_3276951
  have hstable : (prefixWord ++ tailWord_3276951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276951).length < 2 ^ (prefixWord ++ tailWord_3276951).sum := by decide
  have hdescent : baseEnd_3276951 < baseStart_3276951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276979 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 9]
def baseStart_3276979 : Nat := 118140960795 + 3276979 * 2 ^ 59
def prefixEnd_3276979 : Nat := 4983230072969 + 3 ^ 40 * 3276979 * 2
def baseEnd_3276979 : Nat := 373925627042231008509323

theorem tailTrace_3276979 : CollatzResearch.WordTrace tailWord_3276979 prefixEnd_3276979 373925627042231008509323 := by
  unfold tailWord_3276979
  simp only [CollatzResearch.WordTrace]
  refine ⟨119521243195072221301225991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79680828796714814200817327 119521243195072221301225991)
  ·
    refine ⟨179281864792608331951838987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119521243195072221301225991 179281864792608331951838987)
    ·
      refine ⟨268922797188912497927758481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179281864792608331951838987 268922797188912497927758481)
      ·
        refine ⟨201692097891684373445818861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268922797188912497927758481 201692097891684373445818861)
        ·
          refine ⟨75634536709381640042182073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201692097891684373445818861 75634536709381640042182073)
          ·
            refine ⟨56725902532036230031636555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75634536709381640042182073 56725902532036230031636555)
            ·
              refine ⟨85088853798054345047454833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56725902532036230031636555 85088853798054345047454833)
              ·
                refine ⟨63816640348540758785591125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85088853798054345047454833 63816640348540758785591125)
                ·
                  refine ⟨373925627042231008509323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63816640348540758785591125 373925627042231008509323)
                  ·
                    rfl

theorem cell22_3276979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_3276979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276979 prefixEnd_3276979 := by exact prefixLift 3276979
  have htrace : WordTrace (prefixWord ++ tailWord_3276979) baseStart_3276979 baseEnd_3276979 := by
    simpa [prefixWord, tailWord_3276979, baseEnd_3276979] using wordTrace_append hprefix tailTrace_3276979
  have hstable : (prefixWord ++ tailWord_3276979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276979).length < 2 ^ (prefixWord ++ tailWord_3276979).sum := by decide
  have hdescent : baseEnd_3276979 < baseStart_3276979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276983 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 3, 3]
def baseStart_3276983 : Nat := 118140960795 + 3276983 * 2 ^ 59
def prefixEnd_3276983 : Nat := 4983230072969 + 3 ^ 40 * 3276983 * 2
def baseEnd_3276983 : Nat := 1121778250408438348427957

theorem tailTrace_3276983 : CollatzResearch.WordTrace tailWord_3276983 prefixEnd_3276983 1121778250408438348427957 := by
  unfold tailWord_3276983
  simp only [CollatzResearch.WordTrace]
  refine ⟨119521389087057729984371603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79680926058038486656247735 119521389087057729984371603)
  ·
    refine ⟨179282083630586594976557405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119521389087057729984371603 179282083630586594976557405)
    ·
      refine ⟨67230781361469973116209027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179282083630586594976557405 67230781361469973116209027)
      ·
        refine ⟨100846172042204959674313541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67230781361469973116209027 100846172042204959674313541)
        ·
          refine ⟨18908657257913429938933789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100846172042204959674313541 18908657257913429938933789)
          ·
            refine ⟨7090746471717536227100171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18908657257913429938933789 7090746471717536227100171)
            ·
              refine ⟨10636119707576304340650257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090746471717536227100171 10636119707576304340650257)
              ·
                refine ⟨7977089780682228255487693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10636119707576304340650257 7977089780682228255487693)
                ·
                  refine ⟨2991408667755835595807885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7977089780682228255487693 2991408667755835595807885)
                  ·
                    refine ⟨1121778250408438348427957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991408667755835595807885 1121778250408438348427957)
                    ·
                      rfl

theorem cell22_3276983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_3276983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3276983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3276983 prefixEnd_3276983 := by exact prefixLift 3276983
  have htrace : WordTrace (prefixWord ++ tailWord_3276983) baseStart_3276983 baseEnd_3276983 := by
    simpa [prefixWord, tailWord_3276983, baseEnd_3276983] using wordTrace_append hprefix tailTrace_3276983
  have hstable : (prefixWord ++ tailWord_3276983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276983).length < 2 ^ (prefixWord ++ tailWord_3276983).sum := by decide
  have hdescent : baseEnd_3276983 < baseStart_3276983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277013 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 7]
def baseStart_3277013 : Nat := 118140960795 + 3277013 * 2 ^ 59
def prefixEnd_3277013 : Nat := 4983230072969 + 3 ^ 40 * 3277013 * 2
def baseEnd_3277013 : Nat := 373929506673842756725955

theorem tailTrace_3277013 : CollatzResearch.WordTrace tailWord_3277013 prefixEnd_3277013 373929506673842756725955 := by
  unfold tailWord_3277013
  simp only [CollatzResearch.WordTrace]
  refine ⟨119522483276949045107963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79681655517966030071975795 119522483276949045107963693)
  ·
    refine ⟨44820931228855891915486385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119522483276949045107963693 44820931228855891915486385)
    ·
      refine ⟨33615698421641918936614789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44820931228855891915486385 33615698421641918936614789)
      ·
        refine ⟨6302943454057859800615273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33615698421641918936614789 6302943454057859800615273)
        ·
          refine ⟨4727207590543394850461455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302943454057859800615273 4727207590543394850461455)
          ·
            refine ⟨7090811385815092275692183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727207590543394850461455 7090811385815092275692183)
            ·
              refine ⟨10636217078722638413538275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090811385815092275692183 10636217078722638413538275)
              ·
                refine ⟨15954325618083957620307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10636217078722638413538275 15954325618083957620307413)
                ·
                  refine ⟨373929506673842756725955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15954325618083957620307413 373929506673842756725955)
                  ·
                    rfl

theorem cell22_3277013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_3277013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277013 prefixEnd_3277013 := by exact prefixLift 3277013
  have htrace : WordTrace (prefixWord ++ tailWord_3277013) baseStart_3277013 baseEnd_3277013 := by
    simpa [prefixWord, tailWord_3277013, baseEnd_3277013] using wordTrace_append hprefix tailTrace_3277013
  have hstable : (prefixWord ++ tailWord_3277013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277013).length < 2 ^ (prefixWord ++ tailWord_3277013).sum := by decide
  have hdescent : baseEnd_3277013 < baseStart_3277013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277041 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 6]
def baseStart_3277041 : Nat := 118140960795 + 3277041 * 2 ^ 59
def prefixEnd_3277041 : Nat := 4983230072969 + 3 ^ 40 * 3277041 * 2
def baseEnd_3277041 : Nat := 373932701664581843492593

theorem tailTrace_3277041 : CollatzResearch.WordTrace tailWord_3277041 prefixEnd_3277041 373932701664581843492593 := by
  unfold tailWord_3277041
  simp only [CollatzResearch.WordTrace]
  refine ⟨119523504520847605889982977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79682336347231737259988651 119523504520847605889982977)
  ·
    refine ⟨89642628390635704417487233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119523504520847605889982977 89642628390635704417487233)
    ·
      refine ⟨67231971292976778313115425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89642628390635704417487233 67231971292976778313115425)
      ·
        refine ⟨50423978469732583734836569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67231971292976778313115425 50423978469732583734836569)
        ·
          refine ⟨37817983852299437801127427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50423978469732583734836569 37817983852299437801127427)
          ·
            refine ⟨56726975778449156701691141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37817983852299437801127427 56726975778449156701691141)
            ·
              refine ⟨10636307958459216881567089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56726975778449156701691141 10636307958459216881567089)
              ·
                refine ⟨7977230968844412661175317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10636307958459216881567089 7977230968844412661175317)
                ·
                  refine ⟨373932701664581843492593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7977230968844412661175317 373932701664581843492593)
                  ·
                    rfl

theorem cell22_3277041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_3277041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277041 prefixEnd_3277041 := by exact prefixLift 3277041
  have htrace : WordTrace (prefixWord ++ tailWord_3277041) baseStart_3277041 baseEnd_3277041 := by
    simpa [prefixWord, tailWord_3277041, baseEnd_3277041] using wordTrace_append hprefix tailTrace_3277041
  have hstable : (prefixWord ++ tailWord_3277041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277041).length < 2 ^ (prefixWord ++ tailWord_3277041).sum := by decide
  have hdescent : baseEnd_3277041 < baseStart_3277041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277043 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 1, 4]
def baseStart_3277043 : Nat := 118140960795 + 3277043 * 2 ^ 59
def prefixEnd_3277043 : Nat := 4983230072969 + 3 ^ 40 * 3277043 * 2
def baseEnd_3277043 : Nat := 1121798789634618191927773

theorem tailTrace_3277043 : CollatzResearch.WordTrace tailWord_3277043 prefixEnd_3277043 1121798789634618191927773 := by
  unfold tailWord_3277043
  simp only [CollatzResearch.WordTrace]
  refine ⟨119523577466840360231555783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79682384977893573487703855 119523577466840360231555783)
  ·
    refine ⟨179285366200260540347333675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119523577466840360231555783 179285366200260540347333675)
    ·
      refine ⟨268928049300390810521000513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179285366200260540347333675 268928049300390810521000513)
      ·
        refine ⟨201696036975293107890750385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268928049300390810521000513 201696036975293107890750385)
        ·
          refine ⟨151272027731469830918062789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201696036975293107890750385 151272027731469830918062789)
          ·
            refine ⟨28363505199650593297136773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151272027731469830918062789 28363505199650593297136773)
            ·
              refine ⟨5318157224934486243213145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28363505199650593297136773 5318157224934486243213145)
              ·
                refine ⟨3988617918700864682409859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318157224934486243213145 3988617918700864682409859)
                ·
                  refine ⟨5982926878051297023614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988617918700864682409859 5982926878051297023614789)
                  ·
                    refine ⟨1121798789634618191927773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5982926878051297023614789 1121798789634618191927773)
                    ·
                      rfl

theorem cell22_3277043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_3277043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277043 prefixEnd_3277043 := by exact prefixLift 3277043
  have htrace : WordTrace (prefixWord ++ tailWord_3277043) baseStart_3277043 baseEnd_3277043 := by
    simpa [prefixWord, tailWord_3277043, baseEnd_3277043] using wordTrace_append hprefix tailTrace_3277043
  have hstable : (prefixWord ++ tailWord_3277043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277043).length < 2 ^ (prefixWord ++ tailWord_3277043).sum := by decide
  have hdescent : baseEnd_3277043 < baseStart_3277043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277056 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_3277056 : Nat := 118140960795 + 3277056 * 2 ^ 59
def prefixEnd_3277056 : Nat := 4983230072969 + 3 ^ 40 * 3277056 * 2
def baseEnd_3277056 : Nat := 1121803239800290491352733

theorem tailTrace_3277056 : CollatzResearch.WordTrace tailWord_3277056 prefixEnd_3277056 1121803239800290491352733 := by
  unfold tailWord_3277056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59762025807896631725889511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79682701077195508967852681 59762025807896631725889511)
  ·
    refine ⟨89643038711844947588834267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59762025807896631725889511 89643038711844947588834267)
    ·
      refine ⟨134464558067767421383251401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89643038711844947588834267 134464558067767421383251401)
      ·
        refine ⟨100848418550825566037438551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134464558067767421383251401 100848418550825566037438551)
        ·
          refine ⟨151272627826238349056157827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100848418550825566037438551 151272627826238349056157827)
          ·
            refine ⟨226908941739357523584236741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151272627826238349056157827 226908941739357523584236741)
            ·
              refine ⟨42545426576129535672044389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226908941739357523584236741 42545426576129535672044389)
              ·
                refine ⟨7977267483024287938508323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42545426576129535672044389 7977267483024287938508323)
                ·
                  refine ⟨11965901224536431907762485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977267483024287938508323 11965901224536431907762485)
                  ·
                    refine ⟨1121803239800290491352733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11965901224536431907762485 1121803239800290491352733)
                    ·
                      rfl

theorem cell22_3277056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_3277056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277056 prefixEnd_3277056 := by exact prefixLift 3277056
  have htrace : WordTrace (prefixWord ++ tailWord_3277056) baseStart_3277056 baseEnd_3277056 := by
    simpa [prefixWord, tailWord_3277056, baseEnd_3277056] using wordTrace_append hprefix tailTrace_3277056
  have hstable : (prefixWord ++ tailWord_3277056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277056).length < 2 ^ (prefixWord ++ tailWord_3277056).sum := by decide
  have hdescent : baseEnd_3277056 < baseStart_3277056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277073 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_3277073 : Nat := 118140960795 + 3277073 * 2 ^ 59
def prefixEnd_3277073 : Nat := 4983230072969 + 3 ^ 40 * 3277073 * 2
def baseEnd_3277073 : Nat := 1121809059247708113677681

theorem tailTrace_3277073 : CollatzResearch.WordTrace tailWord_3277073 prefixEnd_3277073 1121809059247708113677681 := by
  unfold tailWord_3277073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119524671656731675355147873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79683114437821116903431915 119524671656731675355147873)
  ·
    refine ⟨89643503742548756516360905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119524671656731675355147873 89643503742548756516360905)
    ·
      refine ⟨67232627806911567387270679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89643503742548756516360905 67232627806911567387270679)
      ·
        refine ⟨100848941710367351080906019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67232627806911567387270679 100848941710367351080906019)
        ·
          refine ⟨151273412565551026621359029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100848941710367351080906019 151273412565551026621359029)
          ·
            refine ⟨14181882428020408745752409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151273412565551026621359029 14181882428020408745752409)
            ·
              refine ⟨10636411821015306559314307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14181882428020408745752409 10636411821015306559314307)
              ·
                refine ⟨15954617731522959838971461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10636411821015306559314307 15954617731522959838971461)
                ·
                  refine ⟨2991490824660554969807149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15954617731522959838971461 2991490824660554969807149)
                  ·
                    refine ⟨1121809059247708113677681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991490824660554969807149 1121809059247708113677681)
                    ·
                      rfl

theorem cell22_3277073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_3277073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277073 prefixEnd_3277073 := by exact prefixLift 3277073
  have htrace : WordTrace (prefixWord ++ tailWord_3277073) baseStart_3277073 baseEnd_3277073 := by
    simpa [prefixWord, tailWord_3277073, baseEnd_3277073] using wordTrace_append hprefix tailTrace_3277073
  have hstable : (prefixWord ++ tailWord_3277073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277073).length < 2 ^ (prefixWord ++ tailWord_3277073).sum := by decide
  have hdescent : baseEnd_3277073 < baseStart_3277073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277105 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3277105 : Nat := 118140960795 + 3277105 * 2 ^ 59
def prefixEnd_3277105 : Nat := 4983230072969 + 3 ^ 40 * 3277105 * 2
def baseEnd_3277105 : Nat := 1121820013501670696877583

theorem tailTrace_3277105 : CollatzResearch.WordTrace tailWord_3277105 prefixEnd_3277105 1121820013501670696877583 := by
  unfold tailWord_3277105
  simp only [CollatzResearch.WordTrace]
  refine ⟨119525838792615744820312769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79683892528410496546875179 119525838792615744820312769)
  ·
    refine ⟨89644379094461808615234577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119525838792615744820312769 89644379094461808615234577)
    ·
      refine ⟨67233284320846356461425933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89644379094461808615234577 67233284320846356461425933)
      ·
        refine ⟨25212481620317383673034725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67233284320846356461425933 25212481620317383673034725)
        ·
          refine ⟨4727340303809509438694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25212481620317383673034725 4727340303809509438694011)
          ·
            refine ⟨7091010455714264158041017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727340303809509438694011 7091010455714264158041017)
            ·
              refine ⟨5318257841785698118530763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7091010455714264158041017 5318257841785698118530763)
              ·
                refine ⟨7977386762678547177796145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318257841785698118530763 7977386762678547177796145)
                ·
                  refine ⟨5983040072008910383347109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7977386762678547177796145 5983040072008910383347109)
                  ·
                    refine ⟨1121820013501670696877583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983040072008910383347109 1121820013501670696877583)
                    ·
                      rfl

theorem cell22_3277105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3277105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277105 prefixEnd_3277105 := by exact prefixLift 3277105
  have htrace : WordTrace (prefixWord ++ tailWord_3277105) baseStart_3277105 baseEnd_3277105 := by
    simpa [prefixWord, tailWord_3277105, baseEnd_3277105] using wordTrace_append hprefix tailTrace_3277105
  have hstable : (prefixWord ++ tailWord_3277105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277105).length < 2 ^ (prefixWord ++ tailWord_3277105).sum := by decide
  have hdescent : baseEnd_3277105 < baseStart_3277105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277124 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3277124 : Nat := 118140960795 + 3277124 * 2 ^ 59
def prefixEnd_3277124 : Nat := 4983230072969 + 3 ^ 40 * 3277124 * 2
def baseEnd_3277124 : Nat := 1121826517589960980652525

theorem tailTrace_3277124 : CollatzResearch.WordTrace tailWord_3277124 prefixEnd_3277124 1121826517589960980652525 := by
  unfold tailWord_3277124
  simp only [CollatzResearch.WordTrace]
  refine ⟨59763265889773455532627213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79684354519697940710169617 59763265889773455532627213)
  ·
    refine ⟨22411224708665045824735205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59763265889773455532627213 22411224708665045824735205)
    ·
      refine ⟨4202104632874696092137851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22411224708665045824735205 4202104632874696092137851)
      ·
        refine ⟨6303156949312044138206777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202104632874696092137851 6303156949312044138206777)
        ·
          refine ⟨4727367711984033103655083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303156949312044138206777 4727367711984033103655083)
          ·
            refine ⟨7091051567976049655482625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727367711984033103655083 7091051567976049655482625)
            ·
              refine ⟨5318288675982037241611969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7091051567976049655482625 5318288675982037241611969)
              ·
                refine ⟨3988716506986527931208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318288675982037241611969 3988716506986527931208977)
                ·
                  refine ⟨2991537380239895948406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988716506986527931208977 2991537380239895948406733)
                  ·
                    refine ⟨1121826517589960980652525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991537380239895948406733 1121826517589960980652525)
                    ·
                      rfl

theorem cell22_3277124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3277124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277124 prefixEnd_3277124 := by exact prefixLift 3277124
  have htrace : WordTrace (prefixWord ++ tailWord_3277124) baseStart_3277124 baseEnd_3277124 := by
    simpa [prefixWord, tailWord_3277124, baseEnd_3277124] using wordTrace_append hprefix tailTrace_3277124
  have hstable : (prefixWord ++ tailWord_3277124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277124).length < 2 ^ (prefixWord ++ tailWord_3277124).sum := by decide
  have hdescent : baseEnd_3277124 < baseStart_3277124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277193 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 6]
def baseStart_3277193 : Nat := 118140960795 + 3277193 * 2 ^ 59
def prefixEnd_3277193 : Nat := 4983230072969 + 3 ^ 40 * 3277193 * 2
def baseEnd_3277193 : Nat := 373950045900022600225771

theorem tailTrace_3277193 : CollatzResearch.WordTrace tailWord_3277193 prefixEnd_3277193 373950045900022600225771 := by
  unfold tailWord_3277193
  simp only [CollatzResearch.WordTrace]
  refine ⟨119529048416296935849516233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79686032277531290566344155 119529048416296935849516233)
  ·
    refine ⟨89646786312222701887137175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119529048416296935849516233 89646786312222701887137175)
    ·
      refine ⟨134470179468334052830705763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89646786312222701887137175 134470179468334052830705763)
      ·
        refine ⟨201705269202501079246058645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134470179468334052830705763 201705269202501079246058645)
        ·
          refine ⟨9454934493867238089658999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201705269202501079246058645 9454934493867238089658999)
          ·
            refine ⟨14182401740800857134488499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454934493867238089658999 14182401740800857134488499)
            ·
              refine ⟨21273602611201285701732749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182401740800857134488499 21273602611201285701732749)
              ·
                refine ⟨7977600979200482138149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21273602611201285701732749 7977600979200482138149781)
                ·
                  refine ⟨373950045900022600225771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7977600979200482138149781 373950045900022600225771)
                  ·
                    rfl

theorem cell22_3277193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_3277193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277193 prefixEnd_3277193 := by exact prefixLift 3277193
  have htrace : WordTrace (prefixWord ++ tailWord_3277193) baseStart_3277193 baseEnd_3277193 := by
    simpa [prefixWord, tailWord_3277193, baseEnd_3277193] using wordTrace_append hprefix tailTrace_3277193
  have hstable : (prefixWord ++ tailWord_3277193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277193).length < 2 ^ (prefixWord ++ tailWord_3277193).sum := by decide
  have hdescent : baseEnd_3277193 < baseStart_3277193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277244 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_3277244 : Nat := 118140960795 + 3277244 * 2 ^ 59
def prefixEnd_3277244 : Nat := 4983230072969 + 3 ^ 40 * 3277244 * 2
def baseEnd_3277244 : Nat := 373955865347440222550719

theorem tailTrace_3277244 : CollatzResearch.WordTrace tailWord_3277244 prefixEnd_3277244 373955865347440222550719 := by
  unfold tailWord_3277244
  simp only [CollatzResearch.WordTrace]
  refine ⟨59765454269556085779811393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79687272359408114373081857 59765454269556085779811393)
  ·
    refine ⟨44824090702167064334858545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59765454269556085779811393 44824090702167064334858545)
    ·
      refine ⟨33618068026625298251143909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44824090702167064334858545 33618068026625298251143909)
      ·
        refine ⟨6303387754992243422089483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33618068026625298251143909 6303387754992243422089483)
        ·
          refine ⟨9455081632488365133134225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303387754992243422089483 9455081632488365133134225)
          ·
            refine ⟨7091311224366273849850669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9455081632488365133134225 7091311224366273849850669)
            ·
              refine ⟨2659241709137352693694001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7091311224366273849850669 2659241709137352693694001)
              ·
                refine ⟨1994431281853014520270501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659241709137352693694001 1994431281853014520270501)
                ·
                  refine ⟨373955865347440222550719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994431281853014520270501 373955865347440222550719)
                  ·
                    rfl

theorem cell22_3277244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_3277244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277244 prefixEnd_3277244 := by exact prefixLift 3277244
  have htrace : WordTrace (prefixWord ++ tailWord_3277244) baseStart_3277244 baseEnd_3277244 := by
    simpa [prefixWord, tailWord_3277244, baseEnd_3277244] using wordTrace_append hprefix tailTrace_3277244
  have hstable : (prefixWord ++ tailWord_3277244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277244).length < 2 ^ (prefixWord ++ tailWord_3277244).sum := by decide
  have hdescent : baseEnd_3277244 < baseStart_3277244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277347 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 1, 4]
def baseStart_3277347 : Nat := 118140960795 + 3277347 * 2 ^ 59
def prefixEnd_3277347 : Nat := 4983230072969 + 3 ^ 40 * 3277347 * 2
def baseEnd_3277347 : Nat := 1121902855047262732326841

theorem tailTrace_3277347 : CollatzResearch.WordTrace tailWord_3277347 prefixEnd_3277347 1121902855047262732326841 := by
  unfold tailWord_3277347
  simp only [CollatzResearch.WordTrace]
  refine ⟨119534665257739020150622295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79689776838492680100414863 119534665257739020150622295)
  ·
    refine ⟨179301997886608530225933443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119534665257739020150622295 179301997886608530225933443)
    ·
      refine ⟨268952996829912795338900165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179301997886608530225933443 268952996829912795338900165)
      ·
        refine ⟨50428686905608649126043781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268952996829912795338900165 50428686905608649126043781)
        ·
          refine ⟨9455378794801621711133209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50428686905608649126043781 9455378794801621711133209)
          ·
            refine ⟨7091534096101216283349907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9455378794801621711133209 7091534096101216283349907)
            ·
              refine ⟨10637301144151824425024861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091534096101216283349907 10637301144151824425024861)
              ·
                refine ⟨3988987929056934159384323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10637301144151824425024861 3988987929056934159384323)
                ·
                  refine ⟨5983481893585401239076485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988987929056934159384323 5983481893585401239076485)
                  ·
                    refine ⟨1121902855047262732326841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983481893585401239076485 1121902855047262732326841)
                    ·
                      rfl

theorem cell22_3277347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_3277347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277347 prefixEnd_3277347 := by exact prefixLift 3277347
  have htrace : WordTrace (prefixWord ++ tailWord_3277347) baseStart_3277347 baseEnd_3277347 := by
    simpa [prefixWord, tailWord_3277347, baseEnd_3277347] using wordTrace_append hprefix tailTrace_3277347
  have hstable : (prefixWord ++ tailWord_3277347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277347).length < 2 ^ (prefixWord ++ tailWord_3277347).sum := by decide
  have hdescent : baseEnd_3277347 < baseStart_3277347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277351 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 5]
def baseStart_3277351 : Nat := 118140960795 + 3277351 * 2 ^ 59
def prefixEnd_3277351 : Nat := 4983230072969 + 3 ^ 40 * 3277351 * 2
def baseEnd_3277351 : Nat := 373968074776336018408943

theorem tailTrace_3277351 : CollatzResearch.WordTrace tailWord_3277351 prefixEnd_3277351 373968074776336018408943 := by
  unfold tailWord_3277351
  simp only [CollatzResearch.WordTrace]
  refine ⟨119534811149724528833767907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79689874099816352555845271 119534811149724528833767907)
  ·
    refine ⟨179302216724586793250651861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119534811149724528833767907 179302216724586793250651861)
    ·
      refine ⟨4202395704482502966812153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 179302216724586793250651861 4202395704482502966812153)
      ·
        refine ⟨3151796778361877225109115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4202395704482502966812153 3151796778361877225109115)
        ·
          refine ⟨4727695167542815837663673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151796778361877225109115 4727695167542815837663673)
          ·
            refine ⟨3545771375657111878247755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727695167542815837663673 3545771375657111878247755)
            ·
              refine ⟨5318657063485667817371633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545771375657111878247755 5318657063485667817371633)
              ·
                refine ⟨3988992797614250863028725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318657063485667817371633 3988992797614250863028725)
                ·
                  refine ⟨373968074776336018408943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3988992797614250863028725 373968074776336018408943)
                  ·
                    rfl

theorem cell22_3277351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].length) (baseStart_3277351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277351 prefixEnd_3277351 := by exact prefixLift 3277351
  have htrace : WordTrace (prefixWord ++ tailWord_3277351) baseStart_3277351 baseEnd_3277351 := by
    simpa [prefixWord, tailWord_3277351, baseEnd_3277351] using wordTrace_append hprefix tailTrace_3277351
  have hstable : (prefixWord ++ tailWord_3277351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277351).length < 2 ^ (prefixWord ++ tailWord_3277351).sum := by decide
  have hdescent : baseEnd_3277351 < baseStart_3277351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277362 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_3277362 : Nat := 118140960795 + 3277362 * 2 ^ 59
def prefixEnd_3277362 : Nat := 4983230072969 + 3 ^ 40 * 3277362 * 2
def baseEnd_3277362 : Nat := 373969329951269231067265

theorem tailTrace_3277362 : CollatzResearch.WordTrace tailWord_3277362 prefixEnd_3277362 373969329951269231067265 := by
  unfold tailWord_3277362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29883803088171169428104585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79690141568456451808278893 29883803088171169428104585)
  ·
    refine ⟨22412852316128377071078439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29883803088171169428104585 22412852316128377071078439)
    ·
      refine ⟨33619278474192565606617659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22412852316128377071078439 33619278474192565606617659)
      ·
        refine ⟨50428917711288848409926489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33619278474192565606617659 50428917711288848409926489)
        ·
          refine ⟨37821688283466636307444867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50428917711288848409926489 37821688283466636307444867)
          ·
            refine ⟨56732532425199954461167301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37821688283466636307444867 56732532425199954461167301)
            ·
              refine ⟨10637349829724991461468869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56732532425199954461167301 10637349829724991461468869)
              ·
                refine ⟨1994503093073435899025413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10637349829724991461468869 1994503093073435899025413)
                ·
                  refine ⟨373969329951269231067265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994503093073435899025413 373969329951269231067265)
                  ·
                    rfl

theorem cell22_3277362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_3277362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277362 prefixEnd_3277362 := by exact prefixLift 3277362
  have htrace : WordTrace (prefixWord ++ tailWord_3277362) baseStart_3277362 baseEnd_3277362 := by
    simpa [prefixWord, tailWord_3277362, baseEnd_3277362] using wordTrace_append hprefix tailTrace_3277362
  have hstable : (prefixWord ++ tailWord_3277362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277362).length < 2 ^ (prefixWord ++ tailWord_3277362).sum := by decide
  have hdescent : baseEnd_3277362 < baseStart_3277362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277377 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3277377 : Nat := 118140960795 + 3277377 * 2 ^ 59
def prefixEnd_3277377 : Nat := 4983230072969 + 3 ^ 40 * 3277377 * 2
def baseEnd_3277377 : Nat := 1121913124660352654076749

theorem tailTrace_3277377 : CollatzResearch.WordTrace tailWord_3277377 prefixEnd_3277377 1121913124660352654076749 := by
  unfold tailWord_3277377
  simp only [CollatzResearch.WordTrace]
  refine ⟨119535759447630335274214385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79690506298420223516142923 119535759447630335274214385)
  ·
    refine ⟨89651819585722751455660789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119535759447630335274214385 89651819585722751455660789)
    ·
      refine ⟨8404858086161507948968199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89651819585722751455660789 8404858086161507948968199)
      ·
        refine ⟨12607287129242261923452299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404858086161507948968199 12607287129242261923452299)
        ·
          refine ⟨18910930693863392885178449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12607287129242261923452299 18910930693863392885178449)
          ·
            refine ⟨14183198020397544663883837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18910930693863392885178449 14183198020397544663883837)
            ·
              refine ⟨5318699257649079248956439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14183198020397544663883837 5318699257649079248956439)
              ·
                refine ⟨7978048886473618873434659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318699257649079248956439 7978048886473618873434659)
                ·
                  refine ⟨11967073329710428310151989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978048886473618873434659 11967073329710428310151989)
                  ·
                    refine ⟨1121913124660352654076749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11967073329710428310151989 1121913124660352654076749)
                    ·
                      rfl

theorem cell22_3277377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3277377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277377 prefixEnd_3277377 := by exact prefixLift 3277377
  have htrace : WordTrace (prefixWord ++ tailWord_3277377) baseStart_3277377 baseEnd_3277377 := by
    simpa [prefixWord, tailWord_3277377, baseEnd_3277377] using wordTrace_append hprefix tailTrace_3277377
  have hstable : (prefixWord ++ tailWord_3277377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277377).length < 2 ^ (prefixWord ++ tailWord_3277377).sum := by decide
  have hdescent : baseEnd_3277377 < baseStart_3277377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277512 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3277512 : Nat := 118140960795 + 3277512 * 2 ^ 59
def prefixEnd_3277512 : Nat := 4983230072969 + 3 ^ 40 * 3277512 * 2
def baseEnd_3277512 : Nat := 1121959337919257301951335

theorem tailTrace_3277512 : CollatzResearch.WordTrace tailWord_3277512 prefixEnd_3277512 1121959337919257301951335 := by
  unfold tailWord_3277512
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770341651070626665189395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79693788868094168886919193 59770341651070626665189395)
  ·
    refine ⟨89655512476605939997784093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59770341651070626665189395 89655512476605939997784093)
    ·
      refine ⟨33620817178727227499169035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89655512476605939997784093 33620817178727227499169035)
      ·
        refine ⟨50431225768090841248753553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33620817178727227499169035 50431225768090841248753553)
        ·
          refine ⟨37823419326068130936565165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50431225768090841248753553 37823419326068130936565165)
          ·
            refine ⟨14183782247275549101211937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37823419326068130936565165 14183782247275549101211937)
            ·
              refine ⟨10637836685456661825908953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14183782247275549101211937 10637836685456661825908953)
              ·
                refine ⟨7978377514092496369431715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637836685456661825908953 7978377514092496369431715)
                ·
                  refine ⟨11967566271138744554147573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978377514092496369431715 11967566271138744554147573)
                  ·
                    refine ⟨1121959337919257301951335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11967566271138744554147573 1121959337919257301951335)
                    ·
                      rfl

theorem cell22_3277512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3277512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277512 prefixEnd_3277512 := by exact prefixLift 3277512
  have htrace : WordTrace (prefixWord ++ tailWord_3277512) baseStart_3277512 baseEnd_3277512 := by
    simpa [prefixWord, tailWord_3277512, baseEnd_3277512] using wordTrace_append hprefix tailTrace_3277512
  have hstable : (prefixWord ++ tailWord_3277512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277512).length < 2 ^ (prefixWord ++ tailWord_3277512).sum := by decide
  have hdescent : baseEnd_3277512 < baseStart_3277512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277514 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_3277514 : Nat := 118140960795 + 3277514 * 2 ^ 59
def prefixEnd_3277514 : Nat := 4983230072969 + 3 ^ 40 * 3277514 * 2
def baseEnd_3277514 : Nat := 373986674186709987800443

theorem tailTrace_3277514 : CollatzResearch.WordTrace tailWord_3277514 prefixEnd_3277514 373986674186709987800443 := by
  unfold tailWord_3277514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885189062033501917987899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79693837498756005114634397 29885189062033501917987899)
  ·
    refine ⟨44827783593050252876981849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885189062033501917987899 44827783593050252876981849)
    ·
      refine ⟨33620837694787689657736387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44827783593050252876981849 33620837694787689657736387)
      ·
        refine ⟨50431256542181534486604581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33620837694787689657736387 50431256542181534486604581)
        ·
          refine ⟨9455860601659037716238359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50431256542181534486604581 9455860601659037716238359)
          ·
            refine ⟨14183790902488556574357539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455860601659037716238359 14183790902488556574357539)
            ·
              refine ⟨21275686353732834861536309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14183790902488556574357539 21275686353732834861536309)
              ·
                refine ⟨1994595595662453268269029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21275686353732834861536309 1994595595662453268269029)
                ·
                  refine ⟨373986674186709987800443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994595595662453268269029 373986674186709987800443)
                  ·
                    rfl

theorem cell22_3277514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_3277514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277514 prefixEnd_3277514 := by exact prefixLift 3277514
  have htrace : WordTrace (prefixWord ++ tailWord_3277514) baseStart_3277514 baseEnd_3277514 := by
    simpa [prefixWord, tailWord_3277514, baseEnd_3277514] using wordTrace_append hprefix tailTrace_3277514
  have hstable : (prefixWord ++ tailWord_3277514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277514).length < 2 ^ (prefixWord ++ tailWord_3277514).sum := by decide
  have hdescent : baseEnd_3277514 < baseStart_3277514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277516 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_3277516 : Nat := 118140960795 + 3277516 * 2 ^ 59
def prefixEnd_3277516 : Nat := 4983230072969 + 3 ^ 40 * 3277516 * 2
def baseEnd_3277516 : Nat := 1121960707201002624851323

theorem tailTrace_3277516 : CollatzResearch.WordTrace tailWord_3277516 prefixEnd_3277516 1121960707201002624851323 := by
  unfold tailWord_3277516
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770414597063381006762201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79693886129417841342349601 59770414597063381006762201)
  ·
    refine ⟨44827810947797535755071651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59770414597063381006762201 44827810947797535755071651)
    ·
      refine ⟨67241716421696303632607477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44827810947797535755071651 67241716421696303632607477)
      ·
        refine ⟨6303910914534028465556951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67241716421696303632607477 6303910914534028465556951)
        ·
          refine ⟨9455866371801042698335427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303910914534028465556951 9455866371801042698335427)
          ·
            refine ⟨14183799557701564047503141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455866371801042698335427 14183799557701564047503141)
            ·
              refine ⟨2659462417069043258906839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14183799557701564047503141 2659462417069043258906839)
              ·
                refine ⟨3989193625603564888360259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659462417069043258906839 3989193625603564888360259)
                ·
                  refine ⟨5983790438405347332540389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989193625603564888360259 5983790438405347332540389)
                  ·
                    refine ⟨1121960707201002624851323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983790438405347332540389 1121960707201002624851323)
                    ·
                      rfl

theorem cell22_3277516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_3277516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277516 prefixEnd_3277516 := by exact prefixLift 3277516
  have htrace : WordTrace (prefixWord ++ tailWord_3277516) baseStart_3277516 baseEnd_3277516 := by
    simpa [prefixWord, tailWord_3277516, baseEnd_3277516] using wordTrace_append hprefix tailTrace_3277516
  have hstable : (prefixWord ++ tailWord_3277516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277516).length < 2 ^ (prefixWord ++ tailWord_3277516).sum := by decide
  have hdescent : baseEnd_3277516 < baseStart_3277516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277587 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 5]
def baseStart_3277587 : Nat := 118140960795 + 3277587 * 2 ^ 59
def prefixEnd_3277587 : Nat := 4983230072969 + 3 ^ 40 * 3277587 * 2
def baseEnd_3277587 : Nat := 373995003983994035442035

theorem tailTrace_3277587 : CollatzResearch.WordTrace tailWord_3277587 prefixEnd_3277587 373995003983994035442035 := by
  unfold tailWord_3277587
  simp only [CollatzResearch.WordTrace]
  refine ⟨119543418776869541139359015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695612517913027426239343 119543418776869541139359015)
  ·
    refine ⟨179315128165304311709038523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119543418776869541139359015 179315128165304311709038523)
    ·
      refine ⟨268972692247956467563557785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179315128165304311709038523 268972692247956467563557785)
      ·
        refine ⟨201729519185967350672668339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268972692247956467563557785 201729519185967350672668339)
        ·
          refine ⟨302594278778951026009002509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201729519185967350672668339 302594278778951026009002509)
          ·
            refine ⟨113472854542106634753375941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302594278778951026009002509 113472854542106634753375941)
            ·
              refine ⟨21276160226644994016257989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113472854542106634753375941 21276160226644994016257989)
              ·
                refine ⟨3989280042495936378048373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21276160226644994016257989 3989280042495936378048373)
                ·
                  refine ⟨373995003983994035442035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3989280042495936378048373 373995003983994035442035)
                  ·
                    rfl

theorem cell22_3277587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].length) (baseStart_3277587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277587 prefixEnd_3277587 := by exact prefixLift 3277587
  have htrace : WordTrace (prefixWord ++ tailWord_3277587) baseStart_3277587 baseEnd_3277587 := by
    simpa [prefixWord, tailWord_3277587, baseEnd_3277587] using wordTrace_append hprefix tailTrace_3277587
  have hstable : (prefixWord ++ tailWord_3277587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277587).length < 2 ^ (prefixWord ++ tailWord_3277587).sum := by decide
  have hdescent : baseEnd_3277587 < baseStart_3277587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277597 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_3277597 : Nat := 118140960795 + 3277597 * 2 ^ 59
def prefixEnd_3277597 : Nat := 4983230072969 + 3 ^ 40 * 3277597 * 2
def baseEnd_3277597 : Nat := 1121988435156345413576075

theorem tailTrace_3277597 : CollatzResearch.WordTrace tailWord_3277597 prefixEnd_3277597 1121988435156345413576075 := by
  unfold tailWord_3277597
  simp only [CollatzResearch.WordTrace]
  refine ⟨119543783506833312847223045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695855671222208564815363 119543783506833312847223045)
  ·
    refine ⟨22414459407531246158854321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119543783506833312847223045 22414459407531246158854321)
    ·
      refine ⟨16810844555648434619140741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22414459407531246158854321 16810844555648434619140741)
      ·
        refine ⟨3152033354184081491088889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16810844555648434619140741 3152033354184081491088889)
        ·
          refine ⟨2364025015638061118316667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152033354184081491088889 2364025015638061118316667)
          ·
            refine ⟨3546037523457091677475001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364025015638061118316667 3546037523457091677475001)
            ·
              refine ⟨2659528142592818758106251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3546037523457091677475001 2659528142592818758106251)
              ·
                refine ⟨3989292213889228137159377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659528142592818758106251 3989292213889228137159377)
                ·
                  refine ⟨2991969160416921102869533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989292213889228137159377 2991969160416921102869533)
                  ·
                    refine ⟨1121988435156345413576075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991969160416921102869533 1121988435156345413576075)
                    ·
                      rfl

theorem cell22_3277597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_3277597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277597 prefixEnd_3277597 := by exact prefixLift 3277597
  have htrace : WordTrace (prefixWord ++ tailWord_3277597) baseStart_3277597 baseEnd_3277597 := by
    simpa [prefixWord, tailWord_3277597, baseEnd_3277597] using wordTrace_append hprefix tailTrace_3277597
  have hstable : (prefixWord ++ tailWord_3277597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277597).length < 2 ^ (prefixWord ++ tailWord_3277597).sum := by decide
  have hdescent : baseEnd_3277597 < baseStart_3277597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277664 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_3277664 : Nat := 118140960795 + 3277664 * 2 ^ 59
def prefixEnd_3277664 : Nat := 4983230072969 + 3 ^ 40 * 3277664 * 2
def baseEnd_3277664 : Nat := 1122011370625579572150869

theorem tailTrace_3277664 : CollatzResearch.WordTrace tailWord_3277664 prefixEnd_3277664 1122011370625579572150869 := by
  unfold tailWord_3277664
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773113598795291644956023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79697484798393722193274697 59773113598795291644956023)
  ·
    refine ⟨89659670398192937467434035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59773113598795291644956023 89659670398192937467434035)
    ·
      refine ⟨134489505597289406201151053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89659670398192937467434035 134489505597289406201151053)
      ·
        refine ⟨50433564598983527325431645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134489505597289406201151053 50433564598983527325431645)
        ·
          refine ⟨18912586724618822747036867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50433564598983527325431645 18912586724618822747036867)
          ·
            refine ⟨28368880086928234120555301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18912586724618822747036867 28368880086928234120555301)
            ·
              refine ⟨5319165016299043897604119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28368880086928234120555301 5319165016299043897604119)
              ·
                refine ⟨7978747524448565846406179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319165016299043897604119 7978747524448565846406179)
                ·
                  refine ⟨11968121286672848769609269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978747524448565846406179 11968121286672848769609269)
                  ·
                    refine ⟨1122011370625579572150869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11968121286672848769609269 1122011370625579572150869)
                    ·
                      rfl

theorem cell22_3277664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_3277664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277664 prefixEnd_3277664 := by exact prefixLift 3277664
  have htrace : WordTrace (prefixWord ++ tailWord_3277664) baseStart_3277664 baseEnd_3277664 := by
    simpa [prefixWord, tailWord_3277664, baseEnd_3277664] using wordTrace_append hprefix tailTrace_3277664
  have hstable : (prefixWord ++ tailWord_3277664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277664).length < 2 ^ (prefixWord ++ tailWord_3277664).sum := by decide
  have hdescent : baseEnd_3277664 < baseStart_3277664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277666 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3277666 : Nat := 118140960795 + 3277666 * 2 ^ 59
def prefixEnd_3277666 : Nat := 4983230072969 + 3 ^ 40 * 3277666 * 2
def baseEnd_3277666 : Nat := 374004018422150744533621

theorem tailTrace_3277666 : CollatzResearch.WordTrace tailWord_3277666 prefixEnd_3277666 374004018422150744533621 := by
  unfold tailWord_3277666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886575035895834407871213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79697533429055558420989901 29886575035895834407871213)
  ·
    refine ⟨11207465638460937902951705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29886575035895834407871213 11207465638460937902951705)
    ·
      refine ⟨8405599228845703427213779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11207465638460937902951705 8405599228845703427213779)
      ·
        refine ⟨12608398843268555140820669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405599228845703427213779 12608398843268555140820669)
        ·
          refine ⟨4728149566225708177807751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12608398843268555140820669 4728149566225708177807751)
          ·
            refine ⟨7092224349338562266711627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728149566225708177807751 7092224349338562266711627)
            ·
              refine ⟨10638336524007843400067441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092224349338562266711627 10638336524007843400067441)
              ·
                refine ⟨7978752393005882550050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10638336524007843400067441 7978752393005882550050581)
                ·
                  refine ⟨374004018422150744533621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7978752393005882550050581 374004018422150744533621)
                  ·
                    rfl

theorem cell22_3277666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3277666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277666 prefixEnd_3277666 := by exact prefixLift 3277666
  have htrace : WordTrace (prefixWord ++ tailWord_3277666) baseStart_3277666 baseEnd_3277666 := by
    simpa [prefixWord, tailWord_3277666, baseEnd_3277666] using wordTrace_append hprefix tailTrace_3277666
  have hstable : (prefixWord ++ tailWord_3277666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277666).length < 2 ^ (prefixWord ++ tailWord_3277666).sum := by decide
  have hdescent : baseEnd_3277666 < baseStart_3277666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277692 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3277692 : Nat := 118140960795 + 3277692 * 2 ^ 59
def prefixEnd_3277692 : Nat := 4983230072969 + 3 ^ 40 * 3277692 * 2
def baseEnd_3277692 : Nat := 1122020955597796832450783

theorem tailTrace_3277692 : CollatzResearch.WordTrace tailWord_3277692 prefixEnd_3277692 1122020955597796832450783 := by
  unfold tailWord_3277692
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773624220744572035965665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79698165627659429381287553 59773624220744572035965665)
  ·
    refine ⟨44830218165558429026974249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59773624220744572035965665 44830218165558429026974249)
    ·
      refine ⟨33622663624168821770230687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44830218165558429026974249 33622663624168821770230687)
      ·
        refine ⟨50433995436253232655346031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33622663624168821770230687 50433995436253232655346031)
        ·
          refine ⟨75650993154379848983019047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50433995436253232655346031 75650993154379848983019047)
          ·
            refine ⟨113476489731569773474528571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75650993154379848983019047 113476489731569773474528571)
            ·
              refine ⟨170214734597354660211792857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113476489731569773474528571 170214734597354660211792857)
              ·
                refine ⟨127661050948015995158844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170214734597354660211792857 127661050948015995158844643)
                ·
                  refine ⟨191491576422023992738266965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127661050948015995158844643 191491576422023992738266965)
                  ·
                    refine ⟨1122020955597796832450783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 191491576422023992738266965 1122020955597796832450783)
                    ·
                      rfl

theorem cell22_3277692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3277692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277692 prefixEnd_3277692 := by exact prefixLift 3277692
  have htrace : WordTrace (prefixWord ++ tailWord_3277692) baseStart_3277692 baseEnd_3277692 := by
    simpa [prefixWord, tailWord_3277692, baseEnd_3277692] using wordTrace_append hprefix tailTrace_3277692
  have hstable : (prefixWord ++ tailWord_3277692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277692).length < 2 ^ (prefixWord ++ tailWord_3277692).sum := by decide
  have hdescent : baseEnd_3277692 < baseStart_3277692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277707 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_3277707 : Nat := 118140960795 + 3277707 * 2 ^ 59
def prefixEnd_3277707 : Nat := 4983230072969 + 3 ^ 40 * 3277707 * 2
def baseEnd_3277707 : Nat := 1122026090404341793325737

theorem tailTrace_3277707 : CollatzResearch.WordTrace tailWord_3277707 prefixEnd_3277707 1122026090404341793325737 := by
  unfold tailWord_3277707
  simp only [CollatzResearch.WordTrace]
  refine ⟨119547795536434801633727375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79698530357623201089151583 119547795536434801633727375)
  ·
    refine ⟨179321693304652202450591063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119547795536434801633727375 179321693304652202450591063)
    ·
      refine ⟨268982539956978303675886595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179321693304652202450591063 268982539956978303675886595)
      ·
        refine ⟨403473809935467455513829893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268982539956978303675886595 403473809935467455513829893)
        ·
          refine ⟨75651339362900147908843105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403473809935467455513829893 75651339362900147908843105)
          ·
            refine ⟨56738504522175110931632329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75651339362900147908843105 56738504522175110931632329)
            ·
              refine ⟨42553878391631333198724247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56738504522175110931632329 42553878391631333198724247)
              ·
                refine ⟨63830817587446999798086371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42553878391631333198724247 63830817587446999798086371)
                ·
                  refine ⟨95746226381170499697129557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63830817587446999798086371 95746226381170499697129557)
                  ·
                    refine ⟨1122026090404341793325737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95746226381170499697129557 1122026090404341793325737)
                    ·
                      rfl

theorem cell22_3277707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_3277707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277707 prefixEnd_3277707 := by exact prefixLift 3277707
  have htrace : WordTrace (prefixWord ++ tailWord_3277707) baseStart_3277707 baseEnd_3277707 := by
    simpa [prefixWord, tailWord_3277707, baseEnd_3277707] using wordTrace_append hprefix tailTrace_3277707
  have hstable : (prefixWord ++ tailWord_3277707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277707).length < 2 ^ (prefixWord ++ tailWord_3277707).sum := by decide
  have hdescent : baseEnd_3277707 < baseStart_3277707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277760 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_3277760 : Nat := 118140960795 + 3277760 * 2 ^ 59
def prefixEnd_3277760 : Nat := 4983230072969 + 3 ^ 40 * 3277760 * 2
def baseEnd_3277760 : Nat := 1122044233387467321750575

theorem tailTrace_3277760 : CollatzResearch.WordTrace tailWord_3277760 prefixEnd_3277760 1122044233387467321750575 := by
  unfold tailWord_3277760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59774864302621395842703367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79699819070161861123604489 59774864302621395842703367)
  ·
    refine ⟨89662296453932093764055051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59774864302621395842703367 89662296453932093764055051)
    ·
      refine ⟨134493444680898140646082577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89662296453932093764055051 134493444680898140646082577)
      ·
        refine ⟨100870083510673605484561933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134493444680898140646082577 100870083510673605484561933)
        ·
          refine ⟨37826281316502602056710725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100870083510673605484561933 37826281316502602056710725)
          ·
            refine ⟨7092427746844237885633261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37826281316502602056710725 7092427746844237885633261)
            ·
              refine ⟨2659660405066589207112473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7092427746844237885633261 2659660405066589207112473)
              ·
                refine ⟨1994745303799941905334355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659660405066589207112473 1994745303799941905334355)
                ·
                  refine ⟨2992117955699912858001533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994745303799941905334355 2992117955699912858001533)
                  ·
                    refine ⟨1122044233387467321750575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992117955699912858001533 1122044233387467321750575)
                    ·
                      rfl

theorem cell22_3277760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_3277760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277760 prefixEnd_3277760 := by exact prefixLift 3277760
  have htrace : WordTrace (prefixWord ++ tailWord_3277760) baseStart_3277760 baseEnd_3277760 := by
    simpa [prefixWord, tailWord_3277760, baseEnd_3277760] using wordTrace_append hprefix tailTrace_3277760
  have hstable : (prefixWord ++ tailWord_3277760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277760).length < 2 ^ (prefixWord ++ tailWord_3277760).sum := by decide
  have hdescent : baseEnd_3277760 < baseStart_3277760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277786 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_3277786 : Nat := 118140960795 + 3277786 * 2 ^ 59
def prefixEnd_3277786 : Nat := 4983230072969 + 3 ^ 40 * 3277786 * 2
def baseEnd_3277786 : Nat := 1122053133718811920600495

theorem tailTrace_3277786 : CollatzResearch.WordTrace tailWord_3277786 prefixEnd_3277786 1122053133718811920600495 := by
  unfold tailWord_3277786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29887669225787149531463303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79700451268765732083902141 29887669225787149531463303)
  ·
    refine ⟨44831503838680724297194955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29887669225787149531463303 44831503838680724297194955)
    ·
      refine ⟨67247255758021086445792433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44831503838680724297194955 67247255758021086445792433)
      ·
        refine ⟨50435441818515814834344325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67247255758021086445792433 50435441818515814834344325)
        ·
          refine ⟨9456645340971715281439561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50435441818515814834344325 9456645340971715281439561)
          ·
            refine ⟨7092484005728786461079671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9456645340971715281439561 7092484005728786461079671)
            ·
              refine ⟨10638726008593179691619507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092484005728786461079671 10638726008593179691619507)
              ·
                refine ⟨15958089012889769537429261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10638726008593179691619507 15958089012889769537429261)
                ·
                  refine ⟨5984283379833663576535973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15958089012889769537429261 5984283379833663576535973)
                  ·
                    refine ⟨1122053133718811920600495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5984283379833663576535973 1122053133718811920600495)
                    ·
                      rfl

theorem cell22_3277786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_3277786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277786 prefixEnd_3277786 := by exact prefixLift 3277786
  have htrace : WordTrace (prefixWord ++ tailWord_3277786) baseStart_3277786 baseEnd_3277786 := by
    simpa [prefixWord, tailWord_3277786, baseEnd_3277786] using wordTrace_append hprefix tailTrace_3277786
  have hstable : (prefixWord ++ tailWord_3277786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277786).length < 2 ^ (prefixWord ++ tailWord_3277786).sum := by decide
  have hdescent : baseEnd_3277786 < baseStart_3277786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277848 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_3277848 : Nat := 118140960795 + 3277848 * 2 ^ 59
def prefixEnd_3277848 : Nat := 4983230072969 + 3 ^ 40 * 3277848 * 2
def baseEnd_3277848 : Nat := 1122074357585864425550305

theorem tailTrace_3277848 : CollatzResearch.WordTrace tailWord_3277848 prefixEnd_3277848 1122074357585864425550305 := by
  unfold tailWord_3277848
  simp only [CollatzResearch.WordTrace]
  refine ⟨59776469114461991357305099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79701958819282655143073465 59776469114461991357305099)
  ·
    refine ⟨89664703671692987035957649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59776469114461991357305099 89664703671692987035957649)
    ·
      refine ⟨67248527753769740276968237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89664703671692987035957649 67248527753769740276968237)
      ·
        refine ⟨25218197907663652603863089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67248527753769740276968237 25218197907663652603863089)
        ·
          refine ⟨18913648430747739452897317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25218197907663652603863089 18913648430747739452897317)
          ·
            refine ⟨3546309080765201147418247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18913648430747739452897317 3546309080765201147418247)
            ·
              refine ⟨5319463621147801721127371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546309080765201147418247 5319463621147801721127371)
              ·
                refine ⟨7979195431721702581691057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319463621147801721127371 7979195431721702581691057)
                ·
                  refine ⟨5984396573791276936268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979195431721702581691057 5984396573791276936268293)
                  ·
                    refine ⟨1122074357585864425550305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5984396573791276936268293 1122074357585864425550305)
                    ·
                      rfl

theorem cell22_3277848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_3277848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277848 prefixEnd_3277848 := by exact prefixLift 3277848
  have htrace : WordTrace (prefixWord ++ tailWord_3277848) baseStart_3277848 baseEnd_3277848 := by
    simpa [prefixWord, tailWord_3277848, baseEnd_3277848] using wordTrace_append hprefix tailTrace_3277848
  have hstable : (prefixWord ++ tailWord_3277848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277848).length < 2 ^ (prefixWord ++ tailWord_3277848).sum := by decide
  have hdescent : baseEnd_3277848 < baseStart_3277848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277861 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_3277861 : Nat := 118140960795 + 3277861 * 2 ^ 59
def prefixEnd_3277861 : Nat := 4983230072969 + 3 ^ 40 * 3277861 * 2
def baseEnd_3277861 : Nat := 1122078807751536724975265

theorem tailTrace_3277861 : CollatzResearch.WordTrace tailWord_3277861 prefixEnd_3277861 1122078807751536724975265 := by
  unfold tailWord_3277861
  simp only [CollatzResearch.WordTrace]
  refine ⟨119553412377876885934833437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79702274918584590623222291 119553412377876885934833437)
  ·
    refine ⟨44832529641703832225562539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119553412377876885934833437 44832529641703832225562539)
    ·
      refine ⟨67248794462555748338343809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44832529641703832225562539 67248794462555748338343809)
      ·
        refine ⟨50436595846916811253757857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67248794462555748338343809 50436595846916811253757857)
        ·
          refine ⟨37827446885187608440318393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50436595846916811253757857 37827446885187608440318393)
          ·
            refine ⟨28370585163890706330238795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37827446885187608440318393 28370585163890706330238795)
            ·
              refine ⟨42555877745836059495358193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28370585163890706330238795 42555877745836059495358193)
              ·
                refine ⟨31916908309377044621518645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42555877745836059495358193 31916908309377044621518645)
                ·
                  refine ⟨2992210154004097933267373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31916908309377044621518645 2992210154004097933267373)
                  ·
                    refine ⟨1122078807751536724975265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992210154004097933267373 1122078807751536724975265)
                    ·
                      rfl

theorem cell22_3277861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_3277861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277861 prefixEnd_3277861 := by exact prefixLift 3277861
  have htrace : WordTrace (prefixWord ++ tailWord_3277861) baseStart_3277861 baseEnd_3277861 := by
    simpa [prefixWord, tailWord_3277861, baseEnd_3277861] using wordTrace_append hprefix tailTrace_3277861
  have hstable : (prefixWord ++ tailWord_3277861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277861).length < 2 ^ (prefixWord ++ tailWord_3277861).sum := by decide
  have hdescent : baseEnd_3277861 < baseStart_3277861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277904 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_3277904 : Nat := 118140960795 + 3277904 * 2 ^ 59
def prefixEnd_3277904 : Nat := 4983230072969 + 3 ^ 40 * 3277904 * 2
def baseEnd_3277904 : Nat := 1122093527530298946150133

theorem tailTrace_3277904 : CollatzResearch.WordTrace tailWord_3277904 prefixEnd_3277904 1122093527530298946150133 := by
  unfold tailWord_3277904
  simp only [CollatzResearch.WordTrace]
  refine ⟨59777490358360552139324383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79703320477814069519099177 59777490358360552139324383)
  ·
    refine ⟨89666235537540828208986575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59777490358360552139324383 89666235537540828208986575)
    ·
      refine ⟨134499353306311242313479863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89666235537540828208986575 134499353306311242313479863)
      ·
        refine ⟨201749029959466863470219795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134499353306311242313479863 201749029959466863470219795)
        ·
          refine ⟨302623544939200295205329693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201749029959466863470219795 302623544939200295205329693)
          ·
            refine ⟨113483829352200110701998635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302623544939200295205329693 113483829352200110701998635)
            ·
              refine ⟨170225744028300166052997953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113483829352200110701998635 170225744028300166052997953)
              ·
                refine ⟨127669308021225124539748465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170225744028300166052997953 127669308021225124539748465)
                ·
                  refine ⟨95751981015918843404811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127669308021225124539748465 95751981015918843404811349)
                  ·
                    refine ⟨1122093527530298946150133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95751981015918843404811349 1122093527530298946150133)
                    ·
                      rfl

theorem cell22_3277904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_3277904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277904 prefixEnd_3277904 := by exact prefixLift 3277904
  have htrace : WordTrace (prefixWord ++ tailWord_3277904) baseStart_3277904 baseEnd_3277904 := by
    simpa [prefixWord, tailWord_3277904, baseEnd_3277904] using wordTrace_append hprefix tailTrace_3277904
  have hstable : (prefixWord ++ tailWord_3277904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277904).length < 2 ^ (prefixWord ++ tailWord_3277904).sum := by decide
  have hdescent : baseEnd_3277904 < baseStart_3277904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277985 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3277985 : Nat := 118140960795 + 3277985 * 2 ^ 59
def prefixEnd_3277985 : Nat := 4983230072969 + 3 ^ 40 * 3277985 * 2
def baseEnd_3277985 : Nat := 1122121255485641734874885

theorem tailTrace_3277985 : CollatzResearch.WordTrace tailWord_3277985 prefixEnd_3277985 1122121255485641734874885 := by
  unfold tailWord_3277985
  simp only [CollatzResearch.WordTrace]
  refine ⟨119557935029427655112347409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79705290019618436741564939 119557935029427655112347409)
  ·
    refine ⟨89668451272070741334260557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119557935029427655112347409 89668451272070741334260557)
    ·
      refine ⟨33625669227026528000347709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89668451272070741334260557 33625669227026528000347709)
      ·
        refine ⟨12609625960134948000130391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33625669227026528000347709 12609625960134948000130391)
        ·
          refine ⟨18914438940202422000195587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12609625960134948000130391 18914438940202422000195587)
          ·
            refine ⟨28371658410303633000293381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18914438940202422000195587 28371658410303633000293381)
            ·
              refine ⟨5319685951931931187555009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28371658410303633000293381 5319685951931931187555009)
              ·
                refine ⟨3989764463948948390666257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319685951931931187555009 3989764463948948390666257)
                ·
                  refine ⟨2992323347961711292999693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989764463948948390666257 2992323347961711292999693)
                  ·
                    refine ⟨1122121255485641734874885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992323347961711292999693 1122121255485641734874885)
                    ·
                      rfl

theorem cell22_3277985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3277985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3277985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3277985 prefixEnd_3277985 := by exact prefixLift 3277985
  have htrace : WordTrace (prefixWord ++ tailWord_3277985) baseStart_3277985 baseEnd_3277985 := by
    simpa [prefixWord, tailWord_3277985, baseEnd_3277985] using wordTrace_append hprefix tailTrace_3277985
  have hstable : (prefixWord ++ tailWord_3277985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277985).length < 2 ^ (prefixWord ++ tailWord_3277985).sum := by decide
  have hdescent : baseEnd_3277985 < baseStart_3277985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278013 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_3278013 : Nat := 118140960795 + 3278013 * 2 ^ 59
def prefixEnd_3278013 : Nat := 4983230072969 + 3 ^ 40 * 3278013 * 2
def baseEnd_3278013 : Nat := 1122130840457858995174799

theorem tailTrace_3278013 : CollatzResearch.WordTrace tailWord_3278013 prefixEnd_3278013 1122130840457858995174799 := by
  unfold tailWord_3278013
  simp only [CollatzResearch.WordTrace]
  refine ⟨119558956273326215894366693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79705970848884143929577795 119558956273326215894366693)
  ·
    refine ⟨22417304301248665480193755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119558956273326215894366693 22417304301248665480193755)
    ·
      refine ⟨33625956451872998220290633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22417304301248665480193755 33625956451872998220290633)
      ·
        refine ⟨25219467338904748665217975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33625956451872998220290633 25219467338904748665217975)
        ·
          refine ⟨37829201008357122997826963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25219467338904748665217975 37829201008357122997826963)
          ·
            refine ⟨56743801512535684496740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37829201008357122997826963 56743801512535684496740445)
            ·
              refine ⟨21278925567200881686277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56743801512535684496740445 21278925567200881686277667)
              ·
                refine ⟨31918388350801322529416501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278925567200881686277667 31918388350801322529416501)
                ·
                  refine ⟨2992348907887623987132797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31918388350801322529416501 2992348907887623987132797)
                  ·
                    refine ⟨1122130840457858995174799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992348907887623987132797 1122130840457858995174799)
                    ·
                      rfl

theorem cell22_3278013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_3278013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278013 prefixEnd_3278013 := by exact prefixLift 3278013
  have htrace : WordTrace (prefixWord ++ tailWord_3278013) baseStart_3278013 baseEnd_3278013 := by
    simpa [prefixWord, tailWord_3278013, baseEnd_3278013] using wordTrace_append hprefix tailTrace_3278013
  have hstable : (prefixWord ++ tailWord_3278013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278013).length < 2 ^ (prefixWord ++ tailWord_3278013).sum := by decide
  have hdescent : baseEnd_3278013 < baseStart_3278013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278017 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3278017 : Nat := 118140960795 + 3278017 * 2 ^ 59
def prefixEnd_3278017 : Nat := 4983230072969 + 3 ^ 40 * 3278017 * 2
def baseEnd_3278017 : Nat := 1122132209739604318074787

theorem tailTrace_3278017 : CollatzResearch.WordTrace tailWord_3278017 prefixEnd_3278017 1122132209739604318074787 := by
  unfold tailWord_3278017
  simp only [CollatzResearch.WordTrace]
  refine ⟨119559102165311724577512305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79706068110207816385008203 119559102165311724577512305)
  ·
    refine ⟨89669326623983793433134229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119559102165311724577512305 89669326623983793433134229)
    ·
      refine ⟨4203249685499240317178167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89669326623983793433134229 4203249685499240317178167)
      ·
        refine ⟨6304874528248860475767251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203249685499240317178167 6304874528248860475767251)
        ·
          refine ⟨9457311792373290713650877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304874528248860475767251 9457311792373290713650877)
          ·
            refine ⟨3546491922139984017619079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9457311792373290713650877 3546491922139984017619079)
            ·
              refine ⟨5319737883209976026428619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546491922139984017619079 5319737883209976026428619)
              ·
                refine ⟨7979606824814964039642929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319737883209976026428619 7979606824814964039642929)
                ·
                  refine ⟨5984705118611223029732197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979606824814964039642929 5984705118611223029732197)
                  ·
                    refine ⟨1122132209739604318074787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5984705118611223029732197 1122132209739604318074787)
                    ·
                      rfl

theorem cell22_3278017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3278017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278017 prefixEnd_3278017 := by exact prefixLift 3278017
  have htrace : WordTrace (prefixWord ++ tailWord_3278017) baseStart_3278017 baseEnd_3278017 := by
    simpa [prefixWord, tailWord_3278017, baseEnd_3278017] using wordTrace_append hprefix tailTrace_3278017
  have hstable : (prefixWord ++ tailWord_3278017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278017).length < 2 ^ (prefixWord ++ tailWord_3278017).sum := by decide
  have hdescent : baseEnd_3278017 < baseStart_3278017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278036 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3278036 : Nat := 118140960795 + 3278036 * 2 ^ 59
def prefixEnd_3278036 : Nat := 4983230072969 + 3 ^ 40 * 3278036 * 2
def baseEnd_3278036 : Nat := 1122138713827894601849729

theorem tailTrace_3278036 : CollatzResearch.WordTrace tailWord_3278036 prefixEnd_3278036 1122138713827894601849729 := by
  unfold tailWord_3278036
  simp only [CollatzResearch.WordTrace]
  refine ⟨59779897576121445411226981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79706530101495260548302641 59779897576121445411226981)
  ·
    refine ⟨11208730795522771014605059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59779897576121445411226981 11208730795522771014605059)
    ·
      refine ⟨16813096193284156521907589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208730795522771014605059 16813096193284156521907589)
      ·
        refine ⟨3152455536240779347857673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16813096193284156521907589 3152455536240779347857673)
        ·
          refine ⟨2364341652180584510893255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152455536240779347857673 2364341652180584510893255)
          ·
            refine ⟨3546512478270876766339883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364341652180584510893255 3546512478270876766339883)
            ·
              refine ⟨5319768717406315149509825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546512478270876766339883 5319768717406315149509825)
              ·
                refine ⟨3989826538054736362132369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319768717406315149509825 3989826538054736362132369)
                ·
                  refine ⟨2992369903541052271599277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989826538054736362132369 2992369903541052271599277)
                  ·
                    refine ⟨1122138713827894601849729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992369903541052271599277 1122138713827894601849729)
                    ·
                      rfl

theorem cell22_3278036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3278036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278036 prefixEnd_3278036 := by exact prefixLift 3278036
  have htrace : WordTrace (prefixWord ++ tailWord_3278036) baseStart_3278036 baseEnd_3278036 := by
    simpa [prefixWord, tailWord_3278036, baseEnd_3278036] using wordTrace_append hprefix tailTrace_3278036
  have hstable : (prefixWord ++ tailWord_3278036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278036).length < 2 ^ (prefixWord ++ tailWord_3278036).sum := by decide
  have hdescent : baseEnd_3278036 < baseStart_3278036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278058 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3278058 : Nat := 118140960795 + 3278058 * 2 ^ 59
def prefixEnd_3278058 : Nat := 4983230072969 + 3 ^ 40 * 3278058 * 2
def baseEnd_3278058 : Nat := 1122146244877493877799661

theorem tailTrace_3278058 : CollatzResearch.WordTrace tailWord_3278058 prefixEnd_3278058 1122146244877493877799661 := by
  unfold tailWord_3278058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890149389540797144938707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79707065038775459053169885 29890149389540797144938707)
  ·
    refine ⟨44835224084311195717408061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29890149389540797144938707 44835224084311195717408061)
    ·
      refine ⟨16813209031616698394028023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44835224084311195717408061 16813209031616698394028023)
      ·
        refine ⟨25219813547425047591042035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16813209031616698394028023 25219813547425047591042035)
        ·
          refine ⟨37829720321137571386563053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25219813547425047591042035 37829720321137571386563053)
          ·
            refine ⟨14186145120426589269961145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37829720321137571386563053 14186145120426589269961145)
            ·
              refine ⟨10639608840319941952470859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14186145120426589269961145 10639608840319941952470859)
              ·
                refine ⟨15959413260479912928706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10639608840319941952470859 15959413260479912928706289)
                ·
                  refine ⟨11969559945359934696529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15959413260479912928706289 11969559945359934696529717)
                  ·
                    refine ⟨1122146244877493877799661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11969559945359934696529717 1122146244877493877799661)
                    ·
                      rfl

theorem cell22_3278058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3278058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278058 prefixEnd_3278058 := by exact prefixLift 3278058
  have htrace : WordTrace (prefixWord ++ tailWord_3278058) baseStart_3278058 baseEnd_3278058 := by
    simpa [prefixWord, tailWord_3278058, baseEnd_3278058] using wordTrace_append hprefix tailTrace_3278058
  have hstable : (prefixWord ++ tailWord_3278058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278058).length < 2 ^ (prefixWord ++ tailWord_3278058).sum := by decide
  have hdescent : baseEnd_3278058 < baseStart_3278058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278060 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_3278060 : Nat := 118140960795 + 3278060 * 2 ^ 59
def prefixEnd_3278060 : Nat := 4983230072969 + 3 ^ 40 * 3278060 * 2
def baseEnd_3278060 : Nat := 374048976506122179749885

theorem tailTrace_3278060 : CollatzResearch.WordTrace tailWord_3278060 prefixEnd_3278060 374048976506122179749885 := by
  unfold tailWord_3278060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59780335252077971460663817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79707113669437295280885089 59780335252077971460663817)
  ·
    refine ⟨44835251439058478595497863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59780335252077971460663817 44835251439058478595497863)
    ·
      refine ⟨67252877158587717893246795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44835251439058478595497863 67252877158587717893246795)
      ·
        refine ⟨100879315737881576839870193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67252877158587717893246795 100879315737881576839870193)
        ·
          refine ⟨75659486803411182629902645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100879315737881576839870193 75659486803411182629902645)
          ·
            refine ⟨7093076887819798371553373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75659486803411182629902645 7093076887819798371553373)
            ·
              refine ⟨2659903832932424389332515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7093076887819798371553373 2659903832932424389332515)
              ·
                refine ⟨3989855749398636583998773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659903832932424389332515 3989855749398636583998773)
                ·
                  refine ⟨374048976506122179749885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3989855749398636583998773 374048976506122179749885)
                  ·
                    rfl

theorem cell22_3278060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_3278060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278060 prefixEnd_3278060 := by exact prefixLift 3278060
  have htrace : WordTrace (prefixWord ++ tailWord_3278060) baseStart_3278060 baseEnd_3278060 := by
    simpa [prefixWord, tailWord_3278060, baseEnd_3278060] using wordTrace_append hprefix tailTrace_3278060
  have hstable : (prefixWord ++ tailWord_3278060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278060).length < 2 ^ (prefixWord ++ tailWord_3278060).sum := by decide
  have hdescent : baseEnd_3278060 < baseStart_3278060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278098 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3278098 : Nat := 118140960795 + 3278098 * 2 ^ 59
def prefixEnd_3278098 : Nat := 4983230072969 + 3 ^ 40 * 3278098 * 2
def baseEnd_3278098 : Nat := 1122159937694947106799539

theorem tailTrace_3278098 : CollatzResearch.WordTrace tailWord_3278098 prefixEnd_3278098 1122159937694947106799539 := by
  unfold tailWord_3278098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890514119504568852802737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79708037652012183607473965 29890514119504568852802737)
  ·
    refine ⟨22417885589628426639602053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29890514119504568852802737 22417885589628426639602053)
    ·
      refine ⟨4203353548055329994925385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22417885589628426639602053 4203353548055329994925385)
      ·
        refine ⟨3152515161041497496194039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4203353548055329994925385 3152515161041497496194039)
        ·
          refine ⟨4728772741562246244291059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152515161041497496194039 4728772741562246244291059)
          ·
            refine ⟨7093159112343369366436589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728772741562246244291059 7093159112343369366436589)
            ·
              refine ⟨2659934667128763512413721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7093159112343369366436589 2659934667128763512413721)
              ·
                refine ⟨1994951000346572634310291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659934667128763512413721 1994951000346572634310291)
                ·
                  refine ⟨2992426500519858951465437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994951000346572634310291 2992426500519858951465437)
                  ·
                    refine ⟨1122159937694947106799539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992426500519858951465437 1122159937694947106799539)
                    ·
                      rfl

theorem cell22_3278098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3278098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278098 prefixEnd_3278098 := by exact prefixLift 3278098
  have htrace : WordTrace (prefixWord ++ tailWord_3278098) baseStart_3278098 baseEnd_3278098 := by
    simpa [prefixWord, tailWord_3278098, baseEnd_3278098] using wordTrace_append hprefix tailTrace_3278098
  have hstable : (prefixWord ++ tailWord_3278098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278098).length < 2 ^ (prefixWord ++ tailWord_3278098).sum := by decide
  have hdescent : baseEnd_3278098 < baseStart_3278098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278133 : List Nat := [1, 3, 3, 1, 2, 2, 2, 8]
def baseStart_3278133 : Nat := 118140960795 + 3278133 * 2 ^ 59
def prefixEnd_3278133 : Nat := 4983230072969 + 3 ^ 40 * 3278133 * 2
def baseEnd_3278133 : Nat := 124685768767802075797159

theorem tailTrace_3278133 : CollatzResearch.WordTrace tailWord_3278133 prefixEnd_3278133 124685768767802075797159 := by
  unfold tailWord_3278133
  simp only [CollatzResearch.WordTrace]
  refine ⟨119563333032891476388735053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79708888688594317592490035 119563333032891476388735053)
  ·
    refine ⟨44836249887334303645775645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119563333032891476388735053 44836249887334303645775645)
    ·
      refine ⟨16813593707750363867165867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44836249887334303645775645 16813593707750363867165867)
      ·
        refine ⟨25220390561625545800748801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16813593707750363867165867 25220390561625545800748801)
        ·
          refine ⟨18915292921219159350561601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25220390561625545800748801 18915292921219159350561601)
          ·
            refine ⟨14186469690914369512921201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18915292921219159350561601 14186469690914369512921201)
            ·
              refine ⟨10639852268185777134690901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14186469690914369512921201 10639852268185777134690901)
              ·
                refine ⟨124685768767802075797159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10639852268185777134690901 124685768767802075797159)
                ·
                  rfl

theorem cell22_3278133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 8].length) (baseStart_3278133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278133 prefixEnd_3278133 := by exact prefixLift 3278133
  have htrace : WordTrace (prefixWord ++ tailWord_3278133) baseStart_3278133 baseEnd_3278133 := by
    simpa [prefixWord, tailWord_3278133, baseEnd_3278133] using wordTrace_append hprefix tailTrace_3278133
  have hstable : (prefixWord ++ tailWord_3278133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278133).length < 2 ^ (prefixWord ++ tailWord_3278133).sum := by decide
  have hdescent : baseEnd_3278133 < baseStart_3278133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278212 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3278212 : Nat := 118140960795 + 3278212 * 2 ^ 59
def prefixEnd_3278212 : Nat := 4983230072969 + 3 ^ 40 * 3278212 * 2
def baseEnd_3278212 : Nat := 374066320741562936483063

theorem tailTrace_3278212 : CollatzResearch.WordTrace tailWord_3278212 prefixEnd_3278212 374066320741562936483063 := by
  unfold tailWord_3278212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59783107199802636440430445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79710809599736848587240593 59783107199802636440430445)
  ·
    refine ⟨22418665199925988665161417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59783107199802636440430445 22418665199925988665161417)
    ·
      refine ⟨16813998899944491498871063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22418665199925988665161417 16813998899944491498871063)
      ·
        refine ⟨25220998349916737248306595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16813998899944491498871063 25220998349916737248306595)
        ·
          refine ⟨37831497524875105872459893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25220998349916737248306595 37831497524875105872459893)
          ·
            refine ⟨3546702892957041175543115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37831497524875105872459893 3546702892957041175543115)
            ·
              refine ⟨5320054339435561763314673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546702892957041175543115 5320054339435561763314673)
              ·
                refine ⟨3990040754576671322486005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320054339435561763314673 3990040754576671322486005)
                ·
                  refine ⟨374066320741562936483063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990040754576671322486005 374066320741562936483063)
                  ·
                    rfl

theorem cell22_3278212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3278212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278212 prefixEnd_3278212 := by exact prefixLift 3278212
  have htrace : WordTrace (prefixWord ++ tailWord_3278212) baseStart_3278212 baseEnd_3278212 := by
    simpa [prefixWord, tailWord_3278212, baseEnd_3278212] using wordTrace_append hprefix tailTrace_3278212
  have hstable : (prefixWord ++ tailWord_3278212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278212).length < 2 ^ (prefixWord ++ tailWord_3278212).sum := by decide
  have hdescent : baseEnd_3278212 < baseStart_3278212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278242 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3278242 : Nat := 118140960795 + 3278242 * 2 ^ 59
def prefixEnd_3278242 : Nat := 4983230072969 + 3 ^ 40 * 3278242 * 2
def baseEnd_3278242 : Nat := 1122209231837778731199097

theorem tailTrace_3278242 : CollatzResearch.WordTrace tailWord_3278242 prefixEnd_3278242 1122209231837778731199097 := by
  unfold tailWord_3278242
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891827147374147001113245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79711539059664392002968653 29891827147374147001113245)
  ·
    refine ⟨11209435180265305125417467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29891827147374147001113245 11209435180265305125417467)
    ·
      refine ⟨16814152770397957688126201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11209435180265305125417467 16814152770397957688126201)
      ·
        refine ⟨12610614577798468266094651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16814152770397957688126201 12610614577798468266094651)
        ·
          refine ⟨18915921866697702399141977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12610614577798468266094651 18915921866697702399141977)
          ·
            refine ⟨14186941400023276799356483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18915921866697702399141977 14186941400023276799356483)
            ·
              refine ⟨21280412100034915199034725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14186941400023276799356483 21280412100034915199034725)
              ·
                refine ⟨3990077268756546599819011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21280412100034915199034725 3990077268756546599819011)
                ·
                  refine ⟨5985115903134819899728517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990077268756546599819011 5985115903134819899728517)
                  ·
                    refine ⟨1122209231837778731199097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985115903134819899728517 1122209231837778731199097)
                    ·
                      rfl

theorem cell22_3278242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3278242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278242 prefixEnd_3278242 := by exact prefixLift 3278242
  have htrace : WordTrace (prefixWord ++ tailWord_3278242) baseStart_3278242 baseEnd_3278242 := by
    simpa [prefixWord, tailWord_3278242, baseEnd_3278242] using wordTrace_append hprefix tailTrace_3278242
  have hstable : (prefixWord ++ tailWord_3278242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278242).length < 2 ^ (prefixWord ++ tailWord_3278242).sum := by decide
  have hdescent : baseEnd_3278242 < baseStart_3278242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278345 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_3278345 : Nat := 118140960795 + 3278345 * 2 ^ 59
def prefixEnd_3278345 : Nat := 4983230072969 + 3 ^ 40 * 3278345 * 2
def baseEnd_3278345 : Nat := 1122244490842720795873781

theorem tailTrace_3278345 : CollatzResearch.WordTrace tailWord_3278345 prefixEnd_3278345 1122244490842720795873781 := by
  unfold tailWord_3278345
  simp only [CollatzResearch.WordTrace]
  refine ⟨119571065308123436595452489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79714043538748957730301659 119571065308123436595452489)
  ·
    refine ⟨89678298981092577446589367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119571065308123436595452489 89678298981092577446589367)
    ·
      refine ⟨134517448471638866169884051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89678298981092577446589367 134517448471638866169884051)
      ·
        refine ⟨201776172707458299254826077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134517448471638866169884051 201776172707458299254826077)
        ·
          refine ⟨75666064765296862220559779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201776172707458299254826077 75666064765296862220559779)
          ·
            refine ⟨113499097147945293330839669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75666064765296862220559779 113499097147945293330839669)
            ·
              refine ⟨10640540357619871249766219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113499097147945293330839669 10640540357619871249766219)
              ·
                refine ⟨15960810536429806874649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10640540357619871249766219 15960810536429806874649329)
                ·
                  refine ⟨11970607902322355155986997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15960810536429806874649329 11970607902322355155986997)
                  ·
                    refine ⟨1122244490842720795873781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11970607902322355155986997 1122244490842720795873781)
                    ·
                      rfl

theorem cell22_3278345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_3278345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278345 prefixEnd_3278345 := by exact prefixLift 3278345
  have htrace : WordTrace (prefixWord ++ tailWord_3278345) baseStart_3278345 baseEnd_3278345 := by
    simpa [prefixWord, tailWord_3278345, baseEnd_3278345] using wordTrace_append hprefix tailTrace_3278345
  have hstable : (prefixWord ++ tailWord_3278345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278345).length < 2 ^ (prefixWord ++ tailWord_3278345).sum := by decide
  have hdescent : baseEnd_3278345 < baseStart_3278345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278392 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_3278392 : Nat := 118140960795 + 3278392 * 2 ^ 59
def prefixEnd_3278392 : Nat := 4983230072969 + 3 ^ 40 * 3278392 * 2
def baseEnd_3278392 : Nat := 374086859967742779982879

theorem tailTrace_3278392 : CollatzResearch.WordTrace tailWord_3278392 prefixEnd_3278392 374086859967742779982879 := by
  unfold tailWord_3278392
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786389769476581811206715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79715186359302109081608953 59786389769476581811206715)
  ·
    refine ⟨89679584654214872716810073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59786389769476581811206715 89679584654214872716810073)
    ·
      refine ⟨67259688490661154537607555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89679584654214872716810073 67259688490661154537607555)
      ·
        refine ⟨100889532735991731806411333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67259688490661154537607555 100889532735991731806411333)
        ·
          refine ⟨18916787387998449713702125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100889532735991731806411333 18916787387998449713702125)
          ·
            refine ⟨7093795270499418642638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18916787387998449713702125 7093795270499418642638297)
            ·
              refine ⟨5320346452874563981978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093795270499418642638297 5320346452874563981978723)
              ·
                refine ⟨7980519679311845972968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320346452874563981978723 7980519679311845972968085)
                ·
                  refine ⟨374086859967742779982879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7980519679311845972968085 374086859967742779982879)
                  ·
                    rfl

theorem cell22_3278392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_3278392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278392 prefixEnd_3278392 := by exact prefixLift 3278392
  have htrace : WordTrace (prefixWord ++ tailWord_3278392) baseStart_3278392 baseEnd_3278392 := by
    simpa [prefixWord, tailWord_3278392, baseEnd_3278392] using wordTrace_append hprefix tailTrace_3278392
  have hstable : (prefixWord ++ tailWord_3278392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278392).length < 2 ^ (prefixWord ++ tailWord_3278392).sum := by decide
  have hdescent : baseEnd_3278392 < baseStart_3278392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278405 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3278405 : Nat := 118140960795 + 3278405 * 2 ^ 59
def prefixEnd_3278405 : Nat := 4983230072969 + 3 ^ 40 * 3278405 * 2
def baseEnd_3278405 : Nat := 1122265030068900639373597

theorem tailTrace_3278405 : CollatzResearch.WordTrace tailWord_3278405 prefixEnd_3278405 1122265030068900639373597 := by
  unfold tailWord_3278405
  simp only [CollatzResearch.WordTrace]
  refine ⟨119573253687906066842636669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79715502458604044561757779 119573253687906066842636669)
  ·
    refine ⟨44839970132964775065988751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119573253687906066842636669 44839970132964775065988751)
    ·
      refine ⟨67259955199447162598983127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44839970132964775065988751 67259955199447162598983127)
      ·
        refine ⟨100889932799170743898474691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67259955199447162598983127 100889932799170743898474691)
        ·
          refine ⟨151334899198756115847712037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100889932799170743898474691 151334899198756115847712037)
          ·
            refine ⟨28375293599766771721446007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151334899198756115847712037 28375293599766771721446007)
            ·
              refine ⟨42562940399650157582169011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28375293599766771721446007 42562940399650157582169011)
              ·
                refine ⟨63844410599475236373253517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42562940399650157582169011 63844410599475236373253517)
                ·
                  refine ⟨23941653974803213639970069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63844410599475236373253517 23941653974803213639970069)
                  ·
                    refine ⟨1122265030068900639373597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23941653974803213639970069 1122265030068900639373597)
                    ·
                      rfl

theorem cell22_3278405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3278405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278405 prefixEnd_3278405 := by exact prefixLift 3278405
  have htrace : WordTrace (prefixWord ++ tailWord_3278405) baseStart_3278405 baseEnd_3278405 := by
    simpa [prefixWord, tailWord_3278405, baseEnd_3278405] using wordTrace_append hprefix tailTrace_3278405
  have hstable : (prefixWord ++ tailWord_3278405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278405).length < 2 ^ (prefixWord ++ tailWord_3278405).sum := by decide
  have hdescent : baseEnd_3278405 < baseStart_3278405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278437 : List Nat := [1, 3, 1, 3, 3, 3, 8]
def baseStart_3278437 : Nat := 118140960795 + 3278437 * 2 ^ 59
def prefixEnd_3278437 : Nat := 4983230072969 + 3 ^ 40 * 3278437 * 2
def baseEnd_3278437 : Nat := 41565777197143082317537

theorem tailTrace_3278437 : CollatzResearch.WordTrace tailWord_3278437 prefixEnd_3278437 41565777197143082317537 := by
  unfold tailWord_3278437
  simp only [CollatzResearch.WordTrace]
  refine ⟨119574420823790136307801565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79716280549193424205201043 119574420823790136307801565)
  ·
    refine ⟨44840407808921301115425587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119574420823790136307801565 44840407808921301115425587)
    ·
      refine ⟨67260611713381951673138381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44840407808921301115425587 67260611713381951673138381)
      ·
        refine ⟨25222729392518231877426893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67260611713381951673138381 25222729392518231877426893)
        ·
          refine ⟨9458523522194336954035085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25222729392518231877426893 9458523522194336954035085)
          ·
            refine ⟨3546946320822876357763157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9458523522194336954035085 3546946320822876357763157)
            ·
              refine ⟨41565777197143082317537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3546946320822876357763157 41565777197143082317537)
              ·
                rfl

theorem cell22_3278437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 8].length) (baseStart_3278437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278437 prefixEnd_3278437 := by exact prefixLift 3278437
  have htrace : WordTrace (prefixWord ++ tailWord_3278437) baseStart_3278437 baseEnd_3278437 := by
    simpa [prefixWord, tailWord_3278437, baseEnd_3278437] using wordTrace_append hprefix tailTrace_3278437
  have hstable : (prefixWord ++ tailWord_3278437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278437).length < 2 ^ (prefixWord ++ tailWord_3278437).sum := by decide
  have hdescent : baseEnd_3278437 < baseStart_3278437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278454 : List Nat := [5, 1, 1, 2, 2, 2, 2, 7]
def baseStart_3278454 : Nat := 118140960795 + 3278454 * 2 ^ 59
def prefixEnd_3278454 : Nat := 4983230072969 + 3 ^ 40 * 3278454 * 2
def baseEnd_3278454 : Nat := 124697978196697871655383

theorem tailTrace_3278454 : CollatzResearch.WordTrace tailWord_3278454 prefixEnd_3278454 124697978196697871655383 := by
  unfold tailWord_3278454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473440054045534263198151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79716693909819032140780277 7473440054045534263198151)
  ·
    refine ⟨11210160081068301394797227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7473440054045534263198151 11210160081068301394797227)
    ·
      refine ⟨16815240121602452092195841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11210160081068301394797227 16815240121602452092195841)
      ·
        refine ⟨12611430091201839069146881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16815240121602452092195841 12611430091201839069146881)
        ·
          refine ⟨9458572568401379301860161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611430091201839069146881 9458572568401379301860161)
          ·
            refine ⟨7093929426301034476395121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458572568401379301860161 7093929426301034476395121)
            ·
              refine ⟨5320447069725775857296341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093929426301034476395121 5320447069725775857296341)
              ·
                refine ⟨124697978196697871655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5320447069725775857296341 124697978196697871655383)
                ·
                  rfl

theorem cell22_3278454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_3278454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278454 prefixEnd_3278454 := by exact prefixLift 3278454
  have htrace : WordTrace (prefixWord ++ tailWord_3278454) baseStart_3278454 baseEnd_3278454 := by
    simpa [prefixWord, tailWord_3278454, baseEnd_3278454] using wordTrace_append hprefix tailTrace_3278454
  have hstable : (prefixWord ++ tailWord_3278454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278454).length < 2 ^ (prefixWord ++ tailWord_3278454).sum := by decide
  have hdescent : baseEnd_3278454 < baseStart_3278454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278512 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_3278512 : Nat := 118140960795 + 3278512 * 2 ^ 59
def prefixEnd_3278512 : Nat := 4983230072969 + 3 ^ 40 * 3278512 * 2
def baseEnd_3278512 : Nat := 1122301658355588026948269

theorem tailTrace_3278512 : CollatzResearch.WordTrace tailWord_3278512 prefixEnd_3278512 1122301658355588026948269 := by
  unfold tailWord_3278512
  simp only [CollatzResearch.WordTrace]
  refine ⟨59788578149259212058390895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79718104199012282744521193 59788578149259212058390895)
  ·
    refine ⟨89682867223888818087586343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59788578149259212058390895 89682867223888818087586343)
    ·
      refine ⟨134524300835833227131379515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89682867223888818087586343 134524300835833227131379515)
      ·
        refine ⟨201786451253749840697069273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134524300835833227131379515 201786451253749840697069273)
        ·
          refine ⟨151339838440312380522801955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201786451253749840697069273 151339838440312380522801955)
          ·
            refine ⟨227009757660468570784202933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151339838440312380522801955 227009757660468570784202933)
            ·
              refine ⟨21282164780668928511019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227009757660468570784202933 21282164780668928511019025)
              ·
                refine ⟨15961623585501696383264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21282164780668928511019025 15961623585501696383264269)
                ·
                  refine ⟨5985608844563136143724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15961623585501696383264269 5985608844563136143724101)
                  ·
                    refine ⟨1122301658355588026948269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985608844563136143724101 1122301658355588026948269)
                    ·
                      rfl

theorem cell22_3278512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_3278512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278512 prefixEnd_3278512 := by exact prefixLift 3278512
  have htrace : WordTrace (prefixWord ++ tailWord_3278512) baseStart_3278512 baseEnd_3278512 := by
    simpa [prefixWord, tailWord_3278512, baseEnd_3278512] using wordTrace_append hprefix tailTrace_3278512
  have hstable : (prefixWord ++ tailWord_3278512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278512).length < 2 ^ (prefixWord ++ tailWord_3278512).sum := by decide
  have hdescent : baseEnd_3278512 < baseStart_3278512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278527 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 6]
def baseStart_3278527 : Nat := 118140960795 + 3278527 * 2 ^ 59
def prefixEnd_3278527 : Nat := 4983230072969 + 3 ^ 40 * 3278527 * 2
def baseEnd_3278527 : Nat := 374102264387377662607741

theorem tailTrace_3278527 : CollatzResearch.WordTrace tailWord_3278527 prefixEnd_3278527 374102264387377662607741 := by
  unfold tailWord_3278527
  simp only [CollatzResearch.WordTrace]
  refine ⟨119577703393464081678577835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79718468928976054452385223 119577703393464081678577835)
  ·
    refine ⟨179366555090196122517866753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119577703393464081678577835 179366555090196122517866753)
    ·
      refine ⟨134524916317647091888400065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179366555090196122517866753 134524916317647091888400065)
      ·
        refine ⟨100893687238235318916300049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134524916317647091888400065 100893687238235318916300049)
        ·
          refine ⟨75670265428676489187225037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100893687238235318916300049 75670265428676489187225037)
          ·
            refine ⟨28376349535753683445209389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75670265428676489187225037 28376349535753683445209389)
            ·
              refine ⟨10641131075907631291953521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28376349535753683445209389 10641131075907631291953521)
              ·
                refine ⟨7980848306930723468965141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10641131075907631291953521 7980848306930723468965141)
                ·
                  refine ⟨374102264387377662607741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7980848306930723468965141 374102264387377662607741)
                  ·
                    rfl

theorem cell22_3278527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_3278527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278527 prefixEnd_3278527 := by exact prefixLift 3278527
  have htrace : WordTrace (prefixWord ++ tailWord_3278527) baseStart_3278527 baseEnd_3278527 := by
    simpa [prefixWord, tailWord_3278527, baseEnd_3278527] using wordTrace_append hprefix tailTrace_3278527
  have hstable : (prefixWord ++ tailWord_3278527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278527).length < 2 ^ (prefixWord ++ tailWord_3278527).sum := by decide
  have hdescent : baseEnd_3278527 < baseStart_3278527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278546 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3278546 : Nat := 118140960795 + 3278546 * 2 ^ 59
def prefixEnd_3278546 : Nat := 4983230072969 + 3 ^ 40 * 3278546 * 2
def baseEnd_3278546 : Nat := 1122313297250423271598165

theorem tailTrace_3278546 : CollatzResearch.WordTrace tailWord_3278546 prefixEnd_3278546 1122313297250423271598165 := by
  unfold tailWord_3278546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894599095098811980879873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79718930920263498615679661 29894599095098811980879873)
  ·
    refine ⟨22420949321324108985659905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29894599095098811980879873 22420949321324108985659905)
    ·
      refine ⟨16815711990993081739244929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22420949321324108985659905 16815711990993081739244929)
      ·
        refine ⟨12611783993244811304433697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16815711990993081739244929 12611783993244811304433697)
        ·
          refine ⟨9458837994933608478325273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611783993244811304433697 9458837994933608478325273)
          ·
            refine ⟨7094128496200206358743955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458837994933608478325273 7094128496200206358743955)
            ·
              refine ⟨10641192744300309538115933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094128496200206358743955 10641192744300309538115933)
              ·
                refine ⟨3990447279112616076793475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10641192744300309538115933 3990447279112616076793475)
                ·
                  refine ⟨5985670918668924115190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990447279112616076793475 5985670918668924115190213)
                  ·
                    refine ⟨1122313297250423271598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985670918668924115190213 1122313297250423271598165)
                    ·
                      rfl

theorem cell22_3278546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3278546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278546 prefixEnd_3278546 := by exact prefixLift 3278546
  have htrace : WordTrace (prefixWord ++ tailWord_3278546) baseStart_3278546 baseEnd_3278546 := by
    simpa [prefixWord, tailWord_3278546, baseEnd_3278546] using wordTrace_append hprefix tailTrace_3278546
  have hstable : (prefixWord ++ tailWord_3278546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278546).length < 2 ^ (prefixWord ++ tailWord_3278546).sum := by decide
  have hdescent : baseEnd_3278546 < baseStart_3278546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278550 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3278550 : Nat := 118140960795 + 3278550 * 2 ^ 59
def prefixEnd_3278550 : Nat := 4983230072969 + 3 ^ 40 * 3278550 * 2
def baseEnd_3278550 : Nat := 374104888844056198166051

theorem tailTrace_3278550 : CollatzResearch.WordTrace tailWord_3278550 prefixEnd_3278550 374104888844056198166051 := by
  unfold tailWord_3278550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473658892023797287916569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79719028181587171071110069 7473658892023797287916569)
  ·
    refine ⟨5605244169017847965937427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7473658892023797287916569 5605244169017847965937427)
    ·
      refine ⟨8407866253526771948906141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605244169017847965937427 8407866253526771948906141)
      ·
        refine ⟨3152949845072539480839803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8407866253526771948906141 3152949845072539480839803)
        ·
          refine ⟨4729424767608809221259705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152949845072539480839803 4729424767608809221259705)
          ·
            refine ⟨3547068575706606915944779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4729424767608809221259705 3547068575706606915944779)
            ·
              refine ⟨5320602863559910373917169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547068575706606915944779 5320602863559910373917169)
              ·
                refine ⟨3990452147669932780437877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320602863559910373917169 3990452147669932780437877)
                ·
                  refine ⟨374104888844056198166051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990452147669932780437877 374104888844056198166051)
                  ·
                    rfl

theorem cell22_3278550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3278550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278550 prefixEnd_3278550 := by exact prefixLift 3278550
  have htrace : WordTrace (prefixWord ++ tailWord_3278550) baseStart_3278550 baseEnd_3278550 := by
    simpa [prefixWord, tailWord_3278550, baseEnd_3278550] using wordTrace_append hprefix tailTrace_3278550
  have hstable : (prefixWord ++ tailWord_3278550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278550).length < 2 ^ (prefixWord ++ tailWord_3278550).sum := by decide
  have hdescent : baseEnd_3278550 < baseStart_3278550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278559 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 4, 3]
def baseStart_3278559 : Nat := 118140960795 + 3278559 * 2 ^ 59
def prefixEnd_3278559 : Nat := 4983230072969 + 3 ^ 40 * 3278559 * 2
def baseEnd_3278559 : Nat := 1122317747416095571023125

theorem tailTrace_3278559 : CollatzResearch.WordTrace tailWord_3278559 prefixEnd_3278559 1122317747416095571023125 := by
  unfold tailWord_3278559
  simp only [CollatzResearch.WordTrace]
  refine ⟨119578870529348151143742731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79719247019565434095828487 119578870529348151143742731)
  ·
    refine ⟨179368305794022226715614097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119578870529348151143742731 179368305794022226715614097)
    ·
      refine ⟨134526229345516670036710573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179368305794022226715614097 134526229345516670036710573)
      ·
        refine ⟨50447336004568751263766465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134526229345516670036710573 50447336004568751263766465)
        ·
          refine ⟨37835502003426563447824849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50447336004568751263766465 37835502003426563447824849)
          ·
            refine ⟨28376626502569922585868637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37835502003426563447824849 28376626502569922585868637)
            ·
              refine ⟨10641234938463720969700739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28376626502569922585868637 10641234938463720969700739)
              ·
                refine ⟨15961852407695581454551109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641234938463720969700739 15961852407695581454551109)
                ·
                  refine ⟨2992847326442921522728333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15961852407695581454551109 2992847326442921522728333)
                  ·
                    refine ⟨1122317747416095571023125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992847326442921522728333 1122317747416095571023125)
                    ·
                      rfl

theorem cell22_3278559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_3278559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278559 prefixEnd_3278559 := by exact prefixLift 3278559
  have htrace : WordTrace (prefixWord ++ tailWord_3278559) baseStart_3278559 baseEnd_3278559 := by
    simpa [prefixWord, tailWord_3278559, baseEnd_3278559] using wordTrace_append hprefix tailTrace_3278559
  have hstable : (prefixWord ++ tailWord_3278559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278559).length < 2 ^ (prefixWord ++ tailWord_3278559).sum := by decide
  have hdescent : baseEnd_3278559 < baseStart_3278559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278580 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3278580 : Nat := 118140960795 + 3278580 * 2 ^ 59
def prefixEnd_3278580 : Nat := 4983230072969 + 3 ^ 40 * 3278580 * 2
def baseEnd_3278580 : Nat := 1122324936145258516248061

theorem tailTrace_3278580 : CollatzResearch.WordTrace tailWord_3278580 prefixEnd_3278580 1122324936145258516248061 := by
  unfold tailWord_3278580
  simp only [CollatzResearch.WordTrace]
  refine ⟨59789818231136035865128597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79719757641514714486838129 59789818231136035865128597)
  ·
    refine ⟨2802647729584501681177903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59789818231136035865128597 2802647729584501681177903)
    ·
      refine ⟨4203971594376752521766855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802647729584501681177903 4203971594376752521766855)
      ·
        refine ⟨6305957391565128782650283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203971594376752521766855 6305957391565128782650283)
        ·
          refine ⟨9458936087347693173975425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305957391565128782650283 9458936087347693173975425)
          ·
            refine ⟨7094202065510769880481569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458936087347693173975425 7094202065510769880481569)
            ·
              refine ⟨5320651549133077410361177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7094202065510769880481569 5320651549133077410361177)
              ·
                refine ⟨3990488661849808057770883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320651549133077410361177 3990488661849808057770883)
                ·
                  refine ⟨5985732992774712086656325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990488661849808057770883 5985732992774712086656325)
                  ·
                    refine ⟨1122324936145258516248061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985732992774712086656325 1122324936145258516248061)
                    ·
                      rfl

theorem cell22_3278580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3278580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278580 prefixEnd_3278580 := by exact prefixLift 3278580
  have htrace : WordTrace (prefixWord ++ tailWord_3278580) baseStart_3278580 baseEnd_3278580 := by
    simpa [prefixWord, tailWord_3278580, baseEnd_3278580] using wordTrace_append hprefix tailTrace_3278580
  have hstable : (prefixWord ++ tailWord_3278580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278580).length < 2 ^ (prefixWord ++ tailWord_3278580).sum := by decide
  have hdescent : baseEnd_3278580 < baseStart_3278580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278604 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_3278604 : Nat := 118140960795 + 3278604 * 2 ^ 59
def prefixEnd_3278604 : Nat := 4983230072969 + 3 ^ 40 * 3278604 * 2
def baseEnd_3278604 : Nat := 1122333151835730453647987

theorem tailTrace_3278604 : CollatzResearch.WordTrace tailWord_3278604 prefixEnd_3278604 1122333151835730453647987 := by
  unfold tailWord_3278604
  simp only [CollatzResearch.WordTrace]
  refine ⟨59790255907092561914565433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79720341209456749219420577 59790255907092561914565433)
  ·
    refine ⟨44842691930319421435924075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59790255907092561914565433 44842691930319421435924075)
    ·
      refine ⟨67264037895479132153886113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44842691930319421435924075 67264037895479132153886113)
      ·
        refine ⟨50448028421609349115414585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67264037895479132153886113 50448028421609349115414585)
        ·
          refine ⟨37836021316207011836560939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50448028421609349115414585 37836021316207011836560939)
          ·
            refine ⟨56754031974310517754841409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37836021316207011836560939 56754031974310517754841409)
            ·
              refine ⟨42565523980732888316131057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56754031974310517754841409 42565523980732888316131057)
              ·
                refine ⟨31924142985549666237098293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42565523980732888316131057 31924142985549666237098293)
                ·
                  refine ⟨2992888404895281209727965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31924142985549666237098293 2992888404895281209727965)
                  ·
                    refine ⟨1122333151835730453647987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2992888404895281209727965 1122333151835730453647987)
                    ·
                      rfl

theorem cell22_3278604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_3278604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278604 prefixEnd_3278604 := by exact prefixLift 3278604
  have htrace : WordTrace (prefixWord ++ tailWord_3278604) baseStart_3278604 baseEnd_3278604 := by
    simpa [prefixWord, tailWord_3278604, baseEnd_3278604] using wordTrace_append hprefix tailTrace_3278604
  have hstable : (prefixWord ++ tailWord_3278604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278604).length < 2 ^ (prefixWord ++ tailWord_3278604).sum := by decide
  have hdescent : baseEnd_3278604 < baseStart_3278604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278612 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3278612 : Nat := 118140960795 + 3278612 * 2 ^ 59
def prefixEnd_3278612 : Nat := 4983230072969 + 3 ^ 40 * 3278612 * 2
def baseEnd_3278612 : Nat := 374111963466407033149321

theorem tailTrace_3278612 : CollatzResearch.WordTrace tailWord_3278612 prefixEnd_3278612 374111963466407033149321 := by
  unfold tailWord_3278612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59790401799078070597711045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79720535732104094130281393 59790401799078070597711045)
  ·
    refine ⟨11210700337327138237070821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59790401799078070597711045 11210700337327138237070821)
    ·
      refine ⟨2102006313248838419450779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11210700337327138237070821 2102006313248838419450779)
      ·
        refine ⟨3153009469873257629176169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102006313248838419450779 3153009469873257629176169)
        ·
          refine ⟨2364757102404943221882127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153009469873257629176169 2364757102404943221882127)
          ·
            refine ⟨3547135653607414832823191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364757102404943221882127 3547135653607414832823191)
            ·
              refine ⟨5320703480411122249234787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547135653607414832823191 5320703480411122249234787)
              ·
                refine ⟨7981055220616683373852181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320703480411122249234787 7981055220616683373852181)
                ·
                  refine ⟨374111963466407033149321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7981055220616683373852181 374111963466407033149321)
                  ·
                    rfl

theorem cell22_3278612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3278612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278612 prefixEnd_3278612 := by exact prefixLift 3278612
  have htrace : WordTrace (prefixWord ++ tailWord_3278612) baseStart_3278612 baseEnd_3278612 := by
    simpa [prefixWord, tailWord_3278612, baseEnd_3278612] using wordTrace_append hprefix tailTrace_3278612
  have hstable : (prefixWord ++ tailWord_3278612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278612).length < 2 ^ (prefixWord ++ tailWord_3278612).sum := by decide
  have hdescent : baseEnd_3278612 < baseStart_3278612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278728 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_3278728 : Nat := 118140960795 + 3278728 * 2 ^ 59
def prefixEnd_3278728 : Nat := 4983230072969 + 3 ^ 40 * 3278728 * 2
def baseEnd_3278728 : Nat := 1122375599569835463547607

theorem tailTrace_3278728 : CollatzResearch.WordTrace tailWord_3278728 prefixEnd_3278728 1122375599569835463547607 := by
  unfold tailWord_3278728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59792517232867946503322419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79723356310490595337763225 59792517232867946503322419)
  ·
    refine ⟨89688775849301919754983629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59792517232867946503322419 89688775849301919754983629)
    ·
      refine ⟨33633290943488219908118861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89688775849301919754983629 33633290943488219908118861)
      ·
        refine ⟨12612484103808082465544573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33633290943488219908118861 12612484103808082465544573)
        ·
          refine ⟨4729681538928030924579215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12612484103808082465544573 4729681538928030924579215)
          ·
            refine ⟨7094522308392046386868823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729681538928030924579215 7094522308392046386868823)
            ·
              refine ⟨10641783462588069580303235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094522308392046386868823 10641783462588069580303235)
              ·
                refine ⟨15962675193882104370454853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641783462588069580303235 15962675193882104370454853)
                ·
                  refine ⟨2993001598852894569460285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15962675193882104370454853 2993001598852894569460285)
                  ·
                    refine ⟨1122375599569835463547607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993001598852894569460285 1122375599569835463547607)
                    ·
                      rfl

theorem cell22_3278728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_3278728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278728 prefixEnd_3278728 := by exact prefixLift 3278728
  have htrace : WordTrace (prefixWord ++ tailWord_3278728) baseStart_3278728 baseEnd_3278728 := by
    simpa [prefixWord, tailWord_3278728, baseEnd_3278728] using wordTrace_append hprefix tailTrace_3278728
  have hstable : (prefixWord ++ tailWord_3278728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278728).length < 2 ^ (prefixWord ++ tailWord_3278728).sum := by decide
  have hdescent : baseEnd_3278728 < baseStart_3278728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278884 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3278884 : Nat := 118140960795 + 3278884 * 2 ^ 59
def prefixEnd_3278884 : Nat := 4983230072969 + 3 ^ 40 * 3278884 * 2
def baseEnd_3278884 : Nat := 1122429001557903056647129

theorem tailTrace_3278884 : CollatzResearch.WordTrace tailWord_3278884 prefixEnd_3278884 1122429001557903056647129 := by
  unfold tailWord_3278884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59795362126585365824661853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79727149502113821099549137 59795362126585365824661853)
  ·
    refine ⟨22423260797469512184248195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59795362126585365824661853 22423260797469512184248195)
    ·
      refine ⟨33634891196204268276372293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22423260797469512184248195 33634891196204268276372293)
      ·
        refine ⟨6306542099288300301819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33634891196204268276372293 6306542099288300301819805)
        ·
          refine ⟨2364953287233112613182427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6306542099288300301819805 2364953287233112613182427)
          ·
            refine ⟨3547429930849668919773641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364953287233112613182427 3547429930849668919773641)
            ·
              refine ⟨2660572448137251689830231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547429930849668919773641 2660572448137251689830231)
              ·
                refine ⟨3990858672205877534745347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660572448137251689830231 3990858672205877534745347)
                ·
                  refine ⟨5986288008308816302118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990858672205877534745347 5986288008308816302118021)
                  ·
                    refine ⟨1122429001557903056647129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986288008308816302118021 1122429001557903056647129)
                    ·
                      rfl

theorem cell22_3278884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3278884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278884 prefixEnd_3278884 := by exact prefixLift 3278884
  have htrace : WordTrace (prefixWord ++ tailWord_3278884) baseStart_3278884 baseEnd_3278884 := by
    simpa [prefixWord, tailWord_3278884, baseEnd_3278884] using wordTrace_append hprefix tailTrace_3278884
  have hstable : (prefixWord ++ tailWord_3278884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278884).length < 2 ^ (prefixWord ++ tailWord_3278884).sum := by decide
  have hdescent : baseEnd_3278884 < baseStart_3278884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278925 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3278925 : Nat := 118140960795 + 3278925 * 2 ^ 59
def prefixEnd_3278925 : Nat := 4983230072969 + 3 ^ 40 * 3278925 * 2
def baseEnd_3278925 : Nat := 1122443036695792616372003

theorem tailTrace_3278925 : CollatzResearch.WordTrace tailWord_3278925 prefixEnd_3278925 1122443036695792616372003 := by
  unfold tailWord_3278925
  simp only [CollatzResearch.WordTrace]
  refine ⟨119592219646022195651566229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79728146430681463767710819 119592219646022195651566229)
  ·
    refine ⟨5605885295907290421167167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119592219646022195651566229 5605885295907290421167167)
    ·
      refine ⟨8408827943860935631750751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605885295907290421167167 8408827943860935631750751)
      ·
        refine ⟨12613241915791403447626127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408827943860935631750751 12613241915791403447626127)
        ·
          refine ⟨18919862873687105171439191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12613241915791403447626127 18919862873687105171439191)
          ·
            refine ⟨28379794310530657757158787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18919862873687105171439191 28379794310530657757158787)
            ·
              refine ⟨42569691465795986635738181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28379794310530657757158787 42569691465795986635738181)
              ·
                refine ⟨7981817149836747494200909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42569691465795986635738181 7981817149836747494200909)
                ·
                  refine ⟨2993181431188780310325341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7981817149836747494200909 2993181431188780310325341)
                  ·
                    refine ⟨1122443036695792616372003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993181431188780310325341 1122443036695792616372003)
                    ·
                      rfl

theorem cell22_3278925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3278925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3278925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3278925 prefixEnd_3278925 := by exact prefixLift 3278925
  have htrace : WordTrace (prefixWord ++ tailWord_3278925) baseStart_3278925 baseEnd_3278925 := by
    simpa [prefixWord, tailWord_3278925, baseEnd_3278925] using wordTrace_append hprefix tailTrace_3278925
  have hstable : (prefixWord ++ tailWord_3278925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278925).length < 2 ^ (prefixWord ++ tailWord_3278925).sum := by decide
  have hdescent : baseEnd_3278925 < baseStart_3278925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279013 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3279013 : Nat := 118140960795 + 3279013 * 2 ^ 59
def prefixEnd_3279013 : Nat := 4983230072969 + 3 ^ 40 * 3279013 * 2
def baseEnd_3279013 : Nat := 1122473160894189720171733

theorem tailTrace_3279013 : CollatzResearch.WordTrace tailWord_3279013 prefixEnd_3279013 1122473160894189720171733 := by
  unfold tailWord_3279013
  simp only [CollatzResearch.WordTrace]
  refine ⟨119595429269703386680769693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79730286179802257787179795 119595429269703386680769693)
  ·
    refine ⟨44848285976138770005288635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119595429269703386680769693 44848285976138770005288635)
    ·
      refine ⟨67272428964208155007932953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44848285976138770005288635 67272428964208155007932953)
      ·
        refine ⟨50454321723156116255949715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67272428964208155007932953 50454321723156116255949715)
        ·
          refine ⟨75681482584734174383924573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50454321723156116255949715 75681482584734174383924573)
          ·
            refine ⟨28380555969275315393971715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75681482584734174383924573 28380555969275315393971715)
            ·
              refine ⟨42570833953912973090957573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28380555969275315393971715 42570833953912973090957573)
              ·
                refine ⟨7982031366358682454554545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42570833953912973090957573 7982031366358682454554545)
                ·
                  refine ⟨5986523524769011840915909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982031366358682454554545 5986523524769011840915909)
                  ·
                    refine ⟨1122473160894189720171733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986523524769011840915909 1122473160894189720171733)
                    ·
                      rfl

theorem cell22_3279013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3279013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279013 prefixEnd_3279013 := by exact prefixLift 3279013
  have htrace : WordTrace (prefixWord ++ tailWord_3279013) baseStart_3279013 baseEnd_3279013 := by
    simpa [prefixWord, tailWord_3279013, baseEnd_3279013] using wordTrace_append hprefix tailTrace_3279013
  have hstable : (prefixWord ++ tailWord_3279013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279013).length < 2 ^ (prefixWord ++ tailWord_3279013).sum := by decide
  have hdescent : baseEnd_3279013 < baseStart_3279013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279073 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 7]
def baseStart_3279073 : Nat := 118140960795 + 3279073 * 2 ^ 59
def prefixEnd_3279073 : Nat := 4983230072969 + 3 ^ 40 * 3279073 * 2
def baseEnd_3279073 : Nat := 374164566706789854557183

theorem tailTrace_3279073 : CollatzResearch.WordTrace tailWord_3279073 prefixEnd_3279073 374164566706789854557183 := by
  unfold tailWord_3279073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119597617649486016927953873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79731745099657344618635915 119597617649486016927953873)
  ·
    refine ⟨89698213237114512695965405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119597617649486016927953873 89698213237114512695965405)
    ·
      refine ⟨33636829963917942260987027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89698213237114512695965405 33636829963917942260987027)
      ·
        refine ⟨50455244945876913391480541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33636829963917942260987027 50455244945876913391480541)
        ·
          refine ⟨18920716854703842521805203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50455244945876913391480541 18920716854703842521805203)
          ·
            refine ⟨28381075282055763782707805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18920716854703842521805203 28381075282055763782707805)
            ·
              refine ⟨10642903230770911418515427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28381075282055763782707805 10642903230770911418515427)
              ·
                refine ⟨15964354846156367127773141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10642903230770911418515427 15964354846156367127773141)
                ·
                  refine ⟨374164566706789854557183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15964354846156367127773141 374164566706789854557183)
                  ·
                    rfl

theorem cell22_3279073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_3279073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279073 prefixEnd_3279073 := by exact prefixLift 3279073
  have htrace : WordTrace (prefixWord ++ tailWord_3279073) baseStart_3279073 baseEnd_3279073 := by
    simpa [prefixWord, tailWord_3279073, baseEnd_3279073] using wordTrace_append hprefix tailTrace_3279073
  have hstable : (prefixWord ++ tailWord_3279073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279073).length < 2 ^ (prefixWord ++ tailWord_3279073).sum := by decide
  have hdescent : baseEnd_3279073 < baseStart_3279073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279077 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_3279077 : Nat := 118140960795 + 3279077 * 2 ^ 59
def prefixEnd_3279077 : Nat := 4983230072969 + 3 ^ 40 * 3279077 * 2
def baseEnd_3279077 : Nat := 1122495069402114886571537

theorem tailTrace_3279077 : CollatzResearch.WordTrace tailWord_3279077 prefixEnd_3279077 1122495069402114886571537 := by
  unfold tailWord_3279077
  simp only [CollatzResearch.WordTrace]
  refine ⟨119597763541471525611099485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79731842360981017074066323 119597763541471525611099485)
  ·
    refine ⟨44849161328051822104162307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119597763541471525611099485 44849161328051822104162307)
    ·
      refine ⟨67273741992077733156243461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44849161328051822104162307 67273741992077733156243461)
      ·
        refine ⟨12613826623514574966795649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67273741992077733156243461 12613826623514574966795649)
        ·
          refine ⟨9460369967635931225096737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12613826623514574966795649 9460369967635931225096737)
          ·
            refine ⟨7095277475726948418822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9460369967635931225096737 7095277475726948418822553)
            ·
              refine ⟨5321458106795211314116915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095277475726948418822553 5321458106795211314116915)
              ·
                refine ⟨7982187160192816971175373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321458106795211314116915 7982187160192816971175373)
                ·
                  refine ⟨2993320185072306364190765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7982187160192816971175373 2993320185072306364190765)
                  ·
                    refine ⟨1122495069402114886571537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993320185072306364190765 1122495069402114886571537)
                    ·
                      rfl

theorem cell22_3279077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_3279077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279077 prefixEnd_3279077 := by exact prefixLift 3279077
  have htrace : WordTrace (prefixWord ++ tailWord_3279077) baseStart_3279077 baseEnd_3279077 := by
    simpa [prefixWord, tailWord_3279077, baseEnd_3279077] using wordTrace_append hprefix tailTrace_3279077
  have hstable : (prefixWord ++ tailWord_3279077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279077).length < 2 ^ (prefixWord ++ tailWord_3279077).sum := by decide
  have hdescent : baseEnd_3279077 < baseStart_3279077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279135 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 6]
def baseStart_3279135 : Nat := 118140960795 + 3279135 * 2 ^ 59
def prefixEnd_3279135 : Nat := 4983230072969 + 3 ^ 40 * 3279135 * 2
def baseEnd_3279135 : Nat := 374171641329140689540453

theorem tailTrace_3279135 : CollatzResearch.WordTrace tailWord_3279135 prefixEnd_3279135 374171641329140689540453 := by
  unfold tailWord_3279135
  simp only [CollatzResearch.WordTrace]
  refine ⟨119599878975261401516710859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79733252650174267677807239 119599878975261401516710859)
  ·
    refine ⟨179399818462892102275066289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119599878975261401516710859 179399818462892102275066289)
    ·
      refine ⟨134549863847169076706299717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179399818462892102275066289 134549863847169076706299717)
      ·
        refine ⟨25228099471344201882431197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134549863847169076706299717 25228099471344201882431197)
        ·
          refine ⟨9460537301754075705911699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25228099471344201882431197 9460537301754075705911699)
          ·
            refine ⟨14190805952631113558867549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9460537301754075705911699 14190805952631113558867549)
            ·
              refine ⟨5321552232236667584575331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14190805952631113558867549 5321552232236667584575331)
              ·
                refine ⟨7982328348355001376862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321552232236667584575331 7982328348355001376862997)
                ·
                  refine ⟨374171641329140689540453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7982328348355001376862997 374171641329140689540453)
                  ·
                    rfl

theorem cell22_3279135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_3279135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279135 prefixEnd_3279135 := by exact prefixLift 3279135
  have htrace : WordTrace (prefixWord ++ tailWord_3279135) baseStart_3279135 baseEnd_3279135 := by
    simpa [prefixWord, tailWord_3279135, baseEnd_3279135] using wordTrace_append hprefix tailTrace_3279135
  have hstable : (prefixWord ++ tailWord_3279135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279135).length < 2 ^ (prefixWord ++ tailWord_3279135).sum := by decide
  have hdescent : baseEnd_3279135 < baseStart_3279135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279148 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3279148 : Nat := 118140960795 + 3279148 * 2 ^ 59
def prefixEnd_3279148 : Nat := 4983230072969 + 3 ^ 40 * 3279148 * 2
def baseEnd_3279148 : Nat := 1122519374153094368046319

theorem tailTrace_3279148 : CollatzResearch.WordTrace tailWord_3279148 prefixEnd_3279148 1122519374153094368046319 := by
  unfold tailWord_3279148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59800176562107152368467049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79733568749476203157956065 59800176562107152368467049)
  ·
    refine ⟨44850132421580364276350287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59800176562107152368467049 44850132421580364276350287)
    ·
      refine ⟨67275198632370546414525431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44850132421580364276350287 67275198632370546414525431)
      ·
        refine ⟨100912797948555819621788147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67275198632370546414525431 100912797948555819621788147)
        ·
          refine ⟨151369196922833729432682221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100912797948555819621788147 151369196922833729432682221)
          ·
            refine ⟨56763448846062648537255833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151369196922833729432682221 56763448846062648537255833)
            ·
              refine ⟨42572586634546986402941875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56763448846062648537255833 42572586634546986402941875)
              ·
                refine ⟨63858879951820479604412813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42572586634546986402941875 63858879951820479604412813)
                ·
                  refine ⟨23947079981932679851654805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63858879951820479604412813 23947079981932679851654805)
                  ·
                    refine ⟨1122519374153094368046319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23947079981932679851654805 1122519374153094368046319)
                    ·
                      rfl

theorem cell22_3279148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3279148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279148 prefixEnd_3279148 := by exact prefixLift 3279148
  have htrace : WordTrace (prefixWord ++ tailWord_3279148) baseStart_3279148 baseEnd_3279148 := by
    simpa [prefixWord, tailWord_3279148, baseEnd_3279148] using wordTrace_append hprefix tailTrace_3279148
  have hstable : (prefixWord ++ tailWord_3279148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279148).length < 2 ^ (prefixWord ++ tailWord_3279148).sum := by decide
  have hdescent : baseEnd_3279148 < baseStart_3279148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279154 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3279154 : Nat := 118140960795 + 3279154 * 2 ^ 59
def prefixEnd_3279154 : Nat := 4983230072969 + 3 ^ 40 * 3279154 * 2
def baseEnd_3279154 : Nat := 1122521428075712352396301

theorem tailTrace_3279154 : CollatzResearch.WordTrace tailWord_3279154 prefixEnd_3279154 1122521428075712352396301 := by
  unfold tailWord_3279154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900142990548141940413129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79733714641461711841101677 29900142990548141940413129)
  ·
    refine ⟨22425107242911106455309847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29900142990548141940413129 22425107242911106455309847)
    ·
      refine ⟨33637660864366659682964771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22425107242911106455309847 33637660864366659682964771)
      ·
        refine ⟨50456491296549989524447157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33637660864366659682964771 50456491296549989524447157)
        ·
          refine ⟨4730296059051561517916921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50456491296549989524447157 4730296059051561517916921)
          ·
            refine ⟨3547722044288671138437691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730296059051561517916921 3547722044288671138437691)
            ·
              refine ⟨5321583066433006707656537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547722044288671138437691 5321583066433006707656537)
              ·
                refine ⟨3991187299824755030742403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5321583066433006707656537 3991187299824755030742403)
                ·
                  refine ⟨5986780949737132546113605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991187299824755030742403 5986780949737132546113605)
                  ·
                    refine ⟨1122521428075712352396301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986780949737132546113605 1122521428075712352396301)
                    ·
                      rfl

theorem cell22_3279154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3279154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279154 prefixEnd_3279154 := by exact prefixLift 3279154
  have htrace : WordTrace (prefixWord ++ tailWord_3279154) baseStart_3279154 baseEnd_3279154 := by
    simpa [prefixWord, tailWord_3279154, baseEnd_3279154] using wordTrace_append hprefix tailTrace_3279154
  have hstable : (prefixWord ++ tailWord_3279154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279154).length < 2 ^ (prefixWord ++ tailWord_3279154).sum := by decide
  have hdescent : baseEnd_3279154 < baseStart_3279154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279229 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_3279229 : Nat := 118140960795 + 3279229 * 2 ^ 59
def prefixEnd_3279229 : Nat := 4983230072969 + 3 ^ 40 * 3279229 * 2
def baseEnd_3279229 : Nat := 1122547102108437156771071

theorem tailTrace_3279229 : CollatzResearch.WordTrace tailWord_3279229 prefixEnd_3279229 1122547102108437156771071 := by
  unfold tailWord_3279229
  simp only [CollatzResearch.WordTrace]
  refine ⟨119603307436920855570632741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79735538291280570380421827 119603307436920855570632741)
  ·
    refine ⟨22425620144422660419493639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119603307436920855570632741 22425620144422660419493639)
    ·
      refine ⟨33638430216633990629240459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22425620144422660419493639 33638430216633990629240459)
      ·
        refine ⟨50457645324950985943860689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33638430216633990629240459 50457645324950985943860689)
        ·
          refine ⟨37843233993713239457895517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50457645324950985943860689 37843233993713239457895517)
          ·
            refine ⟨14191212747642464796710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37843233993713239457895517 14191212747642464796710819)
            ·
              refine ⟨21286819121463697195066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14191212747642464796710819 21286819121463697195066229)
              ·
                refine ⟨1995639292637221612037459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21286819121463697195066229 1995639292637221612037459)
                ·
                  refine ⟨2993458938955832418056189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995639292637221612037459 2993458938955832418056189)
                  ·
                    refine ⟨1122547102108437156771071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993458938955832418056189 1122547102108437156771071)
                    ·
                      rfl

theorem cell22_3279229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_3279229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279229 prefixEnd_3279229 := by exact prefixLift 3279229
  have htrace : WordTrace (prefixWord ++ tailWord_3279229) baseStart_3279229 baseEnd_3279229 := by
    simpa [prefixWord, tailWord_3279229, baseEnd_3279229] using wordTrace_append hprefix tailTrace_3279229
  have hstable : (prefixWord ++ tailWord_3279229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279229).length < 2 ^ (prefixWord ++ tailWord_3279229).sum := by decide
  have hdescent : baseEnd_3279229 < baseStart_3279229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279240 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3279240 : Nat := 118140960795 + 3279240 * 2 ^ 59
def prefixEnd_3279240 : Nat := 4983230072969 + 3 ^ 40 * 3279240 * 2
def baseEnd_3279240 : Nat := 1122550867633236794746037

theorem tailTrace_3279240 : CollatzResearch.WordTrace tailWord_3279240 prefixEnd_3279240 1122550867633236794746037 := by
  unfold tailWord_3279240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59801854319940502224641587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79735805759920669632855449 59801854319940502224641587)
  ·
    refine ⟨89702781479910753336962381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59801854319940502224641587 89702781479910753336962381)
    ·
      refine ⟨33638543054966532501360893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89702781479910753336962381 33638543054966532501360893)
      ·
        refine ⟨12614453645612449688010335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33638543054966532501360893 12614453645612449688010335)
        ·
          refine ⟨18921680468418674532015503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12614453645612449688010335 18921680468418674532015503)
          ·
            refine ⟨28382520702628011798023255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18921680468418674532015503 28382520702628011798023255)
            ·
              refine ⟨42573781053942017697034883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28382520702628011798023255 42573781053942017697034883)
              ·
                refine ⟨63860671580913026545552325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42573781053942017697034883 63860671580913026545552325)
                ·
                  refine ⟨11973875921421192477291061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63860671580913026545552325 11973875921421192477291061)
                  ·
                    refine ⟨1122550867633236794746037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11973875921421192477291061 1122550867633236794746037)
                    ·
                      rfl

theorem cell22_3279240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3279240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279240 prefixEnd_3279240 := by exact prefixLift 3279240
  have htrace : WordTrace (prefixWord ++ tailWord_3279240) baseStart_3279240 baseEnd_3279240 := by
    simpa [prefixWord, tailWord_3279240, baseEnd_3279240] using wordTrace_append hprefix tailTrace_3279240
  have hstable : (prefixWord ++ tailWord_3279240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279240).length < 2 ^ (prefixWord ++ tailWord_3279240).sum := by decide
  have hdescent : baseEnd_3279240 < baseStart_3279240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279246 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3279246 : Nat := 118140960795 + 3279246 * 2 ^ 59
def prefixEnd_3279246 : Nat := 4983230072969 + 3 ^ 40 * 3279246 * 2
def baseEnd_3279246 : Nat := 1122552921555854779096019

theorem tailTrace_3279246 : CollatzResearch.WordTrace tailWord_3279246 prefixEnd_3279246 1122552921555854779096019 := by
  unfold tailWord_3279246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14950490934732408434250199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79735951651906178316001061 14950490934732408434250199)
  ·
    refine ⟨22425736402098612651375299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14950490934732408434250199 22425736402098612651375299)
    ·
      refine ⟨33638604603147918977062949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22425736402098612651375299 33638604603147918977062949)
      ·
        refine ⟨6307238363090234808199303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33638604603147918977062949 6307238363090234808199303)
        ·
          refine ⟨9460857544635352212298955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6307238363090234808199303 9460857544635352212298955)
          ·
            refine ⟨14191286316953028318448433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9460857544635352212298955 14191286316953028318448433)
            ·
              refine ⟨10643464737714771238836325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14191286316953028318448433 10643464737714771238836325)
              ·
                refine ⟨1995649638321519607281811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10643464737714771238836325 1995649638321519607281811)
                ·
                  refine ⟨2993474457482279410922717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995649638321519607281811 2993474457482279410922717)
                  ·
                    refine ⟨1122552921555854779096019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993474457482279410922717 1122552921555854779096019)
                    ·
                      rfl

theorem cell22_3279246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3279246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279246 prefixEnd_3279246 := by exact prefixLift 3279246
  have htrace : WordTrace (prefixWord ++ tailWord_3279246) baseStart_3279246 baseEnd_3279246 := by
    simpa [prefixWord, tailWord_3279246, baseEnd_3279246] using wordTrace_append hprefix tailTrace_3279246
  have hstable : (prefixWord ++ tailWord_3279246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279246).length < 2 ^ (prefixWord ++ tailWord_3279246).sum := by decide
  have hdescent : baseEnd_3279246 < baseStart_3279246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279255 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3279255 : Nat := 118140960795 + 3279255 * 2 ^ 59
def prefixEnd_3279255 : Nat := 4983230072969 + 3 ^ 40 * 3279255 * 2
def baseEnd_3279255 : Nat := 1122556002439781755620991

theorem tailTrace_3279255 : CollatzResearch.WordTrace tailWord_3279255 prefixEnd_3279255 1122556002439781755620991 := by
  unfold tailWord_3279255
  simp only [CollatzResearch.WordTrace]
  refine ⟨119604255734826662011079219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79736170489884441340719479 119604255734826662011079219)
  ·
    refine ⟨179406383602239993016618829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119604255734826662011079219 179406383602239993016618829)
    ·
      refine ⟨67277393850839997381232061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179406383602239993016618829 67277393850839997381232061)
      ·
        refine ⟨25229022694064999017962023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67277393850839997381232061 25229022694064999017962023)
        ·
          refine ⟨37843534041097498526943035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25229022694064999017962023 37843534041097498526943035)
          ·
            refine ⟨56765301061646247790414553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37843534041097498526943035 56765301061646247790414553)
            ·
              refine ⟨42573975796234685842810915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56765301061646247790414553 42573975796234685842810915)
              ·
                refine ⟨63860963694352028764216373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42573975796234685842810915 63860963694352028764216373)
                ·
                  refine ⟨5986965346345502696645285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63860963694352028764216373 5986965346345502696645285)
                  ·
                    refine ⟨1122556002439781755620991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986965346345502696645285 1122556002439781755620991)
                    ·
                      rfl

theorem cell22_3279255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3279255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279255 prefixEnd_3279255 := by exact prefixLift 3279255
  have htrace : WordTrace (prefixWord ++ tailWord_3279255) baseStart_3279255 baseEnd_3279255 := by
    simpa [prefixWord, tailWord_3279255, baseEnd_3279255] using wordTrace_append hprefix tailTrace_3279255
  have hstable : (prefixWord ++ tailWord_3279255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279255).length < 2 ^ (prefixWord ++ tailWord_3279255).sum := by decide
  have hdescent : baseEnd_3279255 < baseStart_3279255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279297 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3279297 : Nat := 118140960795 + 3279297 * 2 ^ 59
def prefixEnd_3279297 : Nat := 4983230072969 + 3 ^ 40 * 3279297 * 2
def baseEnd_3279297 : Nat := 1122570379898107646070863

theorem tailTrace_3279297 : CollatzResearch.WordTrace tailWord_3279297 prefixEnd_3279297 1122570379898107646070863 := by
  unfold tailWord_3279297
  simp only [CollatzResearch.WordTrace]
  refine ⟨119605787600674503184108145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79737191733783002122738763 119605787600674503184108145)
  ·
    refine ⟨89704340700505877388081109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119605787600674503184108145 89704340700505877388081109)
    ·
      refine ⟨2102445485168106501283151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 89704340700505877388081109 2102445485168106501283151)
      ·
        refine ⟨3153668227752159751924727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102445485168106501283151 3153668227752159751924727)
        ·
          refine ⟨4730502341628239627887091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153668227752159751924727 4730502341628239627887091)
          ·
            refine ⟨7095753512442359441830637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730502341628239627887091 7095753512442359441830637)
            ·
              refine ⟨2660907567165884790686489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7095753512442359441830637 2660907567165884790686489)
              ·
                refine ⟨1995680675374413593014867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660907567165884790686489 1995680675374413593014867)
                ·
                  refine ⟨2993521013061620389522301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995680675374413593014867 2993521013061620389522301)
                  ·
                    refine ⟨1122570379898107646070863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993521013061620389522301 1122570379898107646070863)
                    ·
                      rfl

theorem cell22_3279297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3279297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279297 prefixEnd_3279297 := by exact prefixLift 3279297
  have htrace : WordTrace (prefixWord ++ tailWord_3279297) baseStart_3279297 baseEnd_3279297 := by
    simpa [prefixWord, tailWord_3279297, baseEnd_3279297] using wordTrace_append hprefix tailTrace_3279297
  have hstable : (prefixWord ++ tailWord_3279297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279297).length < 2 ^ (prefixWord ++ tailWord_3279297).sum := by decide
  have hdescent : baseEnd_3279297 < baseStart_3279297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279349 : List Nat := [1, 3, 5, 1, 3, 9]
def baseStart_3279349 : Nat := 118140960795 + 3279349 * 2 ^ 59
def prefixEnd_3279349 : Nat := 4983230072969 + 3 ^ 40 * 3279349 * 2
def baseEnd_3279349 : Nat := 13859113340256751157663

theorem tailTrace_3279349 : CollatzResearch.WordTrace tailWord_3279349 prefixEnd_3279349 13859113340256751157663 := by
  unfold tailWord_3279349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119607684196486116065001101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79738456130990744043334067 119607684196486116065001101)
  ·
    refine ⟨44852881573682293524375413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119607684196486116065001101 44852881573682293524375413)
    ·
      refine ⟨4204957647532715017910195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44852881573682293524375413 4204957647532715017910195)
      ·
        refine ⟨6307436471299072526865293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204957647532715017910195 6307436471299072526865293)
        ·
          refine ⟨2365288676737152197574485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6307436471299072526865293 2365288676737152197574485)
          ·
            refine ⟨13859113340256751157663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2365288676737152197574485 13859113340256751157663)
            ·
              rfl

theorem cell22_3279349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 9].length) (baseStart_3279349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279349 prefixEnd_3279349 := by exact prefixLift 3279349
  have htrace : WordTrace (prefixWord ++ tailWord_3279349) baseStart_3279349 baseEnd_3279349 := by
    simpa [prefixWord, tailWord_3279349, baseEnd_3279349] using wordTrace_append hprefix tailTrace_3279349
  have hstable : (prefixWord ++ tailWord_3279349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279349).length < 2 ^ (prefixWord ++ tailWord_3279349).sum := by decide
  have hdescent : baseEnd_3279349 < baseStart_3279349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279375 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_3279375 : Nat := 118140960795 + 3279375 * 2 ^ 59
def prefixEnd_3279375 : Nat := 4983230072969 + 3 ^ 40 * 3279375 * 2
def baseEnd_3279375 : Nat := 1122597080892141442620623

theorem tailTrace_3279375 : CollatzResearch.WordTrace tailWord_3279375 prefixEnd_3279375 1122597080892141442620623 := by
  unfold tailWord_3279375
  simp only [CollatzResearch.WordTrace]
  refine ⟨119608632494391922505447579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79739088329594615003631719 119608632494391922505447579)
  ·
    refine ⟨179412948741587883758171369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119608632494391922505447579 179412948741587883758171369)
    ·
      refine ⟨134559711556190912818628527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179412948741587883758171369 134559711556190912818628527)
      ·
        refine ⟨201839567334286369227942791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134559711556190912818628527 201839567334286369227942791)
        ·
          refine ⟨302759351001429553841914187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201839567334286369227942791 302759351001429553841914187)
          ·
            refine ⟨454139026502144330762871281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302759351001429553841914187 454139026502144330762871281)
            ·
              refine ⟨340604269876608248072153461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454139026502144330762871281 340604269876608248072153461)
              ·
                refine ⟨31931650300932023256764387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340604269876608248072153461 31931650300932023256764387)
                ·
                  refine ⟨47897475451398034885146581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31931650300932023256764387 47897475451398034885146581)
                  ·
                    refine ⟨1122597080892141442620623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47897475451398034885146581 1122597080892141442620623)
                    ·
                      rfl

theorem cell22_3279375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_3279375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279375 prefixEnd_3279375 := by exact prefixLift 3279375
  have htrace : WordTrace (prefixWord ++ tailWord_3279375) baseStart_3279375 baseEnd_3279375 := by
    simpa [prefixWord, tailWord_3279375, baseEnd_3279375] using wordTrace_append hprefix tailTrace_3279375
  have hstable : (prefixWord ++ tailWord_3279375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279375).length < 2 ^ (prefixWord ++ tailWord_3279375).sum := by decide
  have hdescent : baseEnd_3279375 < baseStart_3279375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279469 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3279469 : Nat := 118140960795 + 3279469 * 2 ^ 59
def prefixEnd_3279469 : Nat := 4983230072969 + 3 ^ 40 * 3279469 * 2
def baseEnd_3279469 : Nat := 1122629259013156530770335

theorem tailTrace_3279469 : CollatzResearch.WordTrace tailWord_3279469 prefixEnd_3279469 1122629259013156530770335 := by
  unfold tailWord_3279469
  simp only [CollatzResearch.WordTrace]
  refine ⟨119612060956051376559369461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79741373970700917706246307 119612060956051376559369461)
  ·
    refine ⟨11213630714629816552440887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119612060956051376559369461 11213630714629816552440887)
    ·
      refine ⟨16820446071944724828661331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11213630714629816552440887 16820446071944724828661331)
      ·
        refine ⟨25230669107917087242991997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16820446071944724828661331 25230669107917087242991997)
        ·
          refine ⟨9461500915468907716121999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25230669107917087242991997 9461500915468907716121999)
          ·
            refine ⟨14192251373203361574182999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461500915468907716121999 14192251373203361574182999)
            ·
              refine ⟨21288377059805042361274499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14192251373203361574182999 21288377059805042361274499)
              ·
                refine ⟨31932565589707563541911749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21288377059805042361274499 31932565589707563541911749)
                ·
                  refine ⟨5987356048070168164108453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31932565589707563541911749 5987356048070168164108453)
                  ·
                    refine ⟨1122629259013156530770335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5987356048070168164108453 1122629259013156530770335)
                    ·
                      rfl

theorem cell22_3279469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3279469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279469 prefixEnd_3279469 := by exact prefixLift 3279469
  have htrace : WordTrace (prefixWord ++ tailWord_3279469) baseStart_3279469 baseEnd_3279469 := by
    simpa [prefixWord, tailWord_3279469, baseEnd_3279469] using wordTrace_append hprefix tailTrace_3279469
  have hstable : (prefixWord ++ tailWord_3279469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279469).length < 2 ^ (prefixWord ++ tailWord_3279469).sum := by decide
  have hdescent : baseEnd_3279469 < baseStart_3279469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279488 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_3279488 : Nat := 118140960795 + 3279488 * 2 ^ 59
def prefixEnd_3279488 : Nat := 4983230072969 + 3 ^ 40 * 3279488 * 2
def baseEnd_3279488 : Nat := 1122635763101446814545277

theorem tailTrace_3279488 : CollatzResearch.WordTrace tailWord_3279488 prefixEnd_3279488 1122635763101446814545277 := by
  unfold tailWord_3279488
  simp only [CollatzResearch.WordTrace]
  refine ⟨59806376971491271402155559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79741835961988361869540745 59806376971491271402155559)
  ·
    refine ⟨89709565457236907103233339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59806376971491271402155559 89709565457236907103233339)
    ·
      refine ⟨134564348185855360654850009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89709565457236907103233339 134564348185855360654850009)
      ·
        refine ⟨100923261139391520491137507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134564348185855360654850009 100923261139391520491137507)
        ·
          refine ⟨151384891709087280736706261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100923261139391520491137507 151384891709087280736706261)
          ·
            refine ⟨3548083399431733142266553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 151384891709087280736706261 3548083399431733142266553)
            ·
              refine ⟨2661062549573799856699915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548083399431733142266553 2661062549573799856699915)
              ·
                refine ⟨3991593824360699785049873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661062549573799856699915 3991593824360699785049873)
                ·
                  refine ⟨2993695368270524838787405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991593824360699785049873 2993695368270524838787405)
                  ·
                    refine ⟨1122635763101446814545277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2993695368270524838787405 1122635763101446814545277)
                    ·
                      rfl

theorem cell22_3279488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_3279488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279488 prefixEnd_3279488 := by exact prefixLift 3279488
  have htrace : WordTrace (prefixWord ++ tailWord_3279488) baseStart_3279488 baseEnd_3279488 := by
    simpa [prefixWord, tailWord_3279488, baseEnd_3279488] using wordTrace_append hprefix tailTrace_3279488
  have hstable : (prefixWord ++ tailWord_3279488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279488).length < 2 ^ (prefixWord ++ tailWord_3279488).sum := by decide
  have hdescent : baseEnd_3279488 < baseStart_3279488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279576 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3279576 : Nat := 118140960795 + 3279576 * 2 ^ 59
def prefixEnd_3279576 : Nat := 4983230072969 + 3 ^ 40 * 3279576 * 2
def baseEnd_3279576 : Nat := 1122665887299843918345007

theorem tailTrace_3279576 : CollatzResearch.WordTrace tailWord_3279576 prefixEnd_3279576 1122665887299843918345007 := by
  unfold tailWord_3279576
  simp only [CollatzResearch.WordTrace]
  refine ⟨59807981783331866916757291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79743975711109155889009721 59807981783331866916757291)
  ·
    refine ⟨89711972674997800375135937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59807981783331866916757291 89711972674997800375135937)
    ·
      refine ⟨67283979506248350281351953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89711972674997800375135937 67283979506248350281351953)
      ·
        refine ⟨50462984629686262711013965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67283979506248350281351953 50462984629686262711013965)
        ·
          refine ⟨18923619236132348516630237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50462984629686262711013965 18923619236132348516630237)
          ·
            refine ⟨7096357213549630693736339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18923619236132348516630237 7096357213549630693736339)
            ·
              refine ⟨10644535820324446040604509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096357213549630693736339 10644535820324446040604509)
              ·
                refine ⟨3991700932621667265226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10644535820324446040604509 3991700932621667265226691)
                ·
                  refine ⟨5987551398932500897840037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991700932621667265226691 5987551398932500897840037)
                  ·
                    refine ⟨1122665887299843918345007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5987551398932500897840037 1122665887299843918345007)
                    ·
                      rfl

theorem cell22_3279576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3279576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279576 prefixEnd_3279576 := by exact prefixLift 3279576
  have htrace : WordTrace (prefixWord ++ tailWord_3279576) baseStart_3279576 baseEnd_3279576 := by
    simpa [prefixWord, tailWord_3279576, baseEnd_3279576] using wordTrace_append hprefix tailTrace_3279576
  have hstable : (prefixWord ++ tailWord_3279576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279576).length < 2 ^ (prefixWord ++ tailWord_3279576).sum := by decide
  have hdescent : baseEnd_3279576 < baseStart_3279576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279649 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3279649 : Nat := 118140960795 + 3279649 * 2 ^ 59
def prefixEnd_3279649 : Nat := 4983230072969 + 3 ^ 40 * 3279649 * 2
def baseEnd_3279649 : Nat := 1122690876691696061269783

theorem tailTrace_3279649 : CollatzResearch.WordTrace tailWord_3279649 prefixEnd_3279649 1122690876691696061269783 := by
  unfold tailWord_3279649
  simp only [CollatzResearch.WordTrace]
  refine ⟨119618626095399267300922001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79745750730266178200614667 119618626095399267300922001)
  ·
    refine ⟨89713969571549450475691501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119618626095399267300922001 89713969571549450475691501)
    ·
      refine ⟨33642738589331043928384313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89713969571549450475691501 33642738589331043928384313)
      ·
        refine ⟨25232053941998282946288235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33642738589331043928384313 25232053941998282946288235)
        ·
          refine ⟨37848080912997424419432353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232053941998282946288235 37848080912997424419432353)
          ·
            refine ⟨28386060684748068314574265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37848080912997424419432353 28386060684748068314574265)
            ·
              refine ⟨21289545513561051235930699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28386060684748068314574265 21289545513561051235930699)
              ·
                refine ⟨31934318270341576853896049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21289545513561051235930699 31934318270341576853896049)
                ·
                  refine ⟨23950738702756182640422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31934318270341576853896049 23950738702756182640422037)
                  ·
                    refine ⟨1122690876691696061269783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23950738702756182640422037 1122690876691696061269783)
                    ·
                      rfl

theorem cell22_3279649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3279649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279649 prefixEnd_3279649 := by exact prefixLift 3279649
  have htrace : WordTrace (prefixWord ++ tailWord_3279649) baseStart_3279649 baseEnd_3279649 := by
    simpa [prefixWord, tailWord_3279649, baseEnd_3279649] using wordTrace_append hprefix tailTrace_3279649
  have hstable : (prefixWord ++ tailWord_3279649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279649).length < 2 ^ (prefixWord ++ tailWord_3279649).sum := by decide
  have hdescent : baseEnd_3279649 < baseStart_3279649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279741 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3279741 : Nat := 118140960795 + 3279741 * 2 ^ 59
def prefixEnd_3279741 : Nat := 4983230072969 + 3 ^ 40 * 3279741 * 2
def baseEnd_3279741 : Nat := 1122722370171838487969501

theorem tailTrace_3279741 : CollatzResearch.WordTrace tailWord_3279741 prefixEnd_3279741 1122722370171838487969501 := by
  unfold tailWord_3279741
  simp only [CollatzResearch.WordTrace]
  refine ⟨119621981611065967013271077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79747987740710644675514051 119621981611065967013271077)
  ·
    refine ⟨22429121552074868814988327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119621981611065967013271077 22429121552074868814988327)
    ·
      refine ⟨33643682328112303222482491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22429121552074868814988327 33643682328112303222482491)
      ·
        refine ⟨50465523492168454833723737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33643682328112303222482491 50465523492168454833723737)
        ·
          refine ⟨37849142619126341125292803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50465523492168454833723737 37849142619126341125292803)
          ·
            refine ⟨56773713928689511687939205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37849142619126341125292803 56773713928689511687939205)
            ·
              refine ⟨10645071361629283441488601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56773713928689511687939205 10645071361629283441488601)
              ·
                refine ⟨7983803521221962581116451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10645071361629283441488601 7983803521221962581116451)
                ·
                  refine ⟨11975705281832943871674677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983803521221962581116451 11975705281832943871674677)
                  ·
                    refine ⟨1122722370171838487969501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11975705281832943871674677 1122722370171838487969501)
                    ·
                      rfl

theorem cell22_3279741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3279741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279741 prefixEnd_3279741 := by exact prefixLift 3279741
  have htrace : WordTrace (prefixWord ++ tailWord_3279741) baseStart_3279741 baseEnd_3279741 := by
    simpa [prefixWord, tailWord_3279741, baseEnd_3279741] using wordTrace_append hprefix tailTrace_3279741
  have hstable : (prefixWord ++ tailWord_3279741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279741).length < 2 ^ (prefixWord ++ tailWord_3279741).sum := by decide
  have hdescent : baseEnd_3279741 < baseStart_3279741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279756 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3279756 : Nat := 118140960795 + 3279756 * 2 ^ 59
def prefixEnd_3279756 : Nat := 4983230072969 + 3 ^ 40 * 3279756 * 2
def baseEnd_3279756 : Nat := 1122727504978383448844455

theorem tailTrace_3279756 : CollatzResearch.WordTrace tailWord_3279756 prefixEnd_3279756 1122727504978383448844455 := by
  unfold tailWord_3279756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59811264353005812287533561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79748352470674416383378081 59811264353005812287533561)
  ·
    refine ⟨44858448264754359215650171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59811264353005812287533561 44858448264754359215650171)
    ·
      refine ⟨67287672397131538823475257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44858448264754359215650171 67287672397131538823475257)
      ·
        refine ⟨50465754297848654117606443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67287672397131538823475257 50465754297848654117606443)
        ·
          refine ⟨75698631446772981176409665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50465754297848654117606443 75698631446772981176409665)
          ·
            refine ⟨56773973585079735882307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75698631446772981176409665 56773973585079735882307249)
            ·
              refine ⟨42580480188809801911730437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56773973585079735882307249 42580480188809801911730437)
              ·
                refine ⟨7983840035401837858449457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42580480188809801911730437 7983840035401837858449457)
                ·
                  refine ⟨5987880026551378393837093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7983840035401837858449457 5987880026551378393837093)
                  ·
                    refine ⟨1122727504978383448844455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5987880026551378393837093 1122727504978383448844455)
                    ·
                      rfl

theorem cell22_3279756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3279756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279756 prefixEnd_3279756 := by exact prefixLift 3279756
  have htrace : WordTrace (prefixWord ++ tailWord_3279756) baseStart_3279756 baseEnd_3279756 := by
    simpa [prefixWord, tailWord_3279756, baseEnd_3279756] using wordTrace_append hprefix tailTrace_3279756
  have hstable : (prefixWord ++ tailWord_3279756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279756).length < 2 ^ (prefixWord ++ tailWord_3279756).sum := by decide
  have hdescent : baseEnd_3279756 < baseStart_3279756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279833 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 5]
def baseStart_3279833 : Nat := 118140960795 + 3279833 * 2 ^ 59
def prefixEnd_3279833 : Nat := 4983230072969 + 3 ^ 40 * 3279833 * 2
def baseEnd_3279833 : Nat := 374251287883993638223073

theorem tailTrace_3279833 : CollatzResearch.WordTrace tailWord_3279833 prefixEnd_3279833 374251287883993638223073 := by
  unfold tailWord_3279833
  simp only [CollatzResearch.WordTrace]
  refine ⟨119625337126732666725620153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79750224751155111150413435 119625337126732666725620153)
  ·
    refine ⟨89719002845049500044215115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119625337126732666725620153 89719002845049500044215115)
    ·
      refine ⟨134578504267574250066322673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89719002845049500044215115 134578504267574250066322673)
      ·
        refine ⟨100933878200680687549742005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134578504267574250066322673 100933878200680687549742005)
        ·
          refine ⟨9462551081313814457788313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100933878200680687549742005 9462551081313814457788313)
          ·
            refine ⟨7096913310985360843341235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462551081313814457788313 7096913310985360843341235)
            ·
              refine ⟨10645369966478041265011853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096913310985360843341235 10645369966478041265011853)
              ·
                refine ⟨3992013737429265474379445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10645369966478041265011853 3992013737429265474379445)
                ·
                  refine ⟨374251287883993638223073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3992013737429265474379445 374251287883993638223073)
                  ·
                    rfl

theorem cell22_3279833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_3279833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279833 prefixEnd_3279833 := by exact prefixLift 3279833
  have htrace : WordTrace (prefixWord ++ tailWord_3279833) baseStart_3279833 baseEnd_3279833 := by
    simpa [prefixWord, tailWord_3279833, baseEnd_3279833] using wordTrace_append hprefix tailTrace_3279833
  have hstable : (prefixWord ++ tailWord_3279833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279833).length < 2 ^ (prefixWord ++ tailWord_3279833).sum := by decide
  have hdescent : baseEnd_3279833 < baseStart_3279833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279891 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_3279891 : Nat := 118140960795 + 3279891 * 2 ^ 59
def prefixEnd_3279891 : Nat := 4983230072969 + 3 ^ 40 * 3279891 * 2
def baseEnd_3279891 : Nat := 1122773718237288096719041

theorem tailTrace_3279891 : CollatzResearch.WordTrace tailWord_3279891 prefixEnd_3279891 1122773718237288096719041 := by
  unfold tailWord_3279891
  simp only [CollatzResearch.WordTrace]
  refine ⟨119627452560522542631231527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79751635040348361754154351 119627452560522542631231527)
  ·
    refine ⟨179441178840783813946847291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119627452560522542631231527 179441178840783813946847291)
    ·
      refine ⟨269161768261175720920270937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179441178840783813946847291 269161768261175720920270937)
      ·
        refine ⟨201871326195881790690203203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269161768261175720920270937 201871326195881790690203203)
        ·
          refine ⟨302806989293822686035304805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201871326195881790690203203 302806989293822686035304805)
          ·
            refine ⟨56776310492591753631619651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302806989293822686035304805 56776310492591753631619651)
            ·
              refine ⟨85164465738887630447429477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56776310492591753631619651 85164465738887630447429477)
              ·
                refine ⟨15968337326041430708893027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85164465738887630447429477 15968337326041430708893027)
                ·
                  refine ⟨23952505989062146063339541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15968337326041430708893027 23952505989062146063339541)
                  ·
                    refine ⟨1122773718237288096719041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23952505989062146063339541 1122773718237288096719041)
                    ·
                      rfl

theorem cell22_3279891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_3279891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279891 prefixEnd_3279891 := by exact prefixLift 3279891
  have htrace : WordTrace (prefixWord ++ tailWord_3279891) baseStart_3279891 baseEnd_3279891 := by
    simpa [prefixWord, tailWord_3279891, baseEnd_3279891] using wordTrace_append hprefix tailTrace_3279891
  have hstable : (prefixWord ++ tailWord_3279891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279891).length < 2 ^ (prefixWord ++ tailWord_3279891).sum := by decide
  have hdescent : baseEnd_3279891 < baseStart_3279891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279893 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3279893 : Nat := 118140960795 + 3279893 * 2 ^ 59
def prefixEnd_3279893 : Nat := 4983230072969 + 3 ^ 40 * 3279893 * 2
def baseEnd_3279893 : Nat := 1122774402878160758169035

theorem tailTrace_3279893 : CollatzResearch.WordTrace tailWord_3279893 prefixEnd_3279893 1122774402878160758169035 := by
  unfold tailWord_3279893
  simp only [CollatzResearch.WordTrace]
  refine ⟨119627525506515296972804333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79751683671010197981869555 119627525506515296972804333)
  ·
    refine ⟨44860322064943236364801625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119627525506515296972804333 44860322064943236364801625)
    ·
      refine ⟨33645241548707427273601219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44860322064943236364801625 33645241548707427273601219)
      ·
        refine ⟨50467862323061140910401829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33645241548707427273601219 50467862323061140910401829)
        ·
          refine ⟨9462724185573963920700343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50467862323061140910401829 9462724185573963920700343)
          ·
            refine ⟨14194086278360945881050515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462724185573963920700343 14194086278360945881050515)
            ·
              refine ⟨21291129417541418821575773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14194086278360945881050515 21291129417541418821575773)
              ·
                refine ⟨7984173531578032058090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21291129417541418821575773 7984173531578032058090915)
                ·
                  refine ⟨11976260297367048087136373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7984173531578032058090915 11976260297367048087136373)
                  ·
                    refine ⟨1122774402878160758169035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11976260297367048087136373 1122774402878160758169035)
                    ·
                      rfl

theorem cell22_3279893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3279893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279893 prefixEnd_3279893 := by exact prefixLift 3279893
  have htrace : WordTrace (prefixWord ++ tailWord_3279893) baseStart_3279893 baseEnd_3279893 := by
    simpa [prefixWord, tailWord_3279893, baseEnd_3279893] using wordTrace_append hprefix tailTrace_3279893
  have hstable : (prefixWord ++ tailWord_3279893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279893).length < 2 ^ (prefixWord ++ tailWord_3279893).sum := by decide
  have hdescent : baseEnd_3279893 < baseStart_3279893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279914 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3279914 : Nat := 118140960795 + 3279914 * 2 ^ 59
def prefixEnd_3279914 : Nat := 4983230072969 + 3 ^ 40 * 3279914 * 2
def baseEnd_3279914 : Nat := 1122781591607323703393971

theorem tailTrace_3279914 : CollatzResearch.WordTrace tailWord_3279914 prefixEnd_3279914 1122781591607323703393971 := by
  unfold tailWord_3279914
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907072859859804389829699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79752194292959478372879197 29907072859859804389829699)
  ·
    refine ⟨44860609289789706584744549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29907072859859804389829699 44860609289789706584744549)
    ·
      refine ⟨8411364241835569984639603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44860609289789706584744549 8411364241835569984639603)
      ·
        refine ⟨12617046362753354976959405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411364241835569984639603 12617046362753354976959405)
        ·
          refine ⟨4731392386032508116359777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12617046362753354976959405 4731392386032508116359777)
          ·
            refine ⟨3548544289524381087269833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731392386032508116359777 3548544289524381087269833)
            ·
              refine ⟨2661408217143285815452375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548544289524381087269833 2661408217143285815452375)
              ·
                refine ⟨3992112325714928723178563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661408217143285815452375 3992112325714928723178563)
                ·
                  refine ⟨5988168488572393084767845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992112325714928723178563 5988168488572393084767845)
                  ·
                    refine ⟨1122781591607323703393971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988168488572393084767845 1122781591607323703393971)
                    ·
                      rfl

theorem cell22_3279914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3279914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279914 prefixEnd_3279914 := by exact prefixLift 3279914
  have htrace : WordTrace (prefixWord ++ tailWord_3279914) baseStart_3279914 baseEnd_3279914 := by
    simpa [prefixWord, tailWord_3279914, baseEnd_3279914] using wordTrace_append hprefix tailTrace_3279914
  have hstable : (prefixWord ++ tailWord_3279914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279914).length < 2 ^ (prefixWord ++ tailWord_3279914).sum := by decide
  have hdescent : baseEnd_3279914 < baseStart_3279914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279951 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 11]
def baseStart_3279951 : Nat := 118140960795 + 3279951 * 2 ^ 59
def prefixEnd_3279951 : Nat := 4983230072969 + 3 ^ 40 * 3279951 * 2
def baseEnd_3279951 : Nat := 374264752487822646739619

theorem tailTrace_3279951 : CollatzResearch.WordTrace tailWord_3279951 prefixEnd_3279951 374264752487822646739619 := by
  unfold tailWord_3279951
  simp only [CollatzResearch.WordTrace]
  refine ⟨119629640940305172878415707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79753093960203448585610471 119629640940305172878415707)
  ·
    refine ⟨179444461410457759317623561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119629640940305172878415707 179444461410457759317623561)
    ·
      refine ⟨134583346057843319488217671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179444461410457759317623561 134583346057843319488217671)
      ·
        refine ⟨201875019086764979232326507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134583346057843319488217671 201875019086764979232326507)
        ·
          refine ⟨302812528630147468848489761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201875019086764979232326507 302812528630147468848489761)
          ·
            refine ⟨227109396472610601636367321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302812528630147468848489761 227109396472610601636367321)
            ·
              refine ⟨170332047354457951227275491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227109396472610601636367321 170332047354457951227275491)
              ·
                refine ⟨255498071031686926840913237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170332047354457951227275491 255498071031686926840913237)
                ·
                  refine ⟨374264752487822646739619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 255498071031686926840913237 374264752487822646739619)
                  ·
                    rfl

theorem cell22_3279951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_3279951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3279951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3279951 prefixEnd_3279951 := by exact prefixLift 3279951
  have htrace : WordTrace (prefixWord ++ tailWord_3279951) baseStart_3279951 baseEnd_3279951 := by
    simpa [prefixWord, tailWord_3279951, baseEnd_3279951] using wordTrace_append hprefix tailTrace_3279951
  have hstable : (prefixWord ++ tailWord_3279951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279951).length < 2 ^ (prefixWord ++ tailWord_3279951).sum := by decide
  have hdescent : baseEnd_3279951 < baseStart_3279951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280032 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_3280032 : Nat := 118140960795 + 3280032 * 2 ^ 59
def prefixEnd_3280032 : Nat := 4983230072969 + 3 ^ 40 * 3280032 * 2
def baseEnd_3280032 : Nat := 1122821985418810728943609

theorem tailTrace_3280032 : CollatzResearch.WordTrace tailWord_3280032 prefixEnd_3280032 1122821985418810728943609 := by
  unfold tailWord_3280032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59816297626505861856057175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79755063502007815808076233 59816297626505861856057175)
  ·
    refine ⟨89724446439758792784085763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59816297626505861856057175 89724446439758792784085763)
    ·
      refine ⟨134586669659638189176128645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89724446439758792784085763 134586669659638189176128645)
      ·
        refine ⟨25235000561182160470524121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134586669659638189176128645 25235000561182160470524121)
        ·
          refine ⟨18926250420886620352893091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25235000561182160470524121 18926250420886620352893091)
          ·
            refine ⟨28389375631329930529339637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18926250420886620352893091 28389375631329930529339637)
            ·
              refine ⟨2661503965437180987125591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28389375631329930529339637 2661503965437180987125591)
              ·
                refine ⟨3992255948155771480688387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661503965437180987125591 3992255948155771480688387)
                ·
                  refine ⟨5988383922233657221032581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992255948155771480688387 5988383922233657221032581)
                  ·
                    refine ⟨1122821985418810728943609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988383922233657221032581 1122821985418810728943609)
                    ·
                      rfl

theorem cell22_3280032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_3280032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280032 prefixEnd_3280032 := by exact prefixLift 3280032
  have htrace : WordTrace (prefixWord ++ tailWord_3280032) baseStart_3280032 baseEnd_3280032 := by
    simpa [prefixWord, tailWord_3280032, baseEnd_3280032] using wordTrace_append hprefix tailTrace_3280032
  have hstable : (prefixWord ++ tailWord_3280032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280032).length < 2 ^ (prefixWord ++ tailWord_3280032).sum := by decide
  have hdescent : baseEnd_3280032 < baseStart_3280032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280047 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 4]
def baseStart_3280047 : Nat := 118140960795 + 3280047 * 2 ^ 59
def prefixEnd_3280047 : Nat := 4983230072969 + 3 ^ 40 * 3280047 * 2
def baseEnd_3280047 : Nat := 374275706741785229939521

theorem tailTrace_3280047 : CollatzResearch.WordTrace tailWord_3280047 prefixEnd_3280047 374275706741785229939521 := by
  unfold tailWord_3280047
  simp only [CollatzResearch.WordTrace]
  refine ⟨119633142347957381273910395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79755428231971587515940263 119633142347957381273910395)
  ·
    refine ⟨179449713521936071910865593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119633142347957381273910395 179449713521936071910865593)
    ·
      refine ⟨134587285141452053933149195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179449713521936071910865593 134587285141452053933149195)
      ·
        refine ⟨201880927712178080899723793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134587285141452053933149195 201880927712178080899723793)
        ·
          refine ⟨151410695784133560674792845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201880927712178080899723793 151410695784133560674792845)
          ·
            refine ⟨56779010919050085253047317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151410695784133560674792845 56779010919050085253047317)
            ·
              refine ⟨2661516136830472746236593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56779010919050085253047317 2661516136830472746236593)
              ·
                refine ⟨1996137102622854559677445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661516136830472746236593 1996137102622854559677445)
                ·
                  refine ⟨374275706741785229939521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996137102622854559677445 374275706741785229939521)
                  ·
                    rfl

theorem cell22_3280047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 4].length) (baseStart_3280047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280047 prefixEnd_3280047 := by exact prefixLift 3280047
  have htrace : WordTrace (prefixWord ++ tailWord_3280047) baseStart_3280047 baseEnd_3280047 := by
    simpa [prefixWord, tailWord_3280047, baseEnd_3280047] using wordTrace_append hprefix tailTrace_3280047
  have hstable : (prefixWord ++ tailWord_3280047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280047).length < 2 ^ (prefixWord ++ tailWord_3280047).sum := by decide
  have hdescent : baseEnd_3280047 < baseStart_3280047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280062 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3280062 : Nat := 118140960795 + 3280062 * 2 ^ 59
def prefixEnd_3280062 : Nat := 4983230072969 + 3 ^ 40 * 3280062 * 2
def baseEnd_3280062 : Nat := 1122832255031900650693517

theorem tailTrace_3280062 : CollatzResearch.WordTrace tailWord_3280062 prefixEnd_3280062 1122832255031900650693517 := by
  unfold tailWord_3280062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954211180362879854463305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79755792961935359223804293 14954211180362879854463305)
  ·
    refine ⟨11215658385272159890847479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14954211180362879854463305 11215658385272159890847479)
    ·
      refine ⟨16823487577908239836271219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215658385272159890847479 16823487577908239836271219)
      ·
        refine ⟨25235231366862359754406829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823487577908239836271219 25235231366862359754406829)
        ·
          refine ⟨9463211762573384907902561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25235231366862359754406829 9463211762573384907902561)
          ·
            refine ⟨7097408821930038680926921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9463211762573384907902561 7097408821930038680926921)
            ·
              refine ⟨5323056616447529010695191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097408821930038680926921 5323056616447529010695191)
              ·
                refine ⟨7984584924671293516042787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323056616447529010695191 7984584924671293516042787)
                ·
                  refine ⟨11976877387006940274064181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7984584924671293516042787 11976877387006940274064181)
                  ·
                    refine ⟨1122832255031900650693517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11976877387006940274064181 1122832255031900650693517)
                    ·
                      rfl

theorem cell22_3280062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3280062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280062 prefixEnd_3280062 := by exact prefixLift 3280062
  have htrace : WordTrace (prefixWord ++ tailWord_3280062) baseStart_3280062 baseEnd_3280062 := by
    simpa [prefixWord, tailWord_3280062, baseEnd_3280062] using wordTrace_append hprefix tailTrace_3280062
  have hstable : (prefixWord ++ tailWord_3280062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280062).length < 2 ^ (prefixWord ++ tailWord_3280062).sum := by decide
  have hdescent : baseEnd_3280062 < baseStart_3280062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280090 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_3280090 : Nat := 118140960795 + 3280090 * 2 ^ 59
def prefixEnd_3280090 : Nat := 4983230072969 + 3 ^ 40 * 3280090 * 2
def baseEnd_3280090 : Nat := 1122841840004117910993431

theorem tailTrace_3280090 : CollatzResearch.WordTrace tailWord_3280090 prefixEnd_3280090 1122841840004117910993431 := by
  unfold tailWord_3280090
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908677671700399904431431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79756473791201066411817149 29908677671700399904431431)
  ·
    refine ⟨44863016507550599856647147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29908677671700399904431431 44863016507550599856647147)
    ·
      refine ⟨67294524761325899784970721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44863016507550599856647147 67294524761325899784970721)
      ·
        refine ⟨50470893570994424838728041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67294524761325899784970721 50470893570994424838728041)
        ·
          refine ⟨37853170178245818629046031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50470893570994424838728041 37853170178245818629046031)
          ·
            refine ⟨56779755267368727943569047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37853170178245818629046031 56779755267368727943569047)
            ·
              refine ⟨85169632901053091915353571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56779755267368727943569047 85169632901053091915353571)
              ·
                refine ⟨127754449351579637873030357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85169632901053091915353571 127754449351579637873030357)
                ·
                  refine ⟨2994244906677647762649149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127754449351579637873030357 2994244906677647762649149)
                  ·
                    refine ⟨1122841840004117910993431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994244906677647762649149 1122841840004117910993431)
                    ·
                      rfl

theorem cell22_3280090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_3280090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280090 prefixEnd_3280090 := by exact prefixLift 3280090
  have htrace : WordTrace (prefixWord ++ tailWord_3280090) baseStart_3280090 baseEnd_3280090 := by
    simpa [prefixWord, tailWord_3280090, baseEnd_3280090] using wordTrace_append hprefix tailTrace_3280090
  have hstable : (prefixWord ++ tailWord_3280090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280090).length < 2 ^ (prefixWord ++ tailWord_3280090).sum := by decide
  have hdescent : baseEnd_3280090 < baseStart_3280090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280107 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 3, 3]
def baseStart_3280107 : Nat := 118140960795 + 3280107 * 2 ^ 59
def prefixEnd_3280107 : Nat := 4983230072969 + 3 ^ 40 * 3280107 * 2
def baseEnd_3280107 : Nat := 1122847659451535533318379

theorem tailTrace_3280107 : CollatzResearch.WordTrace tailWord_3280107 prefixEnd_3280107 1122847659451535533318379 := by
  unfold tailWord_3280107
  simp only [CollatzResearch.WordTrace]
  refine ⟨119635330727740011521094575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79756887151826674347396383 119635330727740011521094575)
  ·
    refine ⟨179452996091610017281641863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119635330727740011521094575 179452996091610017281641863)
    ·
      refine ⟨269179494137415025922462795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179452996091610017281641863 269179494137415025922462795)
      ·
        refine ⟨403769241206122538883694193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269179494137415025922462795 403769241206122538883694193)
        ·
          refine ⟨302826930904591904162770645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403769241206122538883694193 302826930904591904162770645)
          ·
            refine ⟨7097506193076372753814937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 302826930904591904162770645 7097506193076372753814937)
            ·
              refine ⟨5323129644807279565361203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097506193076372753814937 5323129644807279565361203)
              ·
                refine ⟨7984694467210919348041805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323129644807279565361203 7984694467210919348041805)
                ·
                  refine ⟨2994260425204094755515677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7984694467210919348041805 2994260425204094755515677)
                  ·
                    refine ⟨1122847659451535533318379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994260425204094755515677 1122847659451535533318379)
                    ·
                      rfl

theorem cell22_3280107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].length) (baseStart_3280107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280107 prefixEnd_3280107 := by exact prefixLift 3280107
  have htrace : WordTrace (prefixWord ++ tailWord_3280107) baseStart_3280107 baseEnd_3280107 := by
    simpa [prefixWord, tailWord_3280107, baseEnd_3280107] using wordTrace_append hprefix tailTrace_3280107
  have hstable : (prefixWord ++ tailWord_3280107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280107).length < 2 ^ (prefixWord ++ tailWord_3280107).sum := by decide
  have hdescent : baseEnd_3280107 < baseStart_3280107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280158 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3280158 : Nat := 118140960795 + 3280158 * 2 ^ 59
def prefixEnd_3280158 : Nat := 4983230072969 + 3 ^ 40 * 3280158 * 2
def baseEnd_3280158 : Nat := 1122865117793788400293223

theorem tailTrace_3280158 : CollatzResearch.WordTrace tailWord_3280158 prefixEnd_3280158 1122865117793788400293223 := by
  unfold tailWord_3280158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954648856319405903900141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79758127233703498154134085 14954648856319405903900141)
  ·
    refine ⟨5607993321119777213962553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14954648856319405903900141 5607993321119777213962553)
    ·
      refine ⟨4205994990839832910471915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607993321119777213962553 4205994990839832910471915)
      ·
        refine ⟨6308992486259749365707873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205994990839832910471915 6308992486259749365707873)
        ·
          refine ⟨4731744364694812024280905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308992486259749365707873 4731744364694812024280905)
          ·
            refine ⟨3548808273521109018210679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731744364694812024280905 3548808273521109018210679)
            ·
              refine ⟨5323212410281663527316019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548808273521109018210679 5323212410281663527316019)
              ·
                refine ⟨7984818615422495290974029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323212410281663527316019 7984818615422495290974029)
                ·
                  refine ⟨2994306980783435734115261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7984818615422495290974029 2994306980783435734115261)
                  ·
                    refine ⟨1122865117793788400293223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994306980783435734115261 1122865117793788400293223)
                    ·
                      rfl

theorem cell22_3280158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3280158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280158 prefixEnd_3280158 := by exact prefixLift 3280158
  have htrace : WordTrace (prefixWord ++ tailWord_3280158) baseStart_3280158 baseEnd_3280158 := by
    simpa [prefixWord, tailWord_3280158, baseEnd_3280158] using wordTrace_append hprefix tailTrace_3280158
  have hstable : (prefixWord ++ tailWord_3280158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280158).length < 2 ^ (prefixWord ++ tailWord_3280158).sum := by decide
  have hdescent : baseEnd_3280158 < baseStart_3280158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280212 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3280212 : Nat := 118140960795 + 3280212 * 2 ^ 59
def prefixEnd_3280212 : Nat := 4983230072969 + 3 ^ 40 * 3280212 * 2
def baseEnd_3280212 : Nat := 1122883603097350259443057

theorem tailTrace_3280212 : CollatzResearch.WordTrace tailWord_3280212 prefixEnd_3280212 1122883603097350259443057 := by
  unfold tailWord_3280212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59819580196179807226833445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79759440261573076302444593 59819580196179807226833445)
  ·
    refine ⟨11216171286783713855031271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59819580196179807226833445 11216171286783713855031271)
    ·
      refine ⟨16824256930175570782546907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216171286783713855031271 16824256930175570782546907)
      ·
        refine ⟨25236385395263356173820361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16824256930175570782546907 25236385395263356173820361)
        ·
          refine ⟨18927289046447517130365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25236385395263356173820361 18927289046447517130365271)
          ·
            refine ⟨28390933569671275695547907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18927289046447517130365271 28390933569671275695547907)
            ·
              refine ⟨42586400354506913543321861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28390933569671275695547907 42586400354506913543321861)
              ·
                refine ⟨7984950066470046289372849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42586400354506913543321861 7984950066470046289372849)
                ·
                  refine ⟨5988712549852534717029637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7984950066470046289372849 5988712549852534717029637)
                  ·
                    refine ⟨1122883603097350259443057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988712549852534717029637 1122883603097350259443057)
                    ·
                      rfl

theorem cell22_3280212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3280212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280212 prefixEnd_3280212 := by exact prefixLift 3280212
  have htrace : WordTrace (prefixWord ++ tailWord_3280212) baseStart_3280212 baseEnd_3280212 := by
    simpa [prefixWord, tailWord_3280212, baseEnd_3280212] using wordTrace_append hprefix tailTrace_3280212
  have hstable : (prefixWord ++ tailWord_3280212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280212).length < 2 ^ (prefixWord ++ tailWord_3280212).sum := by decide
  have hdescent : baseEnd_3280212 < baseStart_3280212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280227 : List Nat := [1, 1, 1, 5, 2, 4, 1, 7]
def baseStart_3280227 : Nat := 118140960795 + 3280227 * 2 ^ 59
def prefixEnd_3280227 : Nat := 4983230072969 + 3 ^ 40 * 3280227 * 2
def baseEnd_3280227 : Nat := 124765415322655024479779

theorem tailTrace_3280227 : CollatzResearch.WordTrace tailWord_3280227 prefixEnd_3280227 124765415322655024479779 := by
  unfold tailWord_3280227
  simp only [CollatzResearch.WordTrace]
  refine ⟨119639707487305272015462935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79759804991536848010308623 119639707487305272015462935)
  ·
    refine ⟨179459561230957908023194403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119639707487305272015462935 179459561230957908023194403)
    ·
      refine ⟨269189341846436862034791605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179459561230957908023194403 269189341846436862034791605)
      ·
        refine ⟨25236500798103455815761713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269189341846436862034791605 25236500798103455815761713)
        ·
          refine ⟨18927375598577591861821285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25236500798103455815761713 18927375598577591861821285)
          ·
            refine ⟨3548882924733298474091491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18927375598577591861821285 3548882924733298474091491)
            ·
              refine ⟨5323324387099947711137237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548882924733298474091491 5323324387099947711137237)
              ·
                refine ⟨124765415322655024479779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5323324387099947711137237 124765415322655024479779)
                ·
                  rfl

theorem cell22_3280227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 7].length) (baseStart_3280227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280227 prefixEnd_3280227 := by exact prefixLift 3280227
  have htrace : WordTrace (prefixWord ++ tailWord_3280227) baseStart_3280227 baseEnd_3280227 := by
    simpa [prefixWord, tailWord_3280227, baseEnd_3280227] using wordTrace_append hprefix tailTrace_3280227
  have hstable : (prefixWord ++ tailWord_3280227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280227).length < 2 ^ (prefixWord ++ tailWord_3280227).sum := by decide
  have hdescent : baseEnd_3280227 < baseStart_3280227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280240 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_3280240 : Nat := 118140960795 + 3280240 * 2 ^ 59
def prefixEnd_3280240 : Nat := 4983230072969 + 3 ^ 40 * 3280240 * 2
def baseEnd_3280240 : Nat := 1122893188069567519742971

theorem tailTrace_3280240 : CollatzResearch.WordTrace tailWord_3280240 prefixEnd_3280240 1122893188069567519742971 := by
  unfold tailWord_3280240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820090818129087617843087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79760121090838783490457449 59820090818129087617843087)
  ·
    refine ⟨89730136227193631426764631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59820090818129087617843087 89730136227193631426764631)
    ·
      refine ⟨134595204340790447140146947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89730136227193631426764631 134595204340790447140146947)
      ·
        refine ⟨201892806511185670710220421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134595204340790447140146947 201892806511185670710220421)
        ·
          refine ⟨37854901220847313258166329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201892806511185670710220421 37854901220847313258166329)
          ·
            refine ⟨28391175915635484943624747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37854901220847313258166329 28391175915635484943624747)
            ·
              refine ⟨42586763873453227415437121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28391175915635484943624747 42586763873453227415437121)
              ·
                refine ⟨31940072905089920561577841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42586763873453227415437121 31940072905089920561577841)
                ·
                  refine ⟨23955054678817440421183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31940072905089920561577841 23955054678817440421183381)
                  ·
                    refine ⟨1122893188069567519742971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23955054678817440421183381 1122893188069567519742971)
                    ·
                      rfl

theorem cell22_3280240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_3280240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280240 prefixEnd_3280240 := by exact prefixLift 3280240
  have htrace : WordTrace (prefixWord ++ tailWord_3280240) baseStart_3280240 baseEnd_3280240 := by
    simpa [prefixWord, tailWord_3280240, baseEnd_3280240] using wordTrace_append hprefix tailTrace_3280240
  have hstable : (prefixWord ++ tailWord_3280240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280240).length < 2 ^ (prefixWord ++ tailWord_3280240).sum := by decide
  have hdescent : baseEnd_3280240 < baseStart_3280240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280276 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3280276 : Nat := 118140960795 + 3280276 * 2 ^ 59
def prefixEnd_3280276 : Nat := 4983230072969 + 3 ^ 40 * 3280276 * 2
def baseEnd_3280276 : Nat := 1122905511605275425842861

theorem tailTrace_3280276 : CollatzResearch.WordTrace tailWord_3280276 prefixEnd_3280276 1122905511605275425842861 := by
  unfold tailWord_3280276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820747332063876691998341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79760996442751835589331121 59820747332063876691998341)
  ·
    refine ⟨11216390124761976879749689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59820747332063876691998341 11216390124761976879749689)
    ·
      refine ⟨8412292593571482659812267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11216390124761976879749689 8412292593571482659812267)
      ·
        refine ⟨12618438890357223989718401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412292593571482659812267 12618438890357223989718401)
        ·
          refine ⟨9463829167767917992288801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12618438890357223989718401 9463829167767917992288801)
          ·
            refine ⟨7097871875825938494216601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9463829167767917992288801 7097871875825938494216601)
            ·
              refine ⟨5323403906869453870662451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097871875825938494216601 5323403906869453870662451)
              ·
                refine ⟨7985105860304180805993677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323403906869453870662451 7985105860304180805993677)
                ·
                  refine ⟨2994414697614067802247629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7985105860304180805993677 2994414697614067802247629)
                  ·
                    refine ⟨1122905511605275425842861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994414697614067802247629 1122905511605275425842861)
                    ·
                      rfl

theorem cell22_3280276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3280276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280276 prefixEnd_3280276 := by exact prefixLift 3280276
  have htrace : WordTrace (prefixWord ++ tailWord_3280276) baseStart_3280276 baseEnd_3280276 := by
    simpa [prefixWord, tailWord_3280276, baseEnd_3280276] using wordTrace_append hprefix tailTrace_3280276
  have hstable : (prefixWord ++ tailWord_3280276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280276).length < 2 ^ (prefixWord ++ tailWord_3280276).sum := by decide
  have hdescent : baseEnd_3280276 < baseStart_3280276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280287 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_3280287 : Nat := 118140960795 + 3280287 * 2 ^ 59
def prefixEnd_3280287 : Nat := 4983230072969 + 3 ^ 40 * 3280287 * 2
def baseEnd_3280287 : Nat := 1122909277130075063817827

theorem tailTrace_3280287 : CollatzResearch.WordTrace tailWord_3280287 prefixEnd_3280287 1122909277130075063817827 := by
  unfold tailWord_3280287
  simp only [CollatzResearch.WordTrace]
  refine ⟨119641895867087902262647115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79761263911391934841764743 119641895867087902262647115)
  ·
    refine ⟨179462843800631853393970673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119641895867087902262647115 179462843800631853393970673)
    ·
      refine ⟨134597132850473890045478005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179462843800631853393970673 134597132850473890045478005)
      ·
        refine ⟨12618481204731927191763563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134597132850473890045478005 12618481204731927191763563)
        ·
          refine ⟨18927721807097890787645345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12618481204731927191763563 18927721807097890787645345)
          ·
            refine ⟨14195791355323418090734009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18927721807097890787645345 14195791355323418090734009)
            ·
              refine ⟨10646843516492563568050507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195791355323418090734009 10646843516492563568050507)
              ·
                refine ⟨15970265274738845352075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646843516492563568050507 15970265274738845352075761)
                ·
                  refine ⟨11977698956054134014056821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15970265274738845352075761 11977698956054134014056821)
                  ·
                    refine ⟨1122909277130075063817827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11977698956054134014056821 1122909277130075063817827)
                    ·
                      rfl

theorem cell22_3280287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_3280287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280287 prefixEnd_3280287 := by exact prefixLift 3280287
  have htrace : WordTrace (prefixWord ++ tailWord_3280287) baseStart_3280287 baseEnd_3280287 := by
    simpa [prefixWord, tailWord_3280287, baseEnd_3280287] using wordTrace_append hprefix tailTrace_3280287
  have hstable : (prefixWord ++ tailWord_3280287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280287).length < 2 ^ (prefixWord ++ tailWord_3280287).sum := by decide
  have hdescent : baseEnd_3280287 < baseStart_3280287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280334 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_3280334 : Nat := 118140960795 + 3280334 * 2 ^ 59
def prefixEnd_3280334 : Nat := 4983230072969 + 3 ^ 40 * 3280334 * 2
def baseEnd_3280334 : Nat := 374308455396860869297561

theorem tailTrace_3280334 : CollatzResearch.WordTrace tailWord_3280334 prefixEnd_3280334 374308455396860869297561 := by
  unfold tailWord_3280334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955451262239703661201007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79762406731945086193072037 14955451262239703661201007)
  ·
    refine ⟨22433176893359555491801511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14955451262239703661201007 22433176893359555491801511)
    ·
      refine ⟨33649765340039333237702267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22433176893359555491801511 33649765340039333237702267)
      ·
        refine ⟨50474648010058999856553401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33649765340039333237702267 50474648010058999856553401)
        ·
          refine ⟨37855986007544249892415051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50474648010058999856553401 37855986007544249892415051)
          ·
            refine ⟨56783979011316374838622577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37855986007544249892415051 56783979011316374838622577)
            ·
              refine ⟨42587984258487281128966933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56783979011316374838622577 42587984258487281128966933)
              ·
                refine ⟨1996311762116591302920325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42587984258487281128966933 1996311762116591302920325)
                ·
                  refine ⟨374308455396860869297561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996311762116591302920325 374308455396860869297561)
                  ·
                    rfl

theorem cell22_3280334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_3280334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280334 prefixEnd_3280334 := by exact prefixLift 3280334
  have htrace : WordTrace (prefixWord ++ tailWord_3280334) baseStart_3280334 baseEnd_3280334 := by
    simpa [prefixWord, tailWord_3280334, baseEnd_3280334] using wordTrace_append hprefix tailTrace_3280334
  have hstable : (prefixWord ++ tailWord_3280334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280334).length < 2 ^ (prefixWord ++ tailWord_3280334).sum := by decide
  have hdescent : baseEnd_3280334 < baseStart_3280334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280385 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 4]
def baseStart_3280385 : Nat := 118140960795 + 3280385 * 2 ^ 59
def prefixEnd_3280385 : Nat := 4983230072969 + 3 ^ 40 * 3280385 * 2
def baseEnd_3280385 : Nat := 374314274844278491622509

theorem tailTrace_3280385 : CollatzResearch.WordTrace tailWord_3280385 prefixEnd_3280385 374314274844278491622509 := by
  unfold tailWord_3280385
  simp only [CollatzResearch.WordTrace]
  refine ⟨119645470220732864999714609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79763646813821909999809739 119645470220732864999714609)
  ·
    refine ⟨89734102665549648749785957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119645470220732864999714609 89734102665549648749785957)
    ·
      refine ⟨16825144249790559140584867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89734102665549648749785957 16825144249790559140584867)
      ·
        refine ⟨25237716374685838710877301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16825144249790559140584867 25237716374685838710877301)
        ·
          refine ⟨2366035910126797379144747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25237716374685838710877301 2366035910126797379144747)
          ·
            refine ⟨3549053865190196068717121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366035910126797379144747 3549053865190196068717121)
            ·
              refine ⟨2661790398892647051537841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549053865190196068717121 2661790398892647051537841)
              ·
                refine ⟨1996342799169485288653381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661790398892647051537841 1996342799169485288653381)
                ·
                  refine ⟨374314274844278491622509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996342799169485288653381 374314274844278491622509)
                  ·
                    rfl

theorem cell22_3280385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_3280385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280385 prefixEnd_3280385 := by exact prefixLift 3280385
  have htrace : WordTrace (prefixWord ++ tailWord_3280385) baseStart_3280385 baseEnd_3280385 := by
    simpa [prefixWord, tailWord_3280385, baseEnd_3280385] using wordTrace_append hprefix tailTrace_3280385
  have hstable : (prefixWord ++ tailWord_3280385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280385).length < 2 ^ (prefixWord ++ tailWord_3280385).sum := by decide
  have hdescent : baseEnd_3280385 < baseStart_3280385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280392 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3280392 : Nat := 118140960795 + 3280392 * 2 ^ 59
def prefixEnd_3280392 : Nat := 4983230072969 + 3 ^ 40 * 3280392 * 2
def baseEnd_3280392 : Nat := 1122945220775889789942505

theorem tailTrace_3280392 : CollatzResearch.WordTrace tailWord_3280392 prefixEnd_3280392 1122945220775889789942505 := by
  unfold tailWord_3280392
  simp only [CollatzResearch.WordTrace]
  refine ⟨59822862765853752597609715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79763817021138336796812953 59822862765853752597609715)
  ·
    refine ⟨89734294148780628896414573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59822862765853752597609715 89734294148780628896414573)
    ·
      refine ⟨33650360305792735836155465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89734294148780628896414573 33650360305792735836155465)
      ·
        refine ⟨25237770229344551877116599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33650360305792735836155465 25237770229344551877116599)
        ·
          refine ⟨37856655344016827815674899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25237770229344551877116599 37856655344016827815674899)
          ·
            refine ⟨56784983016025241723512349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37856655344016827815674899 56784983016025241723512349)
            ·
              refine ⟨21294368631009465646317131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56784983016025241723512349 21294368631009465646317131)
              ·
                refine ⟨31941552946514198469475697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21294368631009465646317131 31941552946514198469475697)
                ·
                  refine ⟨23956164709885648852106773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31941552946514198469475697 23956164709885648852106773)
                  ·
                    refine ⟨1122945220775889789942505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23956164709885648852106773 1122945220775889789942505)
                    ·
                      rfl

theorem cell22_3280392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3280392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280392 prefixEnd_3280392 := by exact prefixLift 3280392
  have htrace : WordTrace (prefixWord ++ tailWord_3280392) baseStart_3280392 baseEnd_3280392 := by
    simpa [prefixWord, tailWord_3280392, baseEnd_3280392] using wordTrace_append hprefix tailTrace_3280392
  have hstable : (prefixWord ++ tailWord_3280392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280392).length < 2 ^ (prefixWord ++ tailWord_3280392).sum := by decide
  have hdescent : baseEnd_3280392 < baseStart_3280392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280396 : List Nat := [2, 2, 1, 2, 6, 1, 1, 7]
def baseStart_3280396 : Nat := 118140960795 + 3280396 * 2 ^ 59
def prefixEnd_3280396 : Nat := 4983230072969 + 3 ^ 40 * 3280396 * 2
def baseEnd_3280396 : Nat := 124771843339737234760277

theorem tailTrace_3280396 : CollatzResearch.WordTrace tailWord_3280396 prefixEnd_3280396 124771843339737234760277 := by
  unfold tailWord_3280396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59822935711846506939182521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79763914282462009252243361 59822935711846506939182521)
  ·
    refine ⟨44867201783884880204386891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59822935711846506939182521 44867201783884880204386891)
    ·
      refine ⟨67300802675827320306580337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44867201783884880204386891 67300802675827320306580337)
      ·
        refine ⟨50475602006870490229935253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67300802675827320306580337 50475602006870490229935253)
        ·
          refine ⟨2366043844072054229528215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50475602006870490229935253 2366043844072054229528215)
          ·
            refine ⟨3549065766108081344292323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366043844072054229528215 3549065766108081344292323)
            ·
              refine ⟨5323598649162122016438485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549065766108081344292323 5323598649162122016438485)
              ·
                refine ⟨124771843339737234760277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5323598649162122016438485 124771843339737234760277)
                ·
                  rfl

theorem cell22_3280396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_3280396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280396 prefixEnd_3280396 := by exact prefixLift 3280396
  have htrace : WordTrace (prefixWord ++ tailWord_3280396) baseStart_3280396 baseEnd_3280396 := by
    simpa [prefixWord, tailWord_3280396, baseEnd_3280396] using wordTrace_append hprefix tailTrace_3280396
  have hstable : (prefixWord ++ tailWord_3280396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280396).length < 2 ^ (prefixWord ++ tailWord_3280396).sum := by decide
  have hdescent : baseEnd_3280396 < baseStart_3280396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280441 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 5]
def baseStart_3280441 : Nat := 118140960795 + 3280441 * 2 ^ 59
def prefixEnd_3280441 : Nat := 4983230072969 + 3 ^ 40 * 3280441 * 2
def baseEnd_3280441 : Nat := 374320664825756665155785

theorem tailTrace_3280441 : CollatzResearch.WordTrace tailWord_3280441 prefixEnd_3280441 374320664825756665155785 := by
  unfold tailWord_3280441
  simp only [CollatzResearch.WordTrace]
  refine ⟨119647512708529986563753177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79765008472353324375835451 119647512708529986563753177)
  ·
    refine ⟨89735634531397489922814883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119647512708529986563753177 89735634531397489922814883)
    ·
      refine ⟨134603451797096234884222325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89735634531397489922814883 134603451797096234884222325)
      ·
        refine ⟨12619073605977772020395843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134603451797096234884222325 12619073605977772020395843)
        ·
          refine ⟨18928610408966658030593765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12619073605977772020395843 18928610408966658030593765)
          ·
            refine ⟨3549114451681248380736331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18928610408966658030593765 3549114451681248380736331)
            ·
              refine ⟨5323671677521872571104497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549114451681248380736331 5323671677521872571104497)
              ·
                refine ⟨3992753758141404428328373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323671677521872571104497 3992753758141404428328373)
                ·
                  refine ⟨374320664825756665155785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3992753758141404428328373 374320664825756665155785)
                  ·
                    rfl

theorem cell22_3280441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_3280441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280441 prefixEnd_3280441 := by exact prefixLift 3280441
  have htrace : WordTrace (prefixWord ++ tailWord_3280441) baseStart_3280441 baseEnd_3280441 := by
    simpa [prefixWord, tailWord_3280441, baseEnd_3280441] using wordTrace_append hprefix tailTrace_3280441
  have hstable : (prefixWord ++ tailWord_3280441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280441).length < 2 ^ (prefixWord ++ tailWord_3280441).sum := by decide
  have hdescent : baseEnd_3280441 < baseStart_3280441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280467 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_3280467 : Nat := 118140960795 + 3280467 * 2 ^ 59
def prefixEnd_3280467 : Nat := 4983230072969 + 3 ^ 40 * 3280467 * 2
def baseEnd_3280467 : Nat := 1122970894808614594317275

theorem tailTrace_3280467 : CollatzResearch.WordTrace tailWord_3280467 prefixEnd_3280467 1122970894808614594317275 := by
  unfold tailWord_3280467
  simp only [CollatzResearch.WordTrace]
  refine ⟨119648461006435793004199655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79765640670957195336133103 119648461006435793004199655)
  ·
    refine ⟨179472691509653689506299483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119648461006435793004199655 179472691509653689506299483)
    ·
      refine ⟨269209037264480534259449225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179472691509653689506299483 269209037264480534259449225)
      ·
        refine ⟨201906777948360400694586919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269209037264480534259449225 201906777948360400694586919)
        ·
          refine ⟨302860166922540601041880379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201906777948360400694586919 302860166922540601041880379)
          ·
            refine ⟨454290250383810901562820569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302860166922540601041880379 454290250383810901562820569)
            ·
              refine ⟨340717687787858176172115427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454290250383810901562820569 340717687787858176172115427)
              ·
                refine ⟨511076531681787264258173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340717687787858176172115427 511076531681787264258173141)
                ·
                  refine ⟨11978356211291889006050933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 511076531681787264258173141 11978356211291889006050933)
                  ·
                    refine ⟨1122970894808614594317275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11978356211291889006050933 1122970894808614594317275)
                    ·
                      rfl

theorem cell22_3280467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_3280467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280467 prefixEnd_3280467 := by exact prefixLift 3280467
  have htrace : WordTrace (prefixWord ++ tailWord_3280467) baseStart_3280467 baseEnd_3280467 := by
    simpa [prefixWord, tailWord_3280467, baseEnd_3280467] using wordTrace_append hprefix tailTrace_3280467
  have hstable : (prefixWord ++ tailWord_3280467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280467).length < 2 ^ (prefixWord ++ tailWord_3280467).sum := by decide
  have hdescent : baseEnd_3280467 < baseStart_3280467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280471 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3280471 : Nat := 118140960795 + 3280471 * 2 ^ 59
def prefixEnd_3280471 : Nat := 4983230072969 + 3 ^ 40 * 3280471 * 2
def baseEnd_3280471 : Nat := 1122972264090359917217263

theorem tailTrace_3280471 : CollatzResearch.WordTrace tailWord_3280471 prefixEnd_3280471 1122972264090359917217263 := by
  unfold tailWord_3280471
  simp only [CollatzResearch.WordTrace]
  refine ⟨119648606898421301687345267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79765737932280867791563511 119648606898421301687345267)
  ·
    refine ⟨179472910347631952531017901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119648606898421301687345267 179472910347631952531017901)
    ·
      refine ⟨67302341380361982199131713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179472910347631952531017901 67302341380361982199131713)
      ·
        refine ⟨50476756035271486649348785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67302341380361982199131713 50476756035271486649348785)
        ·
          refine ⟨37857567026453614987011589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50476756035271486649348785 37857567026453614987011589)
          ·
            refine ⟨7098293817460052810064673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37857567026453614987011589 7098293817460052810064673)
            ·
              refine ⟨5323720363095039607548505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7098293817460052810064673 5323720363095039607548505)
              ·
                refine ⟨3992790272321279705661379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323720363095039607548505 3992790272321279705661379)
                ·
                  refine ⟨5989185408481919558492069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992790272321279705661379 5989185408481919558492069)
                  ·
                    refine ⟨1122972264090359917217263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989185408481919558492069 1122972264090359917217263)
                    ·
                      rfl

theorem cell22_3280471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3280471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280471 prefixEnd_3280471 := by exact prefixLift 3280471
  have htrace : WordTrace (prefixWord ++ tailWord_3280471) baseStart_3280471 baseEnd_3280471 := by
    simpa [prefixWord, tailWord_3280471, baseEnd_3280471] using wordTrace_append hprefix tailTrace_3280471
  have hstable : (prefixWord ++ tailWord_3280471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280471).length < 2 ^ (prefixWord ++ tailWord_3280471).sum := by decide
  have hdescent : baseEnd_3280471 < baseStart_3280471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280563 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 1, 3]
def baseStart_3280563 : Nat := 118140960795 + 3280563 * 2 ^ 59
def prefixEnd_3280563 : Nat := 4983230072969 + 3 ^ 40 * 3280563 * 2
def baseEnd_3280563 : Nat := 1123003757570502343916981

theorem tailTrace_3280563 : CollatzResearch.WordTrace tailWord_3280563 prefixEnd_3280563 1123003757570502343916981 := by
  unfold tailWord_3280563
  simp only [CollatzResearch.WordTrace]
  refine ⟨119651962414088001399694343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79767974942725334266462895 119651962414088001399694343)
  ·
    refine ⟨179477943621132002099541515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119651962414088001399694343 179477943621132002099541515)
    ·
      refine ⟨269216915431698003149312273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179477943621132002099541515 269216915431698003149312273)
      ·
        refine ⟨201912686573773502361984205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269216915431698003149312273 201912686573773502361984205)
        ·
          refine ⟨75717257465165063385744077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201912686573773502361984205 75717257465165063385744077)
          ·
            refine ⟨28393971549436898769654029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75717257465165063385744077 28393971549436898769654029)
            ·
              refine ⟨10647739331038837038620261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28393971549436898769654029 10647739331038837038620261)
              ·
                refine ⟨1996451124569781944741299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10647739331038837038620261 1996451124569781944741299)
                ·
                  refine ⟨2994676686854672917111949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996451124569781944741299 2994676686854672917111949)
                  ·
                    refine ⟨1123003757570502343916981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994676686854672917111949 1123003757570502343916981)
                    ·
                      rfl

theorem cell22_3280563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 3].length) (baseStart_3280563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280563 prefixEnd_3280563 := by exact prefixLift 3280563
  have htrace : WordTrace (prefixWord ++ tailWord_3280563) baseStart_3280563 baseEnd_3280563 := by
    simpa [prefixWord, tailWord_3280563, baseEnd_3280563] using wordTrace_append hprefix tailTrace_3280563
  have hstable : (prefixWord ++ tailWord_3280563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280563).length < 2 ^ (prefixWord ++ tailWord_3280563).sum := by decide
  have hdescent : baseEnd_3280563 < baseStart_3280563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280619 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_3280619 : Nat := 118140960795 + 3280619 * 2 ^ 59
def prefixEnd_3280619 : Nat := 4983230072969 + 3 ^ 40 * 3280619 * 2
def baseEnd_3280619 : Nat := 1123022927514936864516809

theorem tailTrace_3280619 : CollatzResearch.WordTrace tailWord_3280619 prefixEnd_3280619 1123022927514936864516809 := by
  unfold tailWord_3280619
  simp only [CollatzResearch.WordTrace]
  refine ⟨119654004901885122963732911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79769336601256748642488607 119654004901885122963732911)
  ·
    refine ⟨179481007352827684445599367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119654004901885122963732911 179481007352827684445599367)
    ·
      refine ⟨269221511029241526668399051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179481007352827684445599367 269221511029241526668399051)
      ·
        refine ⟨403832266543862290002598577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269221511029241526668399051 403832266543862290002598577)
        ·
          refine ⟨302874199907896717501948933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403832266543862290002598577 302874199907896717501948933)
          ·
            refine ⟨56788912482730634531615425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302874199907896717501948933 56788912482730634531615425)
            ·
              refine ⟨42591684362047975898711569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56788912482730634531615425 42591684362047975898711569)
              ·
                refine ⟨31943763271535981924033677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42591684362047975898711569 31943763271535981924033677)
                ·
                  refine ⟨11978911226825993221512629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31943763271535981924033677 11978911226825993221512629)
                  ·
                    refine ⟨1123022927514936864516809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11978911226825993221512629 1123022927514936864516809)
                    ·
                      rfl

theorem cell22_3280619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_3280619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280619 prefixEnd_3280619 := by exact prefixLift 3280619
  have htrace : WordTrace (prefixWord ++ tailWord_3280619) baseStart_3280619 baseEnd_3280619 := by
    simpa [prefixWord, tailWord_3280619, baseEnd_3280619] using wordTrace_append hprefix tailTrace_3280619
  have hstable : (prefixWord ++ tailWord_3280619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280619).length < 2 ^ (prefixWord ++ tailWord_3280619).sum := by decide
  have hdescent : baseEnd_3280619 < baseStart_3280619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280621 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 6]
def baseStart_3280621 : Nat := 118140960795 + 3280621 * 2 ^ 59
def prefixEnd_3280621 : Nat := 4983230072969 + 3 ^ 40 * 3280621 * 2
def baseEnd_3280621 : Nat := 374341204051936508655601

theorem tailTrace_3280621 : CollatzResearch.WordTrace tailWord_3280621 prefixEnd_3280621 374341204051936508655601 := by
  unfold tailWord_3280621
  simp only [CollatzResearch.WordTrace]
  refine ⟨119654077847877877305305717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79769385231918584870203811 119654077847877877305305717)
  ·
    refine ⟨11217569798238550997372411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119654077847877877305305717 11217569798238550997372411)
    ·
      refine ⟨16826354697357826496058617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217569798238550997372411 16826354697357826496058617)
      ·
        refine ⟨12619766023018369872043963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16826354697357826496058617 12619766023018369872043963)
        ·
          refine ⟨18929649034527554808065945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12619766023018369872043963 18929649034527554808065945)
          ·
            refine ⟨14197236775895666106049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18929649034527554808065945 14197236775895666106049459)
            ·
              refine ⟨21295855163843499159074189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197236775895666106049459 21295855163843499159074189)
              ·
                refine ⟨7985945686441312184652821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21295855163843499159074189 7985945686441312184652821)
                ·
                  refine ⟨374341204051936508655601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7985945686441312184652821 374341204051936508655601)
                  ·
                    rfl

theorem cell22_3280621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_3280621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280621 prefixEnd_3280621 := by exact prefixLift 3280621
  have htrace : WordTrace (prefixWord ++ tailWord_3280621) baseStart_3280621 baseEnd_3280621 := by
    simpa [prefixWord, tailWord_3280621, baseEnd_3280621] using wordTrace_append hprefix tailTrace_3280621
  have hstable : (prefixWord ++ tailWord_3280621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280621).length < 2 ^ (prefixWord ++ tailWord_3280621).sum := by decide
  have hdescent : baseEnd_3280621 < baseStart_3280621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280666 : List Nat := [3, 1, 1, 3, 2, 4, 8]
def baseStart_3280666 : Nat := 118140960795 + 3280666 * 2 ^ 59
def prefixEnd_3280666 : Nat := 4983230072969 + 3 ^ 40 * 3280666 * 2
def baseEnd_3280666 : Nat := 41594037650942385503395

theorem tailTrace_3280666 : CollatzResearch.WordTrace tailWord_3280666 prefixEnd_3280666 41594037650942385503395 := by
  unfold tailWord_3280666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29913929783178712497673463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79770479421809899993795901 29913929783178712497673463)
  ·
    refine ⟨44870894674768068746510195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29913929783178712497673463 44870894674768068746510195)
    ·
      refine ⟨67306342012152103119765293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44870894674768068746510195 67306342012152103119765293)
      ·
        refine ⟨25239878254557038669911985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67306342012152103119765293 25239878254557038669911985)
        ·
          refine ⟨18929908690917779002433989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25239878254557038669911985 18929908690917779002433989)
          ·
            refine ⟨3549357879547083562956373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18929908690917779002433989 3549357879547083562956373)
            ·
              refine ⟨41594037650942385503395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3549357879547083562956373 41594037650942385503395)
              ·
                rfl

theorem cell22_3280666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 8].length) (baseStart_3280666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280666 prefixEnd_3280666 := by exact prefixLift 3280666
  have htrace : WordTrace (prefixWord ++ tailWord_3280666) baseStart_3280666 baseEnd_3280666 := by
    simpa [prefixWord, tailWord_3280666, baseEnd_3280666] using wordTrace_append hprefix tailTrace_3280666
  have hstable : (prefixWord ++ tailWord_3280666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280666).length < 2 ^ (prefixWord ++ tailWord_3280666).sum := by decide
  have hdescent : baseEnd_3280666 < baseStart_3280666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280775 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3280775 : Nat := 118140960795 + 3280775 * 2 ^ 59
def prefixEnd_3280775 : Nat := 4983230072969 + 3 ^ 40 * 3280775 * 2
def baseEnd_3280775 : Nat := 1123076329503004457616331

theorem tailTrace_3280775 : CollatzResearch.WordTrace tailWord_3280775 prefixEnd_3280775 1123076329503004457616331 := by
  unfold tailWord_3280775
  simp only [CollatzResearch.WordTrace]
  refine ⟨119659694689319961606411779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79773129792879974404274519 119659694689319961606411779)
  ·
    refine ⟨179489542033979942409617669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119659694689319961606411779 179489542033979942409617669)
    ·
      refine ⟨33654289131371239201803313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179489542033979942409617669 33654289131371239201803313)
      ·
        refine ⟨25240716848528429401352485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33654289131371239201803313 25240716848528429401352485)
        ·
          refine ⟨4732634409099080512753591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25240716848528429401352485 4732634409099080512753591)
          ·
            refine ⟨7098951613648620769130387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732634409099080512753591 7098951613648620769130387)
            ·
              refine ⟨10648427420472931153695581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098951613648620769130387 10648427420472931153695581)
              ·
                refine ⟨3993160282677349182635843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10648427420472931153695581 3993160282677349182635843)
                ·
                  refine ⟨5989740424016023773953765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993160282677349182635843 5989740424016023773953765)
                  ·
                    refine ⟨1123076329503004457616331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989740424016023773953765 1123076329503004457616331)
                    ·
                      rfl

theorem cell22_3280775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3280775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280775 prefixEnd_3280775 := by exact prefixLift 3280775
  have htrace : WordTrace (prefixWord ++ tailWord_3280775) baseStart_3280775 baseEnd_3280775 := by
    simpa [prefixWord, tailWord_3280775, baseEnd_3280775] using wordTrace_append hprefix tailTrace_3280775
  have hstable : (prefixWord ++ tailWord_3280775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280775).length < 2 ^ (prefixWord ++ tailWord_3280775).sum := by decide
  have hdescent : baseEnd_3280775 < baseStart_3280775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280908 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_3280908 : Nat := 118140960795 + 3280908 * 2 ^ 59
def prefixEnd_3280908 : Nat := 4983230072969 + 3 ^ 40 * 3280908 * 2
def baseEnd_3280908 : Nat := 374373952707012148013641

theorem tailTrace_3280908 : CollatzResearch.WordTrace tailWord_3280908 prefixEnd_3280908 374373952707012148013641 := by
  unfold tailWord_3280908
  simp only [CollatzResearch.WordTrace]
  refine ⟨59832272798919062660501689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79776363731892083547335585 59832272798919062660501689)
  ·
    refine ⟨44874204599189296995376267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59832272798919062660501689 44874204599189296995376267)
    ·
      refine ⟨67311306898783945493064401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44874204599189296995376267 67311306898783945493064401)
      ·
        refine ⟨50483480174087959119798301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67311306898783945493064401 50483480174087959119798301)
        ·
          refine ⟨18931305065282984669924363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50483480174087959119798301 18931305065282984669924363)
          ·
            refine ⟨28396957597924477004886545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931305065282984669924363 28396957597924477004886545)
            ·
              refine ⟨21297718198443357753664909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28396957597924477004886545 21297718198443357753664909)
              ·
                refine ⟨7986644324416259157624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21297718198443357753664909 7986644324416259157624341)
                ·
                  refine ⟨374373952707012148013641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7986644324416259157624341 374373952707012148013641)
                  ·
                    rfl

theorem cell22_3280908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_3280908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280908 prefixEnd_3280908 := by exact prefixLift 3280908
  have htrace : WordTrace (prefixWord ++ tailWord_3280908) baseStart_3280908 baseEnd_3280908 := by
    simpa [prefixWord, tailWord_3280908, baseEnd_3280908] using wordTrace_append hprefix tailTrace_3280908
  have hstable : (prefixWord ++ tailWord_3280908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280908).length < 2 ^ (prefixWord ++ tailWord_3280908).sum := by decide
  have hdescent : baseEnd_3280908 < baseStart_3280908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280925 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 6]
def baseStart_3280925 : Nat := 118140960795 + 3280925 * 2 ^ 59
def prefixEnd_3280925 : Nat := 4983230072969 + 3 ^ 40 * 3280925 * 2
def baseEnd_3280925 : Nat := 374375892522818022121957

theorem tailTrace_3280925 : CollatzResearch.WordTrace tailWord_3280925 prefixEnd_3280925 374375892522818022121957 := by
  unfold tailWord_3280925
  simp only [CollatzResearch.WordTrace]
  refine ⟨119665165638776537224372229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79776777092517691482914819 119665165638776537224372229)
  ·
    refine ⟨22437218557270600729569793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119665165638776537224372229 22437218557270600729569793)
    ·
      refine ⟨16827913917952950547177345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22437218557270600729569793 16827913917952950547177345)
      ·
        refine ⟨12620935438464712910383009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16827913917952950547177345 12620935438464712910383009)
        ·
          refine ⟨9465701578848534682787257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12620935438464712910383009 9465701578848534682787257)
          ·
            refine ⟨7099276184136401012090443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9465701578848534682787257 7099276184136401012090443)
            ·
              refine ⟨10648914276204601518135665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099276184136401012090443 10648914276204601518135665)
              ·
                refine ⟨7986685707153451138601749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10648914276204601518135665 7986685707153451138601749)
                ·
                  refine ⟨374375892522818022121957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7986685707153451138601749 374375892522818022121957)
                  ·
                    rfl

theorem cell22_3280925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_3280925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280925 prefixEnd_3280925 := by exact prefixLift 3280925
  have htrace : WordTrace (prefixWord ++ tailWord_3280925) baseStart_3280925 baseEnd_3280925 := by
    simpa [prefixWord, tailWord_3280925, baseEnd_3280925] using wordTrace_append hprefix tailTrace_3280925
  have hstable : (prefixWord ++ tailWord_3280925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280925).length < 2 ^ (prefixWord ++ tailWord_3280925).sum := by decide
  have hdescent : baseEnd_3280925 < baseStart_3280925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280942 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3280942 : Nat := 118140960795 + 3280942 * 2 ^ 59
def prefixEnd_3280942 : Nat := 4983230072969 + 3 ^ 40 * 3280942 * 2
def baseEnd_3280942 : Nat := 374377832338623896230273

theorem tailTrace_3280942 : CollatzResearch.WordTrace tailWord_3280942 prefixEnd_3280942 374377832338623896230273 := by
  unfold tailWord_3280942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958223209964368640967635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79777190453143299418494053 14958223209964368640967635)
  ·
    refine ⟨22437334814946552961451453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14958223209964368640967635 22437334814946552961451453)
    ·
      refine ⟨8414000555604957360544295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22437334814946552961451453 8414000555604957360544295)
      ·
        refine ⟨12621000833407436040816443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8414000555604957360544295 12621000833407436040816443)
        ·
          refine ⟨18931501250111154061224665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12621000833407436040816443 18931501250111154061224665)
          ·
            refine ⟨14198625937583365545918499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18931501250111154061224665 14198625937583365545918499)
            ·
              refine ⟨21297938906375048318877749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14198625937583365545918499 21297938906375048318877749)
              ·
                refine ⟨1996681772472660779894789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21297938906375048318877749 1996681772472660779894789)
                ·
                  refine ⟨374377832338623896230273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996681772472660779894789 374377832338623896230273)
                  ·
                    rfl

theorem cell22_3280942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3280942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280942 prefixEnd_3280942 := by exact prefixLift 3280942
  have htrace : WordTrace (prefixWord ++ tailWord_3280942) baseStart_3280942 baseEnd_3280942 := by
    simpa [prefixWord, tailWord_3280942, baseEnd_3280942] using wordTrace_append hprefix tailTrace_3280942
  have hstable : (prefixWord ++ tailWord_3280942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280942).length < 2 ^ (prefixWord ++ tailWord_3280942).sum := by decide
  have hdescent : baseEnd_3280942 < baseStart_3280942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280974 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3280974 : Nat := 118140960795 + 3280974 * 2 ^ 59
def prefixEnd_3280974 : Nat := 4983230072969 + 3 ^ 40 * 3280974 * 2
def baseEnd_3280974 : Nat := 1123144451269834271890721

theorem tailTrace_3280974 : CollatzResearch.WordTrace tailWord_3280974 prefixEnd_3280974 1123144451269834271890721 := by
  unfold tailWord_3280974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958369101949877324113247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79777968543732679061937317 14958369101949877324113247)
  ·
    refine ⟨22437553652924815986169871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14958369101949877324113247 22437553652924815986169871)
    ·
      refine ⟨33656330479387223979254807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22437553652924815986169871 33656330479387223979254807)
      ·
        refine ⟨50484495719080835968882211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33656330479387223979254807 50484495719080835968882211)
        ·
          refine ⟨75726743578621253953323317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50484495719080835968882211 75726743578621253953323317)
          ·
            refine ⟨7099382210495742558124061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75726743578621253953323317 7099382210495742558124061)
            ·
              refine ⟨2662268328935903459296523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7099382210495742558124061 2662268328935903459296523)
              ·
                refine ⟨3993402493403855188944785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662268328935903459296523 3993402493403855188944785)
                ·
                  refine ⟨2995051870052891391708589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3993402493403855188944785 2995051870052891391708589)
                  ·
                    refine ⟨1123144451269834271890721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995051870052891391708589 1123144451269834271890721)
                    ·
                      rfl

theorem cell22_3280974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3280974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280974 prefixEnd_3280974 := by exact prefixLift 3280974
  have htrace : WordTrace (prefixWord ++ tailWord_3280974) baseStart_3280974 baseEnd_3280974 := by
    simpa [prefixWord, tailWord_3280974, baseEnd_3280974] using wordTrace_append hprefix tailTrace_3280974
  have hstable : (prefixWord ++ tailWord_3280974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280974).length < 2 ^ (prefixWord ++ tailWord_3280974).sum := by decide
  have hdescent : baseEnd_3280974 < baseStart_3280974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280983 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3280983 : Nat := 118140960795 + 3280983 * 2 ^ 59
def prefixEnd_3280983 : Nat := 4983230072969 + 3 ^ 40 * 3280983 * 2
def baseEnd_3280983 : Nat := 1123147532153761248415693

theorem tailTrace_3280983 : CollatzResearch.WordTrace tailWord_3280983 prefixEnd_3280983 1123147532153761248415693 := by
  unfold tailWord_3280983
  simp only [CollatzResearch.WordTrace]
  refine ⟨119667281072566413129983603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79778187381710942086655735 119667281072566413129983603)
  ·
    refine ⟨179500921608849619694975405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119667281072566413129983603 179500921608849619694975405)
    ·
      refine ⟨67312845603318607385615777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179500921608849619694975405 67312845603318607385615777)
      ·
        refine ⟨50484634202488955539211833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67312845603318607385615777 50484634202488955539211833)
        ·
          refine ⟨37863475651866716654408875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50484634202488955539211833 37863475651866716654408875)
          ·
            refine ⟨56795213477800074981613313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37863475651866716654408875 56795213477800074981613313)
            ·
              refine ⟨42596410108350056236209985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56795213477800074981613313 42596410108350056236209985)
              ·
                refine ⟨31947307581262542177157489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42596410108350056236209985 31947307581262542177157489)
                ·
                  refine ⟨23960480685946906632868117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31947307581262542177157489 23960480685946906632868117)
                  ·
                    refine ⟨1123147532153761248415693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23960480685946906632868117 1123147532153761248415693)
                    ·
                      rfl

theorem cell22_3280983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3280983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280983 prefixEnd_3280983 := by exact prefixLift 3280983
  have htrace : WordTrace (prefixWord ++ tailWord_3280983) baseStart_3280983 baseEnd_3280983 := by
    simpa [prefixWord, tailWord_3280983, baseEnd_3280983] using wordTrace_append hprefix tailTrace_3280983
  have hstable : (prefixWord ++ tailWord_3280983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280983).length < 2 ^ (prefixWord ++ tailWord_3280983).sum := by decide
  have hdescent : baseEnd_3280983 < baseStart_3280983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280985 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_3280985 : Nat := 118140960795 + 3280985 * 2 ^ 59
def prefixEnd_3280985 : Nat := 4983230072969 + 3 ^ 40 * 3280985 * 2
def baseEnd_3280985 : Nat := 1123148216794633909865687

theorem tailTrace_3280985 : CollatzResearch.WordTrace tailWord_3280985 prefixEnd_3280985 1123148216794633909865687 := by
  unfold tailWord_3280985
  simp only [CollatzResearch.WordTrace]
  refine ⟨119667354018559167471556409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79778236012372778314370939 119667354018559167471556409)
  ·
    refine ⟨89750515513919375603667307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119667354018559167471556409 89750515513919375603667307)
    ·
      refine ⟨134625773270879063405500961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89750515513919375603667307 134625773270879063405500961)
      ·
        refine ⟨100969329953159297554125721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134625773270879063405500961 100969329953159297554125721)
        ·
          refine ⟨75726997464869473165594291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100969329953159297554125721 75726997464869473165594291)
          ·
            refine ⟨113590496197304209748391437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75726997464869473165594291 113590496197304209748391437)
            ·
              refine ⟨42596436073989078655646789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113590496197304209748391437 42596436073989078655646789)
              ·
                refine ⟨7986831763872952247933773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42596436073989078655646789 7986831763872952247933773)
                ·
                  refine ⟨2995061911452357092975165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7986831763872952247933773 2995061911452357092975165)
                  ·
                    refine ⟨1123148216794633909865687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995061911452357092975165 1123148216794633909865687)
                    ·
                      rfl

theorem cell22_3280985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_3280985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3280985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3280985 prefixEnd_3280985 := by exact prefixLift 3280985
  have htrace : WordTrace (prefixWord ++ tailWord_3280985) baseStart_3280985 baseEnd_3280985 := by
    simpa [prefixWord, tailWord_3280985, baseEnd_3280985] using wordTrace_append hprefix tailTrace_3280985
  have hstable : (prefixWord ++ tailWord_3280985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280985).length < 2 ^ (prefixWord ++ tailWord_3280985).sum := by decide
  have hdescent : baseEnd_3280985 < baseStart_3280985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281032 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_3281032 : Nat := 118140960795 + 3281032 * 2 ^ 59
def prefixEnd_3281032 : Nat := 4983230072969 + 3 ^ 40 * 3281032 * 2
def baseEnd_3281032 : Nat := 374388101951713817980181

theorem tailTrace_3281032 : CollatzResearch.WordTrace tailWord_3281032 prefixEnd_3281032 374388101951713817980181 := by
  unfold tailWord_3281032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59834534124694447249258675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79779378832925929665678233 59834534124694447249258675)
  ·
    refine ⟨89751801187041670873888013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59834534124694447249258675 89751801187041670873888013)
    ·
      refine ⟨33656925445140626577708005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89751801187041670873888013 33656925445140626577708005)
      ·
        refine ⟨6310673520963867483320251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33656925445140626577708005 6310673520963867483320251)
        ·
          refine ⟨9466010281445801224980377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310673520963867483320251 9466010281445801224980377)
          ·
            refine ⟨7099507711084350918735283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9466010281445801224980377 7099507711084350918735283)
            ·
              refine ⟨10649261566626526378102925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099507711084350918735283 10649261566626526378102925)
              ·
                refine ⟨3993473087484947391788597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10649261566626526378102925 3993473087484947391788597)
                ·
                  refine ⟨374388101951713817980181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3993473087484947391788597 374388101951713817980181)
                  ·
                    rfl

theorem cell22_3281032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_3281032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281032 prefixEnd_3281032 := by exact prefixLift 3281032
  have htrace : WordTrace (prefixWord ++ tailWord_3281032) baseStart_3281032 baseEnd_3281032 := by
    simpa [prefixWord, tailWord_3281032, baseEnd_3281032] using wordTrace_append hprefix tailTrace_3281032
  have hstable : (prefixWord ++ tailWord_3281032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281032).length < 2 ^ (prefixWord ++ tailWord_3281032).sum := by decide
  have hdescent : baseEnd_3281032 < baseStart_3281032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281043 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 8]
def baseStart_3281043 : Nat := 118140960795 + 3281043 * 2 ^ 59
def prefixEnd_3281043 : Nat := 4983230072969 + 3 ^ 40 * 3281043 * 2
def baseEnd_3281043 : Nat := 374389357126647030638503

theorem tailTrace_3281043 : CollatzResearch.WordTrace tailWord_3281043 prefixEnd_3281043 374389357126647030638503 := by
  unfold tailWord_3281043
  simp only [CollatzResearch.WordTrace]
  refine ⟨119669469452349043377167783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79779646301566028918111855 119669469452349043377167783)
  ·
    refine ⟨179504204178523565065751675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119669469452349043377167783 179504204178523565065751675)
    ·
      refine ⟨269256306267785347598627513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179504204178523565065751675 269256306267785347598627513)
      ·
        refine ⟨201942229700839010698970635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269256306267785347598627513 201942229700839010698970635)
        ·
          refine ⟨302913344551258516048455953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201942229700839010698970635 302913344551258516048455953)
          ·
            refine ⟨227185008413443887036341965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302913344551258516048455953 227185008413443887036341965)
            ·
              refine ⟨85194378155041457638628237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227185008413443887036341965 85194378155041457638628237)
              ·
                refine ⟨31947891808140546614485589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85194378155041457638628237 31947891808140546614485589)
                ·
                  refine ⟨374389357126647030638503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31947891808140546614485589 374389357126647030638503)
                  ·
                    rfl

theorem cell22_3281043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_3281043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281043 prefixEnd_3281043 := by exact prefixLift 3281043
  have htrace : WordTrace (prefixWord ++ tailWord_3281043) baseStart_3281043 baseEnd_3281043 := by
    simpa [prefixWord, tailWord_3281043, baseEnd_3281043] using wordTrace_append hprefix tailTrace_3281043
  have hstable : (prefixWord ++ tailWord_3281043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281043).length < 2 ^ (prefixWord ++ tailWord_3281043).sum := by decide
  have hdescent : baseEnd_3281043 < baseStart_3281043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281045 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3281045 : Nat := 118140960795 + 3281045 * 2 ^ 59
def prefixEnd_3281045 : Nat := 4983230072969 + 3 ^ 40 * 3281045 * 2
def baseEnd_3281045 : Nat := 1123168756020813753365503

theorem tailTrace_3281045 : CollatzResearch.WordTrace tailWord_3281045 prefixEnd_3281045 1123168756020813753365503 := by
  unfold tailWord_3281045
  simp only [CollatzResearch.WordTrace]
  refine ⟨119669542398341797718740589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79779694932227865145827059 119669542398341797718740589)
  ·
    refine ⟨44876078399378174144527721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119669542398341797718740589 44876078399378174144527721)
    ·
      refine ⟨33657058799533630608395791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44876078399378174144527721 33657058799533630608395791)
      ·
        refine ⟨50485588199300445912593687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33657058799533630608395791 50485588199300445912593687)
        ·
          refine ⟨75728382298950668868890531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50485588199300445912593687 75728382298950668868890531)
          ·
            refine ⟨113592573448426003303335797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75728382298950668868890531 113592573448426003303335797)
            ·
              refine ⟨10649303760789937809687731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113592573448426003303335797 10649303760789937809687731)
              ·
                refine ⟨15973955641184906714531597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10649303760789937809687731 15973955641184906714531597)
                ·
                  refine ⟨5990233365444340017949349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15973955641184906714531597 5990233365444340017949349)
                  ·
                    refine ⟨1123168756020813753365503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990233365444340017949349 1123168756020813753365503)
                    ·
                      rfl

theorem cell22_3281045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3281045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281045 prefixEnd_3281045 := by exact prefixLift 3281045
  have htrace : WordTrace (prefixWord ++ tailWord_3281045) baseStart_3281045 baseEnd_3281045 := by
    simpa [prefixWord, tailWord_3281045, baseEnd_3281045] using wordTrace_append hprefix tailTrace_3281045
  have hstable : (prefixWord ++ tailWord_3281045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281045).length < 2 ^ (prefixWord ++ tailWord_3281045).sum := by decide
  have hdescent : baseEnd_3281045 < baseStart_3281045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281092 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3281092 : Nat := 118140960795 + 3281092 * 2 ^ 59
def prefixEnd_3281092 : Nat := 4983230072969 + 3 ^ 40 * 3281092 * 2
def baseEnd_3281092 : Nat := 1123184845081321297440359

theorem tailTrace_3281092 : CollatzResearch.WordTrace tailWord_3281092 prefixEnd_3281092 1123184845081321297440359 := by
  unfold tailWord_3281092
  simp only [CollatzResearch.WordTrace]
  refine ⟨59835628314585762372850765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79780837752781016497134353 59835628314585762372850765)
  ·
    refine ⟨22438360617969660889819037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59835628314585762372850765 22438360617969660889819037)
    ·
      refine ⟨8414385231738622833682139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22438360617969660889819037 8414385231738622833682139)
      ·
        refine ⟨12621577847607934250523209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8414385231738622833682139 12621577847607934250523209)
        ·
          refine ⟨9466183385705950687892407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12621577847607934250523209 9466183385705950687892407)
          ·
            refine ⟨14199275078558926031838611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466183385705950687892407 14199275078558926031838611)
            ·
              refine ⟨21298912617838389047757917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199275078558926031838611 21298912617838389047757917)
              ·
                refine ⟨7987092231689395892909219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21298912617838389047757917 7987092231689395892909219)
                ·
                  refine ⟨11980638347534093839363829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7987092231689395892909219 11980638347534093839363829)
                  ·
                    refine ⟨1123184845081321297440359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11980638347534093839363829 1123184845081321297440359)
                    ·
                      rfl

theorem cell22_3281092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3281092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281092 prefixEnd_3281092 := by exact prefixLift 3281092
  have htrace : WordTrace (prefixWord ++ tailWord_3281092) baseStart_3281092 baseEnd_3281092 := by
    simpa [prefixWord, tailWord_3281092, baseEnd_3281092] using wordTrace_append hprefix tailTrace_3281092
  have hstable : (prefixWord ++ tailWord_3281092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281092).length < 2 ^ (prefixWord ++ tailWord_3281092).sum := by decide
  have hdescent : baseEnd_3281092 < baseStart_3281092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281137 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_3281137 : Nat := 118140960795 + 3281137 * 2 ^ 59
def prefixEnd_3281137 : Nat := 4983230072969 + 3 ^ 40 * 3281137 * 2
def baseEnd_3281137 : Nat := 1123200249500956180065221

theorem tailTrace_3281137 : CollatzResearch.WordTrace tailWord_3281137 prefixEnd_3281137 1123200249500956180065221 := by
  unfold tailWord_3281137
  simp only [CollatzResearch.WordTrace]
  refine ⟨119672897914008497431089665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79781931942672331620726443 119672897914008497431089665)
  ·
    refine ⟨89754673435506373073317249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119672897914008497431089665 89754673435506373073317249)
    ·
      refine ⟨67316005076629779804987937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89754673435506373073317249 67316005076629779804987937)
      ·
        refine ⟨50487003807472334853740953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67316005076629779804987937 50487003807472334853740953)
        ·
          refine ⟨37865252855604251140305715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50487003807472334853740953 37865252855604251140305715)
          ·
            refine ⟨56797879283406376710458573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37865252855604251140305715 56797879283406376710458573)
            ·
              refine ⟨21299204731277391266421965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56797879283406376710458573 21299204731277391266421965)
              ·
                refine ⟨7987201774229021724908237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21299204731277391266421965 7987201774229021724908237)
                ·
                  refine ⟨2995200665335883146840589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7987201774229021724908237 2995200665335883146840589)
                  ·
                    refine ⟨1123200249500956180065221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995200665335883146840589 1123200249500956180065221)
                    ·
                      rfl

theorem cell22_3281137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_3281137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281137 prefixEnd_3281137 := by exact prefixLift 3281137
  have htrace : WordTrace (prefixWord ++ tailWord_3281137) baseStart_3281137 baseEnd_3281137 := by
    simpa [prefixWord, tailWord_3281137, baseEnd_3281137] using wordTrace_append hprefix tailTrace_3281137
  have hstable : (prefixWord ++ tailWord_3281137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281137).length < 2 ^ (prefixWord ++ tailWord_3281137).sum := by decide
  have hdescent : baseEnd_3281137 < baseStart_3281137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281156 : List Nat := [2, 3, 2, 2, 4, 1, 2, 6]
def baseStart_3281156 : Nat := 118140960795 + 3281156 * 2 ^ 59
def prefixEnd_3281156 : Nat := 4983230072969 + 3 ^ 40 * 3281156 * 2
def baseEnd_3281156 : Nat := 124800750398805162648907

theorem tailTrace_3281156 : CollatzResearch.WordTrace tailWord_3281156 prefixEnd_3281156 124800750398805162648907 := by
  unfold tailWord_3281156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59836795450469831838015661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79782393933959775784020881 59836795450469831838015661)
  ·
    refine ⟨22438798293926186939255873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59836795450469831838015661 22438798293926186939255873)
    ·
      refine ⟨16829098720444640204441905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22438798293926186939255873 16829098720444640204441905)
      ·
        refine ⟨12621824040333480153331429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16829098720444640204441905 12621824040333480153331429)
        ·
          refine ⟨2366592007562527528749643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12621824040333480153331429 2366592007562527528749643)
          ·
            refine ⟨3549888011343791293124465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366592007562527528749643 3549888011343791293124465)
            ·
              refine ⟨2662416008507843469843349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549888011343791293124465 2662416008507843469843349)
              ·
                refine ⟨124800750398805162648907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2662416008507843469843349 124800750398805162648907)
                ·
                  rfl

theorem cell22_3281156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_3281156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281156 prefixEnd_3281156 := by exact prefixLift 3281156
  have htrace : WordTrace (prefixWord ++ tailWord_3281156) baseStart_3281156 baseEnd_3281156 := by
    simpa [prefixWord, tailWord_3281156, baseEnd_3281156] using wordTrace_append hprefix tailTrace_3281156
  have hstable : (prefixWord ++ tailWord_3281156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281156).length < 2 ^ (prefixWord ++ tailWord_3281156).sum := by decide
  have hdescent : baseEnd_3281156 < baseStart_3281156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281188 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3281188 : Nat := 118140960795 + 3281188 * 2 ^ 59
def prefixEnd_3281188 : Nat := 4983230072969 + 3 ^ 40 * 3281188 * 2
def baseEnd_3281188 : Nat := 1123217707843209047040065

theorem tailTrace_3281188 : CollatzResearch.WordTrace tailWord_3281188 prefixEnd_3281188 1123217707843209047040065 := by
  unfold tailWord_3281188
  simp only [CollatzResearch.WordTrace]
  refine ⟨59837379018411866570598109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79783172024549155427464145 59837379018411866570598109)
  ·
    refine ⟨22439017131904449963974291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59837379018411866570598109 22439017131904449963974291)
    ·
      refine ⟨33658525697856674945961437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22439017131904449963974291 33658525697856674945961437)
      ·
        refine ⟨12621947136696253104735539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33658525697856674945961437 12621947136696253104735539)
        ·
          refine ⟨18932920705044379657103309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12621947136696253104735539 18932920705044379657103309)
          ·
            refine ⟨7099845264391642371413741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18932920705044379657103309 7099845264391642371413741)
            ·
              refine ⟨2662441974146865889280153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7099845264391642371413741 2662441974146865889280153)
              ·
                refine ⟨1996831480610149416960115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662441974146865889280153 1996831480610149416960115)
                ·
                  refine ⟨2995247220915224125440173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996831480610149416960115 2995247220915224125440173)
                  ·
                    refine ⟨1123217707843209047040065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995247220915224125440173 1123217707843209047040065)
                    ·
                      rfl

theorem cell22_3281188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3281188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281188 prefixEnd_3281188 := by exact prefixLift 3281188
  have htrace : WordTrace (prefixWord ++ tailWord_3281188) baseStart_3281188 baseEnd_3281188 := by
    simpa [prefixWord, tailWord_3281188, baseEnd_3281188] using wordTrace_append hprefix tailTrace_3281188
  have hstable : (prefixWord ++ tailWord_3281188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281188).length < 2 ^ (prefixWord ++ tailWord_3281188).sum := by decide
  have hdescent : baseEnd_3281188 < baseStart_3281188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281201 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 5]
def baseStart_3281201 : Nat := 118140960795 + 3281201 * 2 ^ 59
def prefixEnd_3281201 : Nat := 4983230072969 + 3 ^ 40 * 3281201 * 2
def baseEnd_3281201 : Nat := 374407386002960448821675

theorem tailTrace_3281201 : CollatzResearch.WordTrace tailWord_3281201 prefixEnd_3281201 374407386002960448821675 := by
  unfold tailWord_3281201
  simp only [CollatzResearch.WordTrace]
  refine ⟨119675232185776636361419457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79783488123851090907612971 119675232185776636361419457)
  ·
    refine ⟨89756424139332477271064593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119675232185776636361419457 89756424139332477271064593)
    ·
      refine ⟨67317318104499357953298445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89756424139332477271064593 67317318104499357953298445)
      ·
        refine ⟨25243994289187259232486917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67317318104499357953298445 25243994289187259232486917)
        ·
          refine ⟨4733248929222611106091297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25243994289187259232486917 4733248929222611106091297)
          ·
            refine ⟨3549936696916958329568473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733248929222611106091297 3549936696916958329568473)
            ·
              refine ⟨2662452522687718747176355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549936696916958329568473 2662452522687718747176355)
              ·
                refine ⟨3993678784031578120764533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662452522687718747176355 3993678784031578120764533)
                ·
                  refine ⟨374407386002960448821675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3993678784031578120764533 374407386002960448821675)
                  ·
                    rfl

theorem cell22_3281201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_3281201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281201 prefixEnd_3281201 := by exact prefixLift 3281201
  have htrace : WordTrace (prefixWord ++ tailWord_3281201) baseStart_3281201 baseEnd_3281201 := by
    simpa [prefixWord, tailWord_3281201, baseEnd_3281201] using wordTrace_append hprefix tailTrace_3281201
  have hstable : (prefixWord ++ tailWord_3281201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281201).length < 2 ^ (prefixWord ++ tailWord_3281201).sum := by decide
  have hdescent : baseEnd_3281201 < baseStart_3281201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281214 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3281214 : Nat := 118140960795 + 3281214 * 2 ^ 59
def prefixEnd_3281214 : Nat := 4983230072969 + 3 ^ 40 * 3281214 * 2
def baseEnd_3281214 : Nat := 1123226608174553645889985

theorem tailTrace_3281214 : CollatzResearch.WordTrace tailWord_3281214 prefixEnd_3281214 1123226608174553645889985 := by
  unfold tailWord_3281214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959463291841192447705337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79783804223153026387761797 14959463291841192447705337)
  ·
    refine ⟨11219597468880894335779003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14959463291841192447705337 11219597468880894335779003)
    ·
      refine ⟨16829396203321341503668505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219597468880894335779003 16829396203321341503668505)
      ·
        refine ⟨12622047152491006127751379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16829396203321341503668505 12622047152491006127751379)
        ·
          refine ⟨18933070728736509191627069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622047152491006127751379 18933070728736509191627069)
          ·
            refine ⟨7099901523276190946860151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18933070728736509191627069 7099901523276190946860151)
            ·
              refine ⟨10649852284914286420290227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099901523276190946860151 10649852284914286420290227)
              ·
                refine ⟨15974778427371429630435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10649852284914286420290227 15974778427371429630435341)
                ·
                  refine ⟨5990541910264286111413253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15974778427371429630435341 5990541910264286111413253)
                  ·
                    refine ⟨1123226608174553645889985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990541910264286111413253 1123226608174553645889985)
                    ·
                      rfl

theorem cell22_3281214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3281214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281214 prefixEnd_3281214 := by exact prefixLift 3281214
  have htrace : WordTrace (prefixWord ++ tailWord_3281214) baseStart_3281214 baseEnd_3281214 := by
    simpa [prefixWord, tailWord_3281214, baseEnd_3281214] using wordTrace_append hprefix tailTrace_3281214
  have hstable : (prefixWord ++ tailWord_3281214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281214).length < 2 ^ (prefixWord ++ tailWord_3281214).sum := by decide
  have hdescent : baseEnd_3281214 < baseStart_3281214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 4, 3]
def baseStart_3281227 : Nat := 118140960795 + 3281227 * 2 ^ 59
def prefixEnd_3281227 : Nat := 4983230072969 + 3 ^ 40 * 3281227 * 2
def baseEnd_3281227 : Nat := 1123231058340225945314945

theorem tailTrace_3281227 : CollatzResearch.WordTrace tailWord_3281227 prefixEnd_3281227 1123231058340225945314945 := by
  unfold tailWord_3281227
  simp only [CollatzResearch.WordTrace]
  refine ⟨119676180483682442801865935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79784120322454961867910623 119676180483682442801865935)
  ·
    refine ⟨179514270725523664202798903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119676180483682442801865935 179514270725523664202798903)
    ·
      refine ⟨269271406088285496304198355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179514270725523664202798903 269271406088285496304198355)
      ·
        refine ⟨403907109132428244456297533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269271406088285496304198355 403907109132428244456297533)
        ·
          refine ⟨151465165924660591671111575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403907109132428244456297533 151465165924660591671111575)
          ·
            refine ⟨227197748886990887506667363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151465165924660591671111575 227197748886990887506667363)
            ·
              refine ⟨340796623330486331260001045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227197748886990887506667363 340796623330486331260001045)
              ·
                refine ⟨15974841718616546777812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340796623330486331260001045 15974841718616546777812549)
                ·
                  refine ⟨2995282822240602520839853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15974841718616546777812549 2995282822240602520839853)
                  ·
                    refine ⟨1123231058340225945314945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995282822240602520839853 1123231058340225945314945)
                    ·
                      rfl

theorem cell22_3281227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].length) (baseStart_3281227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281227 prefixEnd_3281227 := by exact prefixLift 3281227
  have htrace : WordTrace (prefixWord ++ tailWord_3281227) baseStart_3281227 baseEnd_3281227 := by
    simpa [prefixWord, tailWord_3281227, baseEnd_3281227] using wordTrace_append hprefix tailTrace_3281227
  have hstable : (prefixWord ++ tailWord_3281227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281227).length < 2 ^ (prefixWord ++ tailWord_3281227).sum := by decide
  have hdescent : baseEnd_3281227 < baseStart_3281227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281282 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3281282 : Nat := 118140960795 + 3281282 * 2 ^ 59
def prefixEnd_3281282 : Nat := 4983230072969 + 3 ^ 40 * 3281282 * 2
def baseEnd_3281282 : Nat := 1123249885964224135189777

theorem tailTrace_3281282 : CollatzResearch.WordTrace tailWord_3281282 prefixEnd_3281282 1123249885964224135189777 := by
  unfold tailWord_3281282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29919546624620796798779525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79785457665655458130078733 29919546624620796798779525)
  ·
    refine ⟨5609914992116399399771161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29919546624620796798779525 5609914992116399399771161)
    ·
      refine ⟨4207436244087299549828371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5609914992116399399771161 4207436244087299549828371)
      ·
        refine ⟨6311154366130949324742557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207436244087299549828371 6311154366130949324742557)
        ·
          refine ⟨2366682887299105996778459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6311154366130949324742557 2366682887299105996778459)
          ·
            refine ⟨3550024330948658995167689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366682887299105996778459 3550024330948658995167689)
            ·
              refine ⟨2662518248211494246375767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550024330948658995167689 2662518248211494246375767)
              ·
                refine ⟨3993777372317241369563651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662518248211494246375767 3993777372317241369563651)
                ·
                  refine ⟨5990666058475862054345477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993777372317241369563651 5990666058475862054345477)
                  ·
                    refine ⟨1123249885964224135189777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990666058475862054345477 1123249885964224135189777)
                    ·
                      rfl

theorem cell22_3281282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3281282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281282 prefixEnd_3281282 := by exact prefixLift 3281282
  have htrace : WordTrace (prefixWord ++ tailWord_3281282) baseStart_3281282 baseEnd_3281282 := by
    simpa [prefixWord, tailWord_3281282, baseEnd_3281282] using wordTrace_append hprefix tailTrace_3281282
  have hstable : (prefixWord ++ tailWord_3281282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281282).length < 2 ^ (prefixWord ++ tailWord_3281282).sum := by decide
  have hdescent : baseEnd_3281282 < baseStart_3281282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281306 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_3281306 : Nat := 118140960795 + 3281306 * 2 ^ 59
def prefixEnd_3281306 : Nat := 4983230072969 + 3 ^ 40 * 3281306 * 2
def baseEnd_3281306 : Nat := 1123258101654696072589703

theorem tailTrace_3281306 : CollatzResearch.WordTrace tailWord_3281306 prefixEnd_3281306 1123258101654696072589703 := by
  unfold tailWord_3281306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29919765462599059823497943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79786041233597492862661181 29919765462599059823497943)
  ·
    refine ⟨44879648193898589735246915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29919765462599059823497943 44879648193898589735246915)
    ·
      refine ⟨67319472290847884602870373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44879648193898589735246915 67319472290847884602870373)
      ·
        refine ⟨12622401054533978363038195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67319472290847884602870373 12622401054533978363038195)
        ·
          refine ⟨18933601581800967544557293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622401054533978363038195 18933601581800967544557293)
          ·
            refine ⟨7100100593175362829208985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18933601581800967544557293 7100100593175362829208985)
            ·
              refine ⟨5325075444881522121906739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100100593175362829208985 5325075444881522121906739)
              ·
                refine ⟨7987613167322283182860109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325075444881522121906739 7987613167322283182860109)
                ·
                  refine ⟨2995354937745856193572541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7987613167322283182860109 2995354937745856193572541)
                  ·
                    refine ⟨1123258101654696072589703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995354937745856193572541 1123258101654696072589703)
                    ·
                      rfl

theorem cell22_3281306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_3281306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281306 prefixEnd_3281306 := by exact prefixLift 3281306
  have htrace : WordTrace (prefixWord ++ tailWord_3281306) baseStart_3281306 baseEnd_3281306 := by
    simpa [prefixWord, tailWord_3281306, baseEnd_3281306] using wordTrace_append hprefix tailTrace_3281306
  have hstable : (prefixWord ++ tailWord_3281306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281306).length < 2 ^ (prefixWord ++ tailWord_3281306).sum := by decide
  have hdescent : baseEnd_3281306 < baseStart_3281306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281317 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3281317 : Nat := 118140960795 + 3281317 * 2 ^ 59
def prefixEnd_3281317 : Nat := 4983230072969 + 3 ^ 40 * 3281317 * 2
def baseEnd_3281317 : Nat := 1123261867179495710564669

theorem tailTrace_3281317 : CollatzResearch.WordTrace tailWord_3281317 prefixEnd_3281317 1123261867179495710564669 := by
  unfold tailWord_3281317
  simp only [CollatzResearch.WordTrace]
  refine ⟨119679463053356388172642205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79786308702237592115094803 119679463053356388172642205)
  ·
    refine ⟨44879798645008645564740827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119679463053356388172642205 44879798645008645564740827)
    ·
      refine ⟨67319697967512968347111241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44879798645008645564740827 67319697967512968347111241)
      ·
        refine ⟨50489773475634726260333431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67319697967512968347111241 50489773475634726260333431)
        ·
          refine ⟨75734660213452089390500147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50489773475634726260333431 75734660213452089390500147)
          ·
            refine ⟨113601990320178134085750221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75734660213452089390500147 113601990320178134085750221)
            ·
              refine ⟨42600746370066800282156333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113601990320178134085750221 42600746370066800282156333)
              ·
                refine ⟨15975279888775050105808625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42600746370066800282156333 15975279888775050105808625)
                ·
                  refine ⟨11981459916581287579356469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15975279888775050105808625 11981459916581287579356469)
                  ·
                    refine ⟨1123261867179495710564669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11981459916581287579356469 1123261867179495710564669)
                    ·
                      rfl

theorem cell22_3281317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3281317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281317 prefixEnd_3281317 := by exact prefixLift 3281317
  have htrace : WordTrace (prefixWord ++ tailWord_3281317) baseStart_3281317 baseEnd_3281317 := by
    simpa [prefixWord, tailWord_3281317, baseEnd_3281317] using wordTrace_append hprefix tailTrace_3281317
  have hstable : (prefixWord ++ tailWord_3281317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281317).length < 2 ^ (prefixWord ++ tailWord_3281317).sum := by decide
  have hdescent : baseEnd_3281317 < baseStart_3281317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281340 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3281340 : Nat := 118140960795 + 3281340 * 2 ^ 59
def prefixEnd_3281340 : Nat := 4983230072969 + 3 ^ 40 * 3281340 * 2
def baseEnd_3281340 : Nat := 1123269740549531317239599

theorem tailTrace_3281340 : CollatzResearch.WordTrace tailWord_3281340 prefixEnd_3281340 1123269740549531317239599 := by
  unfold tailWord_3281340
  simp only [CollatzResearch.WordTrace]
  refine ⟨59840150966136531550364737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79786867954848708733819649 59840150966136531550364737)
  ·
    refine ⟨44880113224602398662773553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59840150966136531550364737 44880113224602398662773553)
    ·
      refine ⟨33660084918451798997080165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44880113224602398662773553 33660084918451798997080165)
      ·
        refine ⟨6311265922209712311952531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33660084918451798997080165 6311265922209712311952531)
        ·
          refine ⟨9466898883314568467928797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311265922209712311952531 9466898883314568467928797)
          ·
            refine ⟨3550087081242963175473299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9466898883314568467928797 3550087081242963175473299)
            ·
              refine ⟨5325130621864444763209949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550087081242963175473299 5325130621864444763209949)
              ·
                refine ⟨1996923983199166786203731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325130621864444763209949 1996923983199166786203731)
                ·
                  refine ⟨2995385974798750179305597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996923983199166786203731 2995385974798750179305597)
                  ·
                    refine ⟨1123269740549531317239599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995385974798750179305597 1123269740549531317239599)
                    ·
                      rfl

theorem cell22_3281340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3281340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281340 prefixEnd_3281340 := by exact prefixLift 3281340
  have htrace : WordTrace (prefixWord ++ tailWord_3281340) baseStart_3281340 baseEnd_3281340 := by
    simpa [prefixWord, tailWord_3281340, baseEnd_3281340] using wordTrace_append hprefix tailTrace_3281340
  have hstable : (prefixWord ++ tailWord_3281340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281340).length < 2 ^ (prefixWord ++ tailWord_3281340).sum := by decide
  have hdescent : baseEnd_3281340 < baseStart_3281340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281366 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3281366 : Nat := 118140960795 + 3281366 * 2 ^ 59
def prefixEnd_3281366 : Nat := 4983230072969 + 3 ^ 40 * 3281366 * 2
def baseEnd_3281366 : Nat := 1123278640880875916089519

theorem tailTrace_3281366 : CollatzResearch.WordTrace tailWord_3281366 prefixEnd_3281366 1123278640880875916089519 := by
  unfold tailWord_3281366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480078139386179346323497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79787500153452579694117301 7480078139386179346323497)
  ·
    refine ⟨5610058604539634509742623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7480078139386179346323497 5610058604539634509742623)
    ·
      refine ⟨8415087906809451764613935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5610058604539634509742623 8415087906809451764613935)
      ·
        refine ⟨12622631860214177646920903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415087906809451764613935 12622631860214177646920903)
        ·
          refine ⟨18933947790321266470381355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622631860214177646920903 18933947790321266470381355)
          ·
            refine ⟨28400921685481899705572033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18933947790321266470381355 28400921685481899705572033)
            ·
              refine ⟨21300691264111424779179025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28400921685481899705572033 21300691264111424779179025)
              ·
                refine ⟨15975518448083568584384269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21300691264111424779179025 15975518448083568584384269)
                ·
                  refine ⟨5990819418031338219144101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15975518448083568584384269 5990819418031338219144101)
                  ·
                    refine ⟨1123278640880875916089519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990819418031338219144101 1123278640880875916089519)
                    ·
                      rfl

theorem cell22_3281366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3281366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281366 prefixEnd_3281366 := by exact prefixLift 3281366
  have htrace : WordTrace (prefixWord ++ tailWord_3281366) baseStart_3281366 baseEnd_3281366 := by
    simpa [prefixWord, tailWord_3281366, baseEnd_3281366] using wordTrace_append hprefix tailTrace_3281366
  have hstable : (prefixWord ++ tailWord_3281366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281366).length < 2 ^ (prefixWord ++ tailWord_3281366).sum := by decide
  have hdescent : baseEnd_3281366 < baseStart_3281366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281392 : List Nat := [2, 1, 1, 1, 3, 3, 1, 10]
def baseStart_3281392 : Nat := 118140960795 + 3281392 * 2 ^ 59
def prefixEnd_3281392 : Nat := 4983230072969 + 3 ^ 40 * 3281392 * 2
def baseEnd_3281392 : Nat := 124809726801357834993271

theorem tailTrace_3281392 : CollatzResearch.WordTrace tailWord_3281392 prefixEnd_3281392 124809726801357834993271 := by
  unfold tailWord_3281392
  simp only [CollatzResearch.WordTrace]
  refine ⟨59841099264042337990811215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79788132352056450654414953 59841099264042337990811215)
  ·
    refine ⟨89761648896063506986216823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59841099264042337990811215 89761648896063506986216823)
    ·
      refine ⟨134642473344095260479325235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89761648896063506986216823 134642473344095260479325235)
      ·
        refine ⟨201963710016142890718987853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134642473344095260479325235 201963710016142890718987853)
        ·
          refine ⟨75736391256053584019620445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201963710016142890718987853 75736391256053584019620445)
          ·
            refine ⟨28401146721020094007357667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75736391256053584019620445 28401146721020094007357667)
            ·
              refine ⟨42601720081530141011036501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28401146721020094007357667 42601720081530141011036501)
              ·
                refine ⟨124809726801357834993271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42601720081530141011036501 124809726801357834993271)
                ·
                  rfl

theorem cell22_3281392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_3281392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281392 prefixEnd_3281392 := by exact prefixLift 3281392
  have htrace : WordTrace (prefixWord ++ tailWord_3281392) baseStart_3281392 baseEnd_3281392 := by
    simpa [prefixWord, tailWord_3281392, baseEnd_3281392] using wordTrace_append hprefix tailTrace_3281392
  have hstable : (prefixWord ++ tailWord_3281392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281392).length < 2 ^ (prefixWord ++ tailWord_3281392).sum := by decide
  have hdescent : baseEnd_3281392 < baseStart_3281392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281415 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 4]
def baseStart_3281415 : Nat := 118140960795 + 3281415 * 2 ^ 59
def prefixEnd_3281415 : Nat := 4983230072969 + 3 ^ 40 * 3281415 * 2
def baseEnd_3281415 : Nat := 374431804860752040538123

theorem tailTrace_3281415 : CollatzResearch.WordTrace tailWord_3281415 prefixEnd_3281415 374431804860752040538123 := by
  unfold tailWord_3281415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119683037407001350909709699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79788691604667567273139799 119683037407001350909709699)
  ·
    refine ⟨179524556110502026364564549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119683037407001350909709699 179524556110502026364564549)
    ·
      refine ⟨33660854270719129943355853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179524556110502026364564549 33660854270719129943355853)
      ·
        refine ⟨12622820351519673728758445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33660854270719129943355853 12622820351519673728758445)
        ·
          refine ⟨4733557631819877648284417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12622820351519673728758445 4733557631819877648284417)
          ·
            refine ⟨3550168223864908236213313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733557631819877648284417 3550168223864908236213313)
            ·
              refine ⟨2662626167898681177159985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550168223864908236213313 2662626167898681177159985)
              ·
                refine ⟨1996969625924010882869989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662626167898681177159985 1996969625924010882869989)
                ·
                  refine ⟨374431804860752040538123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996969625924010882869989 374431804860752040538123)
                  ·
                    rfl

theorem cell22_3281415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 4].length) (baseStart_3281415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281415 prefixEnd_3281415 := by exact prefixLift 3281415
  have htrace : WordTrace (prefixWord ++ tailWord_3281415) baseStart_3281415 baseEnd_3281415 := by
    simpa [prefixWord, tailWord_3281415, baseEnd_3281415] using wordTrace_append hprefix tailTrace_3281415
  have hstable : (prefixWord ++ tailWord_3281415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281415).length < 2 ^ (prefixWord ++ tailWord_3281415).sum := by decide
  have hdescent : baseEnd_3281415 < baseStart_3281415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281441 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3281441 : Nat := 118140960795 + 3281441 * 2 ^ 59
def prefixEnd_3281441 : Nat := 4983230072969 + 3 ^ 40 * 3281441 * 2
def baseEnd_3281441 : Nat := 1123304314913600720464289

theorem tailTrace_3281441 : CollatzResearch.WordTrace tailWord_3281441 prefixEnd_3281441 1123304314913600720464289 := by
  unfold tailWord_3281441
  simp only [CollatzResearch.WordTrace]
  refine ⟨119683985704907157350156177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79789323803271438233437451 119683985704907157350156177)
  ·
    refine ⟨89762989278680368012617133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119683985704907157350156177 89762989278680368012617133)
    ·
      refine ⟨33661120979505138004731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89762989278680368012617133 33661120979505138004731425)
      ·
        refine ⟨25245840734628853503548569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33661120979505138004731425 25245840734628853503548569)
        ·
          refine ⟨18934380550971640127661427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25245840734628853503548569 18934380550971640127661427)
          ·
            refine ⟨28401570826457460191492141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18934380550971640127661427 28401570826457460191492141)
            ·
              refine ⟨10650589059921547571809553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28401570826457460191492141 10650589059921547571809553)
              ·
                refine ⟨7987941794941160678857165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10650589059921547571809553 7987941794941160678857165)
                ·
                  refine ⟨2995478173102935254571437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7987941794941160678857165 2995478173102935254571437)
                  ·
                    refine ⟨1123304314913600720464289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995478173102935254571437 1123304314913600720464289)
                    ·
                      rfl

theorem cell22_3281441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3281441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281441 prefixEnd_3281441 := by exact prefixLift 3281441
  have htrace : WordTrace (prefixWord ++ tailWord_3281441) baseStart_3281441 baseEnd_3281441 := by
    simpa [prefixWord, tailWord_3281441, baseEnd_3281441] using wordTrace_append hprefix tailTrace_3281441
  have hstable : (prefixWord ++ tailWord_3281441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281441).length < 2 ^ (prefixWord ++ tailWord_3281441).sum := by decide
  have hdescent : baseEnd_3281441 < baseStart_3281441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281458 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3281458 : Nat := 118140960795 + 3281458 * 2 ^ 59
def prefixEnd_3281458 : Nat := 4983230072969 + 3 ^ 40 * 3281458 * 2
def baseEnd_3281458 : Nat := 1123310134361018342789237

theorem tailTrace_3281458 : CollatzResearch.WordTrace tailWord_3281458 prefixEnd_3281458 1123310134361018342789237 := by
  unfold tailWord_3281458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29921151436461392313381257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79789737163897046169016685 29921151436461392313381257)
  ·
    refine ⟨22440863577346044235035943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29921151436461392313381257 22440863577346044235035943)
    ·
      refine ⟨33661295366019066352553915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22440863577346044235035943 33661295366019066352553915)
      ·
        refine ⟨50491943049028599528830873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33661295366019066352553915 50491943049028599528830873)
        ·
          refine ⟨37868957286771449646623155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50491943049028599528830873 37868957286771449646623155)
          ·
            refine ⟨56803435930157174469934733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37868957286771449646623155 56803435930157174469934733)
            ·
              refine ⟨21301288473808940426225525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56803435930157174469934733 21301288473808940426225525)
              ·
                refine ⟨1996995794419588164958643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21301288473808940426225525 1996995794419588164958643)
                ·
                  refine ⟨2995493691629382247437965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996995794419588164958643 2995493691629382247437965)
                  ·
                    refine ⟨1123310134361018342789237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995493691629382247437965 1123310134361018342789237)
                    ·
                      rfl

theorem cell22_3281458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3281458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281458 prefixEnd_3281458 := by exact prefixLift 3281458
  have htrace : WordTrace (prefixWord ++ tailWord_3281458) baseStart_3281458 baseEnd_3281458 := by
    simpa [prefixWord, tailWord_3281458, baseEnd_3281458] using wordTrace_append hprefix tailTrace_3281458
  have hstable : (prefixWord ++ tailWord_3281458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281458).length < 2 ^ (prefixWord ++ tailWord_3281458).sum := by decide
  have hdescent : baseEnd_3281458 < baseStart_3281458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281518 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3281518 : Nat := 118140960795 + 3281518 * 2 ^ 59
def prefixEnd_3281518 : Nat := 4983230072969 + 3 ^ 40 * 3281518 * 2
def baseEnd_3281518 : Nat := 1123330673587198186289053

theorem tailTrace_3281518 : CollatzResearch.WordTrace tailWord_3281518 prefixEnd_3281518 1123330673587198186289053 := by
  unfold tailWord_3281518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960849265703524937588651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79791196083752133000472805 14960849265703524937588651)
  ·
    refine ⟨22441273898555287406382977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14960849265703524937588651 22441273898555287406382977)
    ·
      refine ⟨16830955423916465554787233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22441273898555287406382977 16830955423916465554787233)
      ·
        refine ⟨12623216567937349166090425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16830955423916465554787233 12623216567937349166090425)
        ·
          refine ⟨9467412425953011874567819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12623216567937349166090425 9467412425953011874567819)
          ·
            refine ⟨14201118638929517811851729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467412425953011874567819 14201118638929517811851729)
            ·
              refine ⟨10650838979197138358888797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14201118638929517811851729 10650838979197138358888797)
              ·
                refine ⟨3994064617198926884583299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10650838979197138358888797 3994064617198926884583299)
                ·
                  refine ⟨5991096925798390326874949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994064617198926884583299 5991096925798390326874949)
                  ·
                    refine ⟨1123330673587198186289053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5991096925798390326874949 1123330673587198186289053)
                    ·
                      rfl

theorem cell22_3281518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3281518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281518 prefixEnd_3281518 := by exact prefixLift 3281518
  have htrace : WordTrace (prefixWord ++ tailWord_3281518) baseStart_3281518 baseEnd_3281518 := by
    simpa [prefixWord, tailWord_3281518, baseEnd_3281518] using wordTrace_append hprefix tailTrace_3281518
  have hstable : (prefixWord ++ tailWord_3281518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281518).length < 2 ^ (prefixWord ++ tailWord_3281518).sum := by decide
  have hdescent : baseEnd_3281518 < baseStart_3281518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281533 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 6]
def baseStart_3281533 : Nat := 118140960795 + 3281533 * 2 ^ 59
def prefixEnd_3281533 : Nat := 4983230072969 + 3 ^ 40 * 3281533 * 2
def baseEnd_3281533 : Nat := 374445269464581049054669

theorem tailTrace_3281533 : CollatzResearch.WordTrace tailWord_3281533 prefixEnd_3281533 374445269464581049054669 := by
  unfold tailWord_3281533
  simp only [CollatzResearch.WordTrace]
  refine ⟨119687341220573857062505253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79791560813715904708336835 119687341220573857062505253)
  ·
    refine ⟨22441376478857598199219735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119687341220573857062505253 22441376478857598199219735)
    ·
      refine ⟨33662064718286397298829603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22441376478857598199219735 33662064718286397298829603)
      ·
        refine ⟨50493097077429595948244405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33662064718286397298829603 50493097077429595948244405)
        ·
          refine ⟨4733727851009024620147913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50493097077429595948244405 4733727851009024620147913)
          ·
            refine ⟨3550295888256768465110935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733727851009024620147913 3550295888256768465110935)
            ·
              refine ⟨5325443832385152697666403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550295888256768465110935 5325443832385152697666403)
              ·
                refine ⟨7988165748577729046499605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325443832385152697666403 7988165748577729046499605)
                ·
                  refine ⟨374445269464581049054669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7988165748577729046499605 374445269464581049054669)
                  ·
                    rfl

theorem cell22_3281533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_3281533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281533 prefixEnd_3281533 := by exact prefixLift 3281533
  have htrace : WordTrace (prefixWord ++ tailWord_3281533) baseStart_3281533 baseEnd_3281533 := by
    simpa [prefixWord, tailWord_3281533, baseEnd_3281533] using wordTrace_append hprefix tailTrace_3281533
  have hstable : (prefixWord ++ tailWord_3281533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281533).length < 2 ^ (prefixWord ++ tailWord_3281533).sum := by decide
  have hdescent : baseEnd_3281533 < baseStart_3281533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281578 : List Nat := [3, 1, 5, 2, 1, 10]
def baseStart_3281578 : Nat := 118140960795 + 3281578 * 2 ^ 59
def prefixEnd_3281578 : Nat := 4983230072969 + 3 ^ 40 * 3281578 * 2
def baseEnd_3281578 : Nat := 13868533491523185552949

theorem tailTrace_3281578 : CollatzResearch.WordTrace tailWord_3281578 prefixEnd_3281578 13868533491523185552949 := by
  unfold tailWord_3281578
  simp only [CollatzResearch.WordTrace]
  refine ⟨29922245626352707436973347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79792655003607219831928925 29922245626352707436973347)
  ·
    refine ⟨44883368439529061155460021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29922245626352707436973347 44883368439529061155460021)
    ·
      refine ⟨4207815791205849483324377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44883368439529061155460021 4207815791205849483324377)
      ·
        refine ⟨3155861843404387112493283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4207815791205849483324377 3155861843404387112493283)
        ·
          refine ⟨4733792765106580668739925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155861843404387112493283 4733792765106580668739925)
          ·
            refine ⟨13868533491523185552949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4733792765106580668739925 13868533491523185552949)
            ·
              rfl

theorem cell22_3281578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 10].length) (baseStart_3281578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281578 prefixEnd_3281578 := by exact prefixLift 3281578
  have htrace : WordTrace (prefixWord ++ tailWord_3281578) baseStart_3281578 baseEnd_3281578 := by
    simpa [prefixWord, tailWord_3281578, baseEnd_3281578] using wordTrace_append hprefix tailTrace_3281578
  have hstable : (prefixWord ++ tailWord_3281578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281578).length < 2 ^ (prefixWord ++ tailWord_3281578).sum := by decide
  have hdescent : baseEnd_3281578 < baseStart_3281578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281582 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3281582 : Nat := 118140960795 + 3281582 * 2 ^ 59
def prefixEnd_3281582 : Nat := 4983230072969 + 3 ^ 40 * 3281582 * 2
def baseEnd_3281582 : Nat := 1123352582095123352688857

theorem tailTrace_3281582 : CollatzResearch.WordTrace tailWord_3281582 prefixEnd_3281582 1123352582095123352688857 := by
  unfold tailWord_3281582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14961141049674542303879875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79792752264930892287359333 14961141049674542303879875)
  ·
    refine ⟨22441711574511813455819813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14961141049674542303879875 22441711574511813455819813)
    ·
      refine ⟨4207820920220965022966215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22441711574511813455819813 4207820920220965022966215)
      ·
        refine ⟨6311731380331447534449323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207820920220965022966215 6311731380331447534449323)
        ·
          refine ⟨9467597070497171301673985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311731380331447534449323 9467597070497171301673985)
          ·
            refine ⟨7100697802872878476255489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467597070497171301673985 7100697802872878476255489)
            ·
              refine ⟨5325523352154658857191617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100697802872878476255489 5325523352154658857191617)
              ·
                refine ⟨3994142514115994142893713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325523352154658857191617 3994142514115994142893713)
                ·
                  refine ⟨2995606885586995607170285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994142514115994142893713 2995606885586995607170285)
                  ·
                    refine ⟨1123352582095123352688857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995606885586995607170285 1123352582095123352688857)
                    ·
                      rfl

theorem cell22_3281582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3281582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281582 prefixEnd_3281582 := by exact prefixLift 3281582
  have htrace : WordTrace (prefixWord ++ tailWord_3281582) baseStart_3281582 baseEnd_3281582 := by
    simpa [prefixWord, tailWord_3281582, baseEnd_3281582] using wordTrace_append hprefix tailTrace_3281582
  have hstable : (prefixWord ++ tailWord_3281582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281582).length < 2 ^ (prefixWord ++ tailWord_3281582).sum := by decide
  have hdescent : baseEnd_3281582 < baseStart_3281582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281640 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_3281640 : Nat := 118140960795 + 3281640 * 2 ^ 59
def prefixEnd_3281640 : Nat := 4983230072969 + 3 ^ 40 * 3281640 * 2
def baseEnd_3281640 : Nat := 374457478893476844912893

theorem tailTrace_3281640 : CollatzResearch.WordTrace tailWord_3281640 prefixEnd_3281640 374457478893476844912893 := by
  unfold tailWord_3281640
  simp only [CollatzResearch.WordTrace]
  refine ⟨59845621915593107168325187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79794162554124142891100249 59845621915593107168325187)
  ·
    refine ⟨89768432873389660752487781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59845621915593107168325187 89768432873389660752487781)
    ·
      refine ⟨16831581163760561391091459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89768432873389660752487781 16831581163760561391091459)
      ·
        refine ⟨25247371745640842086637189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831581163760561391091459 25247371745640842086637189)
        ·
          refine ⟨4733882202307657891244473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25247371745640842086637189 4733882202307657891244473)
          ·
            refine ⟨3550411651730743418433355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733882202307657891244473 3550411651730743418433355)
            ·
              refine ⟨5325617477596115127650033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550411651730743418433355 5325617477596115127650033)
              ·
                refine ⟨3994213108197086345737525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325617477596115127650033 3994213108197086345737525)
                ·
                  refine ⟨374457478893476844912893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994213108197086345737525 374457478893476844912893)
                  ·
                    rfl

theorem cell22_3281640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_3281640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281640 prefixEnd_3281640 := by exact prefixLift 3281640
  have htrace : WordTrace (prefixWord ++ tailWord_3281640) baseStart_3281640 baseEnd_3281640 := by
    simpa [prefixWord, tailWord_3281640, baseEnd_3281640] using wordTrace_append hprefix tailTrace_3281640
  have hstable : (prefixWord ++ tailWord_3281640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281640).length < 2 ^ (prefixWord ++ tailWord_3281640).sum := by decide
  have hdescent : baseEnd_3281640 < baseStart_3281640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281681 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3281681 : Nat := 118140960795 + 3281681 * 2 ^ 59
def prefixEnd_3281681 : Nat := 4983230072969 + 3 ^ 40 * 3281681 * 2
def baseEnd_3281681 : Nat := 1123386471818320094463553

theorem tailTrace_3281681 : CollatzResearch.WordTrace tailWord_3281681 prefixEnd_3281681 1123386471818320094463553 := by
  unfold tailWord_3281681
  simp only [CollatzResearch.WordTrace]
  refine ⟨119692739224037678338892897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79795159482691785559261931 119692739224037678338892897)
  ·
    refine ⟨89769554418028258754169673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119692739224037678338892897 89769554418028258754169673)
    ·
      refine ⟨67327165813521194065627255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89769554418028258754169673 67327165813521194065627255)
      ·
        refine ⟨100990748720281791098440883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67327165813521194065627255 100990748720281791098440883)
        ·
          refine ⟨151486123080422686647661325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100990748720281791098440883 151486123080422686647661325)
          ·
            refine ⟨56807296155158507492872997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151486123080422686647661325 56807296155158507492872997)
            ·
              refine ⟨10651368029092220154913687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56807296155158507492872997 10651368029092220154913687)
              ·
                refine ⟨15977052043638330232370531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10651368029092220154913687 15977052043638330232370531)
                ·
                  refine ⟨23965578065457495348555797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15977052043638330232370531 23965578065457495348555797)
                  ·
                    refine ⟨1123386471818320094463553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23965578065457495348555797 1123386471818320094463553)
                    ·
                      rfl

theorem cell22_3281681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3281681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281681 prefixEnd_3281681 := by exact prefixLift 3281681
  have htrace : WordTrace (prefixWord ++ tailWord_3281681) baseStart_3281681 baseEnd_3281681 := by
    simpa [prefixWord, tailWord_3281681, baseEnd_3281681] using wordTrace_append hprefix tailTrace_3281681
  have hstable : (prefixWord ++ tailWord_3281681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281681).length < 2 ^ (prefixWord ++ tailWord_3281681).sum := by decide
  have hdescent : baseEnd_3281681 < baseStart_3281681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281696 : List Nat := [2, 1, 1, 5, 1, 2, 10]
def baseStart_3281696 : Nat := 118140960795 + 3281696 * 2 ^ 59
def prefixEnd_3281696 : Nat := 4983230072969 + 3 ^ 40 * 3281696 * 2
def baseEnd_3281696 : Nat := 41607096541661668716241

theorem tailTrace_3281696 : CollatzResearch.WordTrace tailWord_3281696 prefixEnd_3281696 41607096541661668716241 := by
  unfold tailWord_3281696
  simp only [CollatzResearch.WordTrace]
  refine ⟨59846643159491667950344471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79795524212655557267125961 59846643159491667950344471)
  ·
    refine ⟨89769964739237501925516707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59846643159491667950344471 89769964739237501925516707)
    ·
      refine ⟨134654947108856252888275061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89769964739237501925516707 134654947108856252888275061)
      ·
        refine ⟨12623901291455273708275787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134654947108856252888275061 12623901291455273708275787)
        ·
          refine ⟨18935851937182910562413681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623901291455273708275787 18935851937182910562413681)
          ·
            refine ⟨14201888952887182921810261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935851937182910562413681 14201888952887182921810261)
            ·
              refine ⟨41607096541661668716241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14201888952887182921810261 41607096541661668716241)
              ·
                rfl

theorem cell22_3281696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 10].length) (baseStart_3281696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281696 prefixEnd_3281696 := by exact prefixLift 3281696
  have htrace : WordTrace (prefixWord ++ tailWord_3281696) baseStart_3281696 baseEnd_3281696 := by
    simpa [prefixWord, tailWord_3281696, baseEnd_3281696] using wordTrace_append hprefix tailTrace_3281696
  have hstable : (prefixWord ++ tailWord_3281696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281696).length < 2 ^ (prefixWord ++ tailWord_3281696).sum := by decide
  have hdescent : baseEnd_3281696 < baseStart_3281696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281698 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3281698 : Nat := 118140960795 + 3281698 * 2 ^ 59
def prefixEnd_3281698 : Nat := 4983230072969 + 3 ^ 40 * 3281698 * 2
def baseEnd_3281698 : Nat := 1123392291265737716788501

theorem tailTrace_3281698 : CollatzResearch.WordTrace tailWord_3281698 prefixEnd_3281698 1123392291265737716788501 := by
  unfold tailWord_3281698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923339816244022560565437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79795572843317393494841165 29923339816244022560565437)
  ·
    refine ⟨11221252431091508460212039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29923339816244022560565437 11221252431091508460212039)
    ·
      refine ⟨16831878646637262690318059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221252431091508460212039 16831878646637262690318059)
      ·
        refine ⟨25247817969955894035477089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831878646637262690318059 25247817969955894035477089)
        ·
          refine ⟨18935863477466920526607817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25247817969955894035477089 18935863477466920526607817)
          ·
            refine ⟨14201897608100190394955863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935863477466920526607817 14201897608100190394955863)
            ·
              refine ⟨21302846412150285592433795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14201897608100190394955863 21302846412150285592433795)
              ·
                refine ⟨31954269618225428388650693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21302846412150285592433795 31954269618225428388650693)
                ·
                  refine ⟨5991425553417267822872005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31954269618225428388650693 5991425553417267822872005)
                  ·
                    refine ⟨1123392291265737716788501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5991425553417267822872005 1123392291265737716788501)
                    ·
                      rfl

theorem cell22_3281698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3281698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281698 prefixEnd_3281698 := by exact prefixLift 3281698
  have htrace : WordTrace (prefixWord ++ tailWord_3281698) baseStart_3281698 baseEnd_3281698 := by
    simpa [prefixWord, tailWord_3281698, baseEnd_3281698] using wordTrace_append hprefix tailTrace_3281698
  have hstable : (prefixWord ++ tailWord_3281698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281698).length < 2 ^ (prefixWord ++ tailWord_3281698).sum := by decide
  have hdescent : baseEnd_3281698 < baseStart_3281698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281717 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3281717 : Nat := 118140960795 + 3281717 * 2 ^ 59
def prefixEnd_3281717 : Nat := 4983230072969 + 3 ^ 40 * 3281717 * 2
def baseEnd_3281717 : Nat := 1123398795354028000563443

theorem tailTrace_3281717 : CollatzResearch.WordTrace tailWord_3281717 prefixEnd_3281717 1123398795354028000563443 := by
  unfold tailWord_3281717
  simp only [CollatzResearch.WordTrace]
  refine ⟨119694052251907256487203405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79796034834604837658135603 119694052251907256487203405)
  ·
    refine ⟨44885269594465221182701277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119694052251907256487203405 44885269594465221182701277)
    ·
      refine ⟨16831976097924457943512979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44885269594465221182701277 16831976097924457943512979)
      ·
        refine ⟨25247964146886686915269469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831976097924457943512979 25247964146886686915269469)
        ·
          refine ⟨9467986555082507593226051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25247964146886686915269469 9467986555082507593226051)
          ·
            refine ⟨14201979832623761389839077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467986555082507593226051 14201979832623761389839077)
            ·
              refine ⟨2662871218616955260594827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14201979832623761389839077 2662871218616955260594827)
              ·
                refine ⟨3994306827925432890892241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662871218616955260594827 3994306827925432890892241)
                ·
                  refine ⟨2995730120944074668169181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994306827925432890892241 2995730120944074668169181)
                  ·
                    refine ⟨1123398795354028000563443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995730120944074668169181 1123398795354028000563443)
                    ·
                      rfl

theorem cell22_3281717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3281717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281717 prefixEnd_3281717 := by exact prefixLift 3281717
  have htrace : WordTrace (prefixWord ++ tailWord_3281717) baseStart_3281717 baseEnd_3281717 := by
    simpa [prefixWord, tailWord_3281717, baseEnd_3281717] using wordTrace_append hprefix tailTrace_3281717
  have hstable : (prefixWord ++ tailWord_3281717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281717).length < 2 ^ (prefixWord ++ tailWord_3281717).sum := by decide
  have hdescent : baseEnd_3281717 < baseStart_3281717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281728 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_3281728 : Nat := 118140960795 + 3281728 * 2 ^ 59
def prefixEnd_3281728 : Nat := 4983230072969 + 3 ^ 40 * 3281728 * 2
def baseEnd_3281728 : Nat := 1123402560878827638538409

theorem tailTrace_3281728 : CollatzResearch.WordTrace tailWord_3281728 prefixEnd_3281728 1123402560878827638538409 := by
  unfold tailWord_3281728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59847226727433702682926919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79796302303244936910569225 59847226727433702682926919)
  ·
    refine ⟨89770840091150554024390379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59847226727433702682926919 89770840091150554024390379)
    ·
      refine ⟨134656260136725831036585569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89770840091150554024390379 134656260136725831036585569)
      ·
        refine ⟨100992195102544373277439177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134656260136725831036585569 100992195102544373277439177)
        ·
          refine ⟨75744146326908279958079383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100992195102544373277439177 75744146326908279958079383)
          ·
            refine ⟨113616219490362419937119075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75744146326908279958079383 113616219490362419937119075)
            ·
              refine ⟨170424329235543629905678613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113616219490362419937119075 170424329235543629905678613)
              ·
                refine ⟨7988640432916107651828685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170424329235543629905678613 7988640432916107651828685)
                ·
                  refine ⟨2995740162343540369435757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7988640432916107651828685 2995740162343540369435757)
                  ·
                    refine ⟨1123402560878827638538409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995740162343540369435757 1123402560878827638538409)
                    ·
                      rfl

theorem cell22_3281728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_3281728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281728 prefixEnd_3281728 := by exact prefixLift 3281728
  have htrace : WordTrace (prefixWord ++ tailWord_3281728) baseStart_3281728 baseEnd_3281728 := by
    simpa [prefixWord, tailWord_3281728, baseEnd_3281728] using wordTrace_append hprefix tailTrace_3281728
  have hstable : (prefixWord ++ tailWord_3281728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281728).length < 2 ^ (prefixWord ++ tailWord_3281728).sum := by decide
  have hdescent : baseEnd_3281728 < baseStart_3281728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281848 : List Nat := [2, 1, 2, 1, 2, 5, 1, 8]
def baseStart_3281848 : Nat := 118140960795 + 3281848 * 2 ^ 59
def prefixEnd_3281848 : Nat := 4983230072969 + 3 ^ 40 * 3281848 * 2
def baseEnd_3281848 : Nat := 124827071036798591726449

theorem tailTrace_3281848 : CollatzResearch.WordTrace tailWord_3281848 prefixEnd_3281848 124827071036798591726449 := by
  unfold tailWord_3281848
  simp only [CollatzResearch.WordTrace]
  refine ⟨59849415107216332930111099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79799220142955110573481465 59849415107216332930111099)
  ·
    refine ⟨89774122660824499395166649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59849415107216332930111099 89774122660824499395166649)
    ·
      refine ⟨67330591995618374546374987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89774122660824499395166649 67330591995618374546374987)
      ·
        refine ⟨100995887993427561819562481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67330591995618374546374987 100995887993427561819562481)
        ·
          refine ⟨75746915995070671364671861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100995887993427561819562481 75746915995070671364671861)
          ·
            refine ⟨7101273374537875440437987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75746915995070671364671861 7101273374537875440437987)
            ·
              refine ⟨10651910061806813160656981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101273374537875440437987 10651910061806813160656981)
              ·
                refine ⟨124827071036798591726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10651910061806813160656981 124827071036798591726449)
                ·
                  rfl

theorem cell22_3281848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_3281848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281848 prefixEnd_3281848 := by exact prefixLift 3281848
  have htrace : WordTrace (prefixWord ++ tailWord_3281848) baseStart_3281848 baseEnd_3281848 := by
    simpa [prefixWord, tailWord_3281848, baseEnd_3281848] using wordTrace_append hprefix tailTrace_3281848
  have hstable : (prefixWord ++ tailWord_3281848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281848).length < 2 ^ (prefixWord ++ tailWord_3281848).sum := by decide
  have hdescent : baseEnd_3281848 < baseStart_3281848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281931 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 1, 3]
def baseStart_3281931 : Nat := 118140960795 + 3281931 * 2 ^ 59
def prefixEnd_3281931 : Nat := 4983230072969 + 3 ^ 40 * 3281931 * 2
def baseEnd_3281931 : Nat := 1123472051927402775712787

theorem tailTrace_3281931 : CollatzResearch.WordTrace tailWord_3281931 prefixEnd_3281931 1123472051927402775712787 := by
  unfold tailWord_3281931
  simp only [CollatzResearch.WordTrace]
  refine ⟨119701857473131971035493647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79801238315421314023662431 119701857473131971035493647)
  ·
    refine ⟨179552786209697956553240471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119701857473131971035493647 179552786209697956553240471)
    ·
      refine ⟨269329179314546934829860707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179552786209697956553240471 269329179314546934829860707)
      ·
        refine ⟨403993768971820402244791061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269329179314546934829860707 403993768971820402244791061)
        ·
          refine ⟨18937207920554081355224581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 403993768971820402244791061 18937207920554081355224581)
          ·
            refine ⟨3550726485103890254104609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18937207920554081355224581 3550726485103890254104609)
            ·
              refine ⟨2663044863827917690578457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550726485103890254104609 2663044863827917690578457)
              ·
                refine ⟨1997283647870938267933843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663044863827917690578457 1997283647870938267933843)
                ·
                  refine ⟨2995925471806407401900765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997283647870938267933843 2995925471806407401900765)
                  ·
                    refine ⟨1123472051927402775712787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2995925471806407401900765 1123472051927402775712787)
                    ·
                      rfl

theorem cell22_3281931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 3].length) (baseStart_3281931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281931 prefixEnd_3281931 := by exact prefixLift 3281931
  have htrace : WordTrace (prefixWord ++ tailWord_3281931) baseStart_3281931 baseEnd_3281931 := by
    simpa [prefixWord, tailWord_3281931, baseEnd_3281931] using wordTrace_append hprefix tailTrace_3281931
  have hstable : (prefixWord ++ tailWord_3281931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281931).length < 2 ^ (prefixWord ++ tailWord_3281931).sum := by decide
  have hdescent : baseEnd_3281931 < baseStart_3281931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281955 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 6]
def baseStart_3281955 : Nat := 118140960795 + 3281955 * 2 ^ 59
def prefixEnd_3281955 : Nat := 4983230072969 + 3 ^ 40 * 3281955 * 2
def baseEnd_3281955 : Nat := 374493422539291571037571

theorem tailTrace_3281955 : CollatzResearch.WordTrace tailWord_3281955 prefixEnd_3281955 374493422539291571037571 := by
  unfold tailWord_3281955
  simp only [CollatzResearch.WordTrace]
  refine ⟨119702732825045023134367319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79801821883363348756244879 119702732825045023134367319)
  ·
    refine ⟨179554099237567534701550979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119702732825045023134367319 179554099237567534701550979)
    ·
      refine ⟨269331148856351302052326469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179554099237567534701550979 269331148856351302052326469)
      ·
        refine ⟨50499590410565869134811213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269331148856351302052326469 50499590410565869134811213)
        ·
          refine ⟨18937346403962200925554205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50499590410565869134811213 18937346403962200925554205)
          ·
            refine ⟨7101504901485825347082827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18937346403962200925554205 7101504901485825347082827)
            ·
              refine ⟨10652257352228738020624241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101504901485825347082827 10652257352228738020624241)
              ·
                refine ⟨7989193014171553515468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10652257352228738020624241 7989193014171553515468181)
                ·
                  refine ⟨374493422539291571037571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7989193014171553515468181 374493422539291571037571)
                  ·
                    rfl

theorem cell22_3281955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_3281955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281955 prefixEnd_3281955 := by exact prefixLift 3281955
  have htrace : WordTrace (prefixWord ++ tailWord_3281955) baseStart_3281955 baseEnd_3281955 := by
    simpa [prefixWord, tailWord_3281955, baseEnd_3281955] using wordTrace_append hprefix tailTrace_3281955
  have hstable : (prefixWord ++ tailWord_3281955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281955).length < 2 ^ (prefixWord ++ tailWord_3281955).sum := by decide
  have hdescent : baseEnd_3281955 < baseStart_3281955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281970 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_3281970 : Nat := 118140960795 + 3281970 * 2 ^ 59
def prefixEnd_3281970 : Nat := 4983230072969 + 3 ^ 40 * 3281970 * 2
def baseEnd_3281970 : Nat := 1123485402424419673987667

theorem tailTrace_3281970 : CollatzResearch.WordTrace tailWord_3281970 prefixEnd_3281970 1123485402424419673987667 := by
  unfold tailWord_3281970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925819979997670174040841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79802186613327120464108909 29925819979997670174040841)
  ·
    refine ⟨22444364984998252630530631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29925819979997670174040841 22444364984998252630530631)
    ·
      refine ⟨33666547477497378945795947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22444364984998252630530631 33666547477497378945795947)
      ·
        refine ⟨50499821216246068418693921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33666547477497378945795947 50499821216246068418693921)
        ·
          refine ⟨37874865912184551314020441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50499821216246068418693921 37874865912184551314020441)
          ·
            refine ⟨28406149434138413485515331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37874865912184551314020441 28406149434138413485515331)
            ·
              refine ⟨42609224151207620228272997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28406149434138413485515331 42609224151207620228272997)
              ·
                refine ⟨7989229528351428792801187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42609224151207620228272997 7989229528351428792801187)
                ·
                  refine ⟨11983844292527143189201781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989229528351428792801187 11983844292527143189201781)
                  ·
                    refine ⟨1123485402424419673987667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11983844292527143189201781 1123485402424419673987667)
                    ·
                      rfl

theorem cell22_3281970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_3281970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281970 prefixEnd_3281970 := by exact prefixLift 3281970
  have htrace : WordTrace (prefixWord ++ tailWord_3281970) baseStart_3281970 baseEnd_3281970 := by
    simpa [prefixWord, tailWord_3281970, baseEnd_3281970] using wordTrace_append hprefix tailTrace_3281970
  have hstable : (prefixWord ++ tailWord_3281970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281970).length < 2 ^ (prefixWord ++ tailWord_3281970).sum := by decide
  have hdescent : baseEnd_3281970 < baseStart_3281970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3281974 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3281974 : Nat := 118140960795 + 3281974 * 2 ^ 59
def prefixEnd_3281974 : Nat := 4983230072969 + 3 ^ 40 * 3281974 * 2
def baseEnd_3281974 : Nat := 1123486771706164996887655

theorem tailTrace_3281974 : CollatzResearch.WordTrace tailWord_3281974 prefixEnd_3281974 1123486771706164996887655 := by
  unfold tailWord_3281974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481464113248511836206811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79802283874650792919539317 7481464113248511836206811)
  ·
    refine ⟨11222196169872767754310217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7481464113248511836206811 11222196169872767754310217)
    ·
      refine ⟨8416647127404575815732663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11222196169872767754310217 8416647127404575815732663)
      ·
        refine ⟨12624970691106863723598995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416647127404575815732663 12624970691106863723598995)
        ·
          refine ⟨18937456036660295585398493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12624970691106863723598995 18937456036660295585398493)
          ·
            refine ⟨7101546013747610844524435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18937456036660295585398493 7101546013747610844524435)
            ·
              refine ⟨10652319020621416266786653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101546013747610844524435 10652319020621416266786653)
              ·
                refine ⟨3994619632733031100044995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10652319020621416266786653 3994619632733031100044995)
                ·
                  refine ⟨5991929449099546650067493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994619632733031100044995 5991929449099546650067493)
                  ·
                    refine ⟨1123486771706164996887655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5991929449099546650067493 1123486771706164996887655)
                    ·
                      rfl

theorem cell22_3281974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3281974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3281974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3281974 prefixEnd_3281974 := by exact prefixLift 3281974
  have htrace : WordTrace (prefixWord ++ tailWord_3281974) baseStart_3281974 baseEnd_3281974 := by
    simpa [prefixWord, tailWord_3281974, baseEnd_3281974] using wordTrace_append hprefix tailTrace_3281974
  have hstable : (prefixWord ++ tailWord_3281974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3281974).length < 2 ^ (prefixWord ++ tailWord_3281974).sum := by decide
  have hdescent : baseEnd_3281974 < baseStart_3281974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3281974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282045 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3282045 : Nat := 118140960795 + 3282045 * 2 ^ 59
def prefixEnd_3282045 : Nat := 4983230072969 + 3 ^ 40 * 3282045 * 2
def baseEnd_3282045 : Nat := 374503692152381492787479

theorem tailTrace_3282045 : CollatzResearch.WordTrace tailWord_3282045 prefixEnd_3282045 374503692152381492787479 := by
  unfold tailWord_3282045
  simp only [CollatzResearch.WordTrace]
  refine ⟨119706015394718968505143589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79804010263145979003429059 119706015394718968505143589)
  ·
    refine ⟨22444877886509806594714423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119706015394718968505143589 22444877886509806594714423)
    ·
      refine ⟨33667316829764709892071635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22444877886509806594714423 33667316829764709892071635)
      ·
        refine ⟨50500975244647064838107453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33667316829764709892071635 50500975244647064838107453)
        ·
          refine ⟨18937865716742649314290295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50500975244647064838107453 18937865716742649314290295)
          ·
            refine ⟨28406798575113973971435443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18937865716742649314290295 28406798575113973971435443)
            ·
              refine ⟨42610197862670960957153165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28406798575113973971435443 42610197862670960957153165)
              ·
                refine ⟨15978824198501610358932437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42610197862670960957153165 15978824198501610358932437)
                ·
                  refine ⟨374503692152381492787479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15978824198501610358932437 374503692152381492787479)
                  ·
                    rfl

theorem cell22_3282045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3282045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282045 prefixEnd_3282045 := by exact prefixLift 3282045
  have htrace : WordTrace (prefixWord ++ tailWord_3282045) baseStart_3282045 baseEnd_3282045 := by
    simpa [prefixWord, tailWord_3282045, baseEnd_3282045] using wordTrace_append hprefix tailTrace_3282045
  have hstable : (prefixWord ++ tailWord_3282045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282045).length < 2 ^ (prefixWord ++ tailWord_3282045).sum := by decide
  have hdescent : baseEnd_3282045 < baseStart_3282045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282049 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3282049 : Nat := 118140960795 + 3282049 * 2 ^ 59
def prefixEnd_3282049 : Nat := 4983230072969 + 3 ^ 40 * 3282049 * 2
def baseEnd_3282049 : Nat := 1123512445738889801262425

theorem tailTrace_3282049 : CollatzResearch.WordTrace tailWord_3282049 prefixEnd_3282049 1123512445738889801262425 := by
  unfold tailWord_3282049
  simp only [CollatzResearch.WordTrace]
  refine ⟨119706161286704477188289201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79804107524469651458859467 119706161286704477188289201)
  ·
    refine ⟨89779620965028357891216901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119706161286704477188289201 89779620965028357891216901)
    ·
      refine ⟨16833678930942817104603169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89779620965028357891216901 16833678930942817104603169)
      ·
        refine ⟨12625259198207112828452377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16833678930942817104603169 12625259198207112828452377)
        ·
          refine ⟨9468944398655334621339283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12625259198207112828452377 9468944398655334621339283)
          ·
            refine ⟨14203416597983001932008925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468944398655334621339283 14203416597983001932008925)
            ·
              refine ⟨5326281224243625724503347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14203416597983001932008925 5326281224243625724503347)
              ·
                refine ⟨7989421836365438586755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326281224243625724503347 7989421836365438586755021)
                ·
                  refine ⟨2996033188637039470033133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7989421836365438586755021 2996033188637039470033133)
                  ·
                    refine ⟨1123512445738889801262425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996033188637039470033133 1123512445738889801262425)
                    ·
                      rfl

theorem cell22_3282049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3282049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282049 prefixEnd_3282049 := by exact prefixLift 3282049
  have htrace : WordTrace (prefixWord ++ tailWord_3282049) baseStart_3282049 baseEnd_3282049 := by
    simpa [prefixWord, tailWord_3282049, baseEnd_3282049] using wordTrace_append hprefix tailTrace_3282049
  have hstable : (prefixWord ++ tailWord_3282049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282049).length < 2 ^ (prefixWord ++ tailWord_3282049).sum := by decide
  have hdescent : baseEnd_3282049 < baseStart_3282049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282060 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3282060 : Nat := 118140960795 + 3282060 * 2 ^ 59
def prefixEnd_3282060 : Nat := 4983230072969 + 3 ^ 40 * 3282060 * 2
def baseEnd_3282060 : Nat := 1123516211263689439237391

theorem tailTrace_3282060 : CollatzResearch.WordTrace tailWord_3282060 prefixEnd_3282060 1123516211263689439237391 := by
  unfold tailWord_3282060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853281244832313033469817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79804374993109750711293089 59853281244832313033469817)
  ·
    refine ⟨44889960933624234775102363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59853281244832313033469817 44889960933624234775102363)
    ·
      refine ⟨67334941400436352162653545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44889960933624234775102363 67334941400436352162653545)
      ·
        refine ⟨50501206050327264121990159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67334941400436352162653545 50501206050327264121990159)
        ·
          refine ⟨75751809075490896182985239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50501206050327264121990159 75751809075490896182985239)
          ·
            refine ⟨113627713613236344274477859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75751809075490896182985239 113627713613236344274477859)
            ·
              refine ⟨170441570419854516411716789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113627713613236344274477859 170441570419854516411716789)
              ·
                refine ⟨15978897226861360913598449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170441570419854516411716789 15978897226861360913598449)
                ·
                  refine ⟨11984172920146020685198837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15978897226861360913598449 11984172920146020685198837)
                  ·
                    refine ⟨1123516211263689439237391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11984172920146020685198837 1123516211263689439237391)
                    ·
                      rfl

theorem cell22_3282060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3282060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282060 prefixEnd_3282060 := by exact prefixLift 3282060
  have htrace : WordTrace (prefixWord ++ tailWord_3282060) baseStart_3282060 baseEnd_3282060 := by
    simpa [prefixWord, tailWord_3282060, baseEnd_3282060] using wordTrace_append hprefix tailTrace_3282060
  have hstable : (prefixWord ++ tailWord_3282060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282060).length < 2 ^ (prefixWord ++ tailWord_3282060).sum := by decide
  have hdescent : baseEnd_3282060 < baseStart_3282060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282122 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3282122 : Nat := 118140960795 + 3282122 * 2 ^ 59
def prefixEnd_3282122 : Nat := 4983230072969 + 3 ^ 40 * 3282122 * 2
def baseEnd_3282122 : Nat := 1123537435130741944187201

theorem tailTrace_3282122 : CollatzResearch.WordTrace tailWord_3282122 prefixEnd_3282122 1123537435130741944187201 := by
  unfold tailWord_3282122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29927205953860002663924155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79805882543626673770464413 29927205953860002663924155)
  ·
    refine ⟨44890808930790003995886233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29927205953860002663924155 44890808930790003995886233)
    ·
      refine ⟨33668106698092502996914675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44890808930790003995886233 33668106698092502996914675)
      ·
        refine ⟨50502160047138754495372013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33668106698092502996914675 50502160047138754495372013)
        ·
          refine ⟨18938310017677032935764505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50502160047138754495372013 18938310017677032935764505)
          ·
            refine ⟨14203732513257774701823379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938310017677032935764505 14203732513257774701823379)
            ·
              refine ⟨21305598769886662052735069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203732513257774701823379 21305598769886662052735069)
              ·
                refine ⟨7989599538707498269775651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21305598769886662052735069 7989599538707498269775651)
                ·
                  refine ⟨11984399308061247404663477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989599538707498269775651 11984399308061247404663477)
                  ·
                    refine ⟨1123537435130741944187201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11984399308061247404663477 1123537435130741944187201)
                    ·
                      rfl

theorem cell22_3282122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3282122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282122 prefixEnd_3282122 := by exact prefixLift 3282122
  have htrace : WordTrace (prefixWord ++ tailWord_3282122) baseStart_3282122 baseEnd_3282122 := by
    simpa [prefixWord, tailWord_3282122, baseEnd_3282122] using wordTrace_append hprefix tailTrace_3282122
  have hstable : (prefixWord ++ tailWord_3282122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282122).length < 2 ^ (prefixWord ++ tailWord_3282122).sum := by decide
  have hdescent : baseEnd_3282122 < baseStart_3282122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282135 : List Nat := [1, 1, 3, 2, 1, 2, 2, 10]
def baseStart_3282135 : Nat := 118140960795 + 3282135 * 2 ^ 59
def prefixEnd_3282135 : Nat := 4983230072969 + 3 ^ 40 * 3282135 * 2
def baseEnd_3282135 : Nat := 124837987255157138179129

theorem tailTrace_3282135 : CollatzResearch.WordTrace tailWord_3282135 prefixEnd_3282135 124837987255157138179129 := by
  unfold tailWord_3282135
  simp only [CollatzResearch.WordTrace]
  refine ⟨119709297964392913875919859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79806198642928609250613239 119709297964392913875919859)
  ·
    refine ⟨179563946946589370813879789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119709297964392913875919859 179563946946589370813879789)
    ·
      refine ⟨67336480104971014055204921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179563946946589370813879789 67336480104971014055204921)
      ·
        refine ⟨50502360078728260541403691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67336480104971014055204921 50502360078728260541403691)
        ·
          refine ⟨75753540118092390812105537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50502360078728260541403691 75753540118092390812105537)
          ·
            refine ⟨56815155088569293109079153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75753540118092390812105537 56815155088569293109079153)
            ·
              refine ⟨42611366316426969831809365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56815155088569293109079153 42611366316426969831809365)
              ·
                refine ⟨124837987255157138179129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42611366316426969831809365 124837987255157138179129)
                ·
                  rfl

theorem cell22_3282135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 10].length) (baseStart_3282135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282135 prefixEnd_3282135 := by exact prefixLift 3282135
  have htrace : WordTrace (prefixWord ++ tailWord_3282135) baseStart_3282135 baseEnd_3282135 := by
    simpa [prefixWord, tailWord_3282135, baseEnd_3282135] using wordTrace_append hprefix tailTrace_3282135
  have hstable : (prefixWord ++ tailWord_3282135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282135).length < 2 ^ (prefixWord ++ tailWord_3282135).sum := by decide
  have hdescent : baseEnd_3282135 < baseStart_3282135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282156 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_3282156 : Nat := 118140960795 + 3282156 * 2 ^ 59
def prefixEnd_3282156 : Nat := 4983230072969 + 3 ^ 40 * 3282156 * 2
def baseEnd_3282156 : Nat := 1123549074025577188837097

theorem tailTrace_3282156 : CollatzResearch.WordTrace tailWord_3282156 prefixEnd_3282156 1123549074025577188837097 := by
  unfold tailWord_3282156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59855031948658417231217161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79806709264877889641622881 59855031948658417231217161)
  ·
    refine ⟨44891273961493812923412871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59855031948658417231217161 44891273961493812923412871)
    ·
      refine ⟨67336910942240719385119307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44891273961493812923412871 67336910942240719385119307)
      ·
        refine ⟨101005366413361079077678961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67336910942240719385119307 101005366413361079077678961)
        ·
          refine ⟨75754024810020809308259221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101005366413361079077678961 75754024810020809308259221)
          ·
            refine ⟨3550969912969725436324651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75754024810020809308259221 3550969912969725436324651)
            ·
              refine ⟨5326454869454588154486977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550969912969725436324651 5326454869454588154486977)
              ·
                refine ⟨3994841152090941115865233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326454869454588154486977 3994841152090941115865233)
                ·
                  refine ⟨2996130864068205836898925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994841152090941115865233 2996130864068205836898925)
                  ·
                    refine ⟨1123549074025577188837097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996130864068205836898925 1123549074025577188837097)
                    ·
                      rfl

theorem cell22_3282156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_3282156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282156 prefixEnd_3282156 := by exact prefixLift 3282156
  have htrace : WordTrace (prefixWord ++ tailWord_3282156) baseStart_3282156 baseEnd_3282156 := by
    simpa [prefixWord, tailWord_3282156, baseEnd_3282156] using wordTrace_append hprefix tailTrace_3282156
  have hstable : (prefixWord ++ tailWord_3282156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282156).length < 2 ^ (prefixWord ++ tailWord_3282156).sum := by decide
  have hdescent : baseEnd_3282156 < baseStart_3282156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282167 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 7, 3]
def baseStart_3282167 : Nat := 118140960795 + 3282167 * 2 ^ 59
def prefixEnd_3282167 : Nat := 4983230072969 + 3 ^ 40 * 3282167 * 2
def baseEnd_3282167 : Nat := 1123552839550376826812063

theorem tailTrace_3282167 : CollatzResearch.WordTrace tailWord_3282167 prefixEnd_3282167 1123552839550376826812063 := by
  unfold tailWord_3282167
  simp only [CollatzResearch.WordTrace]
  refine ⟨119710465100276983341084755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79806976733517988894056503 119710465100276983341084755)
  ·
    refine ⟨179565697650415475011627133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119710465100276983341084755 179565697650415475011627133)
    ·
      refine ⟨67337136618905803129360175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179565697650415475011627133 67337136618905803129360175)
      ·
        refine ⟨101005704928358704694040263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67337136618905803129360175 101005704928358704694040263)
        ·
          refine ⟨151508557392538057041060395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101005704928358704694040263 151508557392538057041060395)
          ·
            refine ⟨227262836088807085561590593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151508557392538057041060395 227262836088807085561590593)
            ·
              refine ⟨170447127066605314171192945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227262836088807085561590593 170447127066605314171192945)
              ·
                refine ⟨127835345299953985628394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170447127066605314171192945 127835345299953985628394709)
                ·
                  refine ⟨2996140905467671538165501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127835345299953985628394709 2996140905467671538165501)
                  ·
                    refine ⟨1123552839550376826812063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996140905467671538165501 1123552839550376826812063)
                    ·
                      rfl

theorem cell22_3282167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_3282167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282167 prefixEnd_3282167 := by exact prefixLift 3282167
  have htrace : WordTrace (prefixWord ++ tailWord_3282167) baseStart_3282167 baseEnd_3282167 := by
    simpa [prefixWord, tailWord_3282167, baseEnd_3282167] using wordTrace_append hprefix tailTrace_3282167
  have hstable : (prefixWord ++ tailWord_3282167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282167).length < 2 ^ (prefixWord ++ tailWord_3282167).sum := by decide
  have hdescent : baseEnd_3282167 < baseStart_3282167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282218 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3282218 : Nat := 118140960795 + 3282218 * 2 ^ 59
def prefixEnd_3282218 : Nat := 4983230072969 + 3 ^ 40 * 3282218 * 2
def baseEnd_3282218 : Nat := 1123570297892629693786907

theorem tailTrace_3282218 : CollatzResearch.WordTrace tailWord_3282218 prefixEnd_3282218 1123570297892629693786907 := by
  unfold tailWord_3282218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29928081305773054762797827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79808216815394812700794205 29928081305773054762797827)
  ·
    refine ⟨44892121958659582144196741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29928081305773054762797827 44892121958659582144196741)
    ·
      refine ⟨8417272867248671652036889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44892121958659582144196741 8417272867248671652036889)
      ·
        refine ⟨6312954650436503739027667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8417272867248671652036889 6312954650436503739027667)
        ·
          refine ⟨9469431975654755608541501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312954650436503739027667 9469431975654755608541501)
          ·
            refine ⟨3551036990870533353203063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9469431975654755608541501 3551036990870533353203063)
            ·
              refine ⟨5326555486305800029804595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551036990870533353203063 5326555486305800029804595)
              ·
                refine ⟨7989833229458700044706893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326555486305800029804595 7989833229458700044706893)
                ·
                  refine ⟨2996187461047012516765085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7989833229458700044706893 2996187461047012516765085)
                  ·
                    refine ⟨1123570297892629693786907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996187461047012516765085 1123570297892629693786907)
                    ·
                      rfl

theorem cell22_3282218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3282218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282218 prefixEnd_3282218 := by exact prefixLift 3282218
  have htrace : WordTrace (prefixWord ++ tailWord_3282218) baseStart_3282218 baseEnd_3282218 := by
    simpa [prefixWord, tailWord_3282218, baseEnd_3282218] using wordTrace_append hprefix tailTrace_3282218
  have hstable : (prefixWord ++ tailWord_3282218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282218).length < 2 ^ (prefixWord ++ tailWord_3282218).sum := by decide
  have hdescent : baseEnd_3282218 < baseStart_3282218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282259 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 4]
def baseStart_3282259 : Nat := 118140960795 + 3282259 * 2 ^ 59
def prefixEnd_3282259 : Nat := 4983230072969 + 3 ^ 40 * 3282259 * 2
def baseEnd_3282259 : Nat := 374528111010173084503927

theorem tailTrace_3282259 : CollatzResearch.WordTrace tailWord_3282259 prefixEnd_3282259 374528111010173084503927 := by
  unfold tailWord_3282259
  simp only [CollatzResearch.WordTrace]
  refine ⟨119713820615943683053433831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79809213743962455368955887 119713820615943683053433831)
  ·
    refine ⟨179570730923915524580150747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119713820615943683053433831 179570730923915524580150747)
    ·
      refine ⟨269356096385873286870226121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179570730923915524580150747 269356096385873286870226121)
      ·
        refine ⟨202017072289404965152669591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269356096385873286870226121 202017072289404965152669591)
        ·
          refine ⟨303025608434107447729004387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202017072289404965152669591 303025608434107447729004387)
          ·
            refine ⟨454538412651161171593506581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303025608434107447729004387 454538412651161171593506581)
            ·
              refine ⟨21306488093023179918445621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454538412651161171593506581 21306488093023179918445621)
              ·
                refine ⟨1997483258720923117354277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21306488093023179918445621 1997483258720923117354277)
                ·
                  refine ⟨374528111010173084503927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997483258720923117354277 374528111010173084503927)
                  ·
                    rfl

theorem cell22_3282259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 4].length) (baseStart_3282259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282259 prefixEnd_3282259 := by exact prefixLift 3282259
  have htrace : WordTrace (prefixWord ++ tailWord_3282259) baseStart_3282259 baseEnd_3282259 := by
    simpa [prefixWord, tailWord_3282259, baseEnd_3282259] using wordTrace_append hprefix tailTrace_3282259
  have hstable : (prefixWord ++ tailWord_3282259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282259).length < 2 ^ (prefixWord ++ tailWord_3282259).sum := by decide
  have hdescent : baseEnd_3282259 < baseStart_3282259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282274 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3282274 : Nat := 118140960795 + 3282274 * 2 ^ 59
def prefixEnd_3282274 : Nat := 4983230072969 + 3 ^ 40 * 3282274 * 2
def baseEnd_3282274 : Nat := 1123589467837064214386735

theorem tailTrace_3282274 : CollatzResearch.WordTrace tailWord_3282274 prefixEnd_3282274 1123589467837064214386735 := by
  unfold tailWord_3282274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29928591927722335153807469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79809578473926227076819917 29928591927722335153807469)
  ·
    refine ⟨11223221972895875682677801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29928591927722335153807469 11223221972895875682677801)
    ·
      refine ⟨8417416479671906762008351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11223221972895875682677801 8417416479671906762008351)
      ·
        refine ⟨12626124719507860143012527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8417416479671906762008351 12626124719507860143012527)
        ·
          refine ⟨18939187079261790214518791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626124719507860143012527 18939187079261790214518791)
          ·
            refine ⟨28408780618892685321778187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18939187079261790214518791 28408780618892685321778187)
            ·
              refine ⟨42613170928339027982667281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28408780618892685321778187 42613170928339027982667281)
              ·
                refine ⟨31959878196254270987000461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42613170928339027982667281 31959878196254270987000461)
                ·
                  refine ⟨11984954323595351620125173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31959878196254270987000461 11984954323595351620125173)
                  ·
                    refine ⟨1123589467837064214386735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11984954323595351620125173 1123589467837064214386735)
                    ·
                      rfl

theorem cell22_3282274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3282274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282274 prefixEnd_3282274 := by exact prefixLift 3282274
  have htrace : WordTrace (prefixWord ++ tailWord_3282274) baseStart_3282274 baseEnd_3282274 := by
    simpa [prefixWord, tailWord_3282274, baseEnd_3282274] using wordTrace_append hprefix tailTrace_3282274
  have hstable : (prefixWord ++ tailWord_3282274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282274).length < 2 ^ (prefixWord ++ tailWord_3282274).sum := by decide
  have hdescent : baseEnd_3282274 < baseStart_3282274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282276 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3282276 : Nat := 118140960795 + 3282276 * 2 ^ 59
def prefixEnd_3282276 : Nat := 4983230072969 + 3 ^ 40 * 3282276 * 2
def baseEnd_3282276 : Nat := 374530050825978958612243

theorem tailTrace_3282276 : CollatzResearch.WordTrace tailWord_3282276 prefixEnd_3282276 374530050825978958612243 := by
  unfold tailWord_3282276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59857220328441047478401341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79809627104588063304535121 59857220328441047478401341)
  ·
    refine ⟨22446457623165392804400503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59857220328441047478401341 22446457623165392804400503)
    ·
      refine ⟨33669686434748089206600755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22446457623165392804400503 33669686434748089206600755)
      ·
        refine ⟨50504529652122133809901133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33669686434748089206600755 50504529652122133809901133)
        ·
          refine ⟨18939198619545800178712925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50504529652122133809901133 18939198619545800178712925)
          ·
            refine ⟨7102199482329675067017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18939198619545800178712925 7102199482329675067017347)
            ·
              refine ⟨10653299223494512600526021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102199482329675067017347 10653299223494512600526021)
              ·
                refine ⟨1997493604405221112598629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10653299223494512600526021 1997493604405221112598629)
                ·
                  refine ⟨374530050825978958612243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997493604405221112598629 374530050825978958612243)
                  ·
                    rfl

theorem cell22_3282276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3282276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282276 prefixEnd_3282276 := by exact prefixLift 3282276
  have htrace : WordTrace (prefixWord ++ tailWord_3282276) baseStart_3282276 baseEnd_3282276 := by
    simpa [prefixWord, tailWord_3282276, baseEnd_3282276] using wordTrace_append hprefix tailTrace_3282276
  have hstable : (prefixWord ++ tailWord_3282276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282276).length < 2 ^ (prefixWord ++ tailWord_3282276).sum := by decide
  have hdescent : baseEnd_3282276 < baseStart_3282276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
