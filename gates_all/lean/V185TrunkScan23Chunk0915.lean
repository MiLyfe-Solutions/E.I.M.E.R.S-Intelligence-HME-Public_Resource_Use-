import V185TrunkScan23Chunk0914

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5415840 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5415840 : Nat := 118140960795 + 5415840 * 2 ^ 59
def prefixEnd_5415840 : Nat := 4983230072969 + 3 ^ 40 * 5415840 * 2
def baseEnd_5415840 : Nat := 2780929067846195734793011

theorem tailTrace_5415840 : CollatzResearch.WordTrace tailWord_5415840 prefixEnd_5415840 2780929067846195734793011 := by
  unfold tailWord_5415840
  simp only [CollatzResearch.WordTrace]
  refine ⟨98765956349672053338966487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131687941799562737785288649 98765956349672053338966487)
  ·
    refine ⟨148148934524508080008449731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98765956349672053338966487 148148934524508080008449731)
    ·
      refine ⟨222223401786762120012674597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148148934524508080008449731 222223401786762120012674597)
      ·
        refine ⟨41666887835017897502376487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222223401786762120012674597 41666887835017897502376487)
        ·
          refine ⟨62500331752526846253564731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41666887835017897502376487 62500331752526846253564731)
          ·
            refine ⟨93750497628790269380347097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62500331752526846253564731 93750497628790269380347097)
            ·
              refine ⟨70312873221592702035260323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93750497628790269380347097 70312873221592702035260323)
              ·
                refine ⟨105469309832389053052890485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70312873221592702035260323 105469309832389053052890485)
                ·
                  refine ⟨9887747796786473723708483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105469309832389053052890485 9887747796786473723708483)
                  ·
                    refine ⟨14831621695179710585562725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9887747796786473723708483 14831621695179710585562725)
                    ·
                      refine ⟨2780929067846195734793011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14831621695179710585562725 2780929067846195734793011)
                      ·
                        rfl

theorem cell23_5415840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5415840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415840 prefixEnd_5415840 := by exact prefixLift 5415840
  have htrace : WordTrace (prefixWord ++ tailWord_5415840) baseStart_5415840 baseEnd_5415840 := by
    simpa [prefixWord, tailWord_5415840, baseEnd_5415840] using wordTrace_append hprefix tailTrace_5415840
  have hstable : (prefixWord ++ tailWord_5415840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415840).length < 2 ^ (prefixWord ++ tailWord_5415840).sum := by decide
  have hdescent : baseEnd_5415840 < baseStart_5415840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415862 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5415862 : Nat := 118140960795 + 5415862 * 2 ^ 59
def prefixEnd_5415862 : Nat := 4983230072969 + 3 ^ 40 * 5415862 * 2
def baseEnd_5415862 : Nat := 926980121473531549572637

theorem tailTrace_5415862 : CollatzResearch.WordTrace tailWord_5415862 prefixEnd_5415862 926980121473531549572637 := by
  unfold tailWord_5415862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345794694079025277202115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131688476736842936290155893 12345794694079025277202115)
  ·
    refine ⟨18518692041118537915803173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12345794694079025277202115 18518692041118537915803173)
    ·
      refine ⟨3472254757709725859213095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18518692041118537915803173 3472254757709725859213095)
      ·
        refine ⟨5208382136564588788819643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472254757709725859213095 5208382136564588788819643)
        ·
          refine ⟨7812573204846883183229465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208382136564588788819643 7812573204846883183229465)
          ·
            refine ⟨5859429903635162387422099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7812573204846883183229465 5859429903635162387422099)
            ·
              refine ⟨8789144855452743581133149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859429903635162387422099 8789144855452743581133149)
              ·
                refine ⟨3295929320794778842924931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8789144855452743581133149 3295929320794778842924931)
                ·
                  refine ⟨4943893981192168264387397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295929320794778842924931 4943893981192168264387397)
                  ·
                    refine ⟨926980121473531549572637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943893981192168264387397 926980121473531549572637)
                    ·
                      rfl

theorem cell23_5415862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5415862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415862 prefixEnd_5415862 := by exact prefixLift 5415862
  have htrace : WordTrace (prefixWord ++ tailWord_5415862) baseStart_5415862 baseEnd_5415862 := by
    simpa [prefixWord, tailWord_5415862, baseEnd_5415862] using wordTrace_append hprefix tailTrace_5415862
  have hstable : (prefixWord ++ tailWord_5415862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415862).length < 2 ^ (prefixWord ++ tailWord_5415862).sum := by decide
  have hdescent : baseEnd_5415862 < baseStart_5415862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415894 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5415894 : Nat := 118140960795 + 5415894 * 2 ^ 59
def prefixEnd_5415894 : Nat := 4983230072969 + 3 ^ 40 * 5415894 * 2
def baseEnd_5415894 : Nat := 2780956795801538523517763

theorem tailTrace_5415894 : CollatzResearch.WordTrace tailWord_5415894 prefixEnd_5415894 2780956795801538523517763 := by
  unfold tailWord_5415894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345867640071779618774921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131689254827432315933599157 12345867640071779618774921)
  ·
    refine ⟨9259400730053834714081191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12345867640071779618774921 9259400730053834714081191)
    ·
      refine ⟨13889101095080752071121787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9259400730053834714081191 13889101095080752071121787)
      ·
        refine ⟨20833651642621128106682681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13889101095080752071121787 20833651642621128106682681)
        ·
          refine ⟨15625238731965846080012011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20833651642621128106682681 15625238731965846080012011)
          ·
            refine ⟨23437858097948769120018017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625238731965846080012011 23437858097948769120018017)
            ·
              refine ⟨17578393573461576840013513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23437858097948769120018017 17578393573461576840013513)
              ·
                refine ⟨13183795180096182630010135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17578393573461576840013513 13183795180096182630010135)
                ·
                  refine ⟨19775692770144273945015203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13183795180096182630010135 19775692770144273945015203)
                  ·
                    refine ⟨29663539155216410917522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19775692770144273945015203 29663539155216410917522805)
                    ·
                      refine ⟨2780956795801538523517763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29663539155216410917522805 2780956795801538523517763)
                      ·
                        rfl

theorem cell23_5415894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5415894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415894 prefixEnd_5415894 := by exact prefixLift 5415894
  have htrace : WordTrace (prefixWord ++ tailWord_5415894) baseStart_5415894 baseEnd_5415894 := by
    simpa [prefixWord, tailWord_5415894, baseEnd_5415894] using wordTrace_append hprefix tailTrace_5415894
  have hstable : (prefixWord ++ tailWord_5415894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415894).length < 2 ^ (prefixWord ++ tailWord_5415894).sum := by decide
  have hdescent : baseEnd_5415894 < baseStart_5415894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415901 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_5415901 : Nat := 118140960795 + 5415901 * 2 ^ 59
def prefixEnd_5415901 : Nat := 4983230072969 + 3 ^ 40 * 5415901 * 2
def baseEnd_5415901 : Nat := 926986796722039998710077

theorem tailTrace_5415901 : CollatzResearch.WordTrace tailWord_5415901 prefixEnd_5415901 926986796722039998710077 := by
  unfold tailWord_5415901
  simp only [CollatzResearch.WordTrace]
  refine ⟨197534137552123114095903557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131689425034748742730602371 197534137552123114095903557)
  ·
    refine ⟨37037650791023083892981917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197534137552123114095903557 37037650791023083892981917)
    ·
      refine ⟨13889119046633656459868219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37037650791023083892981917 13889119046633656459868219)
      ·
        refine ⟨20833678569950484689802329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13889119046633656459868219 20833678569950484689802329)
        ·
          refine ⟨15625258927462863517351747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20833678569950484689802329 15625258927462863517351747)
          ·
            refine ⟨23437888391194295276027621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625258927462863517351747 23437888391194295276027621)
            ·
              refine ⟨4394604073348930364255179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23437888391194295276027621 4394604073348930364255179)
              ·
                refine ⟨6591906110023395546382769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394604073348930364255179 6591906110023395546382769)
                ·
                  refine ⟨4943929582517546659787077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6591906110023395546382769 4943929582517546659787077)
                  ·
                    refine ⟨926986796722039998710077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943929582517546659787077 926986796722039998710077)
                    ·
                      rfl

theorem cell23_5415901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_5415901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415901 prefixEnd_5415901 := by exact prefixLift 5415901
  have htrace : WordTrace (prefixWord ++ tailWord_5415901) baseStart_5415901 baseEnd_5415901 := by
    simpa [prefixWord, tailWord_5415901, baseEnd_5415901] using wordTrace_append hprefix tailTrace_5415901
  have hstable : (prefixWord ++ tailWord_5415901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415901).length < 2 ^ (prefixWord ++ tailWord_5415901).sum := by decide
  have hdescent : baseEnd_5415901 < baseStart_5415901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415907 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3]
def baseStart_5415907 : Nat := 118140960795 + 5415907 * 2 ^ 59
def prefixEnd_5415907 : Nat := 4983230072969 + 3 ^ 40 * 5415907 * 2
def baseEnd_5415907 : Nat := 2780963471050046972655203

theorem tailTrace_5415907 : CollatzResearch.WordTrace tailWord_5415907 prefixEnd_5415907 2780963471050046972655203 := by
  unfold tailWord_5415907
  simp only [CollatzResearch.WordTrace]
  refine ⟨197534356390101377120621975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131689570926734251413747983 197534356390101377120621975)
  ·
    refine ⟨296301534585152065680932963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197534356390101377120621975 296301534585152065680932963)
    ·
      refine ⟨444452301877728098521399445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296301534585152065680932963 444452301877728098521399445)
      ·
        refine ⟨20833701650518504618190599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 444452301877728098521399445 20833701650518504618190599)
        ·
          refine ⟨31250552475777756927285899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20833701650518504618190599 31250552475777756927285899)
          ·
            refine ⟨46875828713666635390928849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31250552475777756927285899 46875828713666635390928849)
            ·
              refine ⟨35156871535249976543196637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46875828713666635390928849 35156871535249976543196637)
              ·
                refine ⟨13183826825718741203698739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35156871535249976543196637 13183826825718741203698739)
                ·
                  refine ⟨19775740238578111805548109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13183826825718741203698739 19775740238578111805548109)
                  ·
                    refine ⟨7415902589466791927080541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19775740238578111805548109 7415902589466791927080541)
                    ·
                      refine ⟨2780963471050046972655203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7415902589466791927080541 2780963471050046972655203)
                      ·
                        rfl

theorem cell23_5415907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_5415907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415907 prefixEnd_5415907 := by exact prefixLift 5415907
  have htrace : WordTrace (prefixWord ++ tailWord_5415907) baseStart_5415907 baseEnd_5415907 := by
    simpa [prefixWord, tailWord_5415907, baseEnd_5415907] using wordTrace_append hprefix tailTrace_5415907
  have hstable : (prefixWord ++ tailWord_5415907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415907).length < 2 ^ (prefixWord ++ tailWord_5415907).sum := by decide
  have hdescent : baseEnd_5415907 < baseStart_5415907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415911 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5415911 : Nat := 118140960795 + 5415911 * 2 ^ 59
def prefixEnd_5415911 : Nat := 4983230072969 + 3 ^ 40 * 5415911 * 2
def baseEnd_5415911 : Nat := 2780965524972664957005185

theorem tailTrace_5415911 : CollatzResearch.WordTrace tailWord_5415911 prefixEnd_5415911 2780965524972664957005185 := by
  unfold tailWord_5415911
  simp only [CollatzResearch.WordTrace]
  refine ⟨197534502282086885803767587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131689668188057923869178391 197534502282086885803767587)
  ·
    refine ⟨296301753423130328705651381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197534502282086885803767587 296301753423130328705651381)
    ·
      refine ⟨27778289383418468316154817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296301753423130328705651381 27778289383418468316154817)
      ·
        refine ⟨20833717037563851237116113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27778289383418468316154817 20833717037563851237116113)
        ·
          refine ⟨15625287778172888427837085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20833717037563851237116113 15625287778172888427837085)
          ·
            refine ⟨5859482916814833160438907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15625287778172888427837085 5859482916814833160438907)
            ·
              refine ⟨8789224375222249740658361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859482916814833160438907 8789224375222249740658361)
              ·
                refine ⟨6591918281416687305493771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789224375222249740658361 6591918281416687305493771)
                ·
                  refine ⟨9887877422125030958240657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6591918281416687305493771 9887877422125030958240657)
                  ·
                    refine ⟨7415908066593773218680493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9887877422125030958240657 7415908066593773218680493)
                    ·
                      refine ⟨2780965524972664957005185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7415908066593773218680493 2780965524972664957005185)
                      ·
                        rfl

theorem cell23_5415911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5415911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415911 prefixEnd_5415911 := by exact prefixLift 5415911
  have htrace : WordTrace (prefixWord ++ tailWord_5415911) baseStart_5415911 baseEnd_5415911 := by
    simpa [prefixWord, tailWord_5415911, baseEnd_5415911] using wordTrace_append hprefix tailTrace_5415911
  have hstable : (prefixWord ++ tailWord_5415911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415911).length < 2 ^ (prefixWord ++ tailWord_5415911).sum := by decide
  have hdescent : baseEnd_5415911 < baseStart_5415911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415930 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_5415930 : Nat := 118140960795 + 5415930 * 2 ^ 59
def prefixEnd_5415930 : Nat := 4983230072969 + 3 ^ 40 * 5415930 * 2
def baseEnd_5415930 : Nat := 2780975281105100382667597

theorem tailTrace_5415930 : CollatzResearch.WordTrace tailWord_5415930 prefixEnd_5415930 2780975281105100382667597 := by
  unfold tailWord_5415930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49383798817254513012177311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131690130179345368032472829 49383798817254513012177311)
  ·
    refine ⟨74075698225881769518265967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49383798817254513012177311 74075698225881769518265967)
    ·
      refine ⟨111113547338822654277398951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74075698225881769518265967 111113547338822654277398951)
      ·
        refine ⟨166670321008233981416098427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111113547338822654277398951 166670321008233981416098427)
        ·
          refine ⟨250005481512350972124147641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166670321008233981416098427 250005481512350972124147641)
          ·
            refine ⟨187504111134263229093110731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250005481512350972124147641 187504111134263229093110731)
            ·
              refine ⟨281256166701394843639666097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187504111134263229093110731 281256166701394843639666097)
              ·
                refine ⟨210942125026046132729749573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281256166701394843639666097 210942125026046132729749573)
                ·
                  refine ⟨39551648442383649886828045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210942125026046132729749573 39551648442383649886828045)
                  ·
                    refine ⟨14831868165893868707560517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39551648442383649886828045 14831868165893868707560517)
                    ·
                      refine ⟨2780975281105100382667597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14831868165893868707560517 2780975281105100382667597)
                      ·
                        rfl

theorem cell23_5415930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_5415930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415930 prefixEnd_5415930 := by exact prefixLift 5415930
  have htrace : WordTrace (prefixWord ++ tailWord_5415930) baseStart_5415930 baseEnd_5415930 := by
    simpa [prefixWord, tailWord_5415930, baseEnd_5415930] using wordTrace_append hprefix tailTrace_5415930
  have hstable : (prefixWord ++ tailWord_5415930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415930).length < 2 ^ (prefixWord ++ tailWord_5415930).sum := by decide
  have hdescent : baseEnd_5415930 < baseStart_5415930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415957 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_5415957 : Nat := 118140960795 + 5415957 * 2 ^ 59
def prefixEnd_5415957 : Nat := 4983230072969 + 3 ^ 40 * 5415957 * 2
def baseEnd_5415957 : Nat := 926996381694257259009991

theorem tailTrace_5415957 : CollatzResearch.WordTrace tailWord_5415957 prefixEnd_5415957 926996381694257259009991 := by
  unfold tailWord_5415957
  simp only [CollatzResearch.WordTrace]
  refine ⟨197536180039920235659942125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131690786693280157106628083 197536180039920235659942125)
  ·
    refine ⟨74076067514970088372478297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197536180039920235659942125 74076067514970088372478297)
    ·
      refine ⟨55557050636227566279358723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74076067514970088372478297 55557050636227566279358723)
      ·
        refine ⟨83335575954341349419038085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55557050636227566279358723 83335575954341349419038085)
        ·
          refine ⟨15625420491439003016069641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83335575954341349419038085 15625420491439003016069641)
          ·
            refine ⟨11719065368579252262052231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15625420491439003016069641 11719065368579252262052231)
            ·
              refine ⟨17578598052868878393078347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719065368579252262052231 17578598052868878393078347)
              ·
                refine ⟨26367897079303317589617521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17578598052868878393078347 26367897079303317589617521)
                ·
                  refine ⟨19775922809477488192213141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26367897079303317589617521 19775922809477488192213141)
                  ·
                    refine ⟨926996381694257259009991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19775922809477488192213141 926996381694257259009991)
                    ·
                      rfl

theorem cell23_5415957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_5415957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415957 prefixEnd_5415957 := by exact prefixLift 5415957
  have htrace : WordTrace (prefixWord ++ tailWord_5415957) baseStart_5415957 baseEnd_5415957 := by
    simpa [prefixWord, tailWord_5415957, baseEnd_5415957] using wordTrace_append hprefix tailTrace_5415957
  have hstable : (prefixWord ++ tailWord_5415957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415957).length < 2 ^ (prefixWord ++ tailWord_5415957).sum := by decide
  have hdescent : baseEnd_5415957 < baseStart_5415957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5415998 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5415998 : Nat := 118140960795 + 5415998 * 2 ^ 59
def prefixEnd_5415998 : Nat := 4983230072969 + 3 ^ 40 * 5415998 * 2
def baseEnd_5415998 : Nat := 2781010197789606116617285

theorem tailTrace_5415998 : CollatzResearch.WordTrace tailWord_5415998 prefixEnd_5415998 2781010197789606116617285 := by
  unfold tailWord_5415998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692209429096462457773081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131691783621847799774789765 24692209429096462457773081)
  ·
    refine ⟨18519157071822346843329811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24692209429096462457773081 18519157071822346843329811)
    ·
      refine ⟨27778735607733520264994717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18519157071822346843329811 27778735607733520264994717)
      ·
        refine ⟨10417025852900070099373019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27778735607733520264994717 10417025852900070099373019)
        ·
          refine ⟨15625538779350105149059529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10417025852900070099373019 15625538779350105149059529)
          ·
            refine ⟨11719154084512578861794647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15625538779350105149059529 11719154084512578861794647)
            ·
              refine ⟨17578731126768868292691971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719154084512578861794647 17578731126768868292691971)
              ·
                refine ⟨26368096690153302439037957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17578731126768868292691971 26368096690153302439037957)
                ·
                  refine ⟨4944018129403744207319617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26368096690153302439037957 4944018129403744207319617)
                  ·
                    refine ⟨3708013597052808155489713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944018129403744207319617 3708013597052808155489713)
                    ·
                      refine ⟨2781010197789606116617285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708013597052808155489713 2781010197789606116617285)
                      ·
                        rfl

theorem cell23_5415998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5415998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5415998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5415998 prefixEnd_5415998 := by exact prefixLift 5415998
  have htrace : WordTrace (prefixWord ++ tailWord_5415998) baseStart_5415998 baseEnd_5415998 := by
    simpa [prefixWord, tailWord_5415998, baseEnd_5415998] using wordTrace_append hprefix tailTrace_5415998
  have hstable : (prefixWord ++ tailWord_5415998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5415998).length < 2 ^ (prefixWord ++ tailWord_5415998).sum := by decide
  have hdescent : baseEnd_5415998 < baseStart_5415998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5415998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416034 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5416034 : Nat := 118140960795 + 5416034 * 2 ^ 59
def prefixEnd_5416034 : Nat := 4983230072969 + 3 ^ 40 * 5416034 * 2
def baseEnd_5416034 : Nat := 927009561031055991922373

theorem tailTrace_5416034 : CollatzResearch.WordTrace tailWord_5416034 prefixEnd_5416034 927009561031055991922373 := by
  unfold tailWord_5416034
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384747115160319452623789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131692658973760851873663437 49384747115160319452623789)
  ·
    refine ⟨18519280168185119794733921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49384747115160319452623789 18519280168185119794733921)
    ·
      refine ⟨13889460126138839846050441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18519280168185119794733921 13889460126138839846050441)
      ·
        refine ⟨10417095094604129884537831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13889460126138839846050441 10417095094604129884537831)
        ·
          refine ⟨15625642641906194826806747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10417095094604129884537831 15625642641906194826806747)
          ·
            refine ⟨23438463962859292240210121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625642641906194826806747 23438463962859292240210121)
            ·
              refine ⟨17578847972144469180157591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23438463962859292240210121 17578847972144469180157591)
              ·
                refine ⟨26368271958216703770236387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17578847972144469180157591 26368271958216703770236387)
                ·
                  refine ⟨39552407937325055655354581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26368271958216703770236387 39552407937325055655354581)
                  ·
                    refine ⟨927009561031055991922373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39552407937325055655354581 927009561031055991922373)
                    ·
                      rfl

theorem cell23_5416034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5416034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416034 prefixEnd_5416034 := by exact prefixLift 5416034
  have htrace : WordTrace (prefixWord ++ tailWord_5416034) baseStart_5416034 baseEnd_5416034 := by
    simpa [prefixWord, tailWord_5416034, baseEnd_5416034] using wordTrace_append hprefix tailTrace_5416034
  have hstable : (prefixWord ++ tailWord_5416034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416034).length < 2 ^ (prefixWord ++ tailWord_5416034).sum := by decide
  have hdescent : baseEnd_5416034 < baseStart_5416034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416037 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_5416037 : Nat := 118140960795 + 5416037 * 2 ^ 59
def prefixEnd_5416037 : Nat := 4983230072969 + 3 ^ 40 * 5416037 * 2
def baseEnd_5416037 : Nat := 2781030223535131464029605

theorem tailTrace_5416037 : CollatzResearch.WordTrace tailWord_5416037 prefixEnd_5416037 2781030223535131464029605 := by
  unfold tailWord_5416037
  simp only [CollatzResearch.WordTrace]
  refine ⟨197539097879630409322854365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131692731919753606215236243 197539097879630409322854365)
  ·
    refine ⟨74077161704861403496070387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197539097879630409322854365 74077161704861403496070387)
    ·
      refine ⟨111115742557292105244105581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74077161704861403496070387 111115742557292105244105581)
      ·
        refine ⟨41668403458984539466539593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111115742557292105244105581 41668403458984539466539593)
        ·
          refine ⟨31251302594238404599904695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41668403458984539466539593 31251302594238404599904695)
          ·
            refine ⟨46876953891357606899857043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31251302594238404599904695 46876953891357606899857043)
            ·
              refine ⟨70315430837036410349785565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46876953891357606899857043 70315430837036410349785565)
              ·
                refine ⟨26368286563888653881169587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70315430837036410349785565 26368286563888653881169587)
                ·
                  refine ⟨39552429845832980821754381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26368286563888653881169587 39552429845832980821754381)
                  ·
                    refine ⟨14832161192187367808157893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39552429845832980821754381 14832161192187367808157893)
                    ·
                      refine ⟨2781030223535131464029605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832161192187367808157893 2781030223535131464029605)
                      ·
                        rfl

theorem cell23_5416037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_5416037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416037 prefixEnd_5416037 := by exact prefixLift 5416037
  have htrace : WordTrace (prefixWord ++ tailWord_5416037) baseStart_5416037 baseEnd_5416037 := by
    simpa [prefixWord, tailWord_5416037, baseEnd_5416037] using wordTrace_append hprefix tailTrace_5416037
  have hstable : (prefixWord ++ tailWord_5416037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416037).length < 2 ^ (prefixWord ++ tailWord_5416037).sum := by decide
  have hdescent : baseEnd_5416037 < baseStart_5416037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416064 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_5416064 : Nat := 118140960795 + 5416064 * 2 ^ 59
def prefixEnd_5416064 : Nat := 4983230072969 + 3 ^ 40 * 5416064 * 2
def baseEnd_5416064 : Nat := 927014695837600952797327

theorem tailTrace_5416064 : CollatzResearch.WordTrace tailWord_5416064 prefixEnd_5416064 927014695837600952797327 := by
  unfold tailWord_5416064
  simp only [CollatzResearch.WordTrace]
  refine ⟨98770041325266296467043623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131693388433688395289391497 98770041325266296467043623)
  ·
    refine ⟨148155061987899444700565435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98770041325266296467043623 148155061987899444700565435)
    ·
      refine ⟨222232592981849167050848153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148155061987899444700565435 222232592981849167050848153)
      ·
        refine ⟨166674444736386875288136115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222232592981849167050848153 166674444736386875288136115)
        ·
          refine ⟨250011667104580312932204173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166674444736386875288136115 250011667104580312932204173)
          ·
            refine ⟨93754375164217617349576565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250011667104580312932204173 93754375164217617349576565)
            ·
              refine ⟨8789472671645401626522803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93754375164217617349576565 8789472671645401626522803)
              ·
                refine ⟨13184209007468102439784205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789472671645401626522803 13184209007468102439784205)
                ·
                  refine ⟨4944078377800538414919077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13184209007468102439784205 4944078377800538414919077)
                  ·
                    refine ⟨927014695837600952797327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944078377800538414919077 927014695837600952797327)
                    ·
                      rfl

theorem cell23_5416064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_5416064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416064 prefixEnd_5416064 := by exact prefixLift 5416064
  have htrace : WordTrace (prefixWord ++ tailWord_5416064) baseStart_5416064 baseEnd_5416064 := by
    simpa [prefixWord, tailWord_5416064, baseEnd_5416064] using wordTrace_append hprefix tailTrace_5416064
  have hstable : (prefixWord ++ tailWord_5416064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416064).length < 2 ^ (prefixWord ++ tailWord_5416064).sum := by decide
  have hdescent : baseEnd_5416064 < baseStart_5416064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416074 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5416074 : Nat := 118140960795 + 5416074 * 2 ^ 59
def prefixEnd_5416074 : Nat := 4983230072969 + 3 ^ 40 * 5416074 * 2
def baseEnd_5416074 : Nat := 2781049222319347819266935

theorem tailTrace_5416074 : CollatzResearch.WordTrace tailWord_5416074 prefixEnd_5416074 2781049222319347819266935 := by
  unfold tailWord_5416074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385111845124091160487819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131693631586997576427967517 49385111845124091160487819)
  ·
    refine ⟨74077667767686136740731729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49385111845124091160487819 74077667767686136740731729)
    ·
      refine ⟨55558250825764602555548797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74077667767686136740731729 55558250825764602555548797)
      ·
        refine ⟨20834344059661725958330799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55558250825764602555548797 20834344059661725958330799)
        ·
          refine ⟨31251516089492588937496199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20834344059661725958330799 31251516089492588937496199)
          ·
            refine ⟨46877274134238883406244299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31251516089492588937496199 46877274134238883406244299)
            ·
              refine ⟨70315911201358325109366449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46877274134238883406244299 70315911201358325109366449)
              ·
                refine ⟨52736933401018743832024837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70315911201358325109366449 52736933401018743832024837)
                ·
                  refine ⟨9888175012691014468504657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52736933401018743832024837 9888175012691014468504657)
                  ·
                    refine ⟨7416131259518260851378493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9888175012691014468504657 7416131259518260851378493)
                    ·
                      refine ⟨2781049222319347819266935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416131259518260851378493 2781049222319347819266935)
                      ·
                        rfl

theorem cell23_5416074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5416074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416074 prefixEnd_5416074 := by exact prefixLift 5416074
  have htrace : WordTrace (prefixWord ++ tailWord_5416074) baseStart_5416074 baseEnd_5416074 := by
    simpa [prefixWord, tailWord_5416074, baseEnd_5416074] using wordTrace_append hprefix tailTrace_5416074
  have hstable : (prefixWord ++ tailWord_5416074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416074).length < 2 ^ (prefixWord ++ tailWord_5416074).sum := by decide
  have hdescent : baseEnd_5416074 < baseStart_5416074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416124 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_5416124 : Nat := 118140960795 + 5416124 * 2 ^ 59
def prefixEnd_5416124 : Nat := 4983230072969 + 3 ^ 40 * 5416124 * 2
def baseEnd_5416124 : Nat := 927024965450690874547235

theorem tailTrace_5416124 : CollatzResearch.WordTrace tailWord_5416124 prefixEnd_5416124 927024965450690874547235 := by
  unfold tailWord_5416124
  simp only [CollatzResearch.WordTrace]
  refine ⟨98771135515157611590635713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131694847353543482120847617 98771135515157611590635713)
  ·
    refine ⟨74078351636368208692976785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98771135515157611590635713 74078351636368208692976785)
    ·
      refine ⟨55558763727276156519732589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74078351636368208692976785 55558763727276156519732589)
      ·
        refine ⟨20834536397728558694899721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55558763727276156519732589 20834536397728558694899721)
        ·
          refine ⟨15625902298296419021174791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20834536397728558694899721 15625902298296419021174791)
          ·
            refine ⟨23438853447444628531762187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625902298296419021174791 23438853447444628531762187)
            ·
              refine ⟨35158280171166942797643281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23438853447444628531762187 35158280171166942797643281)
              ·
                refine ⟨26368710128375207098232461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35158280171166942797643281 26368710128375207098232461)
                ·
                  refine ⟨9888266298140702661837173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26368710128375207098232461 9888266298140702661837173)
                  ·
                    refine ⟨927024965450690874547235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9888266298140702661837173 927024965450690874547235)
                    ·
                      rfl

theorem cell23_5416124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_5416124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416124 prefixEnd_5416124 := by exact prefixLift 5416124
  have htrace : WordTrace (prefixWord ++ tailWord_5416124) baseStart_5416124 baseEnd_5416124 := by
    simpa [prefixWord, tailWord_5416124, baseEnd_5416124] using wordTrace_append hprefix tailTrace_5416124
  have hstable : (prefixWord ++ tailWord_5416124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416124).length < 2 ^ (prefixWord ++ tailWord_5416124).sum := by decide
  have hdescent : baseEnd_5416124 < baseStart_5416124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416147 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_5416147 : Nat := 118140960795 + 5416147 * 2 ^ 59
def prefixEnd_5416147 : Nat := 4983230072969 + 3 ^ 40 * 5416147 * 2
def baseEnd_5416147 : Nat := 2781086706407126033654099

theorem tailTrace_5416147 : CollatzResearch.WordTrace tailWord_5416147 prefixEnd_5416147 2781086706407126033654099 := by
  unfold tailWord_5416147
  simp only [CollatzResearch.WordTrace]
  refine ⟨197543109909231898109358695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131695406606154598739572463 197543109909231898109358695)
  ·
    refine ⟨296314664863847847164038043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197543109909231898109358695 296314664863847847164038043)
    ·
      refine ⟨444471997295771770746057065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296314664863847847164038043 444471997295771770746057065)
      ·
        refine ⟨333353997971828828059542799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444471997295771770746057065 333353997971828828059542799)
        ·
          refine ⟨500030996957743242089314199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333353997971828828059542799 500030996957743242089314199)
          ·
            refine ⟨750046495436614863133971299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500030996957743242089314199 750046495436614863133971299)
            ·
              refine ⟨1125069743154922294700956949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750046495436614863133971299 1125069743154922294700956949)
              ·
                refine ⟨52737644210386982564107357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1125069743154922294700956949 52737644210386982564107357)
                ·
                  refine ⟨19776616578895118461540259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52737644210386982564107357 19776616578895118461540259)
                  ·
                    refine ⟨29664924868342677692310389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19776616578895118461540259 29664924868342677692310389)
                    ·
                      refine ⟨2781086706407126033654099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29664924868342677692310389 2781086706407126033654099)
                      ·
                        rfl

theorem cell23_5416147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_5416147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416147 prefixEnd_5416147 := by exact prefixLift 5416147
  have htrace : WordTrace (prefixWord ++ tailWord_5416147) baseStart_5416147 baseEnd_5416147 := by
    simpa [prefixWord, tailWord_5416147, baseEnd_5416147] using wordTrace_append hprefix tailTrace_5416147
  have hstable : (prefixWord ++ tailWord_5416147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416147).length < 2 ^ (prefixWord ++ tailWord_5416147).sum := by decide
  have hdescent : baseEnd_5416147 < baseStart_5416147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416154 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_5416154 : Nat := 118140960795 + 5416154 * 2 ^ 59
def prefixEnd_5416154 : Nat := 4983230072969 + 3 ^ 40 * 5416154 * 2
def baseEnd_5416154 : Nat := 927030100257235835422189

theorem tailTrace_5416154 : CollatzResearch.WordTrace tailWord_5416154 prefixEnd_5416154 927030100257235835422189 := by
  unfold tailWord_5416154
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385841305051634576215879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131695576813471025536575677 49385841305051634576215879)
  ·
    refine ⟨74078761957577451864323819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49385841305051634576215879 74078761957577451864323819)
    ·
      refine ⟨111118142936366177796485729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74078761957577451864323819 111118142936366177796485729)
      ·
        refine ⟨83338607202274633347364297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111118142936366177796485729 83338607202274633347364297)
        ·
          refine ⟨62503955401705975010523223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83338607202274633347364297 62503955401705975010523223)
          ·
            refine ⟨93755933102558962515784835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62503955401705975010523223 93755933102558962515784835)
            ·
              refine ⟨140633899653838443773677253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93755933102558962515784835 140633899653838443773677253)
              ·
                refine ⟨26368856185094708207564485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140633899653838443773677253 26368856185094708207564485)
                ·
                  refine ⟨4944160534705257788918341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26368856185094708207564485 4944160534705257788918341)
                  ·
                    refine ⟨927030100257235835422189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944160534705257788918341 927030100257235835422189)
                    ·
                      rfl

theorem cell23_5416154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_5416154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416154 prefixEnd_5416154 := by exact prefixLift 5416154
  have htrace : WordTrace (prefixWord ++ tailWord_5416154) baseStart_5416154 baseEnd_5416154 := by
    simpa [prefixWord, tailWord_5416154, baseEnd_5416154] using wordTrace_append hprefix tailTrace_5416154
  have hstable : (prefixWord ++ tailWord_5416154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416154).length < 2 ^ (prefixWord ++ tailWord_5416154).sum := by decide
  have hdescent : baseEnd_5416154 < baseStart_5416154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416161 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_5416161 : Nat := 118140960795 + 5416161 * 2 ^ 59
def prefixEnd_5416161 : Nat := 4983230072969 + 3 ^ 40 * 5416161 * 2
def baseEnd_5416161 : Nat := 2781093895136288978879035

theorem tailTrace_5416161 : CollatzResearch.WordTrace tailWord_5416161 prefixEnd_5416161 2781093895136288978879035 := by
  unfold tailWord_5416161
  simp only [CollatzResearch.WordTrace]
  refine ⟨197543620531181178500368337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131695747020787452333578891 197543620531181178500368337)
  ·
    refine ⟨148157715398385883875276253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197543620531181178500368337 148157715398385883875276253)
    ·
      refine ⟨55559143274394706453228595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148157715398385883875276253 55559143274394706453228595)
      ·
        refine ⟨83338714911592059679842893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55559143274394706453228595 83338714911592059679842893)
        ·
          refine ⟨31252018091847022379941085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83338714911592059679842893 31252018091847022379941085)
          ·
            refine ⟨11719506784442633392477907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31252018091847022379941085 11719506784442633392477907)
            ·
              refine ⟨17579260176663950088716861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719506784442633392477907 17579260176663950088716861)
              ·
                refine ⟨6592222566248981283268823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17579260176663950088716861 6592222566248981283268823)
                ·
                  refine ⟨9888333849373471924903235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592222566248981283268823 9888333849373471924903235)
                  ·
                    refine ⟨14832500774060207887354853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9888333849373471924903235 14832500774060207887354853)
                    ·
                      refine ⟨2781093895136288978879035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832500774060207887354853 2781093895136288978879035)
                      ·
                        rfl

theorem cell23_5416161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_5416161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416161 prefixEnd_5416161 := by exact prefixLift 5416161
  have htrace : WordTrace (prefixWord ++ tailWord_5416161) baseStart_5416161 baseEnd_5416161 := by
    simpa [prefixWord, tailWord_5416161, baseEnd_5416161] using wordTrace_append hprefix tailTrace_5416161
  have hstable : (prefixWord ++ tailWord_5416161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416161).length < 2 ^ (prefixWord ++ tailWord_5416161).sum := by decide
  have hdescent : baseEnd_5416161 < baseStart_5416161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416171 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 2, 4]
def baseStart_5416171 : Nat := 118140960795 + 5416171 * 2 ^ 59
def prefixEnd_5416171 : Nat := 4983230072969 + 3 ^ 40 * 5416171 * 2
def baseEnd_5416171 : Nat := 927033009980944646584663

theorem tailTrace_5416171 : CollatzResearch.WordTrace tailWord_5416171 prefixEnd_5416171 927033009980944646584663 := by
  unfold tailWord_5416171
  simp only [CollatzResearch.WordTrace]
  refine ⟨197543985261144950208232367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131695990174096633472154911 197543985261144950208232367)
  ·
    refine ⟨296315977891717425312348551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197543985261144950208232367 296315977891717425312348551)
    ·
      refine ⟨444473966837576137968522827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296315977891717425312348551 444473966837576137968522827)
      ·
        refine ⟨666710950256364206952784241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444473966837576137968522827 666710950256364206952784241)
        ·
          refine ⟨500033212692273155214588181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666710950256364206952784241 500033212692273155214588181)
          ·
            refine ⟨23439056844950304150683821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 500033212692273155214588181 23439056844950304150683821)
            ·
              refine ⟨8789646316856364056506433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23439056844950304150683821 8789646316856364056506433)
              ·
                refine ⟨6592234737642273042379825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789646316856364056506433 6592234737642273042379825)
                ·
                  refine ⟨4944176053231704781784869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592234737642273042379825 4944176053231704781784869)
                  ·
                    refine ⟨927033009980944646584663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944176053231704781784869 927033009980944646584663)
                    ·
                      rfl

theorem cell23_5416171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 4].length) (baseStart_5416171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416171 prefixEnd_5416171 := by exact prefixLift 5416171
  have htrace : WordTrace (prefixWord ++ tailWord_5416171) baseStart_5416171 baseEnd_5416171 := by
    simpa [prefixWord, tailWord_5416171, baseEnd_5416171] using wordTrace_append hprefix tailTrace_5416171
  have hstable : (prefixWord ++ tailWord_5416171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416171).length < 2 ^ (prefixWord ++ tailWord_5416171).sum := by decide
  have hdescent : baseEnd_5416171 < baseStart_5416171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416174 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5416174 : Nat := 118140960795 + 5416174 * 2 ^ 59
def prefixEnd_5416174 : Nat := 4983230072969 + 3 ^ 40 * 5416174 * 2
def baseEnd_5416174 : Nat := 2781100570384797428016475

theorem tailTrace_5416174 : CollatzResearch.WordTrace tailWord_5416174 prefixEnd_5416174 2781100570384797428016475 := by
  unfold tailWord_5416174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693011835016760215073947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131696063120089387813727717 24693011835016760215073947)
  ·
    refine ⟨37039517752525140322610921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24693011835016760215073947 37039517752525140322610921)
    ·
      refine ⟨27779638314393855241958191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37039517752525140322610921 27779638314393855241958191)
      ·
        refine ⟨41669457471590782862937287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27779638314393855241958191 41669457471590782862937287)
        ·
          refine ⟨62504186207386174294405931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41669457471590782862937287 62504186207386174294405931)
          ·
            refine ⟨93756279311079261441608897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62504186207386174294405931 93756279311079261441608897)
            ·
              refine ⟨70317209483309446081206673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93756279311079261441608897 70317209483309446081206673)
              ·
                refine ⟨52737907112482084560905005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70317209483309446081206673 52737907112482084560905005)
                ·
                  refine ⟨19776715167180781710339377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52737907112482084560905005 19776715167180781710339377)
                  ·
                    refine ⟨14832536375385586282754533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19776715167180781710339377 14832536375385586282754533)
                    ·
                      refine ⟨2781100570384797428016475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832536375385586282754533 2781100570384797428016475)
                      ·
                        rfl

theorem cell23_5416174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5416174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416174 prefixEnd_5416174 := by exact prefixLift 5416174
  have htrace : WordTrace (prefixWord ++ tailWord_5416174) baseStart_5416174 baseEnd_5416174 := by
    simpa [prefixWord, tailWord_5416174, baseEnd_5416174] using wordTrace_append hprefix tailTrace_5416174
  have hstable : (prefixWord ++ tailWord_5416174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416174).length < 2 ^ (prefixWord ++ tailWord_5416174).sum := by decide
  have hdescent : baseEnd_5416174 < baseStart_5416174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_5416177 : Nat := 118140960795 + 5416177 * 2 ^ 59
def prefixEnd_5416177 : Nat := 4983230072969 + 3 ^ 40 * 5416177 * 2
def baseEnd_5416177 : Nat := 2781102110826760916278961

theorem tailTrace_5416177 : CollatzResearch.WordTrace tailWord_5416177 prefixEnd_5416177 2781102110826760916278961 := by
  unfold tailWord_5416177
  simp only [CollatzResearch.WordTrace]
  refine ⟨197544204099123213232950785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131696136066082142155300523 197544204099123213232950785)
  ·
    refine ⟨148158153074342409924713089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197544204099123213232950785 148158153074342409924713089)
    ·
      refine ⟨111118614805756807443534817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148158153074342409924713089 111118614805756807443534817)
      ·
        refine ⟨83338961104317605582651113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111118614805756807443534817 83338961104317605582651113)
        ·
          refine ⟨62504220828238204186988335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83338961104317605582651113 62504220828238204186988335)
          ·
            refine ⟨93756331242357306280482503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62504220828238204186988335 93756331242357306280482503)
            ·
              refine ⟨140634496863535959420723755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93756331242357306280482503 140634496863535959420723755)
              ·
                refine ⟨210951745295303939131085633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140634496863535959420723755 210951745295303939131085633)
                ·
                  refine ⟨158213808971477954348314225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210951745295303939131085633 158213808971477954348314225)
                  ·
                    refine ⟨118660356728608465761235669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158213808971477954348314225 118660356728608465761235669)
                    ·
                      refine ⟨2781102110826760916278961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118660356728608465761235669 2781102110826760916278961)
                      ·
                        rfl

theorem cell23_5416177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_5416177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416177 prefixEnd_5416177 := by exact prefixLift 5416177
  have htrace : WordTrace (prefixWord ++ tailWord_5416177) baseStart_5416177 baseEnd_5416177 := by
    simpa [prefixWord, tailWord_5416177, baseEnd_5416177] using wordTrace_append hprefix tailTrace_5416177
  have hstable : (prefixWord ++ tailWord_5416177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416177).length < 2 ^ (prefixWord ++ tailWord_5416177).sum := by decide
  have hdescent : baseEnd_5416177 < baseStart_5416177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416188 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5416188 : Nat := 118140960795 + 5416188 * 2 ^ 59
def prefixEnd_5416188 : Nat := 4983230072969 + 3 ^ 40 * 5416188 * 2
def baseEnd_5416188 : Nat := 927035919704653457747137

theorem tailTrace_5416188 : CollatzResearch.WordTrace tailWord_5416188 prefixEnd_5416188 927035919704653457747137 := by
  unfold tailWord_5416188
  simp only [CollatzResearch.WordTrace]
  refine ⟨98772302651041681055800609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131696403534722241407734145 98772302651041681055800609)
  ·
    refine ⟨74079226988281260791850457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98772302651041681055800609 74079226988281260791850457)
    ·
      refine ⟨55559420241210945593887843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74079226988281260791850457 55559420241210945593887843)
      ·
        refine ⟨83339130361816418390831765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55559420241210945593887843 83339130361816418390831765)
        ·
          refine ⟨3906521735710144612070239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83339130361816418390831765 3906521735710144612070239)
          ·
            refine ⟨5859782603565216918105359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906521735710144612070239 5859782603565216918105359)
            ·
              refine ⟨8789673905347825377158039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859782603565216918105359 8789673905347825377158039)
              ·
                refine ⟨13184510858021738065737059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789673905347825377158039 13184510858021738065737059)
                ·
                  refine ⟨19776766287032607098605589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184510858021738065737059 19776766287032607098605589)
                  ·
                    refine ⟨927035919704653457747137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19776766287032607098605589 927035919704653457747137)
                    ·
                      rfl

theorem cell23_5416188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5416188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416188 prefixEnd_5416188 := by exact prefixLift 5416188
  have htrace : WordTrace (prefixWord ++ tailWord_5416188) baseStart_5416188 baseEnd_5416188 := by
    simpa [prefixWord, tailWord_5416188, baseEnd_5416188] using wordTrace_append hprefix tailTrace_5416188
  have hstable : (prefixWord ++ tailWord_5416188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416188).length < 2 ^ (prefixWord ++ tailWord_5416188).sum := by decide
  have hdescent : baseEnd_5416188 < baseStart_5416188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416191 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_5416191 : Nat := 118140960795 + 5416191 * 2 ^ 59
def prefixEnd_5416191 : Nat := 4983230072969 + 3 ^ 40 * 5416191 * 2
def baseEnd_5416191 : Nat := 2781109299555923861503897

theorem tailTrace_5416191 : CollatzResearch.WordTrace tailWord_5416191 prefixEnd_5416191 2781109299555923861503897 := by
  unfold tailWord_5416191
  simp only [CollatzResearch.WordTrace]
  refine ⟨197544714721072493623960427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131696476480714995749306951 197544714721072493623960427)
  ·
    refine ⟨296317072081608740435940641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197544714721072493623960427 296317072081608740435940641)
    ·
      refine ⟨222237804061206555326955481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296317072081608740435940641 222237804061206555326955481)
      ·
        refine ⟨166678353045904916495216611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222237804061206555326955481 166678353045904916495216611)
        ·
          refine ⟨250017529568857374742824917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166678353045904916495216611 250017529568857374742824917)
          ·
            refine ⟨5859785849270094720534959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 250017529568857374742824917 5859785849270094720534959)
            ·
              refine ⟨8789678773905142080802439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859785849270094720534959 8789678773905142080802439)
              ·
                refine ⟨13184518160857713121203659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789678773905142080802439 13184518160857713121203659)
                ·
                  refine ⟨19776777241286569681805489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184518160857713121203659 19776777241286569681805489)
                  ·
                    refine ⟨14832582930964927261354117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19776777241286569681805489 14832582930964927261354117)
                    ·
                      refine ⟨2781109299555923861503897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832582930964927261354117 2781109299555923861503897)
                      ·
                        rfl

theorem cell23_5416191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_5416191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416191 prefixEnd_5416191 := by exact prefixLift 5416191
  have htrace : WordTrace (prefixWord ++ tailWord_5416191) baseStart_5416191 baseEnd_5416191 := by
    simpa [prefixWord, tailWord_5416191, baseEnd_5416191] using wordTrace_append hprefix tailTrace_5416191
  have hstable : (prefixWord ++ tailWord_5416191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416191).length < 2 ^ (prefixWord ++ tailWord_5416191).sum := by decide
  have hdescent : baseEnd_5416191 < baseStart_5416191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416217 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_5416217 : Nat := 118140960795 + 5416217 * 2 ^ 59
def prefixEnd_5416217 : Nat := 4983230072969 + 3 ^ 40 * 5416217 * 2
def baseEnd_5416217 : Nat := 2781122650052940759778777

theorem tailTrace_5416217 : CollatzResearch.WordTrace tailWord_5416217 prefixEnd_5416217 2781122650052940759778777 := by
  unfold tailWord_5416217
  simp only [CollatzResearch.WordTrace]
  refine ⟨197545663018978300064406905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131697108679318866709604603 197545663018978300064406905)
  ·
    refine ⟨148159247264233725048305179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197545663018978300064406905 148159247264233725048305179)
    ·
      refine ⟨222238870896350587572457769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148159247264233725048305179 222238870896350587572457769)
      ·
        refine ⟨166679153172262940679343327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222238870896350587572457769 166679153172262940679343327)
        ·
          refine ⟨250018729758394411019014991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166679153172262940679343327 250018729758394411019014991)
          ·
            refine ⟨375028094637591616528522487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250018729758394411019014991 375028094637591616528522487)
            ·
              refine ⟨562542141956387424792783731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375028094637591616528522487 562542141956387424792783731)
              ·
                refine ⟨843813212934581137189175597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562542141956387424792783731 843813212934581137189175597)
                ·
                  refine ⟨316429954850467926445940849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843813212934581137189175597 316429954850467926445940849)
                  ·
                    refine ⟨237322466137850944834455637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 316429954850467926445940849 237322466137850944834455637)
                    ·
                      refine ⟨2781122650052940759778777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237322466137850944834455637 2781122650052940759778777)
                      ·
                        rfl

theorem cell23_5416217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_5416217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416217 prefixEnd_5416217 := by exact prefixLift 5416217
  have htrace : WordTrace (prefixWord ++ tailWord_5416217) baseStart_5416217 baseEnd_5416217 := by
    simpa [prefixWord, tailWord_5416217, baseEnd_5416217] using wordTrace_append hprefix tailTrace_5416217
  have hstable : (prefixWord ++ tailWord_5416217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416217).length < 2 ^ (prefixWord ++ tailWord_5416217).sum := by decide
  have hdescent : baseEnd_5416217 < baseStart_5416217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416228 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_5416228 : Nat := 118140960795 + 5416228 * 2 ^ 59
def prefixEnd_5416228 : Nat := 4983230072969 + 3 ^ 40 * 5416228 * 2
def baseEnd_5416228 : Nat := 2781128298340140216741227

theorem tailTrace_5416228 : CollatzResearch.WordTrace tailWord_5416228 prefixEnd_5416228 2781128298340140216741227 := by
  unfold tailWord_5416228
  simp only [CollatzResearch.WordTrace]
  refine ⟨98773032110969224471528669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131697376147958965962038225 98773032110969224471528669)
  ·
    refine ⟨37039887041613459176823251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98773032110969224471528669 37039887041613459176823251)
    ·
      refine ⟨55559830562420188765234877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37039887041613459176823251 55559830562420188765234877)
      ·
        refine ⟨20834936460907570786963079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55559830562420188765234877 20834936460907570786963079)
        ·
          refine ⟨31252404691361356180444619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20834936460907570786963079 31252404691361356180444619)
          ·
            refine ⟨46878607037042034270666929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31252404691361356180444619 46878607037042034270666929)
            ·
              refine ⟨35158955277781525703000197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46878607037042034270666929 35158955277781525703000197)
              ·
                refine ⟨6592304114584036069312537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35158955277781525703000197 6592304114584036069312537)
                ·
                  refine ⟨4944228085938027051984403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592304114584036069312537 4944228085938027051984403)
                  ·
                    refine ⟨7416342128907040577976605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944228085938027051984403 7416342128907040577976605)
                    ·
                      refine ⟨2781128298340140216741227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416342128907040577976605 2781128298340140216741227)
                      ·
                        rfl

theorem cell23_5416228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_5416228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416228 prefixEnd_5416228 := by exact prefixLift 5416228
  have htrace : WordTrace (prefixWord ++ tailWord_5416228) baseStart_5416228 baseEnd_5416228 := by
    simpa [prefixWord, tailWord_5416228, baseEnd_5416228] using wordTrace_append hprefix tailTrace_5416228
  have hstable : (prefixWord ++ tailWord_5416228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416228).length < 2 ^ (prefixWord ++ tailWord_5416228).sum := by decide
  have hdescent : baseEnd_5416228 < baseStart_5416228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416245 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_5416245 : Nat := 118140960795 + 5416245 * 2 ^ 59
def prefixEnd_5416245 : Nat := 4983230072969 + 3 ^ 40 * 5416245 * 2
def baseEnd_5416245 : Nat := 2781137027511266650228649

theorem tailTrace_5416245 : CollatzResearch.WordTrace tailWord_5416245 prefixEnd_5416245 2781137027511266650228649 := by
  unfold tailWord_5416245
  simp only [CollatzResearch.WordTrace]
  refine ⟨197546684262876860846426189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131697789508584573897617459 197546684262876860846426189)
  ·
    refine ⟨74080006598578822817409821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197546684262876860846426189 74080006598578822817409821)
    ·
      refine ⟨27780002474467058556528683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74080006598578822817409821 27780002474467058556528683)
      ·
        refine ⟨41670003711700587834793025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27780002474467058556528683 41670003711700587834793025)
        ·
          refine ⟨31252502783775440876094769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41670003711700587834793025 31252502783775440876094769)
          ·
            refine ⟨23439377087831580657071077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31252502783775440876094769 23439377087831580657071077)
            ·
              refine ⟨4394883203968421373200827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23439377087831580657071077 4394883203968421373200827)
              ·
                refine ⟨6592324805952632059801241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394883203968421373200827 6592324805952632059801241)
                ·
                  refine ⟨4944243604464474044850931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592324805952632059801241 4944243604464474044850931)
                  ·
                    refine ⟨7416365406696711067276397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944243604464474044850931 7416365406696711067276397)
                    ·
                      refine ⟨2781137027511266650228649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416365406696711067276397 2781137027511266650228649)
                      ·
                        rfl

theorem cell23_5416245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_5416245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416245 prefixEnd_5416245 := by exact prefixLift 5416245
  have htrace : WordTrace (prefixWord ++ tailWord_5416245) baseStart_5416245 baseEnd_5416245 := by
    simpa [prefixWord, tailWord_5416245, baseEnd_5416245] using wordTrace_append hprefix tailTrace_5416245
  have hstable : (prefixWord ++ tailWord_5416245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416245).length < 2 ^ (prefixWord ++ tailWord_5416245).sum := by decide
  have hdescent : baseEnd_5416245 < baseStart_5416245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416255 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 1, 3, 2]
def baseStart_5416255 : Nat := 118140960795 + 5416255 * 2 ^ 59
def prefixEnd_5416255 : Nat := 4983230072969 + 3 ^ 40 * 5416255 * 2
def baseEnd_5416255 : Nat := 2781142162317811611103603

theorem tailTrace_5416255 : CollatzResearch.WordTrace tailWord_5416255 prefixEnd_5416255 2781142162317811611103603 := by
  unfold tailWord_5416255
  simp only [CollatzResearch.WordTrace]
  refine ⟨197547048992840632554290219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131698032661893755036193479 197547048992840632554290219)
  ·
    refine ⟨296320573489260948831435329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197547048992840632554290219 296320573489260948831435329)
    ·
      refine ⟨222240430116945711623576497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296320573489260948831435329 222240430116945711623576497)
      ·
        refine ⟨166680322587709283717682373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222240430116945711623576497 166680322587709283717682373)
        ·
          refine ⟨31252560485195490697065445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166680322587709283717682373 31252560485195490697065445)
          ·
            refine ⟨5859855090974154505699771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31252560485195490697065445 5859855090974154505699771)
            ·
              refine ⟨8789782636461231758549657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859855090974154505699771 8789782636461231758549657)
              ·
                refine ⟨6592336977345923818912243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789782636461231758549657 6592336977345923818912243)
                ·
                  refine ⟨9888505466018885728368365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592336977345923818912243 9888505466018885728368365)
                  ·
                    refine ⟨3708189549757082148138137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9888505466018885728368365 3708189549757082148138137)
                    ·
                      refine ⟨2781142162317811611103603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708189549757082148138137 2781142162317811611103603)
                      ·
                        rfl

theorem cell23_5416255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_5416255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416255 prefixEnd_5416255 := by exact prefixLift 5416255
  have htrace : WordTrace (prefixWord ++ tailWord_5416255) baseStart_5416255 baseEnd_5416255 := by
    simpa [prefixWord, tailWord_5416255, baseEnd_5416255] using wordTrace_append hprefix tailTrace_5416255
  have hstable : (prefixWord ++ tailWord_5416255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416255).length < 2 ^ (prefixWord ++ tailWord_5416255).sum := by decide
  have hdescent : baseEnd_5416255 < baseStart_5416255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416262 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5416262 : Nat := 118140960795 + 5416262 * 2 ^ 59
def prefixEnd_5416262 : Nat := 4983230072969 + 3 ^ 40 * 5416262 * 2
def baseEnd_5416262 : Nat := 2781145756682393083716071

theorem tailTrace_5416262 : CollatzResearch.WordTrace tailWord_5416262 prefixEnd_5416262 2781145756682393083716071 := by
  unfold tailWord_5416262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6173353259494227273431095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131698202869210181833196693 6173353259494227273431095)
  ·
    refine ⟨9260029889241340910146643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6173353259494227273431095 9260029889241340910146643)
    ·
      refine ⟨13890044833862011365219965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9260029889241340910146643 13890044833862011365219965)
      ·
        refine ⟨5208766812698254261957487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13890044833862011365219965 5208766812698254261957487)
        ·
          refine ⟨7813150219047381392936231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208766812698254261957487 7813150219047381392936231)
          ·
            refine ⟨11719725328571072089404347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813150219047381392936231 11719725328571072089404347)
            ·
              refine ⟨17579587992856608134106521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719725328571072089404347 17579587992856608134106521)
              ·
                refine ⟨13184690994642456100579891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17579587992856608134106521 13184690994642456100579891)
                ·
                  refine ⟨19777036491963684150869837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184690994642456100579891 19777036491963684150869837)
                  ·
                    refine ⟨7416388684486381556576189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19777036491963684150869837 7416388684486381556576189)
                    ·
                      refine ⟨2781145756682393083716071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416388684486381556576189 2781145756682393083716071)
                      ·
                        rfl

theorem cell23_5416262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5416262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416262 prefixEnd_5416262 := by exact prefixLift 5416262
  have htrace : WordTrace (prefixWord ++ tailWord_5416262) baseStart_5416262 baseEnd_5416262 := by
    simpa [prefixWord, tailWord_5416262, baseEnd_5416262] using wordTrace_append hprefix tailTrace_5416262
  have hstable : (prefixWord ++ tailWord_5416262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416262).length < 2 ^ (prefixWord ++ tailWord_5416262).sum := by decide
  have hdescent : baseEnd_5416262 < baseStart_5416262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416264 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_5416264 : Nat := 118140960795 + 5416264 * 2 ^ 59
def prefixEnd_5416264 : Nat := 4983230072969 + 3 ^ 40 * 5416264 * 2
def baseEnd_5416264 : Nat := 2781146783643702075891061

theorem tailTrace_5416264 : CollatzResearch.WordTrace tailWord_5416264 prefixEnd_5416264 2781146783643702075891061 := by
  unfold tailWord_5416264
  simp only [CollatzResearch.WordTrace]
  refine ⟨98773688624904013545683923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131698251499872018060911897 98773688624904013545683923)
  ·
    refine ⟨148160532937356020318525885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98773688624904013545683923 148160532937356020318525885)
    ·
      refine ⟨55560199851508507619447207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148160532937356020318525885 55560199851508507619447207)
      ·
        refine ⟨83340299777262761429170811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55560199851508507619447207 83340299777262761429170811)
        ·
          refine ⟨125010449665894142143756217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83340299777262761429170811 125010449665894142143756217)
          ·
            refine ⟨93757837249420606607817163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125010449665894142143756217 93757837249420606607817163)
            ·
              refine ⟨140636755874130909911725745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93757837249420606607817163 140636755874130909911725745)
              ·
                refine ⟨105477566905598182433794309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140636755874130909911725745 105477566905598182433794309)
                ·
                  refine ⟨19777043794799659206336433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105477566905598182433794309 19777043794799659206336433)
                  ·
                    refine ⟨14832782846099744404752325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19777043794799659206336433 14832782846099744404752325)
                    ·
                      refine ⟨2781146783643702075891061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832782846099744404752325 2781146783643702075891061)
                      ·
                        rfl

theorem cell23_5416264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_5416264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416264 prefixEnd_5416264 := by exact prefixLift 5416264
  have htrace : WordTrace (prefixWord ++ tailWord_5416264) baseStart_5416264 baseEnd_5416264 := by
    simpa [prefixWord, tailWord_5416264, baseEnd_5416264] using wordTrace_append hprefix tailTrace_5416264
  have hstable : (prefixWord ++ tailWord_5416264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416264).length < 2 ^ (prefixWord ++ tailWord_5416264).sum := by decide
  have hdescent : baseEnd_5416264 < baseStart_5416264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416268 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5416268 : Nat := 118140960795 + 5416268 * 2 ^ 59
def prefixEnd_5416268 : Nat := 4983230072969 + 3 ^ 40 * 5416268 * 2
def baseEnd_5416268 : Nat := 2781148837566320060241043

theorem tailTrace_5416268 : CollatzResearch.WordTrace tailWord_5416268 prefixEnd_5416268 2781148837566320060241043 := by
  unfold tailWord_5416268
  simp only [CollatzResearch.WordTrace]
  refine ⟨98773761570896767887256729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131698348761195690516342305 98773761570896767887256729)
  ·
    refine ⟨74080321178172575915442547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98773761570896767887256729 74080321178172575915442547)
    ·
      refine ⟨111120481767258863873163821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74080321178172575915442547 111120481767258863873163821)
      ·
        refine ⟨41670180662722073952436433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111120481767258863873163821 41670180662722073952436433)
        ·
          refine ⟨31252635497041555464327325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41670180662722073952436433 31252635497041555464327325)
          ·
            refine ⟨11719738311390583299122747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31252635497041555464327325 11719738311390583299122747)
            ·
              refine ⟨17579607467085874948684121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719738311390583299122747 17579607467085874948684121)
              ·
                refine ⟨13184705600314406211513091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17579607467085874948684121 13184705600314406211513091)
                ·
                  refine ⟨19777058400471609317269637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184705600314406211513091 19777058400471609317269637)
                  ·
                    refine ⟨3708198450088426746988057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19777058400471609317269637 3708198450088426746988057)
                    ·
                      refine ⟨2781148837566320060241043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708198450088426746988057 2781148837566320060241043)
                      ·
                        rfl

theorem cell23_5416268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5416268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416268 prefixEnd_5416268 := by exact prefixLift 5416268
  have htrace : WordTrace (prefixWord ++ tailWord_5416268) baseStart_5416268 baseEnd_5416268 := by
    simpa [prefixWord, tailWord_5416268, baseEnd_5416268] using wordTrace_append hprefix tailTrace_5416268
  have hstable : (prefixWord ++ tailWord_5416268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416268).length < 2 ^ (prefixWord ++ tailWord_5416268).sum := by decide
  have hdescent : baseEnd_5416268 < baseStart_5416268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416298 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5416298 : Nat := 118140960795 + 5416298 * 2 ^ 59
def prefixEnd_5416298 : Nat := 4983230072969 + 3 ^ 40 * 5416298 * 2
def baseEnd_5416298 : Nat := 2781164241985954942865905

theorem tailTrace_5416298 : CollatzResearch.WordTrace tailWord_5416298 prefixEnd_5416298 2781164241985954942865905 := by
  unfold tailWord_5416298
  simp only [CollatzResearch.WordTrace]
  refine ⟨49387154332921212724526387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131699078221123233932070365 49387154332921212724526387)
  ·
    refine ⟨74080731499381819086789581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49387154332921212724526387 74080731499381819086789581)
    ·
      refine ⟨27780274312268182157546093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74080731499381819086789581 27780274312268182157546093)
      ·
        refine ⟨10417602867100568309079785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27780274312268182157546093 10417602867100568309079785)
        ·
          refine ⟨7813202150325426231809839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10417602867100568309079785 7813202150325426231809839)
          ·
            refine ⟨11719803225488139347714759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813202150325426231809839 11719803225488139347714759)
            ·
              refine ⟨17579704838232209021572139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719803225488139347714759 17579704838232209021572139)
              ·
                refine ⟨26369557257348313532358209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17579704838232209021572139 26369557257348313532358209)
                ·
                  refine ⟨19777167943011235149268657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26369557257348313532358209 19777167943011235149268657)
                  ·
                    refine ⟨14832875957258426361951493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19777167943011235149268657 14832875957258426361951493)
                    ·
                      refine ⟨2781164241985954942865905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832875957258426361951493 2781164241985954942865905)
                      ·
                        rfl

theorem cell23_5416298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5416298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416298 prefixEnd_5416298 := by exact prefixLift 5416298
  have htrace : WordTrace (prefixWord ++ tailWord_5416298) baseStart_5416298 baseEnd_5416298 := by
    simpa [prefixWord, tailWord_5416298, baseEnd_5416298] using wordTrace_append hprefix tailTrace_5416298
  have hstable : (prefixWord ++ tailWord_5416298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416298).length < 2 ^ (prefixWord ++ tailWord_5416298).sum := by decide
  have hdescent : baseEnd_5416298 < baseStart_5416298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416301 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5416301 : Nat := 118140960795 + 5416301 * 2 ^ 59
def prefixEnd_5416301 : Nat := 4983230072969 + 3 ^ 40 * 5416301 * 2
def baseEnd_5416301 : Nat := 2781165782427918431128391

theorem tailTrace_5416301 : CollatzResearch.WordTrace tailWord_5416301 prefixEnd_5416301 2781165782427918431128391 := by
  unfold tailWord_5416301
  simp only [CollatzResearch.WordTrace]
  refine ⟨197548726750673982410464757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131699151167115988273643171 197548726750673982410464757)
  ·
    refine ⟨18520193132875685850981071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197548726750673982410464757 18520193132875685850981071)
    ·
      refine ⟨27780289699313528776471607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18520193132875685850981071 27780289699313528776471607)
      ·
        refine ⟨41670434548970293164707411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27780289699313528776471607 41670434548970293164707411)
        ·
          refine ⟨62505651823455439747061117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41670434548970293164707411 62505651823455439747061117)
          ·
            refine ⟨23439619433795789905147919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62505651823455439747061117 23439619433795789905147919)
            ·
              refine ⟨35159429150693684857721879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23439619433795789905147919 35159429150693684857721879)
              ·
                refine ⟨52739143726040527286582819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35159429150693684857721879 52739143726040527286582819)
                ·
                  refine ⟨79108715589060790929874229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52739143726040527286582819 79108715589060790929874229)
                  ·
                    refine ⟨7416442086474449149675709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79108715589060790929874229 7416442086474449149675709)
                    ·
                      refine ⟨2781165782427918431128391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416442086474449149675709 2781165782427918431128391)
                      ·
                        rfl

theorem cell23_5416301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5416301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416301 prefixEnd_5416301 := by exact prefixLift 5416301
  have htrace : WordTrace (prefixWord ++ tailWord_5416301) baseStart_5416301 baseEnd_5416301 := by
    simpa [prefixWord, tailWord_5416301, baseEnd_5416301] using wordTrace_append hprefix tailTrace_5416301
  have hstable : (prefixWord ++ tailWord_5416301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416301).length < 2 ^ (prefixWord ++ tailWord_5416301).sum := by decide
  have hdescent : baseEnd_5416301 < baseStart_5416301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416302 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5416302 : Nat := 118140960795 + 5416302 * 2 ^ 59
def prefixEnd_5416302 : Nat := 4983230072969 + 3 ^ 40 * 5416302 * 2
def baseEnd_5416302 : Nat := 2781166295908572927215887

theorem tailTrace_5416302 : CollatzResearch.WordTrace tailWord_5416302 prefixEnd_5416302 2781166295908572927215887 := by
  unfold tailWord_5416302
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693595402958794947656395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131699175482446906387500773 24693595402958794947656395)
  ·
    refine ⟨37040393104438192421484593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24693595402958794947656395 37040393104438192421484593)
    ·
      refine ⟨27780294828328644316113445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37040393104438192421484593 27780294828328644316113445)
      ·
        refine ⟨5208805280311620809271271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27780294828328644316113445 5208805280311620809271271)
        ·
          refine ⟨7813207920467431213906907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208805280311620809271271 7813207920467431213906907)
          ·
            refine ⟨11719811880701146820860361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813207920467431213906907 11719811880701146820860361)
            ·
              refine ⟨8789858910525860115645271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11719811880701146820860361 8789858910525860115645271)
              ·
                refine ⟨13184788365788790173467907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789858910525860115645271 13184788365788790173467907)
                ·
                  refine ⟨19777182548683185260201861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184788365788790173467907 19777182548683185260201861)
                  ·
                    refine ⟨3708221727878097236287849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19777182548683185260201861 3708221727878097236287849)
                    ·
                      refine ⟨2781166295908572927215887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708221727878097236287849 2781166295908572927215887)
                      ·
                        rfl

theorem cell23_5416302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5416302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416302 prefixEnd_5416302 := by exact prefixLift 5416302
  have htrace : WordTrace (prefixWord ++ tailWord_5416302) baseStart_5416302 baseEnd_5416302 := by
    simpa [prefixWord, tailWord_5416302, baseEnd_5416302] using wordTrace_append hprefix tailTrace_5416302
  have hstable : (prefixWord ++ tailWord_5416302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416302).length < 2 ^ (prefixWord ++ tailWord_5416302).sum := by decide
  have hdescent : baseEnd_5416302 < baseStart_5416302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416304 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_5416304 : Nat := 118140960795 + 5416304 * 2 ^ 59
def prefixEnd_5416304 : Nat := 4983230072969 + 3 ^ 40 * 5416304 * 2
def baseEnd_5416304 : Nat := 927055774289960639796959

theorem tailTrace_5416304 : CollatzResearch.WordTrace tailWord_5416304 prefixEnd_5416304 927055774289960639796959 := by
  unfold tailWord_5416304
  simp only [CollatzResearch.WordTrace]
  refine ⟨98774418084831556961411983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131699224113108742615215977 98774418084831556961411983)
  ·
    refine ⟨148161627127247335442117975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98774418084831556961411983 148161627127247335442117975)
    ·
      refine ⟨222242440690871003163176963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148161627127247335442117975 222242440690871003163176963)
      ·
        refine ⟨333363661036306504744765445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222242440690871003163176963 333363661036306504744765445)
        ·
          refine ⟨62505686444307469639643521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333363661036306504744765445 62505686444307469639643521)
          ·
            refine ⟨46879264833230602229732641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62505686444307469639643521 46879264833230602229732641)
            ·
              refine ⟨35159448624922951672299481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46879264833230602229732641 35159448624922951672299481)
              ·
                refine ⟨26369586468692213754224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35159448624922951672299481 26369586468692213754224611)
                ·
                  refine ⟨39554379703038320631336917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26369586468692213754224611 39554379703038320631336917)
                  ·
                    refine ⟨927055774289960639796959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39554379703038320631336917 927055774289960639796959)
                    ·
                      rfl

theorem cell23_5416304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_5416304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416304 prefixEnd_5416304 := by exact prefixLift 5416304
  have htrace : WordTrace (prefixWord ++ tailWord_5416304) baseStart_5416304 baseEnd_5416304 := by
    simpa [prefixWord, tailWord_5416304, baseEnd_5416304] using wordTrace_append hprefix tailTrace_5416304
  have hstable : (prefixWord ++ tailWord_5416304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416304).length < 2 ^ (prefixWord ++ tailWord_5416304).sum := by decide
  have hdescent : baseEnd_5416304 < baseStart_5416304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416311 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_5416311 : Nat := 118140960795 + 5416311 * 2 ^ 59
def prefixEnd_5416311 : Nat := 4983230072969 + 3 ^ 40 * 5416311 * 2
def baseEnd_5416311 : Nat := 2781170917234463392003345

theorem tailTrace_5416311 : CollatzResearch.WordTrace tailWord_5416311 prefixEnd_5416311 2781170917234463392003345 := by
  unfold tailWord_5416311
  simp only [CollatzResearch.WordTrace]
  refine ⟨197549091480637754118328787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131699394320425169412219191 197549091480637754118328787)
  ·
    refine ⟨296323637220956631177493181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197549091480637754118328787 296323637220956631177493181)
    ·
      refine ⟨111121363957858736691559943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296323637220956631177493181 111121363957858736691559943)
      ·
        refine ⟨166682045936788105037339915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111121363957858736691559943 166682045936788105037339915)
        ·
          refine ⟨250023068905182157556009873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166682045936788105037339915 250023068905182157556009873)
          ·
            refine ⟨187517301678886618167007405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250023068905182157556009873 187517301678886618167007405)
            ·
              refine ⟨70318988129582481812627777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187517301678886618167007405 70318988129582481812627777)
              ·
                refine ⟨52739241097186861359470833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70318988129582481812627777 52739241097186861359470833)
                ·
                  refine ⟨39554430822890146019603125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52739241097186861359470833 39554430822890146019603125)
                  ·
                    refine ⟨3708227889645951189337793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39554430822890146019603125 3708227889645951189337793)
                    ·
                      refine ⟨2781170917234463392003345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708227889645951189337793 2781170917234463392003345)
                      ·
                        rfl

theorem cell23_5416311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_5416311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416311 prefixEnd_5416311 := by exact prefixLift 5416311
  have htrace : WordTrace (prefixWord ++ tailWord_5416311) baseStart_5416311 baseEnd_5416311 := by
    simpa [prefixWord, tailWord_5416311, baseEnd_5416311] using wordTrace_append hprefix tailTrace_5416311
  have hstable : (prefixWord ++ tailWord_5416311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416311).length < 2 ^ (prefixWord ++ tailWord_5416311).sum := by decide
  have hdescent : baseEnd_5416311 < baseStart_5416311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416341 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_5416341 : Nat := 118140960795 + 5416341 * 2 ^ 59
def prefixEnd_5416341 : Nat := 4983230072969 + 3 ^ 40 * 5416341 * 2
def baseEnd_5416341 : Nat := 2781186321654098274628207

theorem tailTrace_5416341 : CollatzResearch.WordTrace tailWord_5416341 prefixEnd_5416341 2781186321654098274628207 := by
  unfold tailWord_5416341
  simp only [CollatzResearch.WordTrace]
  refine ⟨197550185670529069241920877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131700123780352712827947251 197550185670529069241920877)
  ·
    refine ⟨74081319626448400965720329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197550185670529069241920877 74081319626448400965720329)
    ·
      refine ⟨55560989719836300724290247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74081319626448400965720329 55560989719836300724290247)
      ·
        refine ⟨83341484579754451086435371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55560989719836300724290247 83341484579754451086435371)
        ·
          refine ⟨125012226869631676629653057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83341484579754451086435371 125012226869631676629653057)
          ·
            refine ⟨93759170152223757472239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125012226869631676629653057 93759170152223757472239793)
            ·
              refine ⟨70319377614167818104179845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93759170152223757472239793 70319377614167818104179845)
              ·
                refine ⟨13184883302656465894533721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70319377614167818104179845 13184883302656465894533721)
                ·
                  refine ⟨9888662476992349420900291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13184883302656465894533721 9888662476992349420900291)
                  ·
                    refine ⟨14832993715488524131350437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9888662476992349420900291 14832993715488524131350437)
                    ·
                      refine ⟨2781186321654098274628207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14832993715488524131350437 2781186321654098274628207)
                      ·
                        rfl

theorem cell23_5416341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_5416341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416341 prefixEnd_5416341 := by exact prefixLift 5416341
  have htrace : WordTrace (prefixWord ++ tailWord_5416341) baseStart_5416341 baseEnd_5416341 := by
    simpa [prefixWord, tailWord_5416341, baseEnd_5416341] using wordTrace_append hprefix tailTrace_5416341
  have hstable : (prefixWord ++ tailWord_5416341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416341).length < 2 ^ (prefixWord ++ tailWord_5416341).sum := by decide
  have hdescent : baseEnd_5416341 < baseStart_5416341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416445 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_5416445 : Nat := 118140960795 + 5416445 * 2 ^ 59
def prefixEnd_5416445 : Nat := 4983230072969 + 3 ^ 40 * 5416445 * 2
def baseEnd_5416445 : Nat := 927079907880721955909243

theorem tailTrace_5416445 : CollatzResearch.WordTrace tailWord_5416445 prefixEnd_5416445 927079907880721955909243 := by
  unfold tailWord_5416445
  simp only [CollatzResearch.WordTrace]
  refine ⟨197553978862152295003706789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131702652574768196669137859 197553978862152295003706789)
  ·
    refine ⟨37041371036653555313195023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197553978862152295003706789 37041371036653555313195023)
    ·
      refine ⟨55562056554980332969792535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37041371036653555313195023 55562056554980332969792535)
      ·
        refine ⟨83343084832470499454688803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55562056554980332969792535 83343084832470499454688803)
        ·
          refine ⟨125014627248705749182033205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83343084832470499454688803 125014627248705749182033205)
          ·
            refine ⟨11720121304566163985815613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125014627248705749182033205 11720121304566163985815613)
            ·
              refine ⟨4395045489212311494680855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11720121304566163985815613 4395045489212311494680855)
              ·
                refine ⟨6592568233818467242021283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395045489212311494680855 6592568233818467242021283)
                ·
                  refine ⟨9888852350727700863031925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592568233818467242021283 9888852350727700863031925)
                  ·
                    refine ⟨927079907880721955909243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9888852350727700863031925 927079907880721955909243)
                    ·
                      rfl

theorem cell23_5416445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_5416445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416445 prefixEnd_5416445 := by exact prefixLift 5416445
  have htrace : WordTrace (prefixWord ++ tailWord_5416445) baseStart_5416445 baseEnd_5416445 := by
    simpa [prefixWord, tailWord_5416445, baseEnd_5416445] using wordTrace_append hprefix tailTrace_5416445
  have hstable : (prefixWord ++ tailWord_5416445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416445).length < 2 ^ (prefixWord ++ tailWord_5416445).sum := by decide
  have hdescent : baseEnd_5416445 < baseStart_5416445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416451 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_5416451 : Nat := 118140960795 + 5416451 * 2 ^ 59
def prefixEnd_5416451 : Nat := 4983230072969 + 3 ^ 40 * 5416451 * 2
def baseEnd_5416451 : Nat := 2781242804526092844252701

theorem tailTrace_5416451 : CollatzResearch.WordTrace tailWord_5416451 prefixEnd_5416451 2781242804526092844252701 := by
  unfold tailWord_5416451
  simp only [CollatzResearch.WordTrace]
  refine ⟨197554197700130558028425207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131702798466753705352283471 197554197700130558028425207)
  ·
    refine ⟨296331296550195837042637811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197554197700130558028425207 296331296550195837042637811)
    ·
      refine ⟨444496944825293755563956717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296331296550195837042637811 444496944825293755563956717)
      ·
        refine ⟨166686354309485158336483769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444496944825293755563956717 166686354309485158336483769)
        ·
          refine ⟨125014765732113868752362827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166686354309485158336483769 125014765732113868752362827)
          ·
            refine ⟨187522148598170803128544241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125014765732113868752362827 187522148598170803128544241)
            ·
              refine ⟨140641611448628102346408181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187522148598170803128544241 140641611448628102346408181)
              ·
                refine ⟨13185151073308884594975767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140641611448628102346408181 13185151073308884594975767)
                ·
                  refine ⟨19777726609963326892463651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13185151073308884594975767 19777726609963326892463651)
                  ·
                    refine ⟨29666589914944990338695477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19777726609963326892463651 29666589914944990338695477)
                    ·
                      refine ⟨2781242804526092844252701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29666589914944990338695477 2781242804526092844252701)
                      ·
                        rfl

theorem cell23_5416451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_5416451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416451 prefixEnd_5416451 := by exact prefixLift 5416451
  have htrace : WordTrace (prefixWord ++ tailWord_5416451) baseStart_5416451 baseEnd_5416451 := by
    simpa [prefixWord, tailWord_5416451, baseEnd_5416451] using wordTrace_append hprefix tailTrace_5416451
  have hstable : (prefixWord ++ tailWord_5416451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416451).length < 2 ^ (prefixWord ++ tailWord_5416451).sum := by decide
  have hdescent : baseEnd_5416451 < baseStart_5416451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416465 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_5416465 : Nat := 118140960795 + 5416465 * 2 ^ 59
def prefixEnd_5416465 : Nat := 4983230072969 + 3 ^ 40 * 5416465 * 2
def baseEnd_5416465 : Nat := 2781249993255255789477637

theorem tailTrace_5416465 : CollatzResearch.WordTrace tailWord_5416465 prefixEnd_5416465 2781249993255255789477637 := by
  unfold tailWord_5416465
  simp only [CollatzResearch.WordTrace]
  refine ⟨197554708322079838419434849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131703138881386558946289899 197554708322079838419434849)
  ·
    refine ⟨148166031241559878814576137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197554708322079838419434849 148166031241559878814576137)
    ·
      refine ⟨111124523431169909110932103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148166031241559878814576137 111124523431169909110932103)
      ·
        refine ⟨166686785146754863666398155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111124523431169909110932103 166686785146754863666398155)
        ·
          refine ⟨250030177720132295499597233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166686785146754863666398155 250030177720132295499597233)
          ·
            refine ⟨187522633290099221624697925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250030177720132295499597233 187522633290099221624697925)
            ·
              refine ⟨35160493741893604054630861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187522633290099221624697925 35160493741893604054630861)
              ·
                refine ⟨13185185153210101520486573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35160493741893604054630861 13185185153210101520486573)
                ·
                  refine ⟨4944444432453788070182465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13185185153210101520486573 4944444432453788070182465)
                  ·
                    refine ⟨3708333324340341052636849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944444432453788070182465 3708333324340341052636849)
                    ·
                      refine ⟨2781249993255255789477637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708333324340341052636849 2781249993255255789477637)
                      ·
                        rfl

theorem cell23_5416465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_5416465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416465 prefixEnd_5416465 := by exact prefixLift 5416465
  have htrace : WordTrace (prefixWord ++ tailWord_5416465) baseStart_5416465 baseEnd_5416465 := by
    simpa [prefixWord, tailWord_5416465, baseEnd_5416465] using wordTrace_append hprefix tailTrace_5416465
  have hstable : (prefixWord ++ tailWord_5416465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416465).length < 2 ^ (prefixWord ++ tailWord_5416465).sum := by decide
  have hdescent : baseEnd_5416465 < baseStart_5416465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416499 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 1, 2, 2]
def baseStart_5416499 : Nat := 118140960795 + 5416499 * 2 ^ 59
def prefixEnd_5416499 : Nat := 4983230072969 + 3 ^ 40 * 5416499 * 2
def baseEnd_5416499 : Nat := 2781267451597508656452481

theorem tailTrace_5416499 : CollatzResearch.WordTrace tailWord_5416499 prefixEnd_5416499 2781267451597508656452481 := by
  unfold tailWord_5416499
  simp only [CollatzResearch.WordTrace]
  refine ⟨197555948403956662226172551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131703965602637774817448367 197555948403956662226172551)
  ·
    refine ⟨296333922605934993339258827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197555948403956662226172551 296333922605934993339258827)
    ·
      refine ⟨444500883908902490008888241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296333922605934993339258827 444500883908902490008888241)
      ·
        refine ⟨333375662931676867506666181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444500883908902490008888241 333375662931676867506666181)
        ·
          refine ⟨62507936799689412657499909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333375662931676867506666181 62507936799689412657499909)
          ·
            refine ⟨11720238149941764873281233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62507936799689412657499909 11720238149941764873281233)
            ·
              refine ⟨8790178612456323654960925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11720238149941764873281233 8790178612456323654960925)
              ·
                refine ⟨3296316979671121370610347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8790178612456323654960925 3296316979671121370610347)
                ·
                  refine ⟨4944475469506682055915521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296316979671121370610347 4944475469506682055915521)
                  ·
                    refine ⟨3708356602130011541936641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944475469506682055915521 3708356602130011541936641)
                    ·
                      refine ⟨2781267451597508656452481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708356602130011541936641 2781267451597508656452481)
                      ·
                        rfl

theorem cell23_5416499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 2, 2].length) (baseStart_5416499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416499 prefixEnd_5416499 := by exact prefixLift 5416499
  have htrace : WordTrace (prefixWord ++ tailWord_5416499) baseStart_5416499 baseEnd_5416499 := by
    simpa [prefixWord, tailWord_5416499, baseEnd_5416499] using wordTrace_append hprefix tailTrace_5416499
  have hstable : (prefixWord ++ tailWord_5416499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416499).length < 2 ^ (prefixWord ++ tailWord_5416499).sum := by decide
  have hdescent : baseEnd_5416499 < baseStart_5416499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416509 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_5416509 : Nat := 118140960795 + 5416509 * 2 ^ 59
def prefixEnd_5416509 : Nat := 4983230072969 + 3 ^ 40 * 5416509 * 2
def baseEnd_5416509 : Nat := 927090862134684539109145

theorem tailTrace_5416509 : CollatzResearch.WordTrace tailWord_5416509 prefixEnd_5416509 927090862134684539109145 := by
  unfold tailWord_5416509
  simp only [CollatzResearch.WordTrace]
  refine ⟨197556313133920433934036581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131704208755946955956024387 197556313133920433934036581)
  ·
    refine ⟨37041808712610081362631859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197556313133920433934036581 37041808712610081362631859)
    ·
      refine ⟨55562713068915122043947789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37041808712610081362631859 55562713068915122043947789)
      ·
        refine ⟨20836017400843170766480421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55562713068915122043947789 20836017400843170766480421)
        ·
          refine ⟨3906753262658094518715079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20836017400843170766480421 3906753262658094518715079)
          ·
            refine ⟨5860129893987141778072619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906753262658094518715079 5860129893987141778072619)
            ·
              refine ⟨8790194840980712667108929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860129893987141778072619 8790194840980712667108929)
              ·
                refine ⟨6592646130735534500331697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8790194840980712667108929 6592646130735534500331697)
                ·
                  refine ⟨4944484598051650875248773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592646130735534500331697 4944484598051650875248773)
                  ·
                    refine ⟨927090862134684539109145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944484598051650875248773 927090862134684539109145)
                    ·
                      rfl

theorem cell23_5416509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_5416509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416509 prefixEnd_5416509 := by exact prefixLift 5416509
  have htrace : WordTrace (prefixWord ++ tailWord_5416509) baseStart_5416509 baseEnd_5416509 := by
    simpa [prefixWord, tailWord_5416509, baseEnd_5416509] using wordTrace_append hprefix tailTrace_5416509
  have hstable : (prefixWord ++ tailWord_5416509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416509).length < 2 ^ (prefixWord ++ tailWord_5416509).sum := by decide
  have hdescent : baseEnd_5416509 < baseStart_5416509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416521 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_5416521 : Nat := 118140960795 + 5416521 * 2 ^ 59
def prefixEnd_5416521 : Nat := 4983230072969 + 3 ^ 40 * 5416521 * 2
def baseEnd_5416521 : Nat := 2781278748171907570377379

theorem tailTrace_5416521 : CollatzResearch.WordTrace tailWord_5416521 prefixEnd_5416521 2781278748171907570377379 := by
  unfold tailWord_5416521
  simp only [CollatzResearch.WordTrace]
  refine ⟨197556750809876959983473417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131704500539917973322315611 197556750809876959983473417)
  ·
    refine ⟨148167563107407719987605063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197556750809876959983473417 148167563107407719987605063)
    ·
      refine ⟨222251344661111579981407595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148167563107407719987605063 222251344661111579981407595)
      ·
        refine ⟨333377016991667369972111393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222251344661111579981407595 333377016991667369972111393)
        ·
          refine ⟨250032762743750527479083545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333377016991667369972111393 250032762743750527479083545)
          ·
            refine ⟨187524572057812895609312659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250032762743750527479083545 187524572057812895609312659)
            ·
              refine ⟨281286858086719343413968989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187524572057812895609312659 281286858086719343413968989)
              ·
                refine ⟨105482571782519753780238371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281286858086719343413968989 105482571782519753780238371)
                ·
                  refine ⟨158223857673779630670357557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105482571782519753780238371 158223857673779630670357557)
                  ·
                    refine ⟨14833486656916840375346021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158223857673779630670357557 14833486656916840375346021)
                    ·
                      refine ⟨2781278748171907570377379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14833486656916840375346021 2781278748171907570377379)
                      ·
                        rfl

theorem cell23_5416521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_5416521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416521 prefixEnd_5416521 := by exact prefixLift 5416521
  have htrace : WordTrace (prefixWord ++ tailWord_5416521) baseStart_5416521 baseEnd_5416521 := by
    simpa [prefixWord, tailWord_5416521, baseEnd_5416521] using wordTrace_append hprefix tailTrace_5416521
  have hstable : (prefixWord ++ tailWord_5416521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416521).length < 2 ^ (prefixWord ++ tailWord_5416521).sum := by decide
  have hdescent : baseEnd_5416521 < baseStart_5416521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416561 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 9]
def baseStart_5416561 : Nat := 118140960795 + 5416561 * 2 ^ 59
def prefixEnd_5416561 : Nat := 4983230072969 + 3 ^ 40 * 5416561 * 2
def baseEnd_5416561 : Nat := 309033254155343045986355

theorem tailTrace_5416561 : CollatzResearch.WordTrace tailWord_5416561 prefixEnd_5416561 309033254155343045986355 := by
  unfold tailWord_5416561
  simp only [CollatzResearch.WordTrace]
  refine ⟨197558209729732046814929537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131705473153154697876619691 197558209729732046814929537)
  ·
    refine ⟨148168657297299035111197153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197558209729732046814929537 148168657297299035111197153)
    ·
      refine ⟨111126492972974276333397865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148168657297299035111197153 111126492972974276333397865)
      ·
        refine ⟨83344869729730707250048399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111126492972974276333397865 83344869729730707250048399)
        ·
          refine ⟨125017304594596060875072599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83344869729730707250048399 125017304594596060875072599)
          ·
            refine ⟨187525956891894091312608899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125017304594596060875072599 187525956891894091312608899)
            ·
              refine ⟨281288935337841136968913349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187525956891894091312608899 281288935337841136968913349)
              ·
                refine ⟨52741675375845213181671253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281288935337841136968913349 52741675375845213181671253)
                ·
                  refine ⟨309033254155343045986355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52741675375845213181671253 309033254155343045986355)
                  ·
                    rfl

theorem cell23_5416561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_5416561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416561 prefixEnd_5416561 := by exact prefixLift 5416561
  have htrace : WordTrace (prefixWord ++ tailWord_5416561) baseStart_5416561 baseEnd_5416561 := by
    simpa [prefixWord, tailWord_5416561, baseEnd_5416561] using wordTrace_append hprefix tailTrace_5416561
  have hstable : (prefixWord ++ tailWord_5416561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416561).length < 2 ^ (prefixWord ++ tailWord_5416561).sum := by decide
  have hdescent : baseEnd_5416561 < baseStart_5416561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416571 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_5416571 : Nat := 118140960795 + 5416571 * 2 ^ 59
def prefixEnd_5416571 : Nat := 4983230072969 + 3 ^ 40 * 5416571 * 2
def baseEnd_5416571 : Nat := 2781304422204632374752149

theorem tailTrace_5416571 : CollatzResearch.WordTrace tailWord_5416571 prefixEnd_5416571 2781304422204632374752149 := by
  unfold tailWord_5416571
  simp only [CollatzResearch.WordTrace]
  refine ⟨197558574459695818522793567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131705716306463879015195711 197558574459695818522793567)
  ·
    refine ⟨296337861689543727784190351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197558574459695818522793567 296337861689543727784190351)
    ·
      refine ⟨444506792534315591676285527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296337861689543727784190351 444506792534315591676285527)
      ·
        refine ⟨666760188801473387514428291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444506792534315591676285527 666760188801473387514428291)
        ·
          refine ⟨1000140283202210081271642437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666760188801473387514428291 1000140283202210081271642437)
          ·
            refine ⟨187526303100414390238432957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1000140283202210081271642437 187526303100414390238432957)
            ·
              refine ⟨70322363662655396339412359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187526303100414390238432957 70322363662655396339412359)
              ·
                refine ⟨105483545493983094509118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70322363662655396339412359 105483545493983094509118539)
                ·
                  refine ⟨158225318240974641763677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105483545493983094509118539 158225318240974641763677809)
                  ·
                    refine ⟨118668988680730981322758357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158225318240974641763677809 118668988680730981322758357)
                    ·
                      refine ⟨2781304422204632374752149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118668988680730981322758357 2781304422204632374752149)
                      ·
                        rfl

theorem cell23_5416571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_5416571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416571 prefixEnd_5416571 := by exact prefixLift 5416571
  have htrace : WordTrace (prefixWord ++ tailWord_5416571) baseStart_5416571 baseEnd_5416571 := by
    simpa [prefixWord, tailWord_5416571, baseEnd_5416571] using wordTrace_append hprefix tailTrace_5416571
  have hstable : (prefixWord ++ tailWord_5416571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416571).length < 2 ^ (prefixWord ++ tailWord_5416571).sum := by decide
  have hdescent : baseEnd_5416571 < baseStart_5416571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416572 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_5416572 : Nat := 118140960795 + 5416572 * 2 ^ 59
def prefixEnd_5416572 : Nat := 4983230072969 + 3 ^ 40 * 5416572 * 2
def baseEnd_5416572 : Nat := 2781304935685286870839645

theorem tailTrace_5416572 : CollatzResearch.WordTrace tailWord_5416572 prefixEnd_5416572 2781304935685286870839645 := by
  unfold tailWord_5416572
  simp only [CollatzResearch.WordTrace]
  refine ⟨98779305466346097846789985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131705740621794797129053313 98779305466346097846789985)
  ·
    refine ⟨74084479099759573385092489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98779305466346097846789985 74084479099759573385092489)
    ·
      refine ⟨55563359324819680038819367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74084479099759573385092489 55563359324819680038819367)
      ·
        refine ⟨83345038987229520058229051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55563359324819680038819367 83345038987229520058229051)
        ·
          refine ⟨125017558480844280087343577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83345038987229520058229051 125017558480844280087343577)
          ·
            refine ⟨93763168860633210065507683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125017558480844280087343577 93763168860633210065507683)
            ·
              refine ⟨140644753290949815098261525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93763168860633210065507683 140644753290949815098261525)
              ·
                refine ⟨6592722810513272582731009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140644753290949815098261525 6592722810513272582731009)
                ·
                  refine ⟨4944542107884954437048257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592722810513272582731009 4944542107884954437048257)
                  ·
                    refine ⟨3708406580913715827786193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944542107884954437048257 3708406580913715827786193)
                    ·
                      refine ⟨2781304935685286870839645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708406580913715827786193 2781304935685286870839645)
                      ·
                        rfl

theorem cell23_5416572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_5416572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416572 prefixEnd_5416572 := by exact prefixLift 5416572
  have htrace : WordTrace (prefixWord ++ tailWord_5416572) baseStart_5416572 baseEnd_5416572 := by
    simpa [prefixWord, tailWord_5416572, baseEnd_5416572] using wordTrace_append hprefix tailTrace_5416572
  have hstable : (prefixWord ++ tailWord_5416572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416572).length < 2 ^ (prefixWord ++ tailWord_5416572).sum := by decide
  have hdescent : baseEnd_5416572 < baseStart_5416572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416588 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_5416588 : Nat := 118140960795 + 5416588 * 2 ^ 59
def prefixEnd_5416588 : Nat := 4983230072969 + 3 ^ 40 * 5416588 * 2
def baseEnd_5416588 : Nat := 2781313151375758808239571

theorem tailTrace_5416588 : CollatzResearch.WordTrace tailWord_5416588 prefixEnd_5416588 2781313151375758808239571 := by
  unfold tailWord_5416588
  simp only [CollatzResearch.WordTrace]
  refine ⟨98779597250317115213081209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131706129667089486950774945 98779597250317115213081209)
  ·
    refine ⟨74084697937737836409810907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98779597250317115213081209 74084697937737836409810907)
    ·
      refine ⟨111127046906606754614716361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74084697937737836409810907 111127046906606754614716361)
      ·
        refine ⟨83345285179955065961037271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111127046906606754614716361 83345285179955065961037271)
        ·
          refine ⟨125017927769932598941555907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83345285179955065961037271 125017927769932598941555907)
          ·
            refine ⟨187526891654898898412333861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125017927769932598941555907 187526891654898898412333861)
            ·
              refine ⟨35161292185293543452312599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187526891654898898412333861 35161292185293543452312599)
              ·
                refine ⟨52741938277940315178468899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35161292185293543452312599 52741938277940315178468899)
                ·
                  refine ⟨79112907416910472767703349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52741938277940315178468899 79112907416910472767703349)
                  ·
                    refine ⟨7416835070335356821972189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79112907416910472767703349 7416835070335356821972189)
                    ·
                      refine ⟨2781313151375758808239571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416835070335356821972189 2781313151375758808239571)
                      ·
                        rfl

theorem cell23_5416588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_5416588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416588 prefixEnd_5416588 := by exact prefixLift 5416588
  have htrace : WordTrace (prefixWord ++ tailWord_5416588) baseStart_5416588 baseEnd_5416588 := by
    simpa [prefixWord, tailWord_5416588, baseEnd_5416588] using wordTrace_append hprefix tailTrace_5416588
  have hstable : (prefixWord ++ tailWord_5416588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416588).length < 2 ^ (prefixWord ++ tailWord_5416588).sum := by decide
  have hdescent : baseEnd_5416588 < baseStart_5416588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416645 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_5416645 : Nat := 118140960795 + 5416645 * 2 ^ 59
def prefixEnd_5416645 : Nat := 4983230072969 + 3 ^ 40 * 5416645 * 2
def baseEnd_5416645 : Nat := 2781342419773065085226809

theorem tailTrace_5416645 : CollatzResearch.WordTrace tailWord_5416645 prefixEnd_5416645 2781342419773065085226809 := by
  unfold tailWord_5416645
  simp only [CollatzResearch.WordTrace]
  refine ⟨197561273461427729160987389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131707515640951819440658259 197561273461427729160987389)
  ·
    refine ⟨74085477548035398435370271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197561273461427729160987389 74085477548035398435370271)
    ·
      refine ⟨111128216322053097653055407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74085477548035398435370271 111128216322053097653055407)
      ·
        refine ⟨166692324483079646479583111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111128216322053097653055407 166692324483079646479583111)
        ·
          refine ⟨250038486724619469719374667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166692324483079646479583111 250038486724619469719374667)
          ·
            refine ⟨375057730086929204579062001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250038486724619469719374667 375057730086929204579062001)
            ·
              refine ⟨281293297565196903434296501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375057730086929204579062001 281293297565196903434296501)
              ·
                refine ⟨26371246646737209696965297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281293297565196903434296501 26371246646737209696965297)
                ·
                  refine ⟨19778434985052907272723973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26371246646737209696965297 19778434985052907272723973)
                  ·
                    refine ⟨3708456559697420113635745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19778434985052907272723973 3708456559697420113635745)
                    ·
                      refine ⟨2781342419773065085226809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708456559697420113635745 2781342419773065085226809)
                      ·
                        rfl

theorem cell23_5416645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_5416645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416645 prefixEnd_5416645 := by exact prefixLift 5416645
  have htrace : WordTrace (prefixWord ++ tailWord_5416645) baseStart_5416645 baseEnd_5416645 := by
    simpa [prefixWord, tailWord_5416645, baseEnd_5416645] using wordTrace_append hprefix tailTrace_5416645
  have hstable : (prefixWord ++ tailWord_5416645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416645).length < 2 ^ (prefixWord ++ tailWord_5416645).sum := by decide
  have hdescent : baseEnd_5416645 < baseStart_5416645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416665 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_5416665 : Nat := 118140960795 + 5416665 * 2 ^ 59
def prefixEnd_5416665 : Nat := 4983230072969 + 3 ^ 40 * 5416665 * 2
def baseEnd_5416665 : Nat := 2781352689386155006976717

theorem tailTrace_5416665 : CollatzResearch.WordTrace tailWord_5416665 prefixEnd_5416665 2781352689386155006976717 := by
  unfold tailWord_5416665
  simp only [CollatzResearch.WordTrace]
  refine ⟨197562002921355272576715449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131708001947570181717810299 197562002921355272576715449)
  ·
    refine ⟨148171502191016454432536587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197562002921355272576715449 148171502191016454432536587)
    ·
      refine ⟨222257253286524681648804881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148171502191016454432536587 222257253286524681648804881)
      ·
        refine ⟨166692939964893511236603661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222257253286524681648804881 166692939964893511236603661)
        ·
          refine ⟨62509852486835066713726373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166692939964893511236603661 62509852486835066713726373)
          ·
            refine ⟨11720597341281575008823695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62509852486835066713726373 11720597341281575008823695)
            ·
              refine ⟨17580896011922362513235543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720597341281575008823695 17580896011922362513235543)
              ·
                refine ⟨26371344017883543769853315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17580896011922362513235543 26371344017883543769853315)
                ·
                  refine ⟨39557016026825315654779973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26371344017883543769853315 39557016026825315654779973)
                  ·
                    refine ⟨7416940505029746685271245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39557016026825315654779973 7416940505029746685271245)
                    ·
                      refine ⟨2781352689386155006976717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7416940505029746685271245 2781352689386155006976717)
                      ·
                        rfl

theorem cell23_5416665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_5416665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416665 prefixEnd_5416665 := by exact prefixLift 5416665
  have htrace : WordTrace (prefixWord ++ tailWord_5416665) baseStart_5416665 baseEnd_5416665 := by
    simpa [prefixWord, tailWord_5416665, baseEnd_5416665] using wordTrace_append hprefix tailTrace_5416665
  have hstable : (prefixWord ++ tailWord_5416665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416665).length < 2 ^ (prefixWord ++ tailWord_5416665).sum := by decide
  have hdescent : baseEnd_5416665 < baseStart_5416665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416672 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 1, 4]
def baseStart_5416672 : Nat := 118140960795 + 5416672 * 2 ^ 59
def prefixEnd_5416672 : Nat := 4983230072969 + 3 ^ 40 * 5416672 * 2
def baseEnd_5416672 : Nat := 927118761250245493196395

theorem tailTrace_5416672 : CollatzResearch.WordTrace tailWord_5416672 prefixEnd_5416672 927118761250245493196395 := by
  unfold tailWord_5416672
  simp only [CollatzResearch.WordTrace]
  refine ⟨98781129116164956386110135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131708172154886608514813513 98781129116164956386110135)
  ·
    refine ⟨148171693674247434579165203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98781129116164956386110135 148171693674247434579165203)
    ·
      refine ⟨222257540511371151868747805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148171693674247434579165203 222257540511371151868747805)
      ·
        refine ⟨83346577691764181950780427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222257540511371151868747805 83346577691764181950780427)
        ·
          refine ⟨125019866537646272926170641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83346577691764181950780427 125019866537646272926170641)
          ·
            refine ⟨93764899903234704694627981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125019866537646272926170641 93764899903234704694627981)
            ·
              refine ⟨35161837463713014260485493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93764899903234704694627981 35161837463713014260485493)
              ·
                refine ⟨3296422262223095086920515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35161837463713014260485493 3296422262223095086920515)
                ·
                  refine ⟨4944633393334642630380773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296422262223095086920515 4944633393334642630380773)
                  ·
                    refine ⟨927118761250245493196395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944633393334642630380773 927118761250245493196395)
                    ·
                      rfl

theorem cell23_5416672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_5416672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416672 prefixEnd_5416672 := by exact prefixLift 5416672
  have htrace : WordTrace (prefixWord ++ tailWord_5416672) baseStart_5416672 baseEnd_5416672 := by
    simpa [prefixWord, tailWord_5416672, baseEnd_5416672] using wordTrace_append hprefix tailTrace_5416672
  have hstable : (prefixWord ++ tailWord_5416672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416672).length < 2 ^ (prefixWord ++ tailWord_5416672).sum := by decide
  have hdescent : baseEnd_5416672 < baseStart_5416672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416685 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 8]
def baseStart_5416685 : Nat := 118140960795 + 5416685 * 2 ^ 59
def prefixEnd_5416685 : Nat := 4983230072969 + 3 ^ 40 * 5416685 * 2
def baseEnd_5416685 : Nat := 309040328777693880969625

theorem tailTrace_5416685 : CollatzResearch.WordTrace tailWord_5416685 prefixEnd_5416685 309040328777693880969625 := by
  unfold tailWord_5416685
  simp only [CollatzResearch.WordTrace]
  refine ⟨197562732381282815992443509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131708488254188543994962339 197562732381282815992443509)
  ·
    refine ⟨18521506160745263999291579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197562732381282815992443509 18521506160745263999291579)
    ·
      refine ⟨27782259241117895998937369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18521506160745263999291579 27782259241117895998937369)
      ·
        refine ⟨20836694430838421999203027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27782259241117895998937369 20836694430838421999203027)
        ·
          refine ⟨31255041646257632998804541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20836694430838421999203027 31255041646257632998804541)
          ·
            refine ⟨11720640617346612374551703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31255041646257632998804541 11720640617346612374551703)
            ·
              refine ⟨17580960926019918561827555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720640617346612374551703 17580960926019918561827555)
              ·
                refine ⟨26371441389029877842741333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17580960926019918561827555 26371441389029877842741333)
                ·
                  refine ⟨309040328777693880969625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26371441389029877842741333 309040328777693880969625)
                  ·
                    rfl

theorem cell23_5416685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_5416685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416685 prefixEnd_5416685 := by exact prefixLift 5416685
  have htrace : WordTrace (prefixWord ++ tailWord_5416685) baseStart_5416685 baseEnd_5416685 := by
    simpa [prefixWord, tailWord_5416685, baseEnd_5416685] using wordTrace_append hprefix tailTrace_5416685
  have hstable : (prefixWord ++ tailWord_5416685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416685).length < 2 ^ (prefixWord ++ tailWord_5416685).sum := by decide
  have hdescent : baseEnd_5416685 < baseStart_5416685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416712 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_5416712 : Nat := 118140960795 + 5416712 * 2 ^ 59
def prefixEnd_5416712 : Nat := 4983230072969 + 3 ^ 40 * 5416712 * 2
def baseEnd_5416712 : Nat := 2781376822976916323089001

theorem tailTrace_5416712 : CollatzResearch.WordTrace tailWord_5416712 prefixEnd_5416712 2781376822976916323089001 := by
  unfold tailWord_5416712
  simp only [CollatzResearch.WordTrace]
  refine ⟨98781858576092499801838195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131709144768123333069117593 98781858576092499801838195)
  ·
    refine ⟨148172787864138749702757293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98781858576092499801838195 148172787864138749702757293)
    ·
      refine ⟨55564795449052031138533985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148172787864138749702757293 55564795449052031138533985)
      ·
        refine ⟨41673596586789023353900489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55564795449052031138533985 41673596586789023353900489)
        ·
          refine ⟨31255197440091767515425367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41673596586789023353900489 31255197440091767515425367)
          ·
            refine ⟨46882796160137651273138051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31255197440091767515425367 46882796160137651273138051)
            ·
              refine ⟨70324194240206476909707077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46882796160137651273138051 70324194240206476909707077)
              ·
                refine ⟨13185786420038714420570077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70324194240206476909707077 13185786420038714420570077)
                ·
                  refine ⟨4944669907514517907713779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13185786420038714420570077 4944669907514517907713779)
                  ·
                    refine ⟨7417004861271776861570669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944669907514517907713779 7417004861271776861570669)
                    ·
                      refine ⟨2781376822976916323089001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417004861271776861570669 2781376822976916323089001)
                      ·
                        rfl

theorem cell23_5416712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_5416712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416712 prefixEnd_5416712 := by exact prefixLift 5416712
  have htrace : WordTrace (prefixWord ++ tailWord_5416712) baseStart_5416712 baseEnd_5416712 := by
    simpa [prefixWord, tailWord_5416712, baseEnd_5416712] using wordTrace_append hprefix tailTrace_5416712
  have hstable : (prefixWord ++ tailWord_5416712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416712).length < 2 ^ (prefixWord ++ tailWord_5416712).sum := by decide
  have hdescent : baseEnd_5416712 < baseStart_5416712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416715 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 1, 5]
def baseStart_5416715 : Nat := 118140960795 + 5416715 * 2 ^ 59
def prefixEnd_5416715 : Nat := 4983230072969 + 3 ^ 40 * 5416715 * 2
def baseEnd_5416715 : Nat := 927126121139626603783829

theorem tailTrace_5416715 : CollatzResearch.WordTrace tailWord_5416715 prefixEnd_5416715 927126121139626603783829 := by
  unfold tailWord_5416715
  simp only [CollatzResearch.WordTrace]
  refine ⟨197563826571174131116035599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131709217714116087410690399 197563826571174131116035599)
  ·
    refine ⟨296345739856761196674053399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197563826571174131116035599 296345739856761196674053399)
    ·
      refine ⟨444518609785141795011080099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296345739856761196674053399 444518609785141795011080099)
      ·
        refine ⟨666777914677712692516620149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444518609785141795011080099 666777914677712692516620149)
        ·
          refine ⟨62510429501035564923433139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 666777914677712692516620149 62510429501035564923433139)
          ·
            refine ⟨93765644251553347385149709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62510429501035564923433139 93765644251553347385149709)
            ·
              refine ⟨35162116594332505269431141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93765644251553347385149709 35162116594332505269431141)
              ·
                refine ⟨6592896861437344738018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35162116594332505269431141 6592896861437344738018339)
                ·
                  refine ⟨9889345292156017107027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592896861437344738018339 9889345292156017107027509)
                  ·
                    refine ⟨927126121139626603783829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9889345292156017107027509 927126121139626603783829)
                    ·
                      rfl

theorem cell23_5416715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 5].length) (baseStart_5416715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416715 prefixEnd_5416715 := by exact prefixLift 5416715
  have htrace : WordTrace (prefixWord ++ tailWord_5416715) baseStart_5416715 baseEnd_5416715 := by
    simpa [prefixWord, tailWord_5416715, baseEnd_5416715] using wordTrace_append hprefix tailTrace_5416715
  have hstable : (prefixWord ++ tailWord_5416715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416715).length < 2 ^ (prefixWord ++ tailWord_5416715).sum := by decide
  have hdescent : baseEnd_5416715 < baseStart_5416715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416796 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5416796 : Nat := 118140960795 + 5416796 * 2 ^ 59
def prefixEnd_5416796 : Nat := 4983230072969 + 3 ^ 40 * 5416796 * 2
def baseEnd_5416796 : Nat := 927139985117297998146205

theorem tailTrace_5416796 : CollatzResearch.WordTrace tailWord_5416796 prefixEnd_5416796 927139985117297998146205 := by
  unfold tailWord_5416796
  simp only [CollatzResearch.WordTrace]
  refine ⟨98783390441940340974867121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131711187255920454633156161 98783390441940340974867121)
  ·
    refine ⟨74087542831455255731150341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98783390441940340974867121 74087542831455255731150341)
    ·
      refine ⟨13891414280897860449590689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74087542831455255731150341 13891414280897860449590689)
      ·
        refine ⟨10418560710673395337193017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13891414280897860449590689 10418560710673395337193017)
        ·
          refine ⟨7813920533005046502894763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10418560710673395337193017 7813920533005046502894763)
          ·
            refine ⟨11720880799507569754342145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813920533005046502894763 11720880799507569754342145)
            ·
              refine ⟨8790660599630677315756609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11720880799507569754342145 8790660599630677315756609)
              ·
                refine ⟨6592995449723007986817457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8790660599630677315756609 6592995449723007986817457)
                ·
                  refine ⟨4944746587292255990113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592995449723007986817457 4944746587292255990113093)
                  ·
                    refine ⟨927139985117297998146205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944746587292255990113093 927139985117297998146205)
                    ·
                      rfl

theorem cell23_5416796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5416796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416796 prefixEnd_5416796 := by exact prefixLift 5416796
  have htrace : WordTrace (prefixWord ++ tailWord_5416796) baseStart_5416796 baseEnd_5416796 := by
    simpa [prefixWord, tailWord_5416796, baseEnd_5416796] using wordTrace_append hprefix tailTrace_5416796
  have hstable : (prefixWord ++ tailWord_5416796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416796).length < 2 ^ (prefixWord ++ tailWord_5416796).sum := by decide
  have hdescent : baseEnd_5416796 < baseStart_5416796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416803 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 1, 2, 2]
def baseStart_5416803 : Nat := 118140960795 + 5416803 * 2 ^ 59
def prefixEnd_5416803 : Nat := 4983230072969 + 3 ^ 40 * 5416803 * 2
def baseEnd_5416803 : Nat := 2781423549716475467051083

theorem tailTrace_5416803 : CollatzResearch.WordTrace tailWord_5416803 prefixEnd_5416803 2781423549716475467051083 := by
  unfold tailWord_5416803
  simp only [CollatzResearch.WordTrace]
  refine ⟨197567036194855322145239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131711357463236881430159375 197567036194855322145239063)
  ·
    refine ⟨296350554292282983217858595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197567036194855322145239063 296350554292282983217858595)
    ·
      refine ⟨444525831438424474826787893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296350554292282983217858595 444525831438424474826787893)
      ·
        refine ⟨41674296697352294515011365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 444525831438424474826787893 41674296697352294515011365)
        ·
          refine ⟨7813930630753555221564631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41674296697352294515011365 7813930630753555221564631)
          ·
            refine ⟨11720895946130332832346947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813930630753555221564631 11720895946130332832346947)
            ·
              refine ⟨17581343919195499248520421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720895946130332832346947 17581343919195499248520421)
              ·
                refine ⟨3296501984849156109097579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17581343919195499248520421 3296501984849156109097579)
                ·
                  refine ⟨4944752977273734163646369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296501984849156109097579 4944752977273734163646369)
                  ·
                    refine ⟨3708564732955300622734777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944752977273734163646369 3708564732955300622734777)
                    ·
                      refine ⟨2781423549716475467051083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708564732955300622734777 2781423549716475467051083)
                      ·
                        rfl

theorem cell23_5416803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_5416803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416803 prefixEnd_5416803 := by exact prefixLift 5416803
  have htrace : WordTrace (prefixWord ++ tailWord_5416803) baseStart_5416803 baseEnd_5416803 := by
    simpa [prefixWord, tailWord_5416803, baseEnd_5416803] using wordTrace_append hprefix tailTrace_5416803
  have hstable : (prefixWord ++ tailWord_5416803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416803).length < 2 ^ (prefixWord ++ tailWord_5416803).sum := by decide
  have hdescent : baseEnd_5416803 < baseStart_5416803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416825 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5416825 : Nat := 118140960795 + 5416825 * 2 ^ 59
def prefixEnd_5416825 : Nat := 4983230072969 + 3 ^ 40 * 5416825 * 2
def baseEnd_5416825 : Nat := 2781434846290874380975981

theorem tailTrace_5416825 : CollatzResearch.WordTrace tailWord_5416825 prefixEnd_5416825 2781434846290874380975981 := by
  unfold tailWord_5416825
  simp only [CollatzResearch.WordTrace]
  refine ⟨197567838600775619902539929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131711892400517079935026619 197567838600775619902539929)
  ·
    refine ⟨148175878950581714926904947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197567838600775619902539929 148175878950581714926904947)
    ·
      refine ⟨222263818425872572390357421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148175878950581714926904947 222263818425872572390357421)
      ·
        refine ⟨83348931909702214646384033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222263818425872572390357421 83348931909702214646384033)
        ·
          refine ⟨62511698932276660984788025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83348931909702214646384033 62511698932276660984788025)
          ·
            refine ⟨46883774199207495738591019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62511698932276660984788025 46883774199207495738591019)
            ·
              refine ⟨70325661298811243607886529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46883774199207495738591019 70325661298811243607886529)
              ·
                refine ⟨52744245974108432705914897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70325661298811243607886529 52744245974108432705914897)
                ·
                  refine ⟨39558184480581324529436173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52744245974108432705914897 39558184480581324529436173)
                  ·
                    refine ⟨14834319180217996698538565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39558184480581324529436173 14834319180217996698538565)
                    ·
                      refine ⟨2781434846290874380975981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834319180217996698538565 2781434846290874380975981)
                      ·
                        rfl

theorem cell23_5416825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5416825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416825 prefixEnd_5416825 := by exact prefixLift 5416825
  have htrace : WordTrace (prefixWord ++ tailWord_5416825) baseStart_5416825 baseEnd_5416825 := by
    simpa [prefixWord, tailWord_5416825, baseEnd_5416825] using wordTrace_append hprefix tailTrace_5416825
  have hstable : (prefixWord ++ tailWord_5416825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416825).length < 2 ^ (prefixWord ++ tailWord_5416825).sum := by decide
  have hdescent : baseEnd_5416825 < baseStart_5416825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416829 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_5416829 : Nat := 118140960795 + 5416829 * 2 ^ 59
def prefixEnd_5416829 : Nat := 4983230072969 + 3 ^ 40 * 5416829 * 2
def baseEnd_5416829 : Nat := 2781436900213492365325963

theorem tailTrace_5416829 : CollatzResearch.WordTrace tailWord_5416829 prefixEnd_5416829 2781436900213492365325963 := by
  unfold tailWord_5416829
  simp only [CollatzResearch.WordTrace]
  refine ⟨197567984492761128585685541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131711989661840752390457027 197567984492761128585685541)
  ·
    refine ⟨37043997092392711609816039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197567984492761128585685541 37043997092392711609816039)
    ·
      refine ⟨55565995638589067414724059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37043997092392711609816039 55565995638589067414724059)
      ·
        refine ⟨83348993457883601122086089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55565995638589067414724059 83348993457883601122086089)
        ·
          refine ⟨62511745093412700841564567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83348993457883601122086089 62511745093412700841564567)
          ·
            refine ⟨93767617640119051262346851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62511745093412700841564567 93767617640119051262346851)
            ·
              refine ⟨140651426460178576893520277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93767617640119051262346851 140651426460178576893520277)
              ·
                refine ⟨6593035615320870791883763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140651426460178576893520277 6593035615320870791883763)
                ·
                  refine ⟨9889553422981306187825645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593035615320870791883763 9889553422981306187825645)
                  ·
                    refine ⟨3708582533617989820434617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9889553422981306187825645 3708582533617989820434617)
                    ·
                      refine ⟨2781436900213492365325963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708582533617989820434617 2781436900213492365325963)
                      ·
                        rfl

theorem cell23_5416829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_5416829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416829 prefixEnd_5416829 := by exact prefixLift 5416829
  have htrace : WordTrace (prefixWord ++ tailWord_5416829) baseStart_5416829 baseEnd_5416829 := by
    simpa [prefixWord, tailWord_5416829, baseEnd_5416829] using wordTrace_append hprefix tailTrace_5416829
  have hstable : (prefixWord ++ tailWord_5416829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416829).length < 2 ^ (prefixWord ++ tailWord_5416829).sum := by decide
  have hdescent : baseEnd_5416829 < baseStart_5416829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416852 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5416852 : Nat := 118140960795 + 5416852 * 2 ^ 59
def prefixEnd_5416852 : Nat := 4983230072969 + 3 ^ 40 * 5416852 * 2
def baseEnd_5416852 : Nat := 927149570089515258446119

theorem tailTrace_5416852 : CollatzResearch.WordTrace tailWord_5416852 prefixEnd_5416852 927149570089515258446119 := by
  unfold tailWord_5416852
  simp only [CollatzResearch.WordTrace]
  refine ⟨98784411685838901756886405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131712548914451869009181873 98784411685838901756886405)
  ·
    refine ⟨18522077191094794079416201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98784411685838901756886405 18522077191094794079416201)
    ·
      refine ⟨13891557893321095559562151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18522077191094794079416201 13891557893321095559562151)
      ·
        refine ⟨20837336839981643339343227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13891557893321095559562151 20837336839981643339343227)
        ·
          refine ⟨31256005259972465009014841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20837336839981643339343227 31256005259972465009014841)
          ·
            refine ⟨23442003944979348756761131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31256005259972465009014841 23442003944979348756761131)
            ·
              refine ⟨35163005917469023135141697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23442003944979348756761131 35163005917469023135141697)
              ·
                refine ⟨26372254438101767351356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35163005917469023135141697 26372254438101767351356273)
                ·
                  refine ⟨19779190828576325513517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26372254438101767351356273 19779190828576325513517205)
                  ·
                    refine ⟨927149570089515258446119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19779190828576325513517205 927149570089515258446119)
                    ·
                      rfl

theorem cell23_5416852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5416852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416852 prefixEnd_5416852 := by exact prefixLift 5416852
  have htrace : WordTrace (prefixWord ++ tailWord_5416852) baseStart_5416852 baseEnd_5416852 := by
    simpa [prefixWord, tailWord_5416852, baseEnd_5416852] using wordTrace_append hprefix tailTrace_5416852
  have hstable : (prefixWord ++ tailWord_5416852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416852).length < 2 ^ (prefixWord ++ tailWord_5416852).sum := by decide
  have hdescent : baseEnd_5416852 < baseStart_5416852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416895 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 7]
def baseStart_5416895 : Nat := 118140960795 + 5416895 * 2 ^ 59
def prefixEnd_5416895 : Nat := 4983230072969 + 3 ^ 40 * 5416895 * 2
def baseEnd_5416895 : Nat := 927156929978896369033553

theorem tailTrace_5416895 : CollatzResearch.WordTrace tailWord_5416895 prefixEnd_5416895 927156929978896369033553 := by
  unfold tailWord_5416895
  simp only [CollatzResearch.WordTrace]
  refine ⟨197570391710522021857588139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131713594473681347905058759 197570391710522021857588139)
  ·
    refine ⟨296355587565783032786382209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197570391710522021857588139 296355587565783032786382209)
    ·
      refine ⟨222266690674337274589786657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296355587565783032786382209 222266690674337274589786657)
      ·
        refine ⟨166700018005752955942339993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222266690674337274589786657 166700018005752955942339993)
        ·
          refine ⟨125025013504314716956754995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166700018005752955942339993 125025013504314716956754995)
          ·
            refine ⟨187537520256472075435132493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125025013504314716956754995 187537520256472075435132493)
            ·
              refine ⟨70326570096177028288174685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187537520256472075435132493 70326570096177028288174685)
              ·
                refine ⟨26372463786066385608065507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70326570096177028288174685 26372463786066385608065507)
                ·
                  refine ⟨39558695679099578412098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26372463786066385608065507 39558695679099578412098261)
                  ·
                    refine ⟨927156929978896369033553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39558695679099578412098261 927156929978896369033553)
                    ·
                      rfl

theorem cell23_5416895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_5416895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416895 prefixEnd_5416895 := by exact prefixLift 5416895
  have htrace : WordTrace (prefixWord ++ tailWord_5416895) baseStart_5416895 baseEnd_5416895 := by
    simpa [prefixWord, tailWord_5416895, baseEnd_5416895] using wordTrace_append hprefix tailTrace_5416895
  have hstable : (prefixWord ++ tailWord_5416895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416895).length < 2 ^ (prefixWord ++ tailWord_5416895).sum := by decide
  have hdescent : baseEnd_5416895 < baseStart_5416895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416905 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_5416905 : Nat := 118140960795 + 5416905 * 2 ^ 59
def prefixEnd_5416905 : Nat := 4983230072969 + 3 ^ 40 * 5416905 * 2
def baseEnd_5416905 : Nat := 2781475924743234067975613

theorem tailTrace_5416905 : CollatzResearch.WordTrace tailWord_5416905 prefixEnd_5416905 2781475924743234067975613 := by
  unfold tailWord_5416905
  simp only [CollatzResearch.WordTrace]
  refine ⟨197570756440485793565452169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131713837626990529043634779 197570756440485793565452169)
  ·
    refine ⟨148178067330364345174089127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197570756440485793565452169 148178067330364345174089127)
    ·
      refine ⟨222267100995546517761133691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148178067330364345174089127 222267100995546517761133691)
      ·
        refine ⟨333400651493319776641700537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222267100995546517761133691 333400651493319776641700537)
        ·
          refine ⟨250050488619989832481275403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333400651493319776641700537 250050488619989832481275403)
          ·
            refine ⟨375075732929984748721913105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250050488619989832481275403 375075732929984748721913105)
            ·
              refine ⟨281306799697488561541434829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375075732929984748721913105 281306799697488561541434829)
              ·
                refine ⟨105490049886558210578038061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281306799697488561541434829 105490049886558210578038061)
                ·
                  refine ⟨39558768707459328966764273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105490049886558210578038061 39558768707459328966764273)
                  ·
                    refine ⟨29669076530594496725073205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39558768707459328966764273 29669076530594496725073205)
                    ·
                      refine ⟨2781475924743234067975613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29669076530594496725073205 2781475924743234067975613)
                      ·
                        rfl

theorem cell23_5416905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_5416905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416905 prefixEnd_5416905 := by exact prefixLift 5416905
  have htrace : WordTrace (prefixWord ++ tailWord_5416905) baseStart_5416905 baseEnd_5416905 := by
    simpa [prefixWord, tailWord_5416905, baseEnd_5416905] using wordTrace_append hprefix tailTrace_5416905
  have hstable : (prefixWord ++ tailWord_5416905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416905).length < 2 ^ (prefixWord ++ tailWord_5416905).sum := by decide
  have hdescent : baseEnd_5416905 < baseStart_5416905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416915 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_5416915 : Nat := 118140960795 + 5416915 * 2 ^ 59
def prefixEnd_5416915 : Nat := 4983230072969 + 3 ^ 40 * 5416915 * 2
def baseEnd_5416915 : Nat := 2781481059549779028850567

theorem tailTrace_5416915 : CollatzResearch.WordTrace tailWord_5416915 prefixEnd_5416915 2781481059549779028850567 := by
  unfold tailWord_5416915
  simp only [CollatzResearch.WordTrace]
  refine ⟨197571121170449565273316199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131714080780299710182210799 197571121170449565273316199)
  ·
    refine ⟨296356681755674347909974299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197571121170449565273316199 296356681755674347909974299)
    ·
      refine ⟨444535022633511521864961449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296356681755674347909974299 444535022633511521864961449)
      ·
        refine ⟨333401266975133641398721087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444535022633511521864961449 333401266975133641398721087)
        ·
          refine ⟨500101900462700462098081631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333401266975133641398721087 500101900462700462098081631)
          ·
            refine ⟨750152850694050693147122447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500101900462700462098081631 750152850694050693147122447)
            ·
              refine ⟨1125229276041076039720683671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750152850694050693147122447 1125229276041076039720683671)
              ·
                refine ⟨1687843914061614059581025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125229276041076039720683671 1687843914061614059581025507)
                ·
                  refine ⟨2531765871092421089371538261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687843914061614059581025507 2531765871092421089371538261)
                  ·
                    refine ⟨14834565650932154820536357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2531765871092421089371538261 14834565650932154820536357)
                    ·
                      refine ⟨2781481059549779028850567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834565650932154820536357 2781481059549779028850567)
                      ·
                        rfl

theorem cell23_5416915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_5416915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416915 prefixEnd_5416915 := by exact prefixLift 5416915
  have htrace : WordTrace (prefixWord ++ tailWord_5416915) baseStart_5416915 baseEnd_5416915 := by
    simpa [prefixWord, tailWord_5416915, baseEnd_5416915] using wordTrace_append hprefix tailTrace_5416915
  have hstable : (prefixWord ++ tailWord_5416915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416915).length < 2 ^ (prefixWord ++ tailWord_5416915).sum := by decide
  have hdescent : baseEnd_5416915 < baseStart_5416915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416916 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 5]
def baseStart_5416916 : Nat := 118140960795 + 5416916 * 2 ^ 59
def prefixEnd_5416916 : Nat := 4983230072969 + 3 ^ 40 * 5416916 * 2
def baseEnd_5416916 : Nat := 309053508114492613882007

theorem tailTrace_5416916 : CollatzResearch.WordTrace tailWord_5416916 prefixEnd_5416916 309053508114492613882007 := by
  unfold tailWord_5416916
  simp only [CollatzResearch.WordTrace]
  refine ⟨98785578821722971222051301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131714105095630628296068401 98785578821722971222051301)
  ·
    refine ⟨18522296029073057104134619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98785578821722971222051301 18522296029073057104134619)
    ·
      refine ⟨27783444043609585656201929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522296029073057104134619 27783444043609585656201929)
      ·
        refine ⟨20837583032707189242151447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27783444043609585656201929 20837583032707189242151447)
        ·
          refine ⟨31256374549060783863227171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20837583032707189242151447 31256374549060783863227171)
          ·
            refine ⟨46884561823591175794840757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31256374549060783863227171 46884561823591175794840757)
            ·
              refine ⟨4395427670961672730766321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46884561823591175794840757 4395427670961672730766321)
              ·
                refine ⟨3296570753221254548074741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395427670961672730766321 3296570753221254548074741)
                ·
                  refine ⟨309053508114492613882007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3296570753221254548074741 309053508114492613882007)
                  ·
                    rfl

theorem cell23_5416916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_5416916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416916 prefixEnd_5416916 := by exact prefixLift 5416916
  have htrace : WordTrace (prefixWord ++ tailWord_5416916) baseStart_5416916 baseEnd_5416916 := by
    simpa [prefixWord, tailWord_5416916, baseEnd_5416916] using wordTrace_append hprefix tailTrace_5416916
  have hstable : (prefixWord ++ tailWord_5416916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416916).length < 2 ^ (prefixWord ++ tailWord_5416916).sum := by decide
  have hdescent : baseEnd_5416916 < baseStart_5416916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416932 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_5416932 : Nat := 118140960795 + 5416932 * 2 ^ 59
def prefixEnd_5416932 : Nat := 4983230072969 + 3 ^ 40 * 5416932 * 2
def baseEnd_5416932 : Nat := 2781489788720905462337989

theorem tailTrace_5416932 : CollatzResearch.WordTrace tailWord_5416932 prefixEnd_5416932 2781489788720905462337989 := by
  unfold tailWord_5416932
  simp only [CollatzResearch.WordTrace]
  refine ⟨98785870605693988588342525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131714494140925318117790033 98785870605693988588342525)
  ·
    refine ⟨37044701477135245720628447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98785870605693988588342525 37044701477135245720628447)
    ·
      refine ⟨55567052215702868580942671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37044701477135245720628447 55567052215702868580942671)
      ·
        refine ⟨83350578323554302871414007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55567052215702868580942671 83350578323554302871414007)
        ·
          refine ⟨125025867485331454307121011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83350578323554302871414007 125025867485331454307121011)
          ·
            refine ⟨187538801227997181460681517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125025867485331454307121011 187538801227997181460681517)
            ·
              refine ⟨70327050460498943047755569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187538801227997181460681517 70327050460498943047755569)
              ·
                refine ⟨52745287845374207285816677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70327050460498943047755569 52745287845374207285816677)
                ·
                  refine ⟨9889741471007663866090627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52745287845374207285816677 9889741471007663866090627)
                  ·
                    refine ⟨14834612206511495799135941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9889741471007663866090627 14834612206511495799135941)
                    ·
                      refine ⟨2781489788720905462337989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834612206511495799135941 2781489788720905462337989)
                      ·
                        rfl

theorem cell23_5416932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_5416932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416932 prefixEnd_5416932 := by exact prefixLift 5416932
  have htrace : WordTrace (prefixWord ++ tailWord_5416932) baseStart_5416932 baseEnd_5416932 := by
    simpa [prefixWord, tailWord_5416932, baseEnd_5416932] using wordTrace_append hprefix tailTrace_5416932
  have hstable : (prefixWord ++ tailWord_5416932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416932).length < 2 ^ (prefixWord ++ tailWord_5416932).sum := by decide
  have hdescent : baseEnd_5416932 < baseStart_5416932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416952 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_5416952 : Nat := 118140960795 + 5416952 * 2 ^ 59
def prefixEnd_5416952 : Nat := 4983230072969 + 3 ^ 40 * 5416952 * 2
def baseEnd_5416952 : Nat := 2781500058333995384087897

theorem tailTrace_5416952 : CollatzResearch.WordTrace tailWord_5416952 prefixEnd_5416952 2781500058333995384087897 := by
  unfold tailWord_5416952
  simp only [CollatzResearch.WordTrace]
  refine ⟨98786235335657760296206555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131714980447543680394942073 98786235335657760296206555)
  ·
    refine ⟨148179353003486640444309833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98786235335657760296206555 148179353003486640444309833)
    ·
      refine ⟨111134514752614980333232375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148179353003486640444309833 111134514752614980333232375)
      ·
        refine ⟨166701772128922470499848563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111134514752614980333232375 166701772128922470499848563)
        ·
          refine ⟨250052658193383705749772845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166701772128922470499848563 250052658193383705749772845)
          ·
            refine ⟨93769746822518889656164817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250052658193383705749772845 93769746822518889656164817)
            ·
              refine ⟨70327310116889167242123613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93769746822518889656164817 70327310116889167242123613)
              ·
                refine ⟨26372741293833437715796355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70327310116889167242123613 26372741293833437715796355)
                ·
                  refine ⟨39559111940750156573694533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26372741293833437715796355 39559111940750156573694533)
                  ·
                    refine ⟨7417333488890654357567725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39559111940750156573694533 7417333488890654357567725)
                    ·
                      refine ⟨2781500058333995384087897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417333488890654357567725 2781500058333995384087897)
                      ·
                        rfl

theorem cell23_5416952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_5416952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416952 prefixEnd_5416952 := by exact prefixLift 5416952
  have htrace : WordTrace (prefixWord ++ tailWord_5416952) baseStart_5416952 baseEnd_5416952 := by
    simpa [prefixWord, tailWord_5416952, baseEnd_5416952] using wordTrace_append hprefix tailTrace_5416952
  have hstable : (prefixWord ++ tailWord_5416952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416952).length < 2 ^ (prefixWord ++ tailWord_5416952).sum := by decide
  have hdescent : baseEnd_5416952 < baseStart_5416952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416955 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 10]
def baseStart_5416955 : Nat := 118140960795 + 5416955 * 2 ^ 59
def prefixEnd_5416955 : Nat := 4983230072969 + 3 ^ 40 * 5416955 * 2
def baseEnd_5416955 : Nat := 309055733197328763594487

theorem tailTrace_5416955 : CollatzResearch.WordTrace tailWord_5416955 prefixEnd_5416955 309055733197328763594487 := by
  unfold tailWord_5416955
  simp only [CollatzResearch.WordTrace]
  refine ⟨197572580090304652104772319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131715053393536434736514879 197572580090304652104772319)
  ·
    refine ⟨296358870135456978157158479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197572580090304652104772319 296358870135456978157158479)
    ·
      refine ⟨444538305203185467235737719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296358870135456978157158479 444538305203185467235737719)
      ·
        refine ⟨666807457804778200853606579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444538305203185467235737719 666807457804778200853606579)
        ·
          refine ⟨1000211186707167301280409869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666807457804778200853606579 1000211186707167301280409869)
          ·
            refine ⟨375079195015187737980153701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000211186707167301280409869 375079195015187737980153701)
            ·
              refine ⟨70327349065347700871278819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375079195015187737980153701 70327349065347700871278819)
              ·
                refine ⟨105491023598021551306918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70327349065347700871278819 105491023598021551306918229)
                ·
                  refine ⟨309055733197328763594487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105491023598021551306918229 309055733197328763594487)
                  ·
                    rfl

theorem cell23_5416955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_5416955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416955 prefixEnd_5416955 := by exact prefixLift 5416955
  have htrace : WordTrace (prefixWord ++ tailWord_5416955) baseStart_5416955 baseEnd_5416955 := by
    simpa [prefixWord, tailWord_5416955, baseEnd_5416955] using wordTrace_append hprefix tailTrace_5416955
  have hstable : (prefixWord ++ tailWord_5416955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416955).length < 2 ^ (prefixWord ++ tailWord_5416955).sum := by decide
  have hdescent : baseEnd_5416955 < baseStart_5416955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416989 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 6]
def baseStart_5416989 : Nat := 118140960795 + 5416989 * 2 ^ 59
def prefixEnd_5416989 : Nat := 4983230072969 + 3 ^ 40 * 5416989 * 2
def baseEnd_5416989 : Nat := 309057673013134637702803

theorem tailTrace_5416989 : CollatzResearch.WordTrace tailWord_5416989 prefixEnd_5416989 309057673013134637702803 := by
  unfold tailWord_5416989
  simp only [CollatzResearch.WordTrace]
  refine ⟨197573820172181475911510021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131715880114787650607673347 197573820172181475911510021)
  ·
    refine ⟨37045091282284026733408129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197573820172181475911510021 37045091282284026733408129)
    ·
      refine ⟨27783818461713020050056097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37045091282284026733408129 27783818461713020050056097)
      ·
        refine ⟨20837863846284765037542073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27783818461713020050056097 20837863846284765037542073)
        ·
          refine ⟨15628397884713573778156555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20837863846284765037542073 15628397884713573778156555)
          ·
            refine ⟨23442596827070360667234833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15628397884713573778156555 23442596827070360667234833)
            ·
              refine ⟨17581947620302770500426125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23442596827070360667234833 17581947620302770500426125)
              ·
                refine ⟨6593230357613538937659797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17581947620302770500426125 6593230357613538937659797)
                ·
                  refine ⟨309057673013134637702803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6593230357613538937659797 309057673013134637702803)
                  ·
                    rfl

theorem cell23_5416989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_5416989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5416989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5416989 prefixEnd_5416989 := by exact prefixLift 5416989
  have htrace : WordTrace (prefixWord ++ tailWord_5416989) baseStart_5416989 baseEnd_5416989 := by
    simpa [prefixWord, tailWord_5416989, baseEnd_5416989] using wordTrace_append hprefix tailTrace_5416989
  have hstable : (prefixWord ++ tailWord_5416989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416989).length < 2 ^ (prefixWord ++ tailWord_5416989).sum := by decide
  have hdescent : baseEnd_5416989 < baseStart_5416989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417000 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5417000 : Nat := 118140960795 + 5417000 * 2 ^ 59
def prefixEnd_5417000 : Nat := 4983230072969 + 3 ^ 40 * 5417000 * 2
def baseEnd_5417000 : Nat := 2781524705405411196287677

theorem tailTrace_5417000 : CollatzResearch.WordTrace tailWord_5417000 prefixEnd_5417000 2781524705405411196287677 := by
  unfold tailWord_5417000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98787110687570812395080227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131716147583427749860106969 98787110687570812395080227)
  ·
    refine ⟨148180666031356218592620341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98787110687570812395080227 148180666031356218592620341)
    ·
      refine ⟨13891937440439645493058157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148180666031356218592620341 13891937440439645493058157)
      ·
        refine ⟨5209476540164867059896809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13891937440439645493058157 5209476540164867059896809)
        ·
          refine ⟨3907107405123650294922607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5209476540164867059896809 3907107405123650294922607)
          ·
            refine ⟨5860661107685475442383911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907107405123650294922607 5860661107685475442383911)
            ·
              refine ⟨8790991661528213163575867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860661107685475442383911 8790991661528213163575867)
              ·
                refine ⟨13186487492292319745363801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790991661528213163575867 13186487492292319745363801)
                ·
                  refine ⟨9889865619219239809022851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13186487492292319745363801 9889865619219239809022851)
                  ·
                    refine ⟨14834798428828859713534277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9889865619219239809022851 14834798428828859713534277)
                    ·
                      refine ⟨2781524705405411196287677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834798428828859713534277 2781524705405411196287677)
                      ·
                        rfl

theorem cell23_5417000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5417000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417000 prefixEnd_5417000 := by exact prefixLift 5417000
  have htrace : WordTrace (prefixWord ++ tailWord_5417000) baseStart_5417000 baseEnd_5417000 := by
    simpa [prefixWord, tailWord_5417000, baseEnd_5417000] using wordTrace_append hprefix tailTrace_5417000
  have hstable : (prefixWord ++ tailWord_5417000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417000).length < 2 ^ (prefixWord ++ tailWord_5417000).sum := by decide
  have hdescent : baseEnd_5417000 < baseStart_5417000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417053 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5417053 : Nat := 118140960795 + 5417053 * 2 ^ 59
def prefixEnd_5417053 : Nat := 4983230072969 + 3 ^ 40 * 5417053 * 2
def baseEnd_5417053 : Nat := 927183973293366496308311

theorem tailTrace_5417053 : CollatzResearch.WordTrace tailWord_5417053 prefixEnd_5417053 927183973293366496308311 := by
  unfold tailWord_5417053
  simp only [CollatzResearch.WordTrace]
  refine ⟨197576154443949614841839813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131717436295966409894559875 197576154443949614841839813)
  ·
    refine ⟨37045528958240552782844965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197576154443949614841839813 37045528958240552782844965)
    ·
      refine ⟨6946036679670103646783431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37045528958240552782844965 6946036679670103646783431)
      ·
        refine ⟨10419055019505155470175147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6946036679670103646783431 10419055019505155470175147)
        ·
          refine ⟨15628582529257733205262721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10419055019505155470175147 15628582529257733205262721)
          ·
            refine ⟨11721436896943299903947041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15628582529257733205262721 11721436896943299903947041)
            ·
              refine ⟨8791077672707474927960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11721436896943299903947041 8791077672707474927960281)
              ·
                refine ⟨6593308254530606195970211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791077672707474927960281 6593308254530606195970211)
                ·
                  refine ⟨9889962381795909293955317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593308254530606195970211 9889962381795909293955317)
                  ·
                    refine ⟨927183973293366496308311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9889962381795909293955317 927183973293366496308311)
                    ·
                      rfl

theorem cell23_5417053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5417053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417053 prefixEnd_5417053 := by exact prefixLift 5417053
  have htrace : WordTrace (prefixWord ++ tailWord_5417053) baseStart_5417053 baseEnd_5417053 := by
    simpa [prefixWord, tailWord_5417053, baseEnd_5417053] using wordTrace_append hprefix tailTrace_5417053
  have hstable : (prefixWord ++ tailWord_5417053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417053).length < 2 ^ (prefixWord ++ tailWord_5417053).sum := by decide
  have hdescent : baseEnd_5417053 < baseStart_5417053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417056 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_5417056 : Nat := 118140960795 + 5417056 * 2 ^ 59
def prefixEnd_5417056 : Nat := 4983230072969 + 3 ^ 40 * 5417056 * 2
def baseEnd_5417056 : Nat := 2781553460322062977187419

theorem tailTrace_5417056 : CollatzResearch.WordTrace tailWord_5417056 prefixEnd_5417056 2781553460322062977187419 := by
  unfold tailWord_5417056
  simp only [CollatzResearch.WordTrace]
  refine ⟨98788131931469373177099511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131717509241959164236132681 98788131931469373177099511)
  ·
    refine ⟨148182197897204059765649267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98788131931469373177099511 148182197897204059765649267)
    ·
      refine ⟨222273296845806089648473901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148182197897204059765649267 222273296845806089648473901)
      ·
        refine ⟨83352486317177283618177713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222273296845806089648473901 83352486317177283618177713)
        ·
          refine ⟨62514364737882962713633285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83352486317177283618177713 62514364737882962713633285)
          ·
            refine ⟨11721443388353055508806241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62514364737882962713633285 11721443388353055508806241)
            ·
              refine ⟨8791082541264791631604681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11721443388353055508806241 8791082541264791631604681)
              ·
                refine ⟨6593311905948593723703511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791082541264791631604681 6593311905948593723703511)
                ·
                  refine ⟨9889967858922890585555267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593311905948593723703511 9889967858922890585555267)
                  ·
                    refine ⟨14834951788384335878332901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9889967858922890585555267 14834951788384335878332901)
                    ·
                      refine ⟨2781553460322062977187419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834951788384335878332901 2781553460322062977187419)
                      ·
                        rfl

theorem cell23_5417056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_5417056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417056 prefixEnd_5417056 := by exact prefixLift 5417056
  have htrace : WordTrace (prefixWord ++ tailWord_5417056) baseStart_5417056 baseEnd_5417056 := by
    simpa [prefixWord, tailWord_5417056, baseEnd_5417056] using wordTrace_append hprefix tailTrace_5417056
  have hstable : (prefixWord ++ tailWord_5417056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417056).length < 2 ^ (prefixWord ++ tailWord_5417056).sum := by decide
  have hdescent : baseEnd_5417056 < baseStart_5417056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417059 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3]
def baseStart_5417059 : Nat := 118140960795 + 5417059 * 2 ^ 59
def prefixEnd_5417059 : Nat := 4983230072969 + 3 ^ 40 * 5417059 * 2
def baseEnd_5417059 : Nat := 2781555000764026465449905

theorem tailTrace_5417059 : CollatzResearch.WordTrace tailWord_5417059 prefixEnd_5417059 2781555000764026465449905 := by
  unfold tailWord_5417059
  simp only [CollatzResearch.WordTrace]
  refine ⟨197576373281927877866558231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131717582187951918577705487 197576373281927877866558231)
  ·
    refine ⟨296364559922891816799837347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197576373281927877866558231 296364559922891816799837347)
    ·
      refine ⟨444546839884337725199756021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296364559922891816799837347 444546839884337725199756021)
      ·
        refine ⟨41676266239156661737477127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 444546839884337725199756021 41676266239156661737477127)
        ·
          refine ⟨62514399358734992606215691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41676266239156661737477127 62514399358734992606215691)
          ·
            refine ⟨93771599038102488909323537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62514399358734992606215691 93771599038102488909323537)
            ·
              refine ⟨70328699278576866681992653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93771599038102488909323537 70328699278576866681992653)
              ·
                refine ⟨26373262229466325005747245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70328699278576866681992653 26373262229466325005747245)
                ·
                  refine ⟨9889973336049871877155217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26373262229466325005747245 9889973336049871877155217)
                  ·
                    refine ⟨7417480002037403907866413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9889973336049871877155217 7417480002037403907866413)
                    ·
                      refine ⟨2781555000764026465449905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417480002037403907866413 2781555000764026465449905)
                      ·
                        rfl

theorem cell23_5417059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_5417059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417059 prefixEnd_5417059 := by exact prefixLift 5417059
  have htrace : WordTrace (prefixWord ++ tailWord_5417059) baseStart_5417059 baseEnd_5417059 := by
    simpa [prefixWord, tailWord_5417059, baseEnd_5417059] using wordTrace_append hprefix tailTrace_5417059
  have hstable : (prefixWord ++ tailWord_5417059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417059).length < 2 ^ (prefixWord ++ tailWord_5417059).sum := by decide
  have hdescent : baseEnd_5417059 < baseStart_5417059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417069 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5417069 : Nat := 118140960795 + 5417069 * 2 ^ 59
def prefixEnd_5417069 : Nat := 4983230072969 + 3 ^ 40 * 5417069 * 2
def baseEnd_5417069 : Nat := 2781560135570571426324859

theorem tailTrace_5417069 : CollatzResearch.WordTrace tailWord_5417069 prefixEnd_5417069 2781560135570571426324859 := by
  unfold tailWord_5417069
  simp only [CollatzResearch.WordTrace]
  refine ⟨197576738011891649574422261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131717825341261099716281507 197576738011891649574422261)
  ·
    refine ⟨18522819188614842147602087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197576738011891649574422261 18522819188614842147602087)
    ·
      refine ⟨27784228782922263221403131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522819188614842147602087 27784228782922263221403131)
      ·
        refine ⟨41676343174383394832104697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27784228782922263221403131 41676343174383394832104697)
        ·
          refine ⟨31257257380787546124078523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41676343174383394832104697 31257257380787546124078523)
          ·
            refine ⟨46885886071181319186117785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31257257380787546124078523 46885886071181319186117785)
            ·
              refine ⟨35164414553385989389588339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46885886071181319186117785 35164414553385989389588339)
              ·
                refine ⟨52746621830078984084382509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35164414553385989389588339 52746621830078984084382509)
                ·
                  refine ⟨19779983186279619031643441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52746621830078984084382509 19779983186279619031643441)
                  ·
                    refine ⟨14834987389709714273732581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19779983186279619031643441 14834987389709714273732581)
                    ·
                      refine ⟨2781560135570571426324859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14834987389709714273732581 2781560135570571426324859)
                      ·
                        rfl

theorem cell23_5417069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5417069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417069 prefixEnd_5417069 := by exact prefixLift 5417069
  have htrace : WordTrace (prefixWord ++ tailWord_5417069) baseStart_5417069 baseEnd_5417069 := by
    simpa [prefixWord, tailWord_5417069, baseEnd_5417069] using wordTrace_append hprefix tailTrace_5417069
  have hstable : (prefixWord ++ tailWord_5417069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417069).length < 2 ^ (prefixWord ++ tailWord_5417069).sum := by decide
  have hdescent : baseEnd_5417069 < baseStart_5417069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417099 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 9, 2]
def baseStart_5417099 : Nat := 118140960795 + 5417099 * 2 ^ 59
def prefixEnd_5417099 : Nat := 4983230072969 + 3 ^ 40 * 5417099 * 2
def baseEnd_5417099 : Nat := 2781575539990206308949721

theorem tailTrace_5417099 : CollatzResearch.WordTrace tailWord_5417099 prefixEnd_5417099 2781575539990206308949721 := by
  unfold tailWord_5417099
  simp only [CollatzResearch.WordTrace]
  refine ⟨197577832201782964698014351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131718554801188643132009567 197577832201782964698014351)
  ·
    refine ⟨296366748302674447047021527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197577832201782964698014351 296366748302674447047021527)
    ·
      refine ⟨444550122454011670570532291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296366748302674447047021527 444550122454011670570532291)
      ·
        refine ⟨666825183681017505855798437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444550122454011670570532291 666825183681017505855798437)
        ·
          refine ⟨125029721940190782347962207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 666825183681017505855798437 125029721940190782347962207)
          ·
            refine ⟨187544582910286173521943311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125029721940190782347962207 187544582910286173521943311)
            ·
              refine ⟨281316874365429260282914967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187544582910286173521943311 281316874365429260282914967)
              ·
                refine ⟨421975311548143890424372451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281316874365429260282914967 421975311548143890424372451)
                ·
                  refine ⟨632962967322215835636558677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421975311548143890424372451 632962967322215835636558677)
                  ·
                    refine ⟨3708767386653608411932961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 632962967322215835636558677 3708767386653608411932961)
                    ·
                      refine ⟨2781575539990206308949721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708767386653608411932961 2781575539990206308949721)
                      ·
                        rfl

theorem cell23_5417099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9, 2].length) (baseStart_5417099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417099 prefixEnd_5417099 := by exact prefixLift 5417099
  have htrace : WordTrace (prefixWord ++ tailWord_5417099) baseStart_5417099 baseEnd_5417099 := by
    simpa [prefixWord, tailWord_5417099, baseEnd_5417099] using wordTrace_append hprefix tailTrace_5417099
  have hstable : (prefixWord ++ tailWord_5417099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417099).length < 2 ^ (prefixWord ++ tailWord_5417099).sum := by decide
  have hdescent : baseEnd_5417099 < baseStart_5417099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417106 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_5417106 : Nat := 118140960795 + 5417106 * 2 ^ 59
def prefixEnd_5417106 : Nat := 4983230072969 + 3 ^ 40 * 5417106 * 2
def baseEnd_5417106 : Nat := 2781579134354787781562189

theorem tailTrace_5417106 : CollatzResearch.WordTrace tailWord_5417106 prefixEnd_5417106 2781579134354787781562189 := by
  unfold tailWord_5417106
  simp only [CollatzResearch.WordTrace]
  refine ⟨49394521878189401223379793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131718725008505069929012781 49394521878189401223379793)
  ·
    refine ⟨37045891408642050917534845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49394521878189401223379793 37045891408642050917534845)
    ·
      refine ⟨13892209278240769094075567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37045891408642050917534845 13892209278240769094075567)
      ·
        refine ⟨20838313917361153641113351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892209278240769094075567 20838313917361153641113351)
        ·
          refine ⟨31257470876041730461670027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20838313917361153641113351 31257470876041730461670027)
          ·
            refine ⟨46886206314062595692505041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31257470876041730461670027 46886206314062595692505041)
            ·
              refine ⟨35164654735546946769378781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46886206314062595692505041 35164654735546946769378781)
              ·
                refine ⟨13186745525830105038517043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35164654735546946769378781 13186745525830105038517043)
                ·
                  refine ⟨19780118288745157557775565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13186745525830105038517043 19780118288745157557775565)
                  ·
                    refine ⟨7417544358279434084165837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19780118288745157557775565 7417544358279434084165837)
                    ·
                      refine ⟨2781579134354787781562189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417544358279434084165837 2781579134354787781562189)
                      ·
                        rfl

theorem cell23_5417106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_5417106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417106 prefixEnd_5417106 := by exact prefixLift 5417106
  have htrace : WordTrace (prefixWord ++ tailWord_5417106) baseStart_5417106 baseEnd_5417106 := by
    simpa [prefixWord, tailWord_5417106, baseEnd_5417106] using wordTrace_append hprefix tailTrace_5417106
  have hstable : (prefixWord ++ tailWord_5417106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417106).length < 2 ^ (prefixWord ++ tailWord_5417106).sum := by decide
  have hdescent : baseEnd_5417106 < baseStart_5417106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417141 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5417141 : Nat := 118140960795 + 5417141 * 2 ^ 59
def prefixEnd_5417141 : Nat := 4983230072969 + 3 ^ 40 * 5417141 * 2
def baseEnd_5417141 : Nat := 2781597106177695144624529

theorem tailTrace_5417141 : CollatzResearch.WordTrace tailWord_5417141 prefixEnd_5417141 2781597106177695144624529 := by
  unfold tailWord_5417141
  simp only [CollatzResearch.WordTrace]
  refine ⟨197579364067630805871043277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131719576045087203914028851 197579364067630805871043277)
  ·
    refine ⟨74092261525361552201641229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197579364067630805871043277 74092261525361552201641229)
    ·
      refine ⟨27784598072010582075615461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74092261525361552201641229 27784598072010582075615461)
      ·
        refine ⟨5209612138501984139177899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27784598072010582075615461 5209612138501984139177899)
        ·
          refine ⟨7814418207752976208766849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209612138501984139177899 7814418207752976208766849)
          ·
            refine ⟨5860813655814732156575137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7814418207752976208766849 5860813655814732156575137)
            ·
              refine ⟨4395610241861049117431353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5860813655814732156575137 4395610241861049117431353)
              ·
                refine ⟨3296707681395786838073515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395610241861049117431353 3296707681395786838073515)
                ·
                  refine ⟨4945061522093680257110273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296707681395786838073515 4945061522093680257110273)
                  ·
                    refine ⟨3708796141570260192832705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945061522093680257110273 3708796141570260192832705)
                    ·
                      refine ⟨2781597106177695144624529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708796141570260192832705 2781597106177695144624529)
                      ·
                        rfl

theorem cell23_5417141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5417141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417141 prefixEnd_5417141 := by exact prefixLift 5417141
  have htrace : WordTrace (prefixWord ++ tailWord_5417141) baseStart_5417141 baseEnd_5417141 := by
    simpa [prefixWord, tailWord_5417141, baseEnd_5417141] using wordTrace_append hprefix tailTrace_5417141
  have hstable : (prefixWord ++ tailWord_5417141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417141).length < 2 ^ (prefixWord ++ tailWord_5417141).sum := by decide
  have hdescent : baseEnd_5417141 < baseStart_5417141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417156 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5417156 : Nat := 118140960795 + 5417156 * 2 ^ 59
def prefixEnd_5417156 : Nat := 4983230072969 + 3 ^ 40 * 5417156 * 2
def baseEnd_5417156 : Nat := 927201602795837528645653

theorem tailTrace_5417156 : CollatzResearch.WordTrace tailWord_5417156 prefixEnd_5417156 927201602795837528645653 := by
  unfold tailWord_5417156
  simp only [CollatzResearch.WordTrace]
  refine ⟨98789955581288231716419661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131719940775050975621892881 98789955581288231716419661)
  ·
    refine ⟨37046233342983086893657373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98789955581288231716419661 37046233342983086893657373)
    ·
      refine ⟨13892337503618657585121515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37046233342983086893657373 13892337503618657585121515)
      ·
        refine ⟨20838506255427986377682273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892337503618657585121515 20838506255427986377682273)
        ·
          refine ⟨15628879691570989783261705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20838506255427986377682273 15628879691570989783261705)
          ·
            refine ⟨11721659768678242337446279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15628879691570989783261705 11721659768678242337446279)
            ·
              refine ⟨17582489653017363506169419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721659768678242337446279 17582489653017363506169419)
              ·
                refine ⟨26373734479526045259254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17582489653017363506169419 26373734479526045259254129)
                ·
                  refine ⟨19780300859644533944440597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26373734479526045259254129 19780300859644533944440597)
                  ·
                    refine ⟨927201602795837528645653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19780300859644533944440597 927201602795837528645653)
                    ·
                      rfl

theorem cell23_5417156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5417156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417156 prefixEnd_5417156 := by exact prefixLift 5417156
  have htrace : WordTrace (prefixWord ++ tailWord_5417156) baseStart_5417156 baseEnd_5417156 := by
    simpa [prefixWord, tailWord_5417156, baseEnd_5417156] using wordTrace_append hprefix tailTrace_5417156
  have hstable : (prefixWord ++ tailWord_5417156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417156).length < 2 ^ (prefixWord ++ tailWord_5417156).sum := by decide
  have hdescent : baseEnd_5417156 < baseStart_5417156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417163 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 2, 2, 2]
def baseStart_5417163 : Nat := 118140960795 + 5417163 * 2 ^ 59
def prefixEnd_5417163 : Nat := 4983230072969 + 3 ^ 40 * 5417163 * 2
def baseEnd_5417163 : Nat := 2781608402752094058549427

theorem tailTrace_5417163 : CollatzResearch.WordTrace tailWord_5417163 prefixEnd_5417163 2781608402752094058549427 := by
  unfold tailWord_5417163
  simp only [CollatzResearch.WordTrace]
  refine ⟨197580166473551103628344143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131720110982367402418896095 197580166473551103628344143)
  ·
    refine ⟨296370249710326655442516215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197580166473551103628344143 296370249710326655442516215)
    ·
      refine ⟨444555374565489983163774323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296370249710326655442516215 444555374565489983163774323)
      ·
        refine ⟨666833061848234974745661485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444555374565489983163774323 666833061848234974745661485)
        ·
          refine ⟨250062398193088115529623057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666833061848234974745661485 250062398193088115529623057)
          ·
            refine ⟨187546798644816086647217293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250062398193088115529623057 187546798644816086647217293)
            ·
              refine ⟨70330049491806032492706485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187546798644816086647217293 70330049491806032492706485)
              ·
                refine ⟨6593442139856815546191233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70330049491806032492706485 6593442139856815546191233)
                ·
                  refine ⟨4945081604892611659643425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6593442139856815546191233 4945081604892611659643425)
                  ·
                    refine ⟨3708811203669458744732569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945081604892611659643425 3708811203669458744732569)
                    ·
                      refine ⟨2781608402752094058549427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708811203669458744732569 2781608402752094058549427)
                      ·
                        rfl

theorem cell23_5417163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2, 2].length) (baseStart_5417163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417163 prefixEnd_5417163 := by exact prefixLift 5417163
  have htrace : WordTrace (prefixWord ++ tailWord_5417163) baseStart_5417163 baseEnd_5417163 := by
    simpa [prefixWord, tailWord_5417163, baseEnd_5417163] using wordTrace_append hprefix tailTrace_5417163
  have hstable : (prefixWord ++ tailWord_5417163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417163).length < 2 ^ (prefixWord ++ tailWord_5417163).sum := by decide
  have hdescent : baseEnd_5417163 < baseStart_5417163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3]
def baseStart_5417179 : Nat := 118140960795 + 5417179 * 2 ^ 59
def prefixEnd_5417179 : Nat := 4983230072969 + 3 ^ 40 * 5417179 * 2
def baseEnd_5417179 : Nat := 2781616618442565995949353

theorem tailTrace_5417179 : CollatzResearch.WordTrace tailWord_5417179 prefixEnd_5417179 2781616618442565995949353 := by
  unfold tailWord_5417179
  simp only [CollatzResearch.WordTrace]
  refine ⟨197580750041493138360926591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131720500027662092240617727 197580750041493138360926591)
  ·
    refine ⟨296371125062239707541389887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197580750041493138360926591 296371125062239707541389887)
    ·
      refine ⟨444556687593359561312084831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296371125062239707541389887 444556687593359561312084831)
      ·
        refine ⟨666835031390039341968127247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444556687593359561312084831 666835031390039341968127247)
        ·
          refine ⟨1000252547085059012952190871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666835031390039341968127247 1000252547085059012952190871)
          ·
            refine ⟨1500378820627588519428286307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000252547085059012952190871 1500378820627588519428286307)
            ·
              refine ⟨2250568230941382779142429461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500378820627588519428286307 2250568230941382779142429461)
              ·
                refine ⟨105495385825377317772301381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2250568230941382779142429461 105495385825377317772301381)
                ·
                  refine ⟨19780384842258247082306509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105495385825377317772301381 19780384842258247082306509)
                  ·
                    refine ⟨7417644315846842655864941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19780384842258247082306509 7417644315846842655864941)
                    ·
                      refine ⟨2781616618442565995949353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417644315846842655864941 2781616618442565995949353)
                      ·
                        rfl

theorem cell23_5417179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].length) (baseStart_5417179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417179 prefixEnd_5417179 := by exact prefixLift 5417179
  have htrace : WordTrace (prefixWord ++ tailWord_5417179) baseStart_5417179 baseEnd_5417179 := by
    simpa [prefixWord, tailWord_5417179, baseEnd_5417179] using wordTrace_append hprefix tailTrace_5417179
  have hstable : (prefixWord ++ tailWord_5417179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417179).length < 2 ^ (prefixWord ++ tailWord_5417179).sum := by decide
  have hdescent : baseEnd_5417179 < baseStart_5417179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417219 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_5417219 : Nat := 118140960795 + 5417219 * 2 ^ 59
def prefixEnd_5417219 : Nat := 4983230072969 + 3 ^ 40 * 5417219 * 2
def baseEnd_5417219 : Nat := 2781637157668745839449169

theorem tailTrace_5417219 : CollatzResearch.WordTrace tailWord_5417219 prefixEnd_5417219 2781637157668745839449169 := by
  unfold tailWord_5417219
  simp only [CollatzResearch.WordTrace]
  refine ⟨197582208961348225192382711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131721472640898816794921807 197582208961348225192382711)
  ·
    refine ⟨296373313442022337788574067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197582208961348225192382711 296373313442022337788574067)
    ·
      refine ⟨444559970163033506682861101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296373313442022337788574067 444559970163033506682861101)
      ·
        refine ⟨166709988811137565006072913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444559970163033506682861101 166709988811137565006072913)
        ·
          refine ⟨125032491608353173754554685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166709988811137565006072913 125032491608353173754554685)
          ·
            refine ⟨46887184353132440157958007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125032491608353173754554685 46887184353132440157958007)
            ·
              refine ⟨70330776529698660236937011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46887184353132440157958007 70330776529698660236937011)
              ·
                refine ⟨105496164794547990355405517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70330776529698660236937011 105496164794547990355405517)
                ·
                  refine ⟨39561061797955496383277069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105496164794547990355405517 39561061797955496383277069)
                  ·
                    refine ⟨14835398174233311143728901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39561061797955496383277069 14835398174233311143728901)
                    ·
                      refine ⟨2781637157668745839449169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14835398174233311143728901 2781637157668745839449169)
                      ·
                        rfl

theorem cell23_5417219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_5417219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417219 prefixEnd_5417219 := by exact prefixLift 5417219
  have htrace : WordTrace (prefixWord ++ tailWord_5417219) baseStart_5417219 baseEnd_5417219 := by
    simpa [prefixWord, tailWord_5417219, baseEnd_5417219] using wordTrace_append hprefix tailTrace_5417219
  have hstable : (prefixWord ++ tailWord_5417219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417219).length < 2 ^ (prefixWord ++ tailWord_5417219).sum := by decide
  have hdescent : baseEnd_5417219 < baseStart_5417219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417249 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5417249 : Nat := 118140960795 + 5417249 * 2 ^ 59
def prefixEnd_5417249 : Nat := 4983230072969 + 3 ^ 40 * 5417249 * 2
def baseEnd_5417249 : Nat := 2781652562088380722074031

theorem tailTrace_5417249 : CollatzResearch.WordTrace tailWord_5417249 prefixEnd_5417249 2781652562088380722074031 := by
  unfold tailWord_5417249
  simp only [CollatzResearch.WordTrace]
  refine ⟨197583303151239540315974801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131722202100826360210649867 197583303151239540315974801)
  ·
    refine ⟨148187477363429655236981101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197583303151239540315974801 148187477363429655236981101)
    ·
      refine ⟨55570304011286120713867913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148187477363429655236981101 55570304011286120713867913)
      ·
        refine ⟨41677728008464590535400935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55570304011286120713867913 41677728008464590535400935)
        ·
          refine ⟨62516592012696885803101403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41677728008464590535400935 62516592012696885803101403)
          ·
            refine ⟨93774888019045328704652105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62516592012696885803101403 93774888019045328704652105)
            ·
              refine ⟨70331166014283996528489079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93774888019045328704652105 70331166014283996528489079)
              ·
                refine ⟨105496749021425994792733619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70331166014283996528489079 105496749021425994792733619)
                ·
                  refine ⟨158245123532138992189100429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105496749021425994792733619 158245123532138992189100429)
                  ·
                    refine ⟨59341921324552122070912661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158245123532138992189100429 59341921324552122070912661)
                    ·
                      refine ⟨2781652562088380722074031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59341921324552122070912661 2781652562088380722074031)
                      ·
                        rfl

theorem cell23_5417249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5417249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417249 prefixEnd_5417249 := by exact prefixLift 5417249
  have htrace : WordTrace (prefixWord ++ tailWord_5417249) baseStart_5417249 baseEnd_5417249 := by
    simpa [prefixWord, tailWord_5417249, baseEnd_5417249] using wordTrace_append hprefix tailTrace_5417249
  have hstable : (prefixWord ++ tailWord_5417249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417249).length < 2 ^ (prefixWord ++ tailWord_5417249).sum := by decide
  have hdescent : baseEnd_5417249 < baseStart_5417249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417253 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_5417253 : Nat := 118140960795 + 5417253 * 2 ^ 59
def prefixEnd_5417253 : Nat := 4983230072969 + 3 ^ 40 * 5417253 * 2
def baseEnd_5417253 : Nat := 2781654616010998706424013

theorem tailTrace_5417253 : CollatzResearch.WordTrace tailWord_5417253 prefixEnd_5417253 2781654616010998706424013 := by
  unfold tailWord_5417253
  simp only [CollatzResearch.WordTrace]
  refine ⟨197583449043225048999120413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131722299362150032666080275 197583449043225048999120413)
  ·
    refine ⟨74093793391209393374670155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197583449043225048999120413 74093793391209393374670155)
    ·
      refine ⟨111140690086814090062005233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74093793391209393374670155 111140690086814090062005233)
      ·
        refine ⟨83355517565110567546503925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111140690086814090062005233 83355517565110567546503925)
        ·
          refine ⟨7814579771729115707484743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83355517565110567546503925 7814579771729115707484743)
          ·
            refine ⟨11721869657593673561227115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814579771729115707484743 11721869657593673561227115)
            ·
              refine ⟨17582804486390510341840673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721869657593673561227115 17582804486390510341840673)
              ·
                refine ⟨13187103364792882756380505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17582804486390510341840673 13187103364792882756380505)
                ·
                  refine ⟨9890327523594662067285379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13187103364792882756380505 9890327523594662067285379)
                  ·
                    refine ⟨14835491285391993100928069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9890327523594662067285379 14835491285391993100928069)
                    ·
                      refine ⟨2781654616010998706424013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14835491285391993100928069 2781654616010998706424013)
                      ·
                        rfl

theorem cell23_5417253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_5417253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417253 prefixEnd_5417253 := by exact prefixLift 5417253
  have htrace : WordTrace (prefixWord ++ tailWord_5417253) baseStart_5417253 baseEnd_5417253 := by
    simpa [prefixWord, tailWord_5417253, baseEnd_5417253] using wordTrace_append hprefix tailTrace_5417253
  have hstable : (prefixWord ++ tailWord_5417253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417253).length < 2 ^ (prefixWord ++ tailWord_5417253).sum := by decide
  have hdescent : baseEnd_5417253 < baseStart_5417253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417263 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 1, 4]
def baseStart_5417263 : Nat := 118140960795 + 5417263 * 2 ^ 59
def prefixEnd_5417263 : Nat := 4983230072969 + 3 ^ 40 * 5417263 * 2
def baseEnd_5417263 : Nat := 927219916939181222432989

theorem tailTrace_5417263 : CollatzResearch.WordTrace tailWord_5417263 prefixEnd_5417263 927219916939181222432989 := by
  unfold tailWord_5417263
  simp only [CollatzResearch.WordTrace]
  refine ⟨197583813773188820706984443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131722542515459213804656295 197583813773188820706984443)
  ·
    refine ⟨296375720659783231060476665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197583813773188820706984443 296375720659783231060476665)
    ·
      refine ⟨222281790494837423295357499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296375720659783231060476665 222281790494837423295357499)
      ·
        refine ⟨333422685742256134943036249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222281790494837423295357499 333422685742256134943036249)
        ·
          refine ⟨250067014306692101207277187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333422685742256134943036249 250067014306692101207277187)
          ·
            refine ⟨375100521460038151810915781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250067014306692101207277187 375100521460038151810915781)
            ·
              refine ⟨70331347773757153464546709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375100521460038151810915781 70331347773757153464546709)
              ·
                refine ⟨3296781926894866568650627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70331347773757153464546709 3296781926894866568650627)
                ·
                  refine ⟨4945172890342299852975941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296781926894866568650627 4945172890342299852975941)
                  ·
                    refine ⟨927219916939181222432989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945172890342299852975941 927219916939181222432989)
                    ·
                      rfl

theorem cell23_5417263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_5417263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417263 prefixEnd_5417263 := by exact prefixLift 5417263
  have htrace : WordTrace (prefixWord ++ tailWord_5417263) baseStart_5417263 baseEnd_5417263 := by
    simpa [prefixWord, tailWord_5417263, baseEnd_5417263] using wordTrace_append hprefix tailTrace_5417263
  have hstable : (prefixWord ++ tailWord_5417263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417263).length < 2 ^ (prefixWord ++ tailWord_5417263).sum := by decide
  have hdescent : baseEnd_5417263 < baseStart_5417263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417276 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 6]
def baseStart_5417276 : Nat := 118140960795 + 5417276 * 2 ^ 59
def prefixEnd_5417276 : Nat := 4983230072969 + 3 ^ 40 * 5417276 * 2
def baseEnd_5417276 : Nat := 309074047340672457381823

theorem tailTrace_5417276 : CollatzResearch.WordTrace tailWord_5417276 prefixEnd_5417276 309074047340672457381823 := by
  unfold tailWord_5417276
  simp only [CollatzResearch.WordTrace]
  refine ⟨98792143961070861963603841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131722858614761149284805121 98792143961070861963603841)
  ·
    refine ⟨74094107970803146472702881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98792143961070861963603841 74094107970803146472702881)
    ·
      refine ⟨55570580978102359854527161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74094107970803146472702881 55570580978102359854527161)
      ·
        refine ⟨41677935733576769890895371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55570580978102359854527161 41677935733576769890895371)
        ·
          refine ⟨62516903600365154836343057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41677935733576769890895371 62516903600365154836343057)
          ·
            refine ⟨46887677700273866127257293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62516903600365154836343057 46887677700273866127257293)
            ·
              refine ⟨17582879137602699797721485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46887677700273866127257293 17582879137602699797721485)
              ·
                refine ⟨6593579676601012424145557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17582879137602699797721485 6593579676601012424145557)
                ·
                  refine ⟨309074047340672457381823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6593579676601012424145557 309074047340672457381823)
                  ·
                    rfl

theorem cell23_5417276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_5417276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417276 prefixEnd_5417276 := by exact prefixLift 5417276
  have htrace : WordTrace (prefixWord ++ tailWord_5417276) baseStart_5417276 baseEnd_5417276 := by
    simpa [prefixWord, tailWord_5417276, baseEnd_5417276] using wordTrace_append hprefix tailTrace_5417276
  have hstable : (prefixWord ++ tailWord_5417276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417276).length < 2 ^ (prefixWord ++ tailWord_5417276).sum := by decide
  have hdescent : baseEnd_5417276 < baseStart_5417276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417299 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_5417299 : Nat := 118140960795 + 5417299 * 2 ^ 59
def prefixEnd_5417299 : Nat := 4983230072969 + 3 ^ 40 * 5417299 * 2
def baseEnd_5417299 : Nat := 2781678236121105526448801

theorem tailTrace_5417299 : CollatzResearch.WordTrace tailWord_5417299 prefixEnd_5417299 2781678236121105526448801 := by
  unfold tailWord_5417299
  simp only [CollatzResearch.WordTrace]
  refine ⟨197585126801058398855294951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131723417867372265903529967 197585126801058398855294951)
  ·
    refine ⟨296377690201587598282942427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197585126801058398855294951 296377690201587598282942427)
    ·
      refine ⟨444566535302381397424413641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296377690201587598282942427 444566535302381397424413641)
      ·
        refine ⟨333424901476786048068310231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444566535302381397424413641 333424901476786048068310231)
        ·
          refine ⟨500137352215179072102465347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333424901476786048068310231 500137352215179072102465347)
          ·
            refine ⟨750206028322768608153698021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500137352215179072102465347 750206028322768608153698021)
            ·
              refine ⟨140663630310519114028818379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750206028322768608153698021 140663630310519114028818379)
              ·
                refine ⟨210995445465778671043227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140663630310519114028818379 210995445465778671043227569)
                ·
                  refine ⟨158246584099334003282420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210995445465778671043227569 158246584099334003282420677)
                  ·
                    refine ⟨29671234518625125615453877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158246584099334003282420677 29671234518625125615453877)
                    ·
                      refine ⟨2781678236121105526448801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29671234518625125615453877 2781678236121105526448801)
                      ·
                        rfl

theorem cell23_5417299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_5417299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417299 prefixEnd_5417299 := by exact prefixLift 5417299
  have htrace : WordTrace (prefixWord ++ tailWord_5417299) baseStart_5417299 baseEnd_5417299 := by
    simpa [prefixWord, tailWord_5417299, baseEnd_5417299] using wordTrace_append hprefix tailTrace_5417299
  have hstable : (prefixWord ++ tailWord_5417299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417299).length < 2 ^ (prefixWord ++ tailWord_5417299).sum := by decide
  have hdescent : baseEnd_5417299 < baseStart_5417299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417314 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5417314 : Nat := 118140960795 + 5417314 * 2 ^ 59
def prefixEnd_5417314 : Nat := 4983230072969 + 3 ^ 40 * 5417314 * 2
def baseEnd_5417314 : Nat := 927228646110307655920411

theorem tailTrace_5417314 : CollatzResearch.WordTrace tailWord_5417314 prefixEnd_5417314 927228646110307655920411 := by
  unfold tailWord_5417314
  simp only [CollatzResearch.WordTrace]
  refine ⟨49396418474001014104272749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131723782597336037611393997 49396418474001014104272749)
  ·
    refine ⟨18523656927750380289102281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49396418474001014104272749 18523656927750380289102281)
    ·
      refine ⟨13892742695812785216826711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18523656927750380289102281 13892742695812785216826711)
      ·
        refine ⟨20839114043719177825240067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892742695812785216826711 20839114043719177825240067)
        ·
          refine ⟨31258671065578766737860101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20839114043719177825240067 31258671065578766737860101)
          ·
            refine ⟨5861000824796018763348769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31258671065578766737860101 5861000824796018763348769)
            ·
              refine ⟨4395750618597014072511577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861000824796018763348769 4395750618597014072511577)
              ·
                refine ⟨3296812963947760554383683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395750618597014072511577 3296812963947760554383683)
                ·
                  refine ⟨4945219445921640831575525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296812963947760554383683 4945219445921640831575525)
                  ·
                    refine ⟨927228646110307655920411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945219445921640831575525 927228646110307655920411)
                    ·
                      rfl

theorem cell23_5417314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5417314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417314 prefixEnd_5417314 := by exact prefixLift 5417314
  have htrace : WordTrace (prefixWord ++ tailWord_5417314) baseStart_5417314 baseEnd_5417314 := by
    simpa [prefixWord, tailWord_5417314, baseEnd_5417314] using wordTrace_append hprefix tailTrace_5417314
  have hstable : (prefixWord ++ tailWord_5417314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417314).length < 2 ^ (prefixWord ++ tailWord_5417314).sum := by decide
  have hdescent : baseEnd_5417314 < baseStart_5417314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417347 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 2, 3, 2]
def baseStart_5417347 : Nat := 118140960795 + 5417347 * 2 ^ 59
def prefixEnd_5417347 : Nat := 4983230072969 + 3 ^ 40 * 5417347 * 2
def baseEnd_5417347 : Nat := 2781702883192521338648581

theorem tailTrace_5417347 : CollatzResearch.WordTrace tailWord_5417347 prefixEnd_5417347 2781702883192521338648581 := by
  unfold tailWord_5417347
  simp only [CollatzResearch.WordTrace]
  refine ⟨197586877504884503053042295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131724585003256335368694863 197586877504884503053042295)
  ·
    refine ⟨296380316257326754579563443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197586877504884503053042295 296380316257326754579563443)
    ·
      refine ⟨444570474385990131869345165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296380316257326754579563443 444570474385990131869345165)
      ·
        refine ⟨166713927894746299451004437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444570474385990131869345165 166713927894746299451004437)
        ·
          refine ⟨7814715370066232786765833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166713927894746299451004437 7814715370066232786765833)
          ·
            refine ⟨5861036527549674590074375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7814715370066232786765833 5861036527549674590074375)
            ·
              refine ⟨8791554791324511885111563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861036527549674590074375 8791554791324511885111563)
              ·
                refine ⟨13187332186986767827667345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8791554791324511885111563 13187332186986767827667345)
                ·
                  refine ⟨9890499140240075870750509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13187332186986767827667345 9890499140240075870750509)
                  ·
                    refine ⟨3708937177590028451531441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9890499140240075870750509 3708937177590028451531441)
                    ·
                      refine ⟨2781702883192521338648581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3708937177590028451531441 2781702883192521338648581)
                      ·
                        rfl

theorem cell23_5417347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_5417347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417347 prefixEnd_5417347 := by exact prefixLift 5417347
  have htrace : WordTrace (prefixWord ++ tailWord_5417347) baseStart_5417347 baseEnd_5417347 := by
    simpa [prefixWord, tailWord_5417347, baseEnd_5417347] using wordTrace_append hprefix tailTrace_5417347
  have hstable : (prefixWord ++ tailWord_5417347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417347).length < 2 ^ (prefixWord ++ tailWord_5417347).sum := by decide
  have hdescent : baseEnd_5417347 < baseStart_5417347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417370 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_5417370 : Nat := 118140960795 + 5417370 * 2 ^ 59
def prefixEnd_5417370 : Nat := 4983230072969 + 3 ^ 40 * 5417370 * 2
def baseEnd_5417370 : Nat := 927238231082524916220325

theorem tailTrace_5417370 : CollatzResearch.WordTrace tailWord_5417370 prefixEnd_5417370 927238231082524916220325 := by
  unfold tailWord_5417370
  simp only [CollatzResearch.WordTrace]
  refine ⟨49396929095950294495282391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131725144255867451987419709 49396929095950294495282391)
  ·
    refine ⟨74095393643925441742923587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49396929095950294495282391 74095393643925441742923587)
    ·
      refine ⟨111143090465888162614385381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74095393643925441742923587 111143090465888162614385381)
      ·
        refine ⟨20839329462354030490197259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111143090465888162614385381 20839329462354030490197259)
        ·
          refine ⟨31258994193531045735295889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20839329462354030490197259 31258994193531045735295889)
          ·
            refine ⟨23444245645148284301471917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31258994193531045735295889 23444245645148284301471917)
            ·
              refine ⟨8791592116930606613051969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23444245645148284301471917 8791592116930606613051969)
              ·
                refine ⟨6593694087697954959788977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791592116930606613051969 6593694087697954959788977)
                ·
                  refine ⟨4945270565773466219841733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6593694087697954959788977 4945270565773466219841733)
                  ·
                    refine ⟨927238231082524916220325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945270565773466219841733 927238231082524916220325)
                    ·
                      rfl

theorem cell23_5417370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_5417370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417370 prefixEnd_5417370 := by exact prefixLift 5417370
  have htrace : WordTrace (prefixWord ++ tailWord_5417370) baseStart_5417370 baseEnd_5417370 := by
    simpa [prefixWord, tailWord_5417370, baseEnd_5417370] using wordTrace_append hprefix tailTrace_5417370
  have hstable : (prefixWord ++ tailWord_5417370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417370).length < 2 ^ (prefixWord ++ tailWord_5417370).sum := by decide
  have hdescent : baseEnd_5417370 < baseStart_5417370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417397 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_5417397 : Nat := 118140960795 + 5417397 * 2 ^ 59
def prefixEnd_5417397 : Nat := 4983230072969 + 3 ^ 40 * 5417397 * 2
def baseEnd_5417397 : Nat := 2781728557225246143023351

theorem tailTrace_5417397 : CollatzResearch.WordTrace tailWord_5417397 prefixEnd_5417397 2781728557225246143023351 := by
  unfold tailWord_5417397
  simp only [CollatzResearch.WordTrace]
  refine ⟨197588701154703361592362445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131725800769802241061574963 197588701154703361592362445)
  ·
    refine ⟨74095762933013760597135917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197588701154703361592362445 74095762933013760597135917)
    ·
      refine ⟨27785911099880160223925969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74095762933013760597135917 27785911099880160223925969)
      ·
        refine ⟨20839433324910120167944477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27785911099880160223925969 20839433324910120167944477)
        ·
          refine ⟨7814787496841295062979179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20839433324910120167944477 7814787496841295062979179)
          ·
            refine ⟨11722181245261942594468769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814787496841295062979179 11722181245261942594468769)
            ·
              refine ⟨8791635933946456945851577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11722181245261942594468769 8791635933946456945851577)
              ·
                refine ⟨6593726950459842709388683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791635933946456945851577 6593726950459842709388683)
                ·
                  refine ⟨9890590425689764064083025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593726950459842709388683 9890590425689764064083025)
                  ·
                    refine ⟨7417942819267323048062269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9890590425689764064083025 7417942819267323048062269)
                    ·
                      refine ⟨2781728557225246143023351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7417942819267323048062269 2781728557225246143023351)
                      ·
                        rfl

theorem cell23_5417397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_5417397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417397 prefixEnd_5417397 := by exact prefixLift 5417397
  have htrace : WordTrace (prefixWord ++ tailWord_5417397) baseStart_5417397 baseEnd_5417397 := by
    simpa [prefixWord, tailWord_5417397, baseEnd_5417397] using wordTrace_append hprefix tailTrace_5417397
  have hstable : (prefixWord ++ tailWord_5417397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417397).length < 2 ^ (prefixWord ++ tailWord_5417397).sum := by decide
  have hdescent : baseEnd_5417397 < baseStart_5417397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417454 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_5417454 : Nat := 118140960795 + 5417454 * 2 ^ 59
def prefixEnd_5417454 : Nat := 4983230072969 + 3 ^ 40 * 5417454 * 2
def baseEnd_5417454 : Nat := 2781757825622552420010589

theorem tailTrace_5417454 : CollatzResearch.WordTrace tailWord_5417454 prefixEnd_5417454 2781757825622552420010589 := by
  unfold tailWord_5417454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24698847514437107540898427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131727186743664573551458277 24698847514437107540898427)
  ·
    refine ⟨37048271271655661311347641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24698847514437107540898427 37048271271655661311347641)
    ·
      refine ⟨27786203453741745983510731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37048271271655661311347641 27786203453741745983510731)
      ·
        refine ⟨41679305180612618975266097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27786203453741745983510731 41679305180612618975266097)
        ·
          refine ⟨31259478885459464231449573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41679305180612618975266097 31259478885459464231449573)
          ·
            refine ⟨5861152291023649543396795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31259478885459464231449573 5861152291023649543396795)
            ·
              refine ⟨8791728436535474315095193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861152291023649543396795 8791728436535474315095193)
              ·
                refine ⟨6593796327401605736321395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791728436535474315095193 6593796327401605736321395)
                ·
                  refine ⟨9890694491102408604482093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593796327401605736321395 9890694491102408604482093)
                  ·
                    refine ⟨3709010434163403226680785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9890694491102408604482093 3709010434163403226680785)
                    ·
                      refine ⟨2781757825622552420010589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709010434163403226680785 2781757825622552420010589)
                      ·
                        rfl

theorem cell23_5417454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_5417454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417454 prefixEnd_5417454 := by exact prefixLift 5417454
  have htrace : WordTrace (prefixWord ++ tailWord_5417454) baseStart_5417454 baseEnd_5417454 := by
    simpa [prefixWord, tailWord_5417454, baseEnd_5417454] using wordTrace_append hprefix tailTrace_5417454
  have hstable : (prefixWord ++ tailWord_5417454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417454).length < 2 ^ (prefixWord ++ tailWord_5417454).sum := by decide
  have hdescent : baseEnd_5417454 < baseStart_5417454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417456 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 9]
def baseStart_5417456 : Nat := 118140960795 + 5417456 * 2 ^ 59
def prefixEnd_5417456 : Nat := 4983230072969 + 3 ^ 40 * 5417456 * 2
def baseEnd_5417456 : Nat := 309084316953762379131731

theorem tailTrace_5417456 : CollatzResearch.WordTrace tailWord_5417456 prefixEnd_5417456 309084316953762379131731 := by
  unfold tailWord_5417456
  simp only [CollatzResearch.WordTrace]
  refine ⟨98795426530744807334380111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131727235374326409779173481 98795426530744807334380111)
  ·
    refine ⟨148193139796117211001570167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98795426530744807334380111 148193139796117211001570167)
    ·
      refine ⟨222289709694175816502355251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148193139796117211001570167 222289709694175816502355251)
      ·
        refine ⟨333434564541263724753532877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222289709694175816502355251 333434564541263724753532877)
        ·
          refine ⟨125037961702973896782574829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333434564541263724753532877 125037961702973896782574829)
          ·
            refine ⟨46889235638615211293465561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125037961702973896782574829 46889235638615211293465561)
            ·
              refine ⟨35166926728961408470099171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46889235638615211293465561 35166926728961408470099171)
              ·
                refine ⟨52750390093442112705148757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35166926728961408470099171 52750390093442112705148757)
                ·
                  refine ⟨309084316953762379131731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52750390093442112705148757 309084316953762379131731)
                  ·
                    rfl

theorem cell23_5417456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_5417456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417456 prefixEnd_5417456 := by exact prefixLift 5417456
  have htrace : WordTrace (prefixWord ++ tailWord_5417456) baseStart_5417456 baseEnd_5417456 := by
    simpa [prefixWord, tailWord_5417456, baseEnd_5417456] using wordTrace_append hprefix tailTrace_5417456
  have hstable : (prefixWord ++ tailWord_5417456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417456).length < 2 ^ (prefixWord ++ tailWord_5417456).sum := by decide
  have hdescent : baseEnd_5417456 < baseStart_5417456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_5417466 : Nat := 118140960795 + 5417466 * 2 ^ 59
def prefixEnd_5417466 : Nat := 4983230072969 + 3 ^ 40 * 5417466 * 2
def baseEnd_5417466 : Nat := 2781763987390406373060533

theorem tailTrace_5417466 : CollatzResearch.WordTrace tailWord_5417466 prefixEnd_5417466 2781763987390406373060533 := by
  unfold tailWord_5417466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49397804447863346594156063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131727478527635590917749501 49397804447863346594156063)
  ·
    refine ⟨74096706671795019891234095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49397804447863346594156063 74096706671795019891234095)
    ·
      refine ⟨111145060007692529836851143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74096706671795019891234095 111145060007692529836851143)
      ·
        refine ⟨166717590011538794755276715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111145060007692529836851143 166717590011538794755276715)
        ·
          refine ⟨250076385017308192132915073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166717590011538794755276715 250076385017308192132915073)
          ·
            refine ⟨187557288762981144099686305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250076385017308192132915073 187557288762981144099686305)
            ·
              refine ⟨140667966572235858074764729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187557288762981144099686305 140667966572235858074764729)
              ·
                refine ⟨105500974929176893556073547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140667966572235858074764729 105500974929176893556073547)
                ·
                  refine ⟨158251462393765340334110321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105500974929176893556073547 158251462393765340334110321)
                  ·
                    refine ⟨118688596795324005250582741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158251462393765340334110321 118688596795324005250582741)
                    ·
                      refine ⟨2781763987390406373060533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118688596795324005250582741 2781763987390406373060533)
                      ·
                        rfl

theorem cell23_5417466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_5417466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417466 prefixEnd_5417466 := by exact prefixLift 5417466
  have htrace : WordTrace (prefixWord ++ tailWord_5417466) baseStart_5417466 baseEnd_5417466 := by
    simpa [prefixWord, tailWord_5417466, baseEnd_5417466] using wordTrace_append hprefix tailTrace_5417466
  have hstable : (prefixWord ++ tailWord_5417466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417466).length < 2 ^ (prefixWord ++ tailWord_5417466).sum := by decide
  have hdescent : baseEnd_5417466 < baseStart_5417466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417478 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5417478 : Nat := 118140960795 + 5417478 * 2 ^ 59
def prefixEnd_5417478 : Nat := 4983230072969 + 3 ^ 40 * 5417478 * 2
def baseEnd_5417478 : Nat := 2781770149158260326110479

theorem tailTrace_5417478 : CollatzResearch.WordTrace tailWord_5417478 prefixEnd_5417478 2781770149158260326110479 := by
  unfold tailWord_5417478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174739233356559763314409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131727770311606608284040725 6174739233356559763314409)
  ·
    refine ⟨4631054425017419822485807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6174739233356559763314409 4631054425017419822485807)
    ·
      refine ⟨6946581637526129733728711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631054425017419822485807 6946581637526129733728711)
      ·
        refine ⟨10419872456289194600593067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6946581637526129733728711 10419872456289194600593067)
        ·
          refine ⟨15629808684433791900889601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10419872456289194600593067 15629808684433791900889601)
          ·
            refine ⟨11722356513325343925667201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15629808684433791900889601 11722356513325343925667201)
            ·
              refine ⟨8791767384994007944250401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11722356513325343925667201 8791767384994007944250401)
              ·
                refine ⟨6593825538745505958187801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791767384994007944250401 6593825538745505958187801)
                ·
                  refine ⟨4945369154059129468640851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6593825538745505958187801 4945369154059129468640851)
                  ·
                    refine ⟨7418053731088694202961277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945369154059129468640851 7418053731088694202961277)
                    ·
                      refine ⟨2781770149158260326110479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418053731088694202961277 2781770149158260326110479)
                      ·
                        rfl

theorem cell23_5417478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5417478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417478 prefixEnd_5417478 := by exact prefixLift 5417478
  have htrace : WordTrace (prefixWord ++ tailWord_5417478) baseStart_5417478 baseEnd_5417478 := by
    simpa [prefixWord, tailWord_5417478, baseEnd_5417478] using wordTrace_append hprefix tailTrace_5417478
  have hstable : (prefixWord ++ tailWord_5417478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417478).length < 2 ^ (prefixWord ++ tailWord_5417478).sum := by decide
  have hdescent : baseEnd_5417478 < baseStart_5417478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417484 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_5417484 : Nat := 118140960795 + 5417484 * 2 ^ 59
def prefixEnd_5417484 : Nat := 4983230072969 + 3 ^ 40 * 5417484 * 2
def baseEnd_5417484 : Nat := 2781773230042187302635451

theorem tailTrace_5417484 : CollatzResearch.WordTrace tailWord_5417484 prefixEnd_5417484 2781773230042187302635451 := by
  unfold tailWord_5417484
  simp only [CollatzResearch.WordTrace]
  refine ⟨98795937152694087725389753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131727916203592116967186337 98795937152694087725389753)
  ·
    refine ⟨74096952864520565794042315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98795937152694087725389753 74096952864520565794042315)
    ·
      refine ⟨111145429296780848691063473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74096952864520565794042315 111145429296780848691063473)
      ·
        refine ⟨83359071972585636518297605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111145429296780848691063473 83359071972585636518297605)
        ·
          refine ⟨15629825994859806847180801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83359071972585636518297605 15629825994859806847180801)
          ·
            refine ⟨11722369496144855135385601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15629825994859806847180801 11722369496144855135385601)
            ·
              refine ⟨8791777122108641351539201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11722369496144855135385601 8791777122108641351539201)
              ·
                refine ⟨6593832841581481013654401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791777122108641351539201 6593832841581481013654401)
                ·
                  refine ⟨4945374631186110760240801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6593832841581481013654401 4945374631186110760240801)
                  ·
                    refine ⟨3709030973389583070180601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945374631186110760240801 3709030973389583070180601)
                    ·
                      refine ⟨2781773230042187302635451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709030973389583070180601 2781773230042187302635451)
                      ·
                        rfl

theorem cell23_5417484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_5417484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417484 prefixEnd_5417484 := by exact prefixLift 5417484
  have htrace : WordTrace (prefixWord ++ tailWord_5417484) baseStart_5417484 baseEnd_5417484 := by
    simpa [prefixWord, tailWord_5417484, baseEnd_5417484] using wordTrace_append hprefix tailTrace_5417484
  have hstable : (prefixWord ++ tailWord_5417484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417484).length < 2 ^ (prefixWord ++ tailWord_5417484).sum := by decide
  have hdescent : baseEnd_5417484 < baseStart_5417484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417500 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5417500 : Nat := 118140960795 + 5417500 * 2 ^ 59
def prefixEnd_5417500 : Nat := 4983230072969 + 3 ^ 40 * 5417500 * 2
def baseEnd_5417500 : Nat := 2781781445732659240035377

theorem tailTrace_5417500 : CollatzResearch.WordTrace tailWord_5417500 prefixEnd_5417500 2781781445732659240035377 := by
  unfold tailWord_5417500
  simp only [CollatzResearch.WordTrace]
  refine ⟨98796228936665105091680977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131728305248886806788907969 98796228936665105091680977)
  ·
    refine ⟨74097171702498828818760733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98796228936665105091680977 74097171702498828818760733)
    ·
      refine ⟨27786439388437060807035275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74097171702498828818760733 27786439388437060807035275)
      ·
        refine ⟨41679659082655591210552913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27786439388437060807035275 41679659082655591210552913)
        ·
          refine ⟨31259744311991693407914685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41679659082655591210552913 31259744311991693407914685)
          ·
            refine ⟨11722404116996885027968007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31259744311991693407914685 11722404116996885027968007)
            ·
              refine ⟨17583606175495327541952011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11722404116996885027968007 17583606175495327541952011)
              ·
                refine ⟨26375409263242991312928017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17583606175495327541952011 26375409263242991312928017)
                ·
                  refine ⟨19781556947432243484696013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26375409263242991312928017 19781556947432243484696013)
                  ·
                    refine ⟨7418083855287091306761005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19781556947432243484696013 7418083855287091306761005)
                    ·
                      refine ⟨2781781445732659240035377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418083855287091306761005 2781781445732659240035377)
                      ·
                        rfl

theorem cell23_5417500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5417500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417500 prefixEnd_5417500 := by exact prefixLift 5417500
  have htrace : WordTrace (prefixWord ++ tailWord_5417500) baseStart_5417500 baseEnd_5417500 := by
    simpa [prefixWord, tailWord_5417500, baseEnd_5417500] using wordTrace_append hprefix tailTrace_5417500
  have hstable : (prefixWord ++ tailWord_5417500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417500).length < 2 ^ (prefixWord ++ tailWord_5417500).sum := by decide
  have hdescent : baseEnd_5417500 < baseStart_5417500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417523 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_5417523 : Nat := 118140960795 + 5417523 * 2 ^ 59
def prefixEnd_5417523 : Nat := 4983230072969 + 3 ^ 40 * 5417523 * 2
def baseEnd_5417523 : Nat := 2781793255787712650047771

theorem tailTrace_5417523 : CollatzResearch.WordTrace tailWord_5417523 prefixEnd_5417523 2781793255787712650047771 := by
  unfold tailWord_5417523
  simp only [CollatzResearch.WordTrace]
  refine ⟨197593296752246885111449223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131728864501497923407632815 197593296752246885111449223)
  ·
    refine ⟨296389945128370327667173835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197593296752246885111449223 296389945128370327667173835)
    ·
      refine ⟨444584917692555491500760753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296389945128370327667173835 444584917692555491500760753)
      ·
        refine ⟨333438688269416618625570565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444584917692555491500760753 333438688269416618625570565)
        ·
          refine ⟨62519754050515615992294481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333438688269416618625570565 62519754050515615992294481)
          ·
            refine ⟨46889815537886711994220861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62519754050515615992294481 46889815537886711994220861)
            ·
              refine ⟨17583680826707516997832823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46889815537886711994220861 17583680826707516997832823)
              ·
                refine ⟨26375521240061275496749235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17583680826707516997832823 26375521240061275496749235)
                ·
                  refine ⟨39563281860091913245123853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26375521240061275496749235 39563281860091913245123853)
                  ·
                    refine ⟨14836230697534467466921445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39563281860091913245123853 14836230697534467466921445)
                    ·
                      refine ⟨2781793255787712650047771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14836230697534467466921445 2781793255787712650047771)
                      ·
                        rfl

theorem cell23_5417523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_5417523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417523 prefixEnd_5417523 := by exact prefixLift 5417523
  have htrace : WordTrace (prefixWord ++ tailWord_5417523) baseStart_5417523 baseEnd_5417523 := by
    simpa [prefixWord, tailWord_5417523, baseEnd_5417523] using wordTrace_append hprefix tailTrace_5417523
  have hstable : (prefixWord ++ tailWord_5417523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417523).length < 2 ^ (prefixWord ++ tailWord_5417523).sum := by decide
  have hdescent : baseEnd_5417523 < baseStart_5417523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417550 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_5417550 : Nat := 118140960795 + 5417550 * 2 ^ 59
def prefixEnd_5417550 : Nat := 4983230072969 + 3 ^ 40 * 5417550 * 2
def baseEnd_5417550 : Nat := 927269039921794681470049

theorem tailTrace_5417550 : CollatzResearch.WordTrace tailWord_5417550 prefixEnd_5417550 927269039921794681470049 := by
  unfold tailWord_5417550
  simp only [CollatzResearch.WordTrace]
  refine ⟨24699285190393633590335263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131729521015432712481788069 24699285190393633590335263)
  ·
    refine ⟨37048927785590450385502895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24699285190393633590335263 37048927785590450385502895)
    ·
      refine ⟨55573391678385675578254343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37048927785590450385502895 55573391678385675578254343)
      ·
        refine ⟨83360087517578513367381515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55573391678385675578254343 83360087517578513367381515)
        ·
          refine ⟨125040131276367770051072273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83360087517578513367381515 125040131276367770051072273)
          ·
            refine ⟨93780098457275827538304205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125040131276367770051072273 93780098457275827538304205)
            ·
              refine ⟨35167536921478435326864077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93780098457275827538304205 35167536921478435326864077)
              ·
                refine ⟨13187826345554413247574029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35167536921478435326864077 13187826345554413247574029)
                ·
                  refine ⟨4945434879582904967840261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13187826345554413247574029 4945434879582904967840261)
                  ·
                    refine ⟨927269039921794681470049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945434879582904967840261 927269039921794681470049)
                    ·
                      rfl

theorem cell23_5417550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_5417550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417550 prefixEnd_5417550 := by exact prefixLift 5417550
  have htrace : WordTrace (prefixWord ++ tailWord_5417550) baseStart_5417550 baseEnd_5417550 := by
    simpa [prefixWord, tailWord_5417550, baseEnd_5417550] using wordTrace_append hprefix tailTrace_5417550
  have hstable : (prefixWord ++ tailWord_5417550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417550).length < 2 ^ (prefixWord ++ tailWord_5417550).sum := by decide
  have hdescent : baseEnd_5417550 < baseStart_5417550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417660 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5417660 : Nat := 118140960795 + 5417660 * 2 ^ 59
def prefixEnd_5417660 : Nat := 4983230072969 + 3 ^ 40 * 5417660 * 2
def baseEnd_5417660 : Nat := 2781863602637378614034641

theorem tailTrace_5417660 : CollatzResearch.WordTrace tailWord_5417660 prefixEnd_5417660 2781863602637378614034641 := by
  unfold tailWord_5417660
  simp only [CollatzResearch.WordTrace]
  refine ⟨98799146776375278754593217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131732195701833705006124289 98799146776375278754593217)
  ·
    refine ⟨74099360082281459065944913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98799146776375278754593217 74099360082281459065944913)
    ·
      refine ⟨55574520061711094299458685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74099360082281459065944913 55574520061711094299458685)
      ·
        refine ⟨20840445023141660362297007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55574520061711094299458685 20840445023141660362297007)
        ·
          refine ⟨31260667534712490543445511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20840445023141660362297007 31260667534712490543445511)
          ·
            refine ⟨46891001302068735815168267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31260667534712490543445511 46891001302068735815168267)
            ·
              refine ⟨70336501953103103722752401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46891001302068735815168267 70336501953103103722752401)
              ·
                refine ⟨52752376464827327792064301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70336501953103103722752401 52752376464827327792064301)
                ·
                  refine ⟨19782141174310247922024113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52752376464827327792064301 19782141174310247922024113)
                  ·
                    refine ⟨14836605880732685941518085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19782141174310247922024113 14836605880732685941518085)
                    ·
                      refine ⟨2781863602637378614034641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14836605880732685941518085 2781863602637378614034641)
                      ·
                        rfl

theorem cell23_5417660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5417660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417660 prefixEnd_5417660 := by exact prefixLift 5417660
  have htrace : WordTrace (prefixWord ++ tailWord_5417660) baseStart_5417660 baseEnd_5417660 := by
    simpa [prefixWord, tailWord_5417660, baseEnd_5417660] using wordTrace_append hprefix tailTrace_5417660
  have hstable : (prefixWord ++ tailWord_5417660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417660).length < 2 ^ (prefixWord ++ tailWord_5417660).sum := by decide
  have hdescent : baseEnd_5417660 < baseStart_5417660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417697 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_5417697 : Nat := 118140960795 + 5417697 * 2 ^ 59
def prefixEnd_5417697 : Nat := 4983230072969 + 3 ^ 40 * 5417697 * 2
def baseEnd_5417697 : Nat := 2781882601421594969271971

theorem tailTrace_5417697 : CollatzResearch.WordTrace tailWord_5417697 prefixEnd_5417697 2781882601421594969271971 := by
  unfold tailWord_5417697
  simp only [CollatzResearch.WordTrace]
  refine ⟨197599643053616512828283345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131733095369077675218855563 197599643053616512828283345)
  ·
    refine ⟨148199732290212384621212509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197599643053616512828283345 148199732290212384621212509)
    ·
      refine ⟨55574899608829644232954691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148199732290212384621212509 55574899608829644232954691)
      ·
        refine ⟨83362349413244466349432037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55574899608829644232954691 83362349413244466349432037)
        ·
          refine ⟨15630440514983337440518507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83362349413244466349432037 15630440514983337440518507)
          ·
            refine ⟨23445660772475006160777761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630440514983337440518507 23445660772475006160777761)
            ·
              refine ⟨17584245579356254620583321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23445660772475006160777761 17584245579356254620583321)
              ·
                refine ⟨13188184184517190965437491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17584245579356254620583321 13188184184517190965437491)
                ·
                  refine ⟨19782276276775786448156237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13188184184517190965437491 19782276276775786448156237)
                  ·
                    refine ⟨7418353603790919918058589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19782276276775786448156237 7418353603790919918058589)
                    ·
                      refine ⟨2781882601421594969271971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418353603790919918058589 2781882601421594969271971)
                      ·
                        rfl

theorem cell23_5417697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_5417697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417697 prefixEnd_5417697 := by exact prefixLift 5417697
  have htrace : WordTrace (prefixWord ++ tailWord_5417697) baseStart_5417697 baseEnd_5417697 := by
    simpa [prefixWord, tailWord_5417697, baseEnd_5417697] using wordTrace_append hprefix tailTrace_5417697
  have hstable : (prefixWord ++ tailWord_5417697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417697).length < 2 ^ (prefixWord ++ tailWord_5417697).sum := by decide
  have hdescent : baseEnd_5417697 < baseStart_5417697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417701 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5417701 : Nat := 118140960795 + 5417701 * 2 ^ 59
def prefixEnd_5417701 : Nat := 4983230072969 + 3 ^ 40 * 5417701 * 2
def baseEnd_5417701 : Nat := 2781884655344212953621953

theorem tailTrace_5417701 : CollatzResearch.WordTrace tailWord_5417701 prefixEnd_5417701 2781884655344212953621953 := by
  unfold tailWord_5417701
  simp only [CollatzResearch.WordTrace]
  refine ⟨197599788945602021511428957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131733192630401347674285971 197599788945602021511428957)
  ·
    refine ⟨74099920854600758066785859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197599788945602021511428957 74099920854600758066785859)
    ·
      refine ⟨111149881281901137100178789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74099920854600758066785859 111149881281901137100178789)
      ·
        refine ⟨20840602740356463206283523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111149881281901137100178789 20840602740356463206283523)
        ·
          refine ⟨31260904110534694809425285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20840602740356463206283523 31260904110534694809425285)
          ·
            refine ⟨5861419520725255276767241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31260904110534694809425285 5861419520725255276767241)
            ·
              refine ⟨4396064640543941457575431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861419520725255276767241 4396064640543941457575431)
              ·
                refine ⟨6594096960815912186363147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396064640543941457575431 6594096960815912186363147)
                ·
                  refine ⟨9891145441223868279544721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594096960815912186363147 9891145441223868279544721)
                  ·
                    refine ⟨7418359080917901209658541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9891145441223868279544721 7418359080917901209658541)
                    ·
                      refine ⟨2781884655344212953621953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418359080917901209658541 2781884655344212953621953)
                      ·
                        rfl

theorem cell23_5417701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5417701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417701 prefixEnd_5417701 := by exact prefixLift 5417701
  have htrace : WordTrace (prefixWord ++ tailWord_5417701) baseStart_5417701 baseEnd_5417701 := by
    simpa [prefixWord, tailWord_5417701, baseEnd_5417701] using wordTrace_append hprefix tailTrace_5417701
  have hstable : (prefixWord ++ tailWord_5417701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417701).length < 2 ^ (prefixWord ++ tailWord_5417701).sum := by decide
  have hdescent : baseEnd_5417701 < baseStart_5417701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417714 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5417714 : Nat := 118140960795 + 5417714 * 2 ^ 59
def prefixEnd_5417714 : Nat := 4983230072969 + 3 ^ 40 * 5417714 * 2
def baseEnd_5417714 : Nat := 2781891330592721402759393

theorem tailTrace_5417714 : CollatzResearch.WordTrace tailWord_5417714 prefixEnd_5417714 2781891330592721402759393 := by
  unfold tailWord_5417714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400065773638731182913049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131733508729703283154434797 49400065773638731182913049)
  ·
    refine ⟨37050049330229048387184787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49400065773638731182913049 37050049330229048387184787)
    ·
      refine ⟨55575073995343572580777181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37050049330229048387184787 55575073995343572580777181)
      ·
        refine ⟨20840652748253839717791443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55575073995343572580777181 20840652748253839717791443)
        ·
          refine ⟨31260979122380759576687165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20840652748253839717791443 31260979122380759576687165)
          ·
            refine ⟨11722867170892784841257687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31260979122380759576687165 11722867170892784841257687)
            ·
              refine ⟨17584300756339177261886531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11722867170892784841257687 17584300756339177261886531)
              ·
                refine ⟨26376451134508765892829797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17584300756339177261886531 26376451134508765892829797)
                ·
                  refine ⟨4945584587720393604905587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26376451134508765892829797 4945584587720393604905587)
                  ·
                    refine ⟨7418376881580590407358381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945584587720393604905587 7418376881580590407358381)
                    ·
                      refine ⟨2781891330592721402759393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418376881580590407358381 2781891330592721402759393)
                      ·
                        rfl

theorem cell23_5417714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5417714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417714 prefixEnd_5417714 := by exact prefixLift 5417714
  have htrace : WordTrace (prefixWord ++ tailWord_5417714) baseStart_5417714 baseEnd_5417714 := by
    simpa [prefixWord, tailWord_5417714, baseEnd_5417714] using wordTrace_append hprefix tailTrace_5417714
  have hstable : (prefixWord ++ tailWord_5417714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417714).length < 2 ^ (prefixWord ++ tailWord_5417714).sum := by decide
  have hdescent : baseEnd_5417714 < baseStart_5417714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417740 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5417740 : Nat := 118140960795 + 5417740 * 2 ^ 59
def prefixEnd_5417740 : Nat := 4983230072969 + 3 ^ 40 * 5417740 * 2
def baseEnd_5417740 : Nat := 2781904681089738301034273

theorem tailTrace_5417740 : CollatzResearch.WordTrace tailWord_5417740 prefixEnd_5417740 2781904681089738301034273 := by
  unfold tailWord_5417740
  simp only [CollatzResearch.WordTrace]
  refine ⟨98800605696230365586049337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131734140928307154114732449 98800605696230365586049337)
  ·
    refine ⟨74100454272172774189537003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98800605696230365586049337 74100454272172774189537003)
    ·
      refine ⟨111150681408259161284305505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74100454272172774189537003 111150681408259161284305505)
      ·
        refine ⟨83363011056194370963229129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111150681408259161284305505 83363011056194370963229129)
        ·
          refine ⟨62522258292145778222421847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83363011056194370963229129 62522258292145778222421847)
          ·
            refine ⟨93783387438218667333632771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62522258292145778222421847 93783387438218667333632771)
            ·
              refine ⟨140675081157328001000449157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93783387438218667333632771 140675081157328001000449157)
              ·
                refine ⟨26376577716999000187584217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140675081157328001000449157 26376577716999000187584217)
                ·
                  refine ⟨19782433287749250140688163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26376577716999000187584217 19782433287749250140688163)
                  ·
                    refine ⟨29673649931623875211032245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19782433287749250140688163 29673649931623875211032245)
                    ·
                      refine ⟨2781904681089738301034273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29673649931623875211032245 2781904681089738301034273)
                      ·
                        rfl

theorem cell23_5417740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5417740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417740 prefixEnd_5417740 := by exact prefixLift 5417740
  have htrace : WordTrace (prefixWord ++ tailWord_5417740) baseStart_5417740 baseEnd_5417740 := by
    simpa [prefixWord, tailWord_5417740, baseEnd_5417740] using wordTrace_append hprefix tailTrace_5417740
  have hstable : (prefixWord ++ tailWord_5417740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417740).length < 2 ^ (prefixWord ++ tailWord_5417740).sum := by decide
  have hdescent : baseEnd_5417740 < baseStart_5417740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417754 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_5417754 : Nat := 118140960795 + 5417754 * 2 ^ 59
def prefixEnd_5417754 : Nat := 4983230072969 + 3 ^ 40 * 5417754 * 2
def baseEnd_5417754 : Nat := 2781911869818901246259209

theorem tailTrace_5417754 : CollatzResearch.WordTrace tailWord_5417754 prefixEnd_5417754 2781911869818901246259209 := by
  unfold tailWord_5417754
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400430503602502890777079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131734481342940007708738877 49400430503602502890777079)
  ·
    refine ⟨74100645755403754336165619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49400430503602502890777079 74100645755403754336165619)
    ·
      refine ⟨111150968633105631504248429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74100645755403754336165619 111150968633105631504248429)
      ·
        refine ⟨41681613237414611814093161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111150968633105631504248429 41681613237414611814093161)
        ·
          refine ⟨31261209928060958860569871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41681613237414611814093161 31261209928060958860569871)
          ·
            refine ⟨46891814892091438290854807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31261209928060958860569871 46891814892091438290854807)
            ·
              refine ⟨70337722338137157436282211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46891814892091438290854807 70337722338137157436282211)
              ·
                refine ⟨105506583507205736154423317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70337722338137157436282211 105506583507205736154423317)
                ·
                  refine ⟨4945621101900268882238593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105506583507205736154423317 4945621101900268882238593)
                  ·
                    refine ⟨3709215826425201661678945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945621101900268882238593 3709215826425201661678945)
                    ·
                      refine ⟨2781911869818901246259209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709215826425201661678945 2781911869818901246259209)
                      ·
                        rfl

theorem cell23_5417754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_5417754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417754 prefixEnd_5417754 := by exact prefixLift 5417754
  have htrace : WordTrace (prefixWord ++ tailWord_5417754) baseStart_5417754 baseEnd_5417754 := by
    simpa [prefixWord, tailWord_5417754, baseEnd_5417754] using wordTrace_append hprefix tailTrace_5417754
  have hstable : (prefixWord ++ tailWord_5417754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417754).length < 2 ^ (prefixWord ++ tailWord_5417754).sum := by decide
  have hdescent : baseEnd_5417754 < baseStart_5417754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417782 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5417782 : Nat := 118140960795 + 5417782 * 2 ^ 59
def prefixEnd_5417782 : Nat := 4983230072969 + 3 ^ 40 * 5417782 * 2
def baseEnd_5417782 : Nat := 2781926247277227136709081

theorem tailTrace_5417782 : CollatzResearch.WordTrace tailWord_5417782 prefixEnd_5417782 2781926247277227136709081 := by
  unfold tailWord_5417782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350171453644285771570475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131735162172205714896751733 12350171453644285771570475)
  ·
    refine ⟨18525257180466428657355713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12350171453644285771570475 18525257180466428657355713)
    ·
      refine ⟨13893942885349821493016785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18525257180466428657355713 13893942885349821493016785)
      ·
        refine ⟨10420457164012366119762589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13893942885349821493016785 10420457164012366119762589)
        ·
          refine ⟨3907671436504637294910971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10420457164012366119762589 3907671436504637294910971)
          ·
            refine ⟨5861507154756955942366457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907671436504637294910971 5861507154756955942366457)
            ·
              refine ⟨4396130366067716956774843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861507154756955942366457 4396130366067716956774843)
              ·
                refine ⟨6594195549101575435162265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396130366067716956774843 6594195549101575435162265)
                ·
                  refine ⟨4945646661826181576371699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6594195549101575435162265 4945646661826181576371699)
                  ·
                    refine ⟨7418469992739272364557549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945646661826181576371699 7418469992739272364557549)
                    ·
                      refine ⟨2781926247277227136709081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418469992739272364557549 2781926247277227136709081)
                      ·
                        rfl

theorem cell23_5417782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5417782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417782 prefixEnd_5417782 := by exact prefixLift 5417782
  have htrace : WordTrace (prefixWord ++ tailWord_5417782) baseStart_5417782 baseEnd_5417782 := by
    simpa [prefixWord, tailWord_5417782, baseEnd_5417782] using wordTrace_append hprefix tailTrace_5417782
  have hstable : (prefixWord ++ tailWord_5417782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417782).length < 2 ^ (prefixWord ++ tailWord_5417782).sum := by decide
  have hdescent : baseEnd_5417782 < baseStart_5417782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417797 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_5417797 : Nat := 118140960795 + 5417797 * 2 ^ 59
def prefixEnd_5417797 : Nat := 4983230072969 + 3 ^ 40 * 5417797 * 2
def baseEnd_5417797 : Nat := 2781933949487044578021511

theorem tailTrace_5417797 : CollatzResearch.WordTrace tailWord_5417797 prefixEnd_5417797 2781933949487044578021511 := by
  unfold tailWord_5417797
  simp only [CollatzResearch.WordTrace]
  refine ⟨197603290353254229906923645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131735526902169486604615763 197603290353254229906923645)
  ·
    refine ⟨74101233882470336215096367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197603290353254229906923645 74101233882470336215096367)
    ·
      refine ⟨111151850823705504322644551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74101233882470336215096367 111151850823705504322644551)
      ·
        refine ⟨166727776235558256483966827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111151850823705504322644551 166727776235558256483966827)
        ·
          refine ⟨250091664353337384725950241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166727776235558256483966827 250091664353337384725950241)
          ·
            refine ⟨187568748265003038544462681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250091664353337384725950241 187568748265003038544462681)
            ·
              refine ⟨140676561198752278908347011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187568748265003038544462681 140676561198752278908347011)
              ·
                refine ⟨211014841798128418362520517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140676561198752278908347011 211014841798128418362520517)
                ·
                  refine ⟨39565282837149078442972597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211014841798128418362520517 39565282837149078442972597)
                  ·
                    refine ⟨3709245265982726104028681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39565282837149078442972597 3709245265982726104028681)
                    ·
                      refine ⟨2781933949487044578021511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709245265982726104028681 2781933949487044578021511)
                      ·
                        rfl

theorem cell23_5417797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_5417797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417797 prefixEnd_5417797 := by exact prefixLift 5417797
  have htrace : WordTrace (prefixWord ++ tailWord_5417797) baseStart_5417797 baseEnd_5417797 := by
    simpa [prefixWord, tailWord_5417797, baseEnd_5417797] using wordTrace_append hprefix tailTrace_5417797
  have hstable : (prefixWord ++ tailWord_5417797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417797).length < 2 ^ (prefixWord ++ tailWord_5417797).sum := by decide
  have hdescent : baseEnd_5417797 < baseStart_5417797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417800 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_5417800 : Nat := 118140960795 + 5417800 * 2 ^ 59
def prefixEnd_5417800 : Nat := 4983230072969 + 3 ^ 40 * 5417800 * 2
def baseEnd_5417800 : Nat := 2781935489929008066283997

theorem tailTrace_5417800 : CollatzResearch.WordTrace tailWord_5417800 prefixEnd_5417800 2781935489929008066283997 := by
  unfold tailWord_5417800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98801699886121680709641427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131735599848162240946188569 98801699886121680709641427)
  ·
    refine ⟨148202549829182521064462141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98801699886121680709641427 148202549829182521064462141)
    ·
      refine ⟨55575956185943445399173303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148202549829182521064462141 55575956185943445399173303)
      ·
        refine ⟨83363934278915168098759955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55575956185943445399173303 83363934278915168098759955)
        ·
          refine ⟨125045901418372752148139933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83363934278915168098759955 125045901418372752148139933)
          ·
            refine ⟨46892213031889782055552475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125045901418372752148139933 46892213031889782055552475)
            ·
              refine ⟨70338319547834673083328713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46892213031889782055552475 70338319547834673083328713)
              ·
                refine ⟨52753739660876004812496535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70338319547834673083328713 52753739660876004812496535)
                ·
                  refine ⟨79130609491314007218744803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52753739660876004812496535 79130609491314007218744803)
                  ·
                    refine ⟨118695914236971010828117205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79130609491314007218744803 118695914236971010828117205)
                    ·
                      refine ⟨2781935489929008066283997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118695914236971010828117205 2781935489929008066283997)
                      ·
                        rfl

theorem cell23_5417800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_5417800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417800 prefixEnd_5417800 := by exact prefixLift 5417800
  have htrace : WordTrace (prefixWord ++ tailWord_5417800) baseStart_5417800 baseEnd_5417800 := by
    simpa [prefixWord, tailWord_5417800, baseEnd_5417800] using wordTrace_append hprefix tailTrace_5417800
  have hstable : (prefixWord ++ tailWord_5417800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417800).length < 2 ^ (prefixWord ++ tailWord_5417800).sum := by decide
  have hdescent : baseEnd_5417800 < baseStart_5417800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417847 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_5417847 : Nat := 118140960795 + 5417847 * 2 ^ 59
def prefixEnd_5417847 : Nat := 4983230072969 + 3 ^ 40 * 5417847 * 2
def baseEnd_5417847 : Nat := 2781959623519769382396281

theorem tailTrace_5417847 : CollatzResearch.WordTrace tailWord_5417847 prefixEnd_5417847 2781959623519769382396281 := by
  unfold tailWord_5417847
  simp only [CollatzResearch.WordTrace]
  refine ⟨197605114003073088446243795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131736742668715392297495863 197605114003073088446243795)
  ·
    refine ⟨296407671004609632669365693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197605114003073088446243795 296407671004609632669365693)
    ·
      refine ⟨111152876626728612251012135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296407671004609632669365693 111152876626728612251012135)
      ·
        refine ⟨166729314940092918376518203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111152876626728612251012135 166729314940092918376518203)
        ·
          refine ⟨250093972410139377564777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166729314940092918376518203 250093972410139377564777305)
          ·
            refine ⟨187570479307604533173582979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250093972410139377564777305 187570479307604533173582979)
            ·
              refine ⟨281355718961406799760374469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187570479307604533173582979 281355718961406799760374469)
              ·
                refine ⟨52754197305263774955070213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281355718961406799760374469 52754197305263774955070213)
                ·
                  refine ⟨9891411994736957804075665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52754197305263774955070213 9891411994736957804075665)
                  ·
                    refine ⟨7418558996052718353056749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9891411994736957804075665 7418558996052718353056749)
                    ·
                      refine ⟨2781959623519769382396281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418558996052718353056749 2781959623519769382396281)
                      ·
                        rfl

theorem cell23_5417847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_5417847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417847 prefixEnd_5417847 := by exact prefixLift 5417847
  have htrace : WordTrace (prefixWord ++ tailWord_5417847) baseStart_5417847 baseEnd_5417847 := by
    simpa [prefixWord, tailWord_5417847, baseEnd_5417847] using wordTrace_append hprefix tailTrace_5417847
  have hstable : (prefixWord ++ tailWord_5417847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417847).length < 2 ^ (prefixWord ++ tailWord_5417847).sum := by decide
  have hdescent : baseEnd_5417847 < baseStart_5417847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417850 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_5417850 : Nat := 118140960795 + 5417850 * 2 ^ 59
def prefixEnd_5417850 : Nat := 4983230072969 + 3 ^ 40 * 5417850 * 2
def baseEnd_5417850 : Nat := 309106795995748096739863

theorem tailTrace_5417850 : CollatzResearch.WordTrace tailWord_5417850 prefixEnd_5417850 309106795995748096739863 := by
  unfold tailWord_5417850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49401305855515554989650751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131736815614708146639068669 49401305855515554989650751)
  ·
    refine ⟨74101958783273332484476127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49401305855515554989650751 74101958783273332484476127)
    ·
      refine ⟨111152938174909998726714191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74101958783273332484476127 111152938174909998726714191)
      ·
        refine ⟨166729407262364998090071287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111152938174909998726714191 166729407262364998090071287)
        ·
          refine ⟨250094110893547497135106931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166729407262364998090071287 250094110893547497135106931)
          ·
            refine ⟨375141166340321245702660397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250094110893547497135106931 375141166340321245702660397)
            ·
              refine ⟨140677937377620467138497649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375141166340321245702660397 140677937377620467138497649)
              ·
                refine ⟨105508453033215350353873237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140677937377620467138497649 105508453033215350353873237)
                ·
                  refine ⟨309106795995748096739863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105508453033215350353873237 309106795995748096739863)
                  ·
                    rfl

theorem cell23_5417850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_5417850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417850 prefixEnd_5417850 := by exact prefixLift 5417850
  have htrace : WordTrace (prefixWord ++ tailWord_5417850) baseStart_5417850 baseEnd_5417850 := by
    simpa [prefixWord, tailWord_5417850, baseEnd_5417850] using wordTrace_append hprefix tailTrace_5417850
  have hstable : (prefixWord ++ tailWord_5417850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417850).length < 2 ^ (prefixWord ++ tailWord_5417850).sum := by decide
  have hdescent : baseEnd_5417850 < baseStart_5417850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417864 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5417864 : Nat := 118140960795 + 5417864 * 2 ^ 59
def prefixEnd_5417864 : Nat := 4983230072969 + 3 ^ 40 * 5417864 * 2
def baseEnd_5417864 : Nat := 2781968352690895815883703

theorem tailTrace_5417864 : CollatzResearch.WordTrace tailWord_5417864 prefixEnd_5417864 2781968352690895815883703 := by
  unfold tailWord_5417864
  simp only [CollatzResearch.WordTrace]
  refine ⟨98802867022005750174806323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131737156029341000233075097 98802867022005750174806323)
  ·
    refine ⟨148204300533008625262209485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98802867022005750174806323 148204300533008625262209485)
    ·
      refine ⟨55576612699878234473328557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148204300533008625262209485 55576612699878234473328557)
      ·
        refine ⟨20841229762454337927498209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55576612699878234473328557 20841229762454337927498209)
        ·
          refine ⟨15630922321840753445623657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20841229762454337927498209 15630922321840753445623657)
          ·
            refine ⟨11723191741380565084217743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15630922321840753445623657 11723191741380565084217743)
            ·
              refine ⟨17584787612070847626326615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723191741380565084217743 17584787612070847626326615)
              ·
                refine ⟨26377181418106271439489923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17584787612070847626326615 26377181418106271439489923)
                ·
                  refine ⟨39565772127159407159234885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26377181418106271439489923 39565772127159407159234885)
                  ·
                    refine ⟨7418582273842388842356541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39565772127159407159234885 7418582273842388842356541)
                    ·
                      refine ⟨2781968352690895815883703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418582273842388842356541 2781968352690895815883703)
                      ·
                        rfl

theorem cell23_5417864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5417864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417864 prefixEnd_5417864 := by exact prefixLift 5417864
  have htrace : WordTrace (prefixWord ++ tailWord_5417864) baseStart_5417864 baseEnd_5417864 := by
    simpa [prefixWord, tailWord_5417864, baseEnd_5417864] using wordTrace_append hprefix tailTrace_5417864
  have hstable : (prefixWord ++ tailWord_5417864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417864).length < 2 ^ (prefixWord ++ tailWord_5417864).sum := by decide
  have hdescent : baseEnd_5417864 < baseStart_5417864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417884 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 8]
def baseStart_5417884 : Nat := 118140960795 + 5417884 * 2 ^ 59
def prefixEnd_5417884 : Nat := 4983230072969 + 3 ^ 40 * 5417884 * 2
def baseEnd_5417884 : Nat := 309108735811553970848179

theorem tailTrace_5417884 : CollatzResearch.WordTrace tailWord_5417884 prefixEnd_5417884 309108735811553970848179 := by
  unfold tailWord_5417884
  simp only [CollatzResearch.WordTrace]
  refine ⟨98803231751969521882670353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131737642335959362510227137 98803231751969521882670353)
  ·
    refine ⟨74102423813977141412002765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98803231751969521882670353 74102423813977141412002765)
    ·
      refine ⟨27788408930241428029501037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74102423813977141412002765 27788408930241428029501037)
      ·
        refine ⟨10420653348840535511062889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27788408930241428029501037 10420653348840535511062889)
        ·
          refine ⟨7815490011630401633297167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10420653348840535511062889 7815490011630401633297167)
          ·
            refine ⟨11723235017445602449945751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815490011630401633297167 11723235017445602449945751)
            ·
              refine ⟨17584852526168403674918627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723235017445602449945751 17584852526168403674918627)
              ·
                refine ⟨26377278789252605512377941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17584852526168403674918627 26377278789252605512377941)
                ·
                  refine ⟨309108735811553970848179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26377278789252605512377941 309108735811553970848179)
                  ·
                    rfl

theorem cell23_5417884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_5417884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417884 prefixEnd_5417884 := by exact prefixLift 5417884
  have htrace : WordTrace (prefixWord ++ tailWord_5417884) baseStart_5417884 baseEnd_5417884 := by
    simpa [prefixWord, tailWord_5417884, baseEnd_5417884] using wordTrace_append hprefix tailTrace_5417884
  have hstable : (prefixWord ++ tailWord_5417884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417884).length < 2 ^ (prefixWord ++ tailWord_5417884).sum := by decide
  have hdescent : baseEnd_5417884 < baseStart_5417884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417887 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5417887 : Nat := 118140960795 + 5417887 * 2 ^ 59
def prefixEnd_5417887 : Nat := 4983230072969 + 3 ^ 40 * 5417887 * 2
def baseEnd_5417887 : Nat := 2781980162745949225896097

theorem tailTrace_5417887 : CollatzResearch.WordTrace tailWord_5417887 prefixEnd_5417887 2781980162745949225896097 := by
  unfold tailWord_5417887
  simp only [CollatzResearch.WordTrace]
  refine ⟨197606572922928175277699915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131737715281952116851799943 197606572922928175277699915)
  ·
    refine ⟨296409859384392262916549873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197606572922928175277699915 296409859384392262916549873)
    ·
      refine ⟨222307394538294197187412405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296409859384392262916549873 222307394538294197187412405)
      ·
        refine ⟨20841318237965080986319913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222307394538294197187412405 20841318237965080986319913)
        ·
          refine ⟨15630988678473810739739935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20841318237965080986319913 15630988678473810739739935)
          ·
            refine ⟨23446483017710716109609903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630988678473810739739935 23446483017710716109609903)
            ·
              refine ⟨35169724526566074164414855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23446483017710716109609903 35169724526566074164414855)
              ·
                refine ⟨52754586789849111246622283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35169724526566074164414855 52754586789849111246622283)
                ·
                  refine ⟨79131880184773666869933425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52754586789849111246622283 79131880184773666869933425)
                  ·
                    refine ⟨59348910138580250152450069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79131880184773666869933425 59348910138580250152450069)
                    ·
                      refine ⟨2781980162745949225896097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59348910138580250152450069 2781980162745949225896097)
                      ·
                        rfl

theorem cell23_5417887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5417887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417887 prefixEnd_5417887 := by exact prefixLift 5417887
  have htrace : WordTrace (prefixWord ++ tailWord_5417887) baseStart_5417887 baseEnd_5417887 := by
    simpa [prefixWord, tailWord_5417887, baseEnd_5417887] using wordTrace_append hprefix tailTrace_5417887
  have hstable : (prefixWord ++ tailWord_5417887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417887).length < 2 ^ (prefixWord ++ tailWord_5417887).sum := by decide
  have hdescent : baseEnd_5417887 < baseStart_5417887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417914 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_5417914 : Nat := 118140960795 + 5417914 * 2 ^ 59
def prefixEnd_5417914 : Nat := 4983230072969 + 3 ^ 40 * 5417914 * 2
def baseEnd_5417914 : Nat := 927331342241206873419491

theorem tailTrace_5417914 : CollatzResearch.WordTrace tailWord_5417914 prefixEnd_5417914 927331342241206873419491 := by
  unfold tailWord_5417914
  simp only [CollatzResearch.WordTrace]
  refine ⟨49401889423457589722233199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131738371795886905925955197 49401889423457589722233199)
  ·
    refine ⟨74102834135186384583349799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49401889423457589722233199 74102834135186384583349799)
    ·
      refine ⟨111154251202779576875024699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74102834135186384583349799 111154251202779576875024699)
      ·
        refine ⟨166731376804169365312537049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111154251202779576875024699 166731376804169365312537049)
        ·
          refine ⟨125048532603127023984402787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166731376804169365312537049 125048532603127023984402787)
          ·
            refine ⟨187572798904690535976604181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125048532603127023984402787 187572798904690535976604181)
            ·
              refine ⟨8792474948657368873903321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187572798904690535976604181 8792474948657368873903321)
              ·
                refine ⟨6594356211493026655427491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792474948657368873903321 6594356211493026655427491)
                ·
                  refine ⟨9891534317239539983141237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594356211493026655427491 9891534317239539983141237)
                  ·
                    refine ⟨927331342241206873419491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9891534317239539983141237 927331342241206873419491)
                    ·
                      rfl

theorem cell23_5417914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_5417914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417914 prefixEnd_5417914 := by exact prefixLift 5417914
  have htrace : WordTrace (prefixWord ++ tailWord_5417914) baseStart_5417914 baseEnd_5417914 := by
    simpa [prefixWord, tailWord_5417914, baseEnd_5417914] using wordTrace_append hprefix tailTrace_5417914
  have hstable : (prefixWord ++ tailWord_5417914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417914).length < 2 ^ (prefixWord ++ tailWord_5417914).sum := by decide
  have hdescent : baseEnd_5417914 < baseStart_5417914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417927 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 6]
def baseStart_5417927 : Nat := 118140960795 + 5417927 * 2 ^ 59
def prefixEnd_5417927 : Nat := 4983230072969 + 3 ^ 40 * 5417927 * 2
def baseEnd_5417927 : Nat := 927333567324043023131971

theorem tailTrace_5417927 : CollatzResearch.WordTrace tailWord_5417927 prefixEnd_5417927 927333567324043023131971 := by
  unfold tailWord_5417927
  simp only [CollatzResearch.WordTrace]
  refine ⟨197608031842783262109156035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131738687895188841406104023 197608031842783262109156035)
  ·
    refine ⟨296412047764174893163734053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197608031842783262109156035 296412047764174893163734053)
    ·
      refine ⟨55577258955782792468200135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296412047764174893163734053 55577258955782792468200135)
      ·
        refine ⟨83365888433674188702300203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55577258955782792468200135 83365888433674188702300203)
        ·
          refine ⟨125048832650511283053450305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83365888433674188702300203 125048832650511283053450305)
          ·
            refine ⟨93786624487883462290087729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125048832650511283053450305 93786624487883462290087729)
            ·
              refine ⟨70339968365912596717565797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93786624487883462290087729 70339968365912596717565797)
              ·
                refine ⟨13188744068608611884543587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70339968365912596717565797 13188744068608611884543587)
                ·
                  refine ⟨19783116102912917826815381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13188744068608611884543587 19783116102912917826815381)
                  ·
                    refine ⟨927333567324043023131971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19783116102912917826815381 927333567324043023131971)
                    ·
                      rfl

theorem cell23_5417927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_5417927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417927 prefixEnd_5417927 := by exact prefixLift 5417927
  have htrace : WordTrace (prefixWord ++ tailWord_5417927) baseStart_5417927 baseEnd_5417927 := by
    simpa [prefixWord, tailWord_5417927, baseEnd_5417927] using wordTrace_append hprefix tailTrace_5417927
  have hstable : (prefixWord ++ tailWord_5417927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417927).length < 2 ^ (prefixWord ++ tailWord_5417927).sum := by decide
  have hdescent : baseEnd_5417927 < baseStart_5417927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417938 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5417938 : Nat := 118140960795 + 5417938 * 2 ^ 59
def prefixEnd_5417938 : Nat := 4983230072969 + 3 ^ 40 * 5417938 * 2
def baseEnd_5417938 : Nat := 2782006350259328526358363

theorem tailTrace_5417938 : CollatzResearch.WordTrace tailWord_5417938 prefixEnd_5417938 2782006350259328526358363 := by
  unfold tailWord_5417938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49402108261435852746951617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131738955363828940658537645 49402108261435852746951617)
  ·
    refine ⟨37051581196076889560213713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49402108261435852746951617 37051581196076889560213713)
    ·
      refine ⟨27788685897057667170160285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37051581196076889560213713 27788685897057667170160285)
      ·
        refine ⟨10420757211396625188810107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27788685897057667170160285 10420757211396625188810107)
        ·
          refine ⟨15631135817094937783215161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10420757211396625188810107 15631135817094937783215161)
          ·
            refine ⟨11723351862821203337411371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15631135817094937783215161 11723351862821203337411371)
            ·
              refine ⟨17585027794231805006117057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723351862821203337411371 17585027794231805006117057)
              ·
                refine ⟨13188770845673853754587793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17585027794231805006117057 13188770845673853754587793)
                ·
                  refine ⟨9891578134255390315940845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13188770845673853754587793 9891578134255390315940845)
                  ·
                    refine ⟨3709341800345771368477817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9891578134255390315940845 3709341800345771368477817)
                    ·
                      refine ⟨2782006350259328526358363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709341800345771368477817 2782006350259328526358363)
                      ·
                        rfl

theorem cell23_5417938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5417938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417938 prefixEnd_5417938 := by exact prefixLift 5417938
  have htrace : WordTrace (prefixWord ++ tailWord_5417938) baseStart_5417938 baseEnd_5417938 := by
    simpa [prefixWord, tailWord_5417938, baseEnd_5417938] using wordTrace_append hprefix tailTrace_5417938
  have hstable : (prefixWord ++ tailWord_5417938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417938).length < 2 ^ (prefixWord ++ tailWord_5417938).sum := by decide
  have hdescent : baseEnd_5417938 < baseStart_5417938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417944 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_5417944 : Nat := 118140960795 + 5417944 * 2 ^ 59
def prefixEnd_5417944 : Nat := 4983230072969 + 3 ^ 40 * 5417944 * 2
def baseEnd_5417944 : Nat := 927336477047751834294445

theorem tailTrace_5417944 : CollatzResearch.WordTrace tailWord_5417944 prefixEnd_5417944 927336477047751834294445 := by
  unfold tailWord_5417944
  simp only [CollatzResearch.WordTrace]
  refine ⟨98804325941860837006262443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131739101255814449341683257 98804325941860837006262443)
  ·
    refine ⟨148206488912791255509393665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98804325941860837006262443 148206488912791255509393665)
    ·
      refine ⟨111154866684593441632045249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148206488912791255509393665 111154866684593441632045249)
      ·
        refine ⟨83366150013445081224033937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111154866684593441632045249 83366150013445081224033937)
        ·
          refine ⟨62524612510083810918025453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83366150013445081224033937 62524612510083810918025453)
          ·
            refine ⟨23446729691281429094259545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62524612510083810918025453 23446729691281429094259545)
            ·
              refine ⟨17585047268461071820694659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23446729691281429094259545 17585047268461071820694659)
              ·
                refine ⟨26377570902691607731041989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17585047268461071820694659 26377570902691607731041989)
                ·
                  refine ⟨4945794544254676449570373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26377570902691607731041989 4945794544254676449570373)
                  ·
                    refine ⟨927336477047751834294445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945794544254676449570373 927336477047751834294445)
                    ·
                      rfl

theorem cell23_5417944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_5417944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417944 prefixEnd_5417944 := by exact prefixLift 5417944
  have htrace : WordTrace (prefixWord ++ tailWord_5417944) baseStart_5417944 baseEnd_5417944 := by
    simpa [prefixWord, tailWord_5417944, baseEnd_5417944] using wordTrace_append hprefix tailTrace_5417944
  have hstable : (prefixWord ++ tailWord_5417944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417944).length < 2 ^ (prefixWord ++ tailWord_5417944).sum := by decide
  have hdescent : baseEnd_5417944 < baseStart_5417944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417945 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 1, 1, 3]
def baseStart_5417945 : Nat := 118140960795 + 5417945 * 2 ^ 59
def prefixEnd_5417945 : Nat := 4983230072969 + 3 ^ 40 * 5417945 * 2
def baseEnd_5417945 : Nat := 2782009944623909998970831

theorem tailTrace_5417945 : CollatzResearch.WordTrace tailWord_5417945 prefixEnd_5417945 2782009944623909998970831 := by
  unfold tailWord_5417945
  simp only [CollatzResearch.WordTrace]
  refine ⟨197608688356718051183311289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131739125571145367455540859 197608688356718051183311289)
  ·
    refine ⟨148206516267538538387483467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197608688356718051183311289 148206516267538538387483467)
    ·
      refine ⟨222309774401307807581225201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148206516267538538387483467 222309774401307807581225201)
      ·
        refine ⟨166732330800980855685918901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222309774401307807581225201 166732330800980855685918901)
        ·
          refine ⟨15631156012591955220554897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166732330800980855685918901 15631156012591955220554897)
          ·
            refine ⟨11723367009443966415416173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15631156012591955220554897 11723367009443966415416173)
            ·
              refine ⟨4396262628541487405781065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11723367009443966415416173 4396262628541487405781065)
              ·
                refine ⟨3297196971406115554335799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396262628541487405781065 3297196971406115554335799)
                ·
                  refine ⟨4945795457109173331503699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297196971406115554335799 4945795457109173331503699)
                  ·
                    refine ⟨7418693185663759997255549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945795457109173331503699 7418693185663759997255549)
                    ·
                      refine ⟨2782009944623909998970831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418693185663759997255549 2782009944623909998970831)
                      ·
                        rfl

theorem cell23_5417945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_5417945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417945 prefixEnd_5417945 := by exact prefixLift 5417945
  have htrace : WordTrace (prefixWord ++ tailWord_5417945) baseStart_5417945 baseEnd_5417945 := by
    simpa [prefixWord, tailWord_5417945, baseEnd_5417945] using wordTrace_append hprefix tailTrace_5417945
  have hstable : (prefixWord ++ tailWord_5417945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417945).length < 2 ^ (prefixWord ++ tailWord_5417945).sum := by decide
  have hdescent : baseEnd_5417945 < baseStart_5417945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5417974 : List Nat := [5, 1, 1, 1, 3, 1, 2, 9]
def baseStart_5417974 : Nat := 118140960795 + 5417974 * 2 ^ 59
def prefixEnd_5417974 : Nat := 4983230072969 + 3 ^ 40 * 5417974 * 2
def baseEnd_5417974 : Nat := 103037956872699643907711

theorem tailTrace_5417974 : CollatzResearch.WordTrace tailWord_5417974 prefixEnd_5417974 103037956872699643907711 := by
  unfold tailWord_5417974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350609129600811821007311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131739830715741992757411317 12350609129600811821007311)
  ·
    refine ⟨18525913694401217731510967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12350609129600811821007311 18525913694401217731510967)
    ·
      refine ⟨27788870541601826597266451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18525913694401217731510967 27788870541601826597266451)
      ·
        refine ⟨41683305812402739895899677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27788870541601826597266451 41683305812402739895899677)
        ·
          refine ⟨15631239679651027460962379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41683305812402739895899677 15631239679651027460962379)
          ·
            refine ⟨23446859519476541191443569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15631239679651027460962379 23446859519476541191443569)
            ·
              refine ⟨17585144639607405893582677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23446859519476541191443569 17585144639607405893582677)
              ·
                refine ⟨103037956872699643907711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17585144639607405893582677 103037956872699643907711)
                ·
                  rfl

theorem cell23_5417974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_5417974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5417974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5417974 prefixEnd_5417974 := by exact prefixLift 5417974
  have htrace : WordTrace (prefixWord ++ tailWord_5417974) baseStart_5417974 baseEnd_5417974 := by
    simpa [prefixWord, tailWord_5417974, baseEnd_5417974] using wordTrace_append hprefix tailTrace_5417974
  have hstable : (prefixWord ++ tailWord_5417974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5417974).length < 2 ^ (prefixWord ++ tailWord_5417974).sum := by decide
  have hdescent : baseEnd_5417974 < baseStart_5417974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5417974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418018 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_5418018 : Nat := 118140960795 + 5418018 * 2 ^ 59
def prefixEnd_5418018 : Nat := 4983230072969 + 3 ^ 40 * 5418018 * 2
def baseEnd_5418018 : Nat := 2782047428711688213357995

theorem tailTrace_5418018 : CollatzResearch.WordTrace tailWord_5418018 prefixEnd_5418018 2782047428711688213357995 := by
  unfold tailWord_5418018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49402837721363396162679677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131740900590302389767145805 49402837721363396162679677)
  ·
    refine ⟨18526064145511273561004879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49402837721363396162679677 18526064145511273561004879)
    ·
      refine ⟨27789096218266910341507319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18526064145511273561004879 27789096218266910341507319)
      ·
        refine ⟨41683644327400365512260979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27789096218266910341507319 41683644327400365512260979)
        ·
          refine ⟨62525466491100548268391469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41683644327400365512260979 62525466491100548268391469)
          ·
            refine ⟨23447049934162705600646801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62525466491100548268391469 23447049934162705600646801)
            ·
              refine ⟨17585287450622029200485101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23447049934162705600646801 17585287450622029200485101)
              ·
                refine ⟨6594482793983260950181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17585287450622029200485101 6594482793983260950181913)
                ·
                  refine ⟨4945862095487445712636435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6594482793983260950181913 4945862095487445712636435)
                  ·
                    refine ⟨7418793143231168568954653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945862095487445712636435 7418793143231168568954653)
                    ·
                      refine ⟨2782047428711688213357995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418793143231168568954653 2782047428711688213357995)
                      ·
                        rfl

theorem cell23_5418018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_5418018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418018 prefixEnd_5418018 := by exact prefixLift 5418018
  have htrace : WordTrace (prefixWord ++ tailWord_5418018) baseStart_5418018 baseEnd_5418018 := by
    simpa [prefixWord, tailWord_5418018, baseEnd_5418018] using wordTrace_append hprefix tailTrace_5418018
  have hstable : (prefixWord ++ tailWord_5418018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418018).length < 2 ^ (prefixWord ++ tailWord_5418018).sum := by decide
  have hdescent : baseEnd_5418018 < baseStart_5418018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418045 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5418045 : Nat := 118140960795 + 5418045 * 2 ^ 59
def prefixEnd_5418045 : Nat := 4983230072969 + 3 ^ 40 * 5418045 * 2
def baseEnd_5418045 : Nat := 2782061292689359607720371

theorem tailTrace_5418045 : CollatzResearch.WordTrace tailWord_5418045 prefixEnd_5418045 2782061292689359607720371 := by
  unfold tailWord_5418045
  simp only [CollatzResearch.WordTrace]
  refine ⟨197612335656355768261951589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131741557104237178841301059 197612335656355768261951589)
  ·
    refine ⟨37052312935566706549115923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197612335656355768261951589 37052312935566706549115923)
    ·
      refine ⟨55578469403350059823673885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37052312935566706549115923 55578469403350059823673885)
      ·
        refine ⟨20841926026256272433877707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55578469403350059823673885 20841926026256272433877707)
        ·
          refine ⟨31262889039384408650816561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20841926026256272433877707 31262889039384408650816561)
          ·
            refine ⟨23447166779538306488112421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31262889039384408650816561 23447166779538306488112421)
            ·
              refine ⟨4396343771163432466521079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23447166779538306488112421 4396343771163432466521079)
              ·
                refine ⟨6594515656745148699781619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396343771163432466521079 6594515656745148699781619)
                ·
                  refine ⟨9891773485117723049672429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594515656745148699781619 9891773485117723049672429)
                  ·
                    refine ⟨3709415056919146143627161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9891773485117723049672429 3709415056919146143627161)
                    ·
                      refine ⟨2782061292689359607720371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709415056919146143627161 2782061292689359607720371)
                      ·
                        rfl

theorem cell23_5418045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5418045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418045 prefixEnd_5418045 := by exact prefixLift 5418045
  have htrace : WordTrace (prefixWord ++ tailWord_5418045) baseStart_5418045 baseEnd_5418045 := by
    simpa [prefixWord, tailWord_5418045, baseEnd_5418045] using wordTrace_append hprefix tailTrace_5418045
  have hstable : (prefixWord ++ tailWord_5418045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418045).length < 2 ^ (prefixWord ++ tailWord_5418045).sum := by decide
  have hdescent : baseEnd_5418045 < baseStart_5418045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418047 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 11]
def baseStart_5418047 : Nat := 118140960795 + 5418047 * 2 ^ 59
def prefixEnd_5418047 : Nat := 4983230072969 + 3 ^ 40 * 5418047 * 2
def baseEnd_5418047 : Nat := 309118035516740955543929

theorem tailTrace_5418047 : CollatzResearch.WordTrace tailWord_5418047 prefixEnd_5418047 309118035516740955543929 := by
  unfold tailWord_5418047
  simp only [CollatzResearch.WordTrace]
  refine ⟨197612408602348522603524395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131741605734899015069016263 197612408602348522603524395)
  ·
    refine ⟨296418612903522783905286593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197612408602348522603524395 296418612903522783905286593)
    ·
      refine ⟨222313959677642087928964945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296418612903522783905286593 222313959677642087928964945)
      ·
        refine ⟨166735469758231565946723709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222313959677642087928964945 166735469758231565946723709)
        ·
          refine ⟨62525801159336837230021391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166735469758231565946723709 62525801159336837230021391)
          ·
            refine ⟨93788701739005255845032087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62525801159336837230021391 93788701739005255845032087)
            ·
              refine ⟨140683052608507883767548131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93788701739005255845032087 140683052608507883767548131)
              ·
                refine ⟨211024578912761825651322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140683052608507883767548131 211024578912761825651322197)
                ·
                  refine ⟨309118035516740955543929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 211024578912761825651322197 309118035516740955543929)
                  ·
                    rfl

theorem cell23_5418047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 11].length) (baseStart_5418047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418047 prefixEnd_5418047 := by exact prefixLift 5418047
  have htrace : WordTrace (prefixWord ++ tailWord_5418047) baseStart_5418047 baseEnd_5418047 := by
    simpa [prefixWord, tailWord_5418047, baseEnd_5418047] using wordTrace_append hprefix tailTrace_5418047
  have hstable : (prefixWord ++ tailWord_5418047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418047).length < 2 ^ (prefixWord ++ tailWord_5418047).sum := by decide
  have hdescent : baseEnd_5418047 < baseStart_5418047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_5418057 : Nat := 118140960795 + 5418057 * 2 ^ 59
def prefixEnd_5418057 : Nat := 4983230072969 + 3 ^ 40 * 5418057 * 2
def baseEnd_5418057 : Nat := 2782067454457213560770315

theorem tailTrace_5418057 : CollatzResearch.WordTrace tailWord_5418057 prefixEnd_5418057 2782067454457213560770315 := by
  unfold tailWord_5418057
  simp only [CollatzResearch.WordTrace]
  refine ⟨197612773332312294311388425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131741848888208196207592283 197612773332312294311388425)
  ·
    refine ⟨148209579999234220733541319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197612773332312294311388425 148209579999234220733541319)
    ·
      refine ⟨222314369998851331100311979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148209579999234220733541319 222314369998851331100311979)
      ·
        refine ⟨333471554998276996650467969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222314369998851331100311979 333471554998276996650467969)
        ·
          refine ⟨250103666248707747487850977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333471554998276996650467969 250103666248707747487850977)
          ·
            refine ⟨187577749686530810615888233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250103666248707747487850977 187577749686530810615888233)
            ·
              refine ⟨140683312264898107961916175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187577749686530810615888233 140683312264898107961916175)
              ·
                refine ⟨211024968397347161942874263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140683312264898107961916175 211024968397347161942874263)
                ·
                  refine ⟨316537452596020742914311395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211024968397347161942874263 316537452596020742914311395)
                  ·
                    refine ⟨474806178894031114371467093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 316537452596020742914311395 474806178894031114371467093)
                    ·
                      refine ⟨2782067454457213560770315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 474806178894031114371467093 2782067454457213560770315)
                      ·
                        rfl

theorem cell23_5418057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_5418057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418057 prefixEnd_5418057 := by exact prefixLift 5418057
  have htrace : WordTrace (prefixWord ++ tailWord_5418057) baseStart_5418057 baseEnd_5418057 := by
    simpa [prefixWord, tailWord_5418057, baseEnd_5418057] using wordTrace_append hprefix tailTrace_5418057
  have hstable : (prefixWord ++ tailWord_5418057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418057).length < 2 ^ (prefixWord ++ tailWord_5418057).sum := by decide
  have hdescent : baseEnd_5418057 < baseStart_5418057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_5418067 : Nat := 118140960795 + 5418067 * 2 ^ 59
def prefixEnd_5418067 : Nat := 4983230072969 + 3 ^ 40 * 5418067 * 2
def baseEnd_5418067 : Nat := 2782072589263758521645269

theorem tailTrace_5418067 : CollatzResearch.WordTrace tailWord_5418067 prefixEnd_5418067 2782072589263758521645269 := by
  unfold tailWord_5418067
  simp only [CollatzResearch.WordTrace]
  refine ⟨197613138062276066019252455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131742092041517377346168303 197613138062276066019252455)
  ·
    refine ⟨296419707093414099028878683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197613138062276066019252455 296419707093414099028878683)
    ·
      refine ⟨444629560640121148543318025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296419707093414099028878683 444629560640121148543318025)
      ·
        refine ⟨333472170480090861407488519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444629560640121148543318025 333472170480090861407488519)
        ·
          refine ⟨500208255720136292111232779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333472170480090861407488519 500208255720136292111232779)
          ·
            refine ⟨750312383580204438166849169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500208255720136292111232779 750312383580204438166849169)
            ·
              refine ⟨562734287685153328625136877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750312383580204438166849169 562734287685153328625136877)
              ·
                refine ⟨211025357881932498234426329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562734287685153328625136877 211025357881932498234426329)
                ·
                  refine ⟨158269018411449373675819747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211025357881932498234426329 158269018411449373675819747)
                  ·
                    refine ⟨237403527617174060513729621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158269018411449373675819747 237403527617174060513729621)
                    ·
                      refine ⟨2782072589263758521645269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237403527617174060513729621 2782072589263758521645269)
                      ·
                        rfl

theorem cell23_5418067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_5418067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418067 prefixEnd_5418067 := by exact prefixLift 5418067
  have htrace : WordTrace (prefixWord ++ tailWord_5418067) baseStart_5418067 baseEnd_5418067 := by
    simpa [prefixWord, tailWord_5418067, baseEnd_5418067] using wordTrace_append hprefix tailTrace_5418067
  have hstable : (prefixWord ++ tailWord_5418067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418067).length < 2 ^ (prefixWord ++ tailWord_5418067).sum := by decide
  have hdescent : baseEnd_5418067 < baseStart_5418067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418074 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_5418074 : Nat := 118140960795 + 5418074 * 2 ^ 59
def prefixEnd_5418074 : Nat := 4983230072969 + 3 ^ 40 * 5418074 * 2
def baseEnd_5418074 : Nat := 2782076183628339994257737

theorem tailTrace_5418074 : CollatzResearch.WordTrace tailWord_5418074 prefixEnd_5418074 2782076183628339994257737 := by
  unfold tailWord_5418074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49403348343312676553689319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131742262248833804143171517 49403348343312676553689319)
  ·
    refine ⟨74105022514969014830533979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49403348343312676553689319 74105022514969014830533979)
    ·
      refine ⟨111157533772453522245800969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74105022514969014830533979 111157533772453522245800969)
      ·
        refine ⟨83368150329340141684350727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111157533772453522245800969 83368150329340141684350727)
        ·
          refine ⟨125052225494010212526526091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83368150329340141684350727 125052225494010212526526091)
          ·
            refine ⟨187578338241015318789789137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125052225494010212526526091 187578338241015318789789137)
            ·
              refine ⟨140683753680761489092341853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187578338241015318789789137 140683753680761489092341853)
              ·
                refine ⟨52756407630285558409628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140683753680761489092341853 52756407630285558409628195)
                ·
                  refine ⟨79134611445428337614442293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52756407630285558409628195 79134611445428337614442293)
                  ·
                    refine ⟨7418869823008906651353965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79134611445428337614442293 7418869823008906651353965)
                    ·
                      refine ⟨2782076183628339994257737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7418869823008906651353965 2782076183628339994257737)
                      ·
                        rfl

theorem cell23_5418074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_5418074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418074 prefixEnd_5418074 := by exact prefixLift 5418074
  have htrace : WordTrace (prefixWord ++ tailWord_5418074) baseStart_5418074 baseEnd_5418074 := by
    simpa [prefixWord, tailWord_5418074, baseEnd_5418074] using wordTrace_append hprefix tailTrace_5418074
  have hstable : (prefixWord ++ tailWord_5418074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418074).length < 2 ^ (prefixWord ++ tailWord_5418074).sum := by decide
  have hdescent : baseEnd_5418074 < baseStart_5418074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418131 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 4, 2]
def baseStart_5418131 : Nat := 118140960795 + 5418131 * 2 ^ 59
def prefixEnd_5418131 : Nat := 4983230072969 + 3 ^ 40 * 5418131 * 2
def baseEnd_5418131 : Nat := 2782105452025646271244975

theorem tailTrace_5418131 : CollatzResearch.WordTrace tailWord_5418131 prefixEnd_5418131 2782105452025646271244975 := by
  unfold tailWord_5418131
  simp only [CollatzResearch.WordTrace]
  refine ⟨197615472334044204949582247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131743648222696136633054831 197615472334044204949582247)
  ·
    refine ⟨296423208501066307424373371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197615472334044204949582247 296423208501066307424373371)
    ·
      refine ⟨444634812751599461136560057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296423208501066307424373371 444634812751599461136560057)
      ·
        refine ⟨333476109563699595852420043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444634812751599461136560057 333476109563699595852420043)
        ·
          refine ⟨500214164345549393778630065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333476109563699595852420043 500214164345549393778630065)
          ·
            refine ⟨375160623259162045333972549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500214164345549393778630065 375160623259162045333972549)
            ·
              refine ⟨70342616861092883500119853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375160623259162045333972549 70342616861092883500119853)
              ·
                refine ⟨26378481322909831312544945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70342616861092883500119853 26378481322909831312544945)
                ·
                  refine ⟨19783860992182373484408709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26378481322909831312544945 19783860992182373484408709)
                  ·
                    refine ⟨3709473936034195028326633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19783860992182373484408709 3709473936034195028326633)
                    ·
                      refine ⟨2782105452025646271244975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709473936034195028326633 2782105452025646271244975)
                      ·
                        rfl

theorem cell23_5418131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4, 2].length) (baseStart_5418131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418131 prefixEnd_5418131 := by exact prefixLift 5418131
  have htrace : WordTrace (prefixWord ++ tailWord_5418131) baseStart_5418131 baseEnd_5418131 := by
    simpa [prefixWord, tailWord_5418131, baseEnd_5418131] using wordTrace_append hprefix tailTrace_5418131
  have hstable : (prefixWord ++ tailWord_5418131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418131).length < 2 ^ (prefixWord ++ tailWord_5418131).sum := by decide
  have hdescent : baseEnd_5418131 < baseStart_5418131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418141 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_5418141 : Nat := 118140960795 + 5418141 * 2 ^ 59
def prefixEnd_5418141 : Nat := 4983230072969 + 3 ^ 40 * 5418141 * 2
def baseEnd_5418141 : Nat := 927370195610730410706643

theorem tailTrace_5418141 : CollatzResearch.WordTrace tailWord_5418141 prefixEnd_5418141 927370195610730410706643 := by
  unfold tailWord_5418141
  simp only [CollatzResearch.WordTrace]
  refine ⟨197615837064007976657446277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131743891376005317771630851 197615837064007976657446277)
  ·
    refine ⟨37052969449501495623271177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197615837064007976657446277 37052969449501495623271177)
    ·
      refine ⟨27789727087126121717453383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37052969449501495623271177 27789727087126121717453383)
      ·
        refine ⟨41684590630689182576180075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27789727087126121717453383 41684590630689182576180075)
        ·
          refine ⟨62526885946033773864270113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41684590630689182576180075 62526885946033773864270113)
          ·
            refine ⟨46895164459525330398202585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62526885946033773864270113 46895164459525330398202585)
            ·
              refine ⟨35171373344643997798651939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46895164459525330398202585 35171373344643997798651939)
              ·
                refine ⟨52757060016965996697977909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35171373344643997798651939 52757060016965996697977909)
                ·
                  refine ⟨4945974376590562190435429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52757060016965996697977909 4945974376590562190435429)
                  ·
                    refine ⟨927370195610730410706643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945974376590562190435429 927370195610730410706643)
                    ·
                      rfl

theorem cell23_5418141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_5418141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418141 prefixEnd_5418141 := by exact prefixLift 5418141
  have htrace : WordTrace (prefixWord ++ tailWord_5418141) baseStart_5418141 baseEnd_5418141 := by
    simpa [prefixWord, tailWord_5418141, baseEnd_5418141] using wordTrace_append hprefix tailTrace_5418141
  have hstable : (prefixWord ++ tailWord_5418141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418141).length < 2 ^ (prefixWord ++ tailWord_5418141).sum := by decide
  have hdescent : baseEnd_5418141 < baseStart_5418141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418148 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_5418148 : Nat := 118140960795 + 5418148 * 2 ^ 59
def prefixEnd_5418148 : Nat := 4983230072969 + 3 ^ 40 * 5418148 * 2
def baseEnd_5418148 : Nat := 2782114181196772704732397

theorem tailTrace_5418148 : CollatzResearch.WordTrace tailWord_5418148 prefixEnd_5418148 2782114181196772704732397 := by
  unfold tailWord_5418148
  simp only [CollatzResearch.WordTrace]
  refine ⟨98808046187491308426475549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131744061583321744568634065 98808046187491308426475549)
  ·
    refine ⟨37053017320309240659928331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98808046187491308426475549 37053017320309240659928331)
    ·
      refine ⟨55579525980463860989892497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37053017320309240659928331 55579525980463860989892497)
      ·
        refine ⟨41684644485347895742419373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55579525980463860989892497 41684644485347895742419373)
        ·
          refine ⟨15631741682005460903407265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41684644485347895742419373 15631741682005460903407265)
          ·
            refine ⟨11723806261504095677555449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15631741682005460903407265 11723806261504095677555449)
            ·
              refine ⟨8792854696128071758166587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11723806261504095677555449 8792854696128071758166587)
              ·
                refine ⟨13189282044192107637249881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8792854696128071758166587 13189282044192107637249881)
                ·
                  refine ⟨9891961533144080727937411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13189282044192107637249881 9891961533144080727937411)
                  ·
                    refine ⟨14837942299716121091906117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9891961533144080727937411 14837942299716121091906117)
                    ·
                      refine ⟨2782114181196772704732397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14837942299716121091906117 2782114181196772704732397)
                      ·
                        rfl

theorem cell23_5418148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_5418148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418148 prefixEnd_5418148 := by exact prefixLift 5418148
  have htrace : WordTrace (prefixWord ++ tailWord_5418148) baseStart_5418148 baseEnd_5418148 := by
    simpa [prefixWord, tailWord_5418148, baseEnd_5418148] using wordTrace_append hprefix tailTrace_5418148
  have hstable : (prefixWord ++ tailWord_5418148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418148).length < 2 ^ (prefixWord ++ tailWord_5418148).sum := by decide
  have hdescent : baseEnd_5418148 < baseStart_5418148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418166 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_5418166 : Nat := 118140960795 + 5418166 * 2 ^ 59
def prefixEnd_5418166 : Nat := 4983230072969 + 3 ^ 40 * 5418166 * 2
def baseEnd_5418166 : Nat := 309124824872061514923035

theorem tailTrace_5418166 : CollatzResearch.WordTrace tailWord_5418166 prefixEnd_5418166 309124824872061514923035 := by
  unfold tailWord_5418166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351046805557337870444147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131744499259278270618070901 12351046805557337870444147)
  ·
    refine ⟨18526570208336006805666221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12351046805557337870444147 18526570208336006805666221)
    ·
      refine ⟨6947463828126002552124833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18526570208336006805666221 6947463828126002552124833)
      ·
        refine ⟨5210597871094501914093625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6947463828126002552124833 5210597871094501914093625)
        ·
          refine ⟨3907948403320876435570219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5210597871094501914093625 3907948403320876435570219)
          ·
            refine ⟨5861922604981314653355329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907948403320876435570219 5861922604981314653355329)
            ·
              refine ⟨4396441953735985990016497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861922604981314653355329 4396441953735985990016497)
              ·
                refine ⟨3297331465301989492512373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396441953735985990016497 3297331465301989492512373)
                ·
                  refine ⟨309124824872061514923035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297331465301989492512373 309124824872061514923035)
                  ·
                    rfl

theorem cell23_5418166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_5418166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418166 prefixEnd_5418166 := by exact prefixLift 5418166
  have htrace : WordTrace (prefixWord ++ tailWord_5418166) baseStart_5418166 baseEnd_5418166 := by
    simpa [prefixWord, tailWord_5418166, baseEnd_5418166] using wordTrace_append hprefix tailTrace_5418166
  have hstable : (prefixWord ++ tailWord_5418166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418166).length < 2 ^ (prefixWord ++ tailWord_5418166).sum := by decide
  have hdescent : baseEnd_5418166 < baseStart_5418166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418175 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 1, 4]
def baseStart_5418175 : Nat := 118140960795 + 5418175 * 2 ^ 59
def prefixEnd_5418175 : Nat := 4983230072969 + 3 ^ 40 * 5418175 * 2
def baseEnd_5418175 : Nat := 927376015058148033031591

theorem tailTrace_5418175 : CollatzResearch.WordTrace tailWord_5418175 prefixEnd_5418175 927376015058148033031591 := by
  unfold tailWord_5418175
  simp only [CollatzResearch.WordTrace]
  refine ⟨197617077145884800464183979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131744718097256533642789319 197617077145884800464183979)
  ·
    refine ⟨296425615718827200696275969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197617077145884800464183979 296425615718827200696275969)
    ·
      refine ⟨222319211789120400522206977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296425615718827200696275969 222319211789120400522206977)
      ·
        refine ⟨166739408841840300391655233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222319211789120400522206977 166739408841840300391655233)
        ·
          refine ⟨125054556631380225293741425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166739408841840300391655233 125054556631380225293741425)
          ·
            refine ⟨93790917473535168970306069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125054556631380225293741425 93790917473535168970306069)
            ·
              refine ⟨4396449256571961045483097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93790917473535168970306069 4396449256571961045483097)
              ·
                refine ⟨3297336942428970784112323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396449256571961045483097 3297336942428970784112323)
                ·
                  refine ⟨4946005413643456176168485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297336942428970784112323 4946005413643456176168485)
                  ·
                    refine ⟨927376015058148033031591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946005413643456176168485 927376015058148033031591)
                    ·
                      rfl

theorem cell23_5418175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_5418175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418175 prefixEnd_5418175 := by exact prefixLift 5418175
  have htrace : WordTrace (prefixWord ++ tailWord_5418175) baseStart_5418175 baseEnd_5418175 := by
    simpa [prefixWord, tailWord_5418175, baseEnd_5418175] using wordTrace_append hprefix tailTrace_5418175
  have hstable : (prefixWord ++ tailWord_5418175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418175).length < 2 ^ (prefixWord ++ tailWord_5418175).sum := by decide
  have hdescent : baseEnd_5418175 < baseStart_5418175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418201 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_5418201 : Nat := 118140960795 + 5418201 * 2 ^ 59
def prefixEnd_5418201 : Nat := 4983230072969 + 3 ^ 40 * 5418201 * 2
def baseEnd_5418201 : Nat := 927380465223820332456551

theorem tailTrace_5418201 : CollatzResearch.WordTrace tailWord_5418201 prefixEnd_5418201 927380465223820332456551 := by
  unfold tailWord_5418201
  simp only [CollatzResearch.WordTrace]
  refine ⟨197618025443790606904630457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131745350295860404603086971 197618025443790606904630457)
  ·
    refine ⟨148213519082842955178472843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197618025443790606904630457 148213519082842955178472843)
    ·
      refine ⟨222320278624264432767709265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148213519082842955178472843 222320278624264432767709265)
      ·
        refine ⟨166740208968198324575781949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222320278624264432767709265 166740208968198324575781949)
        ·
          refine ⟨62527578363074371715918231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166740208968198324575781949 62527578363074371715918231)
          ·
            refine ⟨93791367544611557573877347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62527578363074371715918231 93791367544611557573877347)
            ·
              refine ⟨140687051316917336360816021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93791367544611557573877347 140687051316917336360816021)
              ·
                refine ⟨6594705530480500141913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140687051316917336360816021 6594705530480500141913251)
                ·
                  refine ⟨9892058295720750212869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594705530480500141913251 9892058295720750212869877)
                  ·
                    refine ⟨927380465223820332456551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9892058295720750212869877 927380465223820332456551)
                    ·
                      rfl

theorem cell23_5418201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_5418201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418201 prefixEnd_5418201 := by exact prefixLift 5418201
  have htrace : WordTrace (prefixWord ++ tailWord_5418201) baseStart_5418201 baseEnd_5418201 := by
    simpa [prefixWord, tailWord_5418201, baseEnd_5418201] using wordTrace_append hprefix tailTrace_5418201
  have hstable : (prefixWord ++ tailWord_5418201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418201).length < 2 ^ (prefixWord ++ tailWord_5418201).sum := by decide
  have hdescent : baseEnd_5418201 < baseStart_5418201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418208 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2]
def baseStart_5418208 : Nat := 118140960795 + 5418208 * 2 ^ 59
def prefixEnd_5418208 : Nat := 4983230072969 + 3 ^ 40 * 5418208 * 2
def baseEnd_5418208 : Nat := 2782144990036042469982121

theorem tailTrace_5418208 : CollatzResearch.WordTrace tailWord_5418208 prefixEnd_5418208 2782144990036042469982121 := by
  unfold tailWord_5418208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98809140377382623550067639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131745520503176831400090185 98809140377382623550067639)
  ·
    refine ⟨148213710566073935325101459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98809140377382623550067639 148213710566073935325101459)
    ·
      refine ⟨222320565849110902987652189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148213710566073935325101459 222320565849110902987652189)
      ·
        refine ⟨83370212193416588620369571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222320565849110902987652189 83370212193416588620369571)
        ·
          refine ⟨125055318290124882930554357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83370212193416588620369571 125055318290124882930554357)
          ·
            refine ⟨11723936089699207774739471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125055318290124882930554357 11723936089699207774739471)
            ·
              refine ⟨17585904134548811662109207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723936089699207774739471 17585904134548811662109207)
              ·
                refine ⟨26378856201823217493163811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17585904134548811662109207 26378856201823217493163811)
                ·
                  refine ⟨39568284302734826239745717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26378856201823217493163811 39568284302734826239745717)
                  ·
                    refine ⟨3709526653381389959976161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39568284302734826239745717 3709526653381389959976161)
                    ·
                      refine ⟨2782144990036042469982121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709526653381389959976161 2782144990036042469982121)
                      ·
                        rfl

theorem cell23_5418208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_5418208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418208 prefixEnd_5418208 := by exact prefixLift 5418208
  have htrace : WordTrace (prefixWord ++ tailWord_5418208) baseStart_5418208 baseEnd_5418208 := by
    simpa [prefixWord, tailWord_5418208, baseEnd_5418208] using wordTrace_append hprefix tailTrace_5418208
  have hstable : (prefixWord ++ tailWord_5418208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418208).length < 2 ^ (prefixWord ++ tailWord_5418208).sum := by decide
  have hdescent : baseEnd_5418208 < baseStart_5418208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418218 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_5418218 : Nat := 118140960795 + 5418218 * 2 ^ 59
def prefixEnd_5418218 : Nat := 4983230072969 + 3 ^ 40 * 5418218 * 2
def baseEnd_5418218 : Nat := 927383374947529143619025

theorem tailTrace_5418218 : CollatzResearch.WordTrace tailWord_5418218 prefixEnd_5418218 927383374947529143619025 := by
  unfold tailWord_5418218
  simp only [CollatzResearch.WordTrace]
  refine ⟨49404661371182254701999827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131745763656486012538666205 49404661371182254701999827)
  ·
    refine ⟨74106992056773382052999741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49404661371182254701999827 74106992056773382052999741)
    ·
      refine ⟨27790122021290018269874903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74106992056773382052999741 27790122021290018269874903)
      ·
        refine ⟨41685183031935027404812355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27790122021290018269874903 41685183031935027404812355)
        ·
          refine ⟨62527774547902541107218533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41685183031935027404812355 62527774547902541107218533)
          ·
            refine ⟨11723957727731726457603475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62527774547902541107218533 11723957727731726457603475)
            ·
              refine ⟨17585936591597589686405213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723957727731726457603475 17585936591597589686405213)
              ·
                refine ⟨6594726221849096132401955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17585936591597589686405213 6594726221849096132401955)
                ·
                  refine ⟨9892089332773644198602933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594726221849096132401955 9892089332773644198602933)
                  ·
                    refine ⟨927383374947529143619025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9892089332773644198602933 927383374947529143619025)
                    ·
                      rfl

theorem cell23_5418218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_5418218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418218 prefixEnd_5418218 := by exact prefixLift 5418218
  have htrace : WordTrace (prefixWord ++ tailWord_5418218) baseStart_5418218 baseEnd_5418218 := by
    simpa [prefixWord, tailWord_5418218, baseEnd_5418218] using wordTrace_append hprefix tailTrace_5418218
  have hstable : (prefixWord ++ tailWord_5418218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418218).length < 2 ^ (prefixWord ++ tailWord_5418218).sum := by decide
  have hdescent : baseEnd_5418218 < baseStart_5418218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418231 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 4, 4]
def baseStart_5418231 : Nat := 118140960795 + 5418231 * 2 ^ 59
def prefixEnd_5418231 : Nat := 4983230072969 + 3 ^ 40 * 5418231 * 2
def baseEnd_5418231 : Nat := 927385600030365293331505

theorem tailTrace_5418231 : CollatzResearch.WordTrace tailWord_5418231 prefixEnd_5418231 927385600030365293331505 := by
  unfold tailWord_5418231
  simp only [CollatzResearch.WordTrace]
  refine ⟨197619119633681922028222547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131746079755787948018815031 197619119633681922028222547)
  ·
    refine ⟨296428679450522883042333821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197619119633681922028222547 296428679450522883042333821)
    ·
      refine ⟨111160754793946081140875183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296428679450522883042333821 111160754793946081140875183)
      ·
        refine ⟨166741132190919121711312775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111160754793946081140875183 166741132190919121711312775)
        ·
          refine ⟨250111698286378682566969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166741132190919121711312775 250111698286378682566969163)
          ·
            refine ⟨375167547429568023850453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250111698286378682566969163 375167547429568023850453745)
            ·
              refine ⟨281375660572176017887840309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375167547429568023850453745 281375660572176017887840309)
              ·
                refine ⟨26378968178641501676985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281375660572176017887840309 26378968178641501676985029)
                ·
                  refine ⟨4946056533495281564434693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26378968178641501676985029 4946056533495281564434693)
                  ·
                    refine ⟨927385600030365293331505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946056533495281564434693 927385600030365293331505)
                    ·
                      rfl

theorem cell23_5418231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_5418231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418231 prefixEnd_5418231 := by exact prefixLift 5418231
  have htrace : WordTrace (prefixWord ++ tailWord_5418231) baseStart_5418231 baseEnd_5418231 := by
    simpa [prefixWord, tailWord_5418231, baseEnd_5418231] using wordTrace_append hprefix tailTrace_5418231
  have hstable : (prefixWord ++ tailWord_5418231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418231).length < 2 ^ (prefixWord ++ tailWord_5418231).sum := by decide
  have hdescent : baseEnd_5418231 < baseStart_5418231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418241 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5418241 : Nat := 118140960795 + 5418241 * 2 ^ 59
def prefixEnd_5418241 : Nat := 4983230072969 + 3 ^ 40 * 5418241 * 2
def baseEnd_5418241 : Nat := 2782161934897640840869469

theorem tailTrace_5418241 : CollatzResearch.WordTrace tailWord_5418241 prefixEnd_5418241 2782161934897640840869469 := by
  unfold tailWord_5418241
  simp only [CollatzResearch.WordTrace]
  refine ⟨197619484363645693736086577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131746322909097129157391051 197619484363645693736086577)
  ·
    refine ⟨148214613272734270302064933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197619484363645693736086577 148214613272734270302064933)
    ·
      refine ⟨27790239988637675681637175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148214613272734270302064933 27790239988637675681637175)
      ·
        refine ⟨41685359982956513522455763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27790239988637675681637175 41685359982956513522455763)
        ·
          refine ⟨62528039974434770283683645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41685359982956513522455763 62528039974434770283683645)
          ·
            refine ⟨23448014990413038856381367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62528039974434770283683645 23448014990413038856381367)
            ·
              refine ⟨35172022485619558284572051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448014990413038856381367 35172022485619558284572051)
              ·
                refine ⟨52758033728429337426858077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35172022485619558284572051 52758033728429337426858077)
                ·
                  refine ⟨19784262648161001535071779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52758033728429337426858077 19784262648161001535071779)
                  ·
                    refine ⟨29676393972241502302607669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19784262648161001535071779 29676393972241502302607669)
                    ·
                      refine ⟨2782161934897640840869469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29676393972241502302607669 2782161934897640840869469)
                      ·
                        rfl

theorem cell23_5418241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5418241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418241 prefixEnd_5418241 := by exact prefixLift 5418241
  have htrace : WordTrace (prefixWord ++ tailWord_5418241) baseStart_5418241 baseEnd_5418241 := by
    simpa [prefixWord, tailWord_5418241, baseEnd_5418241] using wordTrace_append hprefix tailTrace_5418241
  have hstable : (prefixWord ++ tailWord_5418241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418241).length < 2 ^ (prefixWord ++ tailWord_5418241).sum := by decide
  have hdescent : baseEnd_5418241 < baseStart_5418241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418251 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_5418251 : Nat := 118140960795 + 5418251 * 2 ^ 59
def prefixEnd_5418251 : Nat := 4983230072969 + 3 ^ 40 * 5418251 * 2
def baseEnd_5418251 : Nat := 2782167069704185801744423

theorem tailTrace_5418251 : CollatzResearch.WordTrace tailWord_5418251 prefixEnd_5418251 2782167069704185801744423 := by
  unfold tailWord_5418251
  simp only [CollatzResearch.WordTrace]
  refine ⟨197619849093609465443950607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131746566062406310295967071 197619849093609465443950607)
  ·
    refine ⟨296429773640414198165925911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197619849093609465443950607 296429773640414198165925911)
    ·
      refine ⟨444644660460621297248888867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296429773640414198165925911 444644660460621297248888867)
      ·
        refine ⟨666966990690931945873333301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444644660460621297248888867 666966990690931945873333301)
        ·
          refine ⟨62528155377274869925624997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 666966990690931945873333301 62528155377274869925624997)
          ·
            refine ⟨11724029133239038111054687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62528155377274869925624997 11724029133239038111054687)
            ·
              refine ⟨17586043699858557166582031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724029133239038111054687 17586043699858557166582031)
              ·
                refine ⟨26379065549787835749873047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17586043699858557166582031 26379065549787835749873047)
                ·
                  refine ⟨39568598324681753624809571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26379065549787835749873047 39568598324681753624809571)
                  ·
                    refine ⟨59352897487022630437214357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39568598324681753624809571 59352897487022630437214357)
                    ·
                      refine ⟨2782167069704185801744423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59352897487022630437214357 2782167069704185801744423)
                      ·
                        rfl

theorem cell23_5418251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_5418251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418251 prefixEnd_5418251 := by exact prefixLift 5418251
  have htrace : WordTrace (prefixWord ++ tailWord_5418251) baseStart_5418251 baseEnd_5418251 := by
    simpa [prefixWord, tailWord_5418251, baseEnd_5418251] using wordTrace_append hprefix tailTrace_5418251
  have hstable : (prefixWord ++ tailWord_5418251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418251).length < 2 ^ (prefixWord ++ tailWord_5418251).sum := by decide
  have hdescent : baseEnd_5418251 < baseStart_5418251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418288 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_5418288 : Nat := 118140960795 + 5418288 * 2 ^ 59
def prefixEnd_5418288 : Nat := 4983230072969 + 3 ^ 40 * 5418288 * 2
def baseEnd_5418288 : Nat := 2782186068488402156981753

theorem tailTrace_5418288 : CollatzResearch.WordTrace tailWord_5418288 prefixEnd_5418288 2782186068488402156981753 := by
  unfold tailWord_5418288
  simp only [CollatzResearch.WordTrace]
  refine ⟨98810599297237710381523759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131747465729650280508698345 98810599297237710381523759)
  ·
    refine ⟨148215898945856565572285639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98810599297237710381523759 148215898945856565572285639)
    ·
      refine ⟨222323848418784848358428459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148215898945856565572285639 222323848418784848358428459)
      ·
        refine ⟨333485772628177272537642689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222323848418784848358428459 333485772628177272537642689)
        ·
          refine ⟨250114329471132954403232017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333485772628177272537642689 250114329471132954403232017)
          ·
            refine ⟨187585747103349715802424013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250114329471132954403232017 187585747103349715802424013)
            ·
              refine ⟨70344655163756143425909005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187585747103349715802424013 70344655163756143425909005)
              ·
                refine ⟨26379245686408553784715877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70344655163756143425909005 26379245686408553784715877)
                ·
                  refine ⟨4946108566201603834634227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26379245686408553784715877 4946108566201603834634227)
                  ·
                    refine ⟨7419162849302405751951341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946108566201603834634227 7419162849302405751951341)
                    ·
                      refine ⟨2782186068488402156981753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7419162849302405751951341 2782186068488402156981753)
                      ·
                        rfl

theorem cell23_5418288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_5418288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418288 prefixEnd_5418288 := by exact prefixLift 5418288
  have htrace : WordTrace (prefixWord ++ tailWord_5418288) baseStart_5418288 baseEnd_5418288 := by
    simpa [prefixWord, tailWord_5418288, baseEnd_5418288] using wordTrace_append hprefix tailTrace_5418288
  have hstable : (prefixWord ++ tailWord_5418288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418288).length < 2 ^ (prefixWord ++ tailWord_5418288).sum := by decide
  have hdescent : baseEnd_5418288 < baseStart_5418288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418326 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5418326 : Nat := 118140960795 + 5418326 * 2 ^ 59
def prefixEnd_5418326 : Nat := 4983230072969 + 3 ^ 40 * 5418326 * 2
def baseEnd_5418326 : Nat := 2782205580753273008306579

theorem tailTrace_5418326 : CollatzResearch.WordTrace tailWord_5418326 prefixEnd_5418326 2782205580753273008306579 := by
  unfold tailWord_5418326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351411535521109578308177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131748389712225168835287221 12351411535521109578308177)
  ·
    refine ⟨9263558651640832183731133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12351411535521109578308177 9263558651640832183731133)
    ·
      refine ⟨3473834494365312068899175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9263558651640832183731133 3473834494365312068899175)
      ·
        refine ⟨5210751741547968103348763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473834494365312068899175 5210751741547968103348763)
        ·
          refine ⟨7816127612321952155023145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210751741547968103348763 7816127612321952155023145)
          ·
            refine ⟨5862095709241464116267359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7816127612321952155023145 5862095709241464116267359)
            ·
              refine ⟨8793143563862196174401039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862095709241464116267359 8793143563862196174401039)
              ·
                refine ⟨13189715345793294261601559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8793143563862196174401039 13189715345793294261601559)
                ·
                  refine ⟨19784573018689941392402339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13189715345793294261601559 19784573018689941392402339)
                  ·
                    refine ⟨29676859528034912088603509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19784573018689941392402339 29676859528034912088603509)
                    ·
                      refine ⟨2782205580753273008306579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29676859528034912088603509 2782205580753273008306579)
                      ·
                        rfl

theorem cell23_5418326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5418326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418326 prefixEnd_5418326 := by exact prefixLift 5418326
  have htrace : WordTrace (prefixWord ++ tailWord_5418326) baseStart_5418326 baseEnd_5418326 := by
    simpa [prefixWord, tailWord_5418326, baseEnd_5418326] using wordTrace_append hprefix tailTrace_5418326
  have hstable : (prefixWord ++ tailWord_5418326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418326).length < 2 ^ (prefixWord ++ tailWord_5418326).sum := by decide
  have hdescent : baseEnd_5418326 < baseStart_5418326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418338 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5418338 : Nat := 118140960795 + 5418338 * 2 ^ 59
def prefixEnd_5418338 : Nat := 4983230072969 + 3 ^ 40 * 5418338 * 2
def baseEnd_5418338 : Nat := 927403914173708987118841

theorem tailTrace_5418338 : CollatzResearch.WordTrace tailWord_5418338 prefixEnd_5418338 927403914173708987118841 := by
  unfold tailWord_5418338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49405755561073569825591917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131748681496196186201578445 49405755561073569825591917)
  ·
    refine ⟨18527158335402588684596969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49405755561073569825591917 18527158335402588684596969)
    ·
      refine ⟨13895368751551941513447727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18527158335402588684596969 13895368751551941513447727)
      ·
        refine ⟨20843053127327912270171591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13895368751551941513447727 20843053127327912270171591)
        ·
          refine ⟨31264579690991868405257387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20843053127327912270171591 31264579690991868405257387)
          ·
            refine ⟨46896869536487802607886081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31264579690991868405257387 46896869536487802607886081)
            ·
              refine ⟨35172652152365851955914561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46896869536487802607886081 35172652152365851955914561)
              ·
                refine ⟨26379489114274388966935921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35172652152365851955914561 26379489114274388966935921)
                ·
                  refine ⟨19784616835705791725201941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26379489114274388966935921 19784616835705791725201941)
                  ·
                    refine ⟨927403914173708987118841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19784616835705791725201941 927403914173708987118841)
                    ·
                      rfl

theorem cell23_5418338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5418338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418338 prefixEnd_5418338 := by exact prefixLift 5418338
  have htrace : WordTrace (prefixWord ++ tailWord_5418338) baseStart_5418338 baseEnd_5418338 := by
    simpa [prefixWord, tailWord_5418338, baseEnd_5418338] using wordTrace_append hprefix tailTrace_5418338
  have hstable : (prefixWord ++ tailWord_5418338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418338).length < 2 ^ (prefixWord ++ tailWord_5418338).sum := by decide
  have hdescent : baseEnd_5418338 < baseStart_5418338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418348 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_5418348 : Nat := 118140960795 + 5418348 * 2 ^ 59
def prefixEnd_5418348 : Nat := 4983230072969 + 3 ^ 40 * 5418348 * 2
def baseEnd_5418348 : Nat := 2782216877327671922231477

theorem tailTrace_5418348 : CollatzResearch.WordTrace tailWord_5418348 prefixEnd_5418348 2782216877327671922231477 := by
  unfold tailWord_5418348
  simp only [CollatzResearch.WordTrace]
  refine ⟨98811693487129025505115849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131748924649505367340154465 98811693487129025505115849)
  ·
    refine ⟨74108770115346769128836887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98811693487129025505115849 74108770115346769128836887)
    ·
      refine ⟨111163155173020153693255331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74108770115346769128836887 111163155173020153693255331)
      ·
        refine ⟨166744732759530230539882997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111163155173020153693255331 166744732759530230539882997)
        ·
          refine ⟨15632318696205959113114031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166744732759530230539882997 15632318696205959113114031)
          ·
            refine ⟨23448478044308938669671047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632318696205959113114031 23448478044308938669671047)
            ·
              refine ⟨35172717066463408004506571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448478044308938669671047 35172717066463408004506571)
              ·
                refine ⟨52759075599695112006759857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35172717066463408004506571 52759075599695112006759857)
                ·
                  refine ⟨39569306699771334005069893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52759075599695112006759857 39569306699771334005069893)
                  ·
                    refine ⟨7419245006207125125950605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39569306699771334005069893 7419245006207125125950605)
                    ·
                      refine ⟨2782216877327671922231477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7419245006207125125950605 2782216877327671922231477)
                      ·
                        rfl

theorem cell23_5418348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_5418348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418348 prefixEnd_5418348 := by exact prefixLift 5418348
  have htrace : WordTrace (prefixWord ++ tailWord_5418348) baseStart_5418348 baseEnd_5418348 := by
    simpa [prefixWord, tailWord_5418348, baseEnd_5418348] using wordTrace_append hprefix tailTrace_5418348
  have hstable : (prefixWord ++ tailWord_5418348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418348).length < 2 ^ (prefixWord ++ tailWord_5418348).sum := by decide
  have hdescent : baseEnd_5418348 < baseStart_5418348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418351 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 7]
def baseStart_5418351 : Nat := 118140960795 + 5418351 * 2 ^ 59
def prefixEnd_5418351 : Nat := 4983230072969 + 3 ^ 40 * 5418351 * 2
def baseEnd_5418351 : Nat := 309135379752181712277107

theorem tailTrace_5418351 : CollatzResearch.WordTrace tailWord_5418351 prefixEnd_5418351 309135379752181712277107 := by
  unfold tailWord_5418351
  simp only [CollatzResearch.WordTrace]
  refine ⟨197623496393247182522590907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131748997595498121681727271 197623496393247182522590907)
  ·
    refine ⟨296435244589870773783886361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197623496393247182522590907 296435244589870773783886361)
    ·
      refine ⟨222326433442403080337914771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296435244589870773783886361 222326433442403080337914771)
      ·
        refine ⟨333489650163604620506872157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222326433442403080337914771 333489650163604620506872157)
        ·
          refine ⟨125058618811351732690077059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333489650163604620506872157 125058618811351732690077059)
          ·
            refine ⟨187587928217027599035115589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125058618811351732690077059 187587928217027599035115589)
            ·
              refine ⟨35172736540692674819084173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187587928217027599035115589 35172736540692674819084173)
              ·
                refine ⟨13189776202759753057156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35172736540692674819084173 13189776202759753057156565)
                ·
                  refine ⟨309135379752181712277107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13189776202759753057156565 309135379752181712277107)
                  ·
                    rfl

theorem cell23_5418351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 7].length) (baseStart_5418351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418351 prefixEnd_5418351 := by exact prefixLift 5418351
  have htrace : WordTrace (prefixWord ++ tailWord_5418351) baseStart_5418351 baseEnd_5418351 := by
    simpa [prefixWord, tailWord_5418351, baseEnd_5418351] using wordTrace_append hprefix tailTrace_5418351
  have hstable : (prefixWord ++ tailWord_5418351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418351).length < 2 ^ (prefixWord ++ tailWord_5418351).sum := by decide
  have hdescent : baseEnd_5418351 < baseStart_5418351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418418 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5418418 : Nat := 118140960795 + 5418418 * 2 ^ 59
def prefixEnd_5418418 : Nat := 4983230072969 + 3 ^ 40 * 5418418 * 2
def baseEnd_5418418 : Nat := 2782252820973486648356155

theorem tailTrace_5418418 : CollatzResearch.WordTrace tailWord_5418418 prefixEnd_5418418 2782252820973486648356155 := by
  unfold tailWord_5418418
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406485021001113241319977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131750626722669635310186605 49406485021001113241319977)
  ·
    refine ⟨37054863765750834930989983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49406485021001113241319977 37054863765750834930989983)
    ·
      refine ⟨55582295648626252396484975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37054863765750834930989983 55582295648626252396484975)
      ·
        refine ⟨83373443472939378594727463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55582295648626252396484975 83373443472939378594727463)
        ·
          refine ⟨125060165209409067892091195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83373443472939378594727463 125060165209409067892091195)
          ·
            refine ⟨187590247814113601838136793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125060165209409067892091195 187590247814113601838136793)
            ·
              refine ⟨140692685860585201378602595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187590247814113601838136793 140692685860585201378602595)
              ·
                refine ⟨211039028790877802067903893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140692685860585201378602595 211039028790877802067903893)
                ·
                  refine ⟨9892454474572396971932995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211039028790877802067903893 9892454474572396971932995)
                  ·
                    refine ⟨14838681711858595457899493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892454474572396971932995 14838681711858595457899493)
                    ·
                      refine ⟨2782252820973486648356155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14838681711858595457899493 2782252820973486648356155)
                      ·
                        rfl

theorem cell23_5418418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5418418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418418 prefixEnd_5418418 := by exact prefixLift 5418418
  have htrace : WordTrace (prefixWord ++ tailWord_5418418) baseStart_5418418 baseEnd_5418418 := by
    simpa [prefixWord, tailWord_5418418, baseEnd_5418418] using wordTrace_append hprefix tailTrace_5418418
  have hstable : (prefixWord ++ tailWord_5418418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418418).length < 2 ^ (prefixWord ++ tailWord_5418418).sum := by decide
  have hdescent : baseEnd_5418418 < baseStart_5418418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418452 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5418452 : Nat := 118140960795 + 5418452 * 2 ^ 59
def prefixEnd_5418452 : Nat := 4983230072969 + 3 ^ 40 * 5418452 * 2
def baseEnd_5418452 : Nat := 2782270279315739515330999

theorem tailTrace_5418452 : CollatzResearch.WordTrace tailWord_5418452 prefixEnd_5418452 2782270279315739515330999 := by
  unfold tailWord_5418452
  simp only [CollatzResearch.WordTrace]
  refine ⟨98813590082940638386008805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131751453443920851181345073 98813590082940638386008805)
  ·
    refine ⟨18527548140551369697376651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98813590082940638386008805 18527548140551369697376651)
    ·
      refine ⟨27791322210827054546064977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18527548140551369697376651 27791322210827054546064977)
      ·
        refine ⟨20843491658120290909548733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27791322210827054546064977 20843491658120290909548733)
        ·
          refine ⟨7816309371795109091080775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20843491658120290909548733 7816309371795109091080775)
          ·
            refine ⟨11724464057692663636621163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816309371795109091080775 11724464057692663636621163)
            ·
              refine ⟨17586696086538995454931745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724464057692663636621163 17586696086538995454931745)
              ·
                refine ⟨13190022064904246591198809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17586696086538995454931745 13190022064904246591198809)
                ·
                  refine ⟨9892516548678184943399107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13190022064904246591198809 9892516548678184943399107)
                  ·
                    refine ⟨14838774823017277415098661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892516548678184943399107 14838774823017277415098661)
                    ·
                      refine ⟨2782270279315739515330999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14838774823017277415098661 2782270279315739515330999)
                      ·
                        rfl

theorem cell23_5418452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5418452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418452 prefixEnd_5418452 := by exact prefixLift 5418452
  have htrace : WordTrace (prefixWord ++ tailWord_5418452) baseStart_5418452 baseEnd_5418452 := by
    simpa [prefixWord, tailWord_5418452, baseEnd_5418452] using wordTrace_append hprefix tailTrace_5418452
  have hstable : (prefixWord ++ tailWord_5418452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418452).length < 2 ^ (prefixWord ++ tailWord_5418452).sum := by decide
  have hdescent : baseEnd_5418452 < baseStart_5418452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418458 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_5418458 : Nat := 118140960795 + 5418458 * 2 ^ 59
def prefixEnd_5418458 : Nat := 4983230072969 + 3 ^ 40 * 5418458 * 2
def baseEnd_5418458 : Nat := 309141484466629610206219

theorem tailTrace_5418458 : CollatzResearch.WordTrace tailWord_5418458 prefixEnd_5418458 309141484466629610206219 := by
  unfold tailWord_5418458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406849750964884949184007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131751599335906359864490685 49406849750964884949184007)
  ·
    refine ⟨74110274626447327423776011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49406849750964884949184007 74110274626447327423776011)
    ·
      refine ⟨111165411939670991135664017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74110274626447327423776011 111165411939670991135664017)
      ·
        refine ⟨83374058954753243351748013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111165411939670991135664017 83374058954753243351748013)
        ·
          refine ⟨31265272108032466256905505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83374058954753243351748013 31265272108032466256905505)
          ·
            refine ⟨23448954081024349692679129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31265272108032466256905505 23448954081024349692679129)
            ·
              refine ⟨17586715560768262269509347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23448954081024349692679129 17586715560768262269509347)
              ·
                refine ⟨26380073341152393404264021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17586715560768262269509347 26380073341152393404264021)
                ·
                  refine ⟨309141484466629610206219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26380073341152393404264021 309141484466629610206219)
                  ·
                    rfl

theorem cell23_5418458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_5418458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418458 prefixEnd_5418458 := by exact prefixLift 5418458
  have htrace : WordTrace (prefixWord ++ tailWord_5418458) baseStart_5418458 baseEnd_5418458 := by
    simpa [prefixWord, tailWord_5418458, baseEnd_5418458] using wordTrace_append hprefix tailTrace_5418458
  have hstable : (prefixWord ++ tailWord_5418458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418458).length < 2 ^ (prefixWord ++ tailWord_5418458).sum := by decide
  have hdescent : baseEnd_5418458 < baseStart_5418458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418525 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5418525 : Nat := 118140960795 + 5418525 * 2 ^ 59
def prefixEnd_5418525 : Nat := 4983230072969 + 3 ^ 40 * 5418525 * 2
def baseEnd_5418525 : Nat := 2782307763403517729718163

theorem tailTrace_5418525 : CollatzResearch.WordTrace tailWord_5418525 prefixEnd_5418525 2782307763403517729718163 := by
  unfold tailWord_5418525
  simp only [CollatzResearch.WordTrace]
  refine ⟨197629842694616810239425029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131753228463077873492950019 197629842694616810239425029)
  ·
    refine ⟨37055595505240651919892193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197629842694616810239425029 37055595505240651919892193)
    ·
      refine ⟨27791696628930488939919145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37055595505240651919892193 27791696628930488939919145)
      ·
        refine ⟨20843772471697866704939359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27791696628930488939919145 20843772471697866704939359)
        ·
          refine ⟨31265658707546800057409039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20843772471697866704939359 31265658707546800057409039)
          ·
            refine ⟨46898488061320200086113559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31265658707546800057409039 46898488061320200086113559)
            ·
              refine ⟨70347732091980300129170339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46898488061320200086113559 70347732091980300129170339)
              ·
                refine ⟨105521598137970450193755509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70347732091980300129170339 105521598137970450193755509)
                ·
                  refine ⟨9892649825434729705664579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105521598137970450193755509 9892649825434729705664579)
                  ·
                    refine ⟨14838974738152094558496869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892649825434729705664579 14838974738152094558496869)
                    ·
                      refine ⟨2782307763403517729718163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14838974738152094558496869 2782307763403517729718163)
                      ·
                        rfl

theorem cell23_5418525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5418525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418525 prefixEnd_5418525 := by exact prefixLift 5418525
  have htrace : WordTrace (prefixWord ++ tailWord_5418525) baseStart_5418525 baseEnd_5418525 := by
    simpa [prefixWord, tailWord_5418525, baseEnd_5418525] using wordTrace_append hprefix tailTrace_5418525
  have hstable : (prefixWord ++ tailWord_5418525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418525).length < 2 ^ (prefixWord ++ tailWord_5418525).sum := by decide
  have hdescent : baseEnd_5418525 < baseStart_5418525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418542 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5418542 : Nat := 118140960795 + 5418542 * 2 ^ 59
def prefixEnd_5418542 : Nat := 4983230072969 + 3 ^ 40 * 5418542 * 2
def baseEnd_5418542 : Nat := 2782316492574644163205585

theorem tailTrace_5418542 : CollatzResearch.WordTrace tailWord_5418542 prefixEnd_5418542 2782316492574644163205585 := by
  unfold tailWord_5418542
  simp only [CollatzResearch.WordTrace]
  refine ⟨24703807841944402767849235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131753641823703481428529253 24703807841944402767849235)
  ·
    refine ⟨37055711762916604151773853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24703807841944402767849235 37055711762916604151773853)
    ·
      refine ⟨13895891911093726556915195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37055711762916604151773853 13895891911093726556915195)
      ·
        refine ⟨20843837866640589835372793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13895891911093726556915195 20843837866640589835372793)
        ·
          refine ⟨15632878399980442376529595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20843837866640589835372793 15632878399980442376529595)
          ·
            refine ⟨23449317599970663564794393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632878399980442376529595 23449317599970663564794393)
            ·
              refine ⟨17586988199977997673595795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23449317599970663564794393 17586988199977997673595795)
              ·
                refine ⟨26380482299966996510393693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17586988199977997673595795 26380482299966996510393693)
                ·
                  refine ⟨9892680862487623691397635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26380482299966996510393693 9892680862487623691397635)
                  ·
                    refine ⟨14839021293731435537096453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892680862487623691397635 14839021293731435537096453)
                    ·
                      refine ⟨2782316492574644163205585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14839021293731435537096453 2782316492574644163205585)
                      ·
                        rfl

theorem cell23_5418542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5418542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418542 prefixEnd_5418542 := by exact prefixLift 5418542
  have htrace : WordTrace (prefixWord ++ tailWord_5418542) baseStart_5418542 baseEnd_5418542 := by
    simpa [prefixWord, tailWord_5418542, baseEnd_5418542] using wordTrace_append hprefix tailTrace_5418542
  have hstable : (prefixWord ++ tailWord_5418542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418542).length < 2 ^ (prefixWord ++ tailWord_5418542).sum := by decide
  have hdescent : baseEnd_5418542 < baseStart_5418542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418556 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_5418556 : Nat := 118140960795 + 5418556 * 2 ^ 59
def prefixEnd_5418556 : Nat := 4983230072969 + 3 ^ 40 * 5418556 * 2
def baseEnd_5418556 : Nat := 927441227101269036143507

theorem tailTrace_5418556 : CollatzResearch.WordTrace tailWord_5418556 prefixEnd_5418556 927441227101269036143507 := by
  unfold tailWord_5418556
  simp only [CollatzResearch.WordTrace]
  refine ⟨98815486678752251266901761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131753982238336335022535681 98815486678752251266901761)
  ·
    refine ⟨74111615009064188450176321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98815486678752251266901761 74111615009064188450176321)
    ·
      refine ⟨55583711256798141337632241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74111615009064188450176321 55583711256798141337632241)
      ·
        refine ⟨41687783442598606003224181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55583711256798141337632241 41687783442598606003224181)
        ·
          refine ⟨3908229697743619312802267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41687783442598606003224181 3908229697743619312802267)
          ·
            refine ⟨5862344546615428969203401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908229697743619312802267 5862344546615428969203401)
            ·
              refine ⟨4396758409961571726902551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862344546615428969203401 4396758409961571726902551)
              ·
                refine ⟨6595137614942357590353827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396758409961571726902551 6595137614942357590353827)
                ·
                  refine ⟨9892706422413536385530741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595137614942357590353827 9892706422413536385530741)
                  ·
                    refine ⟨927441227101269036143507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9892706422413536385530741 927441227101269036143507)
                    ·
                      rfl

theorem cell23_5418556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_5418556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418556 prefixEnd_5418556 := by exact prefixLift 5418556
  have htrace : WordTrace (prefixWord ++ tailWord_5418556) baseStart_5418556 baseEnd_5418556 := by
    simpa [prefixWord, tailWord_5418556, baseEnd_5418556] using wordTrace_append hprefix tailTrace_5418556
  have hstable : (prefixWord ++ tailWord_5418556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418556).length < 2 ^ (prefixWord ++ tailWord_5418556).sum := by decide
  have hdescent : baseEnd_5418556 < baseStart_5418556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418559 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 1, 1, 4]
def baseStart_5418559 : Nat := 118140960795 + 5418559 * 2 ^ 59
def prefixEnd_5418559 : Nat := 4983230072969 + 3 ^ 40 * 5418559 * 2
def baseEnd_5418559 : Nat := 2782325221745770596693007

theorem tailTrace_5418559 : CollatzResearch.WordTrace tailWord_5418559 prefixEnd_5418559 2782325221745770596693007 := by
  unfold tailWord_5418559
  simp only [CollatzResearch.WordTrace]
  refine ⟨197631082776493634046162731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131754055184329089364108487 197631082776493634046162731)
  ·
    refine ⟨296446624164740451069244097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197631082776493634046162731 296446624164740451069244097)
    ·
      refine ⟨222334968123555338301933073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296446624164740451069244097 222334968123555338301933073)
      ·
        refine ⟨166751226092666503726449805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222334968123555338301933073 166751226092666503726449805)
        ·
          refine ⟨62531709784749938897418677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166751226092666503726449805 62531709784749938897418677)
          ·
            refine ⟨5862347792320306771633001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62531709784749938897418677 5862347792320306771633001)
            ·
              refine ⟨4396760844240230078724751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862347792320306771633001 4396760844240230078724751)
              ·
                refine ⟨6595141266360345118087127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396760844240230078724751 6595141266360345118087127)
                ·
                  refine ⟨9892711899540517677130691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595141266360345118087127 9892711899540517677130691)
                  ·
                    refine ⟨14839067849310776515696037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892711899540517677130691 14839067849310776515696037)
                    ·
                      refine ⟨2782325221745770596693007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14839067849310776515696037 2782325221745770596693007)
                      ·
                        rfl

theorem cell23_5418559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_5418559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418559 prefixEnd_5418559 := by exact prefixLift 5418559
  have htrace : WordTrace (prefixWord ++ tailWord_5418559) baseStart_5418559 baseEnd_5418559 := by
    simpa [prefixWord, tailWord_5418559, baseEnd_5418559] using wordTrace_append hprefix tailTrace_5418559
  have hstable : (prefixWord ++ tailWord_5418559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418559).length < 2 ^ (prefixWord ++ tailWord_5418559).sum := by decide
  have hdescent : baseEnd_5418559 < baseStart_5418559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418568 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_5418568 : Nat := 118140960795 + 5418568 * 2 ^ 59
def prefixEnd_5418568 : Nat := 4983230072969 + 3 ^ 40 * 5418568 * 2
def baseEnd_5418568 : Nat := 2782329843071661061480465

theorem tailTrace_5418568 : CollatzResearch.WordTrace tailWord_5418568 prefixEnd_5418568 2782329843071661061480465 := by
  unfold tailWord_5418568
  simp only [CollatzResearch.WordTrace]
  refine ⟨98815705516730514291620179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131754274022307352388826905 98815705516730514291620179)
  ·
    refine ⟨148223558275095771437430269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98815705516730514291620179 148223558275095771437430269)
    ·
      refine ⟨55583834353160914289036351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148223558275095771437430269 55583834353160914289036351)
      ·
        refine ⟨83375751529741371433554527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55583834353160914289036351 83375751529741371433554527)
        ·
          refine ⟨125063627294612057150331791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83375751529741371433554527 125063627294612057150331791)
          ·
            refine ⟨187595440941918085725497687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125063627294612057150331791 187595440941918085725497687)
            ·
              refine ⟨281393161412877128588246531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187595440941918085725497687 281393161412877128588246531)
              ·
                refine ⟨422089742119315692882369797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281393161412877128588246531 422089742119315692882369797)
                ·
                  refine ⟨79141826647371692415444337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422089742119315692882369797 79141826647371692415444337)
                  ·
                    refine ⟨59356369985528769311583253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79141826647371692415444337 59356369985528769311583253)
                    ·
                      refine ⟨2782329843071661061480465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59356369985528769311583253 2782329843071661061480465)
                      ·
                        rfl

theorem cell23_5418568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_5418568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418568 prefixEnd_5418568 := by exact prefixLift 5418568
  have htrace : WordTrace (prefixWord ++ tailWord_5418568) baseStart_5418568 baseEnd_5418568 := by
    simpa [prefixWord, tailWord_5418568, baseEnd_5418568] using wordTrace_append hprefix tailTrace_5418568
  have hstable : (prefixWord ++ tailWord_5418568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418568).length < 2 ^ (prefixWord ++ tailWord_5418568).sum := by decide
  have hdescent : baseEnd_5418568 < baseStart_5418568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418589 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5418589 : Nat := 118140960795 + 5418589 * 2 ^ 59
def prefixEnd_5418589 : Nat := 4983230072969 + 3 ^ 40 * 5418589 * 2
def baseEnd_5418589 : Nat := 2782340626165405479317869

theorem tailTrace_5418589 : CollatzResearch.WordTrace tailWord_5418589 prefixEnd_5418589 2782340626165405479317869 := by
  unfold tailWord_5418589
  simp only [CollatzResearch.WordTrace]
  refine ⟨197632176966384949169754821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131754784644256632779836547 197632176966384949169754821)
  ·
    refine ⟨37056033181197177969329029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197632176966384949169754821 37056033181197177969329029)
    ·
      refine ⟨6948006221474470869249193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37056033181197177969329029 6948006221474470869249193)
      ·
        refine ⟨5211004666105853151936895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6948006221474470869249193 5211004666105853151936895)
        ·
          refine ⟨7816506999158779727905343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211004666105853151936895 7816506999158779727905343)
          ·
            refine ⟨11724760498738169591858015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816506999158779727905343 11724760498738169591858015)
            ·
              refine ⟨17587140748107254387787023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724760498738169591858015 17587140748107254387787023)
              ·
                refine ⟨26380711122160881581680535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17587140748107254387787023 26380711122160881581680535)
                ·
                  refine ⟨39571066683241322372520803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26380711122160881581680535 39571066683241322372520803)
                  ·
                    refine ⟨59356600024861983558781205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39571066683241322372520803 59356600024861983558781205)
                    ·
                      refine ⟨2782340626165405479317869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59356600024861983558781205 2782340626165405479317869)
                      ·
                        rfl

theorem cell23_5418589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5418589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418589 prefixEnd_5418589 := by exact prefixLift 5418589
  have htrace : WordTrace (prefixWord ++ tailWord_5418589) baseStart_5418589 baseEnd_5418589 := by
    simpa [prefixWord, tailWord_5418589, baseEnd_5418589] using wordTrace_append hprefix tailTrace_5418589
  have hstable : (prefixWord ++ tailWord_5418589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418589).length < 2 ^ (prefixWord ++ tailWord_5418589).sum := by decide
  have hdescent : baseEnd_5418589 < baseStart_5418589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418635 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3]
def baseStart_5418635 : Nat := 118140960795 + 5418635 * 2 ^ 59
def prefixEnd_5418635 : Nat := 4983230072969 + 3 ^ 40 * 5418635 * 2
def baseEnd_5418635 : Nat := 2782364246275512299342657

theorem tailTrace_5418635 : CollatzResearch.WordTrace tailWord_5418635 prefixEnd_5418635 2782364246275512299342657 := by
  unfold tailWord_5418635
  simp only [CollatzResearch.WordTrace]
  refine ⟨197633854724218299025929359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131755903149478866017286239 197633854724218299025929359)
  ·
    refine ⟨296450782086327448538894039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197633854724218299025929359 296450782086327448538894039)
    ·
      refine ⟨444676173129491172808341059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296450782086327448538894039 444676173129491172808341059)
      ·
        refine ⟨667014259694236759212511589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444676173129491172808341059 667014259694236759212511589)
        ·
          refine ⟨125065173692669392352345923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 667014259694236759212511589 125065173692669392352345923)
          ·
            refine ⟨187597760539004088528518885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125065173692669392352345923 187597760539004088528518885)
            ·
              refine ⟨35174580101063266599097291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187597760539004088528518885 35174580101063266599097291)
              ·
                refine ⟨52761870151594899898645937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35174580101063266599097291 52761870151594899898645937)
                ·
                  refine ⟨39571402613696174923984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52761870151594899898645937 39571402613696174923984453)
                  ·
                    refine ⟨7419637990068032798247085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39571402613696174923984453 7419637990068032798247085)
                    ·
                      refine ⟨2782364246275512299342657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7419637990068032798247085 2782364246275512299342657)
                      ·
                        rfl

theorem cell23_5418635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].length) (baseStart_5418635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418635 prefixEnd_5418635 := by exact prefixLift 5418635
  have htrace : WordTrace (prefixWord ++ tailWord_5418635) baseStart_5418635 baseEnd_5418635 := by
    simpa [prefixWord, tailWord_5418635, baseEnd_5418635] using wordTrace_append hprefix tailTrace_5418635
  have hstable : (prefixWord ++ tailWord_5418635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418635).length < 2 ^ (prefixWord ++ tailWord_5418635).sum := by decide
  have hdescent : baseEnd_5418635 < baseStart_5418635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418645 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_5418645 : Nat := 118140960795 + 5418645 * 2 ^ 59
def prefixEnd_5418645 : Nat := 4983230072969 + 3 ^ 40 * 5418645 * 2
def baseEnd_5418645 : Nat := 2782369381082057260217611

theorem tailTrace_5418645 : CollatzResearch.WordTrace tailWord_5418645 prefixEnd_5418645 2782369381082057260217611 := by
  unfold tailWord_5418645
  simp only [CollatzResearch.WordTrace]
  refine ⟨197634219454182070733793389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131756146302788047155862259 197634219454182070733793389)
  ·
    refine ⟨74112832295318276525172521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197634219454182070733793389 74112832295318276525172521)
    ·
      refine ⟨55584624221488707393879391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74112832295318276525172521 55584624221488707393879391)
      ·
        refine ⟨83376936332233061090819087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55584624221488707393879391 83376936332233061090819087)
        ·
          refine ⟨125065404498349591636228631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83376936332233061090819087 125065404498349591636228631)
          ·
            refine ⟨187598106747524387454342947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125065404498349591636228631 187598106747524387454342947)
            ·
              refine ⟨281397160121286581181514421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187598106747524387454342947 281397160121286581181514421)
              ·
                refine ⟨26380983761370616985766977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281397160121286581181514421 26380983761370616985766977)
                ·
                  refine ⟨19785737821027962739325233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26380983761370616985766977 19785737821027962739325233)
                  ·
                    refine ⟨14839303365770972054493925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19785737821027962739325233 14839303365770972054493925)
                    ·
                      refine ⟨2782369381082057260217611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14839303365770972054493925 2782369381082057260217611)
                      ·
                        rfl

theorem cell23_5418645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_5418645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418645 prefixEnd_5418645 := by exact prefixLift 5418645
  have htrace : WordTrace (prefixWord ++ tailWord_5418645) baseStart_5418645 baseEnd_5418645 := by
    simpa [prefixWord, tailWord_5418645, baseEnd_5418645] using wordTrace_append hprefix tailTrace_5418645
  have hstable : (prefixWord ++ tailWord_5418645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418645).length < 2 ^ (prefixWord ++ tailWord_5418645).sum := by decide
  have hdescent : baseEnd_5418645 < baseStart_5418645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418670 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5418670 : Nat := 118140960795 + 5418670 * 2 ^ 59
def prefixEnd_5418670 : Nat := 4983230072969 + 3 ^ 40 * 5418670 * 2
def baseEnd_5418670 : Nat := 2782382218098419662404997

theorem tailTrace_5418670 : CollatzResearch.WordTrace tailWord_5418670 prefixEnd_5418670 2782382218098419662404997 := by
  unfold tailWord_5418670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24704391409886437500431683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131756754186061000002302309 24704391409886437500431683)
  ·
    refine ⟨37056587114829656250647525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24704391409886437500431683 37056587114829656250647525)
    ·
      refine ⟨6948110084030560546996411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37056587114829656250647525 6948110084030560546996411)
      ·
        refine ⟨10422165126045840820494617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948110084030560546996411 10422165126045840820494617)
        ·
          refine ⟨7816623844534380615370963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10422165126045840820494617 7816623844534380615370963)
          ·
            refine ⟨11724935766801570923056445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816623844534380615370963 11724935766801570923056445)
            ·
              refine ⟨4396850912550589096146167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11724935766801570923056445 4396850912550589096146167)
              ·
                refine ⟨6595276368825883644219251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396850912550589096146167 6595276368825883644219251)
                ·
                  refine ⟨9892914553238825466328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595276368825883644219251 9892914553238825466328877)
                  ·
                    refine ⟨3709842957464559549873329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9892914553238825466328877 3709842957464559549873329)
                    ·
                      refine ⟨2782382218098419662404997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709842957464559549873329 2782382218098419662404997)
                      ·
                        rfl

theorem cell23_5418670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5418670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418670 prefixEnd_5418670 := by exact prefixLift 5418670
  have htrace : WordTrace (prefixWord ++ tailWord_5418670) baseStart_5418670 baseEnd_5418670 := by
    simpa [prefixWord, tailWord_5418670, baseEnd_5418670] using wordTrace_append hprefix tailTrace_5418670
  have hstable : (prefixWord ++ tailWord_5418670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418670).length < 2 ^ (prefixWord ++ tailWord_5418670).sum := by decide
  have hdescent : baseEnd_5418670 < baseStart_5418670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418695 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_5418695 : Nat := 118140960795 + 5418695 * 2 ^ 59
def prefixEnd_5418695 : Nat := 4983230072969 + 3 ^ 40 * 5418695 * 2
def baseEnd_5418695 : Nat := 2782395055114782064592381

theorem tailTrace_5418695 : CollatzResearch.WordTrace tailWord_5418695 prefixEnd_5418695 2782395055114782064592381 := by
  unfold tailWord_5418695
  simp only [CollatzResearch.WordTrace]
  refine ⟨197636043104000929273113539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131757362069333952848742359 197636043104000929273113539)
  ·
    refine ⟨296454064656001393909670309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197636043104000929273113539 296454064656001393909670309)
    ·
      refine ⟨55585137123000261358063183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296454064656001393909670309 55585137123000261358063183)
      ·
        refine ⟨83377705684500392037094775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55585137123000261358063183 83377705684500392037094775)
        ·
          refine ⟨125066558526750588055642163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83377705684500392037094775 125066558526750588055642163)
          ·
            refine ⟨187599837790125882083463245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125066558526750588055642163 187599837790125882083463245)
            ·
              refine ⟨70349939171297205781298717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187599837790125882083463245 70349939171297205781298717)
              ·
                refine ⟨26381227189236452167987019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70349939171297205781298717 26381227189236452167987019)
                ·
                  refine ⟨39571840783854678251980529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26381227189236452167987019 39571840783854678251980529)
                  ·
                    refine ⟨29678880587891008688985397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39571840783854678251980529 29678880587891008688985397)
                    ·
                      refine ⟨2782395055114782064592381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29678880587891008688985397 2782395055114782064592381)
                      ·
                        rfl

theorem cell23_5418695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_5418695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418695 prefixEnd_5418695 := by exact prefixLift 5418695
  have htrace : WordTrace (prefixWord ++ tailWord_5418695) baseStart_5418695 baseEnd_5418695 := by
    simpa [prefixWord, tailWord_5418695, baseEnd_5418695] using wordTrace_append hprefix tailTrace_5418695
  have hstable : (prefixWord ++ tailWord_5418695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418695).length < 2 ^ (prefixWord ++ tailWord_5418695).sum := by decide
  have hdescent : baseEnd_5418695 < baseStart_5418695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418735 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_5418735 : Nat := 118140960795 + 5418735 * 2 ^ 59
def prefixEnd_5418735 : Nat := 4983230072969 + 3 ^ 40 * 5418735 * 2
def baseEnd_5418735 : Nat := 2782415594340961908092197

theorem tailTrace_5418735 : CollatzResearch.WordTrace tailWord_5418735 prefixEnd_5418735 2782415594340961908092197 := by
  unfold tailWord_5418735
  simp only [CollatzResearch.WordTrace]
  refine ⟨197637502023856016104569659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131758334682570677403046439 197637502023856016104569659)
  ·
    refine ⟨296456253035784024156854489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197637502023856016104569659 296456253035784024156854489)
    ·
      refine ⟨222342189776838018117640867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296456253035784024156854489 222342189776838018117640867)
      ·
        refine ⟨333513284665257027176461301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222342189776838018117640867 333513284665257027176461301)
        ·
          refine ⟨31266870437367846297793247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 333513284665257027176461301 31266870437367846297793247)
          ·
            refine ⟨46900305656051769446689871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31266870437367846297793247 46900305656051769446689871)
            ·
              refine ⟨70350458484077654170034807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46900305656051769446689871 70350458484077654170034807)
              ·
                refine ⟨105525687726116481255052211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70350458484077654170034807 105525687726116481255052211)
                ·
                  refine ⟨158288531589174721882578317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105525687726116481255052211 158288531589174721882578317)
                  ·
                    refine ⟨59358199345940520705966869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158288531589174721882578317 59358199345940520705966869)
                    ·
                      refine ⟨2782415594340961908092197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59358199345940520705966869 2782415594340961908092197)
                      ·
                        rfl

theorem cell23_5418735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_5418735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418735 prefixEnd_5418735 := by exact prefixLift 5418735
  have htrace : WordTrace (prefixWord ++ tailWord_5418735) baseStart_5418735 baseEnd_5418735 := by
    simpa [prefixWord, tailWord_5418735, baseEnd_5418735] using wordTrace_append hprefix tailTrace_5418735
  have hstable : (prefixWord ++ tailWord_5418735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418735).length < 2 ^ (prefixWord ++ tailWord_5418735).sum := by decide
  have hdescent : baseEnd_5418735 < baseStart_5418735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418799 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 2, 3, 2]
def baseStart_5418799 : Nat := 118140960795 + 5418799 * 2 ^ 59
def prefixEnd_5418799 : Nat := 4983230072969 + 3 ^ 40 * 5418799 * 2
def baseEnd_5418799 : Nat := 2782448457102849657691903

theorem tailTrace_5418799 : CollatzResearch.WordTrace tailWord_5418799 prefixEnd_5418799 2782448457102849657691903 := by
  unfold tailWord_5418799
  simp only [CollatzResearch.WordTrace]
  refine ⟨197639836295624155034899451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131759890863749436689932967 197639836295624155034899451)
  ·
    refine ⟨296459754443436232552349177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197639836295624155034899451 296459754443436232552349177)
    ·
      refine ⟨222344815832577174414261883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296459754443436232552349177 222344815832577174414261883)
      ·
        refine ⟨333517223748865761621392825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222344815832577174414261883 333517223748865761621392825)
        ·
          refine ⟨250137917811649321216044619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333517223748865761621392825 250137917811649321216044619)
          ·
            refine ⟨375206876717473981824066929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250137917811649321216044619 375206876717473981824066929)
            ·
              refine ⟨281405157538105486368050197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375206876717473981824066929 281405157538105486368050197)
              ·
                refine ⟨13190866759598694673502353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281405157538105486368050197 13190866759598694673502353)
                ·
                  refine ⟨9893150069699021005126765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13190866759598694673502353 9893150069699021005126765)
                  ·
                    refine ⟨3709931276137132876922537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9893150069699021005126765 3709931276137132876922537)
                    ·
                      refine ⟨2782448457102849657691903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3709931276137132876922537 2782448457102849657691903)
                      ·
                        rfl

theorem cell23_5418799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3, 2].length) (baseStart_5418799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418799 prefixEnd_5418799 := by exact prefixLift 5418799
  have htrace : WordTrace (prefixWord ++ tailWord_5418799) baseStart_5418799 baseEnd_5418799 := by
    simpa [prefixWord, tailWord_5418799, baseEnd_5418799] using wordTrace_append hprefix tailTrace_5418799
  have hstable : (prefixWord ++ tailWord_5418799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418799).length < 2 ^ (prefixWord ++ tailWord_5418799).sum := by decide
  have hdescent : baseEnd_5418799 < baseStart_5418799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418839 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 6]
def baseStart_5418839 : Nat := 118140960795 + 5418839 * 2 ^ 59
def prefixEnd_5418839 : Nat := 4983230072969 + 3 ^ 40 * 5418839 * 2
def baseEnd_5418839 : Nat := 927489665443009833730573

theorem tailTrace_5418839 : CollatzResearch.WordTrace tailWord_5418839 prefixEnd_5418839 927489665443009833730573 := by
  unfold tailWord_5418839
  simp only [CollatzResearch.WordTrace]
  refine ⟨197641295215479241866355571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131760863476986161244237047 197641295215479241866355571)
  ·
    refine ⟨296461942823218862799533357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197641295215479241866355571 296461942823218862799533357)
    ·
      refine ⟨111173228558707073549825009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296461942823218862799533357 111173228558707073549825009)
      ·
        refine ⟨83379921419030305162368757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111173228558707073549825009 83379921419030305162368757)
        ·
          refine ⟨7816867633034091108972071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83379921419030305162368757 7816867633034091108972071)
          ·
            refine ⟨11725301449551136663458107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816867633034091108972071 11725301449551136663458107)
            ·
              refine ⟨17587952174326704995187161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11725301449551136663458107 17587952174326704995187161)
              ·
                refine ⟨13190964130745028746390371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17587952174326704995187161 13190964130745028746390371)
                ·
                  refine ⟨19786446196117543119585557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13190964130745028746390371 19786446196117543119585557)
                  ·
                    refine ⟨927489665443009833730573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19786446196117543119585557 927489665443009833730573)
                    ·
                      rfl

theorem cell23_5418839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_5418839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418839 prefixEnd_5418839 := by exact prefixLift 5418839
  have htrace : WordTrace (prefixWord ++ tailWord_5418839) baseStart_5418839 baseEnd_5418839 := by
    simpa [prefixWord, tailWord_5418839, baseEnd_5418839] using wordTrace_append hprefix tailTrace_5418839
  have hstable : (prefixWord ++ tailWord_5418839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418839).length < 2 ^ (prefixWord ++ tailWord_5418839).sum := by decide
  have hdescent : baseEnd_5418839 < baseStart_5418839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418852 : List Nat := [2, 3, 1, 1, 5, 11]
def baseStart_5418852 : Nat := 118140960795 + 5418852 * 2 ^ 59
def prefixEnd_5418852 : Nat := 4983230072969 + 3 ^ 40 * 5418852 * 2
def baseEnd_5418852 : Nat := 11450517166985752882013

theorem tailTrace_5418852 : CollatzResearch.WordTrace tailWord_5418852 prefixEnd_5418852 11450517166985752882013 := by
  unfold tailWord_5418852
  simp only [CollatzResearch.WordTrace]
  refine ⟨98820884682216072543289405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131761179576288096724385873 98820884682216072543289405)
  ·
    refine ⟨37057831755831027203733527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98820884682216072543289405 37057831755831027203733527)
    ·
      refine ⟨55586747633746540805600291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37057831755831027203733527 55586747633746540805600291)
      ·
        refine ⟨83380121450619811208400437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55586747633746540805600291 83380121450619811208400437)
        ·
          refine ⟨7816886385995607300787541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83380121450619811208400437 7816886385995607300787541)
          ·
            refine ⟨11450517166985752882013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7816886385995607300787541 11450517166985752882013)
            ·
              rfl

theorem cell23_5418852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 11].length) (baseStart_5418852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418852 prefixEnd_5418852 := by exact prefixLift 5418852
  have htrace : WordTrace (prefixWord ++ tailWord_5418852) baseStart_5418852 baseEnd_5418852 := by
    simpa [prefixWord, tailWord_5418852, baseEnd_5418852] using wordTrace_append hprefix tailTrace_5418852
  have hstable : (prefixWord ++ tailWord_5418852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418852).length < 2 ^ (prefixWord ++ tailWord_5418852).sum := by decide
  have hdescent : baseEnd_5418852 < baseStart_5418852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418856 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_5418856 : Nat := 118140960795 + 5418856 * 2 ^ 59
def prefixEnd_5418856 : Nat := 4983230072969 + 3 ^ 40 * 5418856 * 2
def baseEnd_5418856 : Nat := 927492575166718644893047

theorem tailTrace_5418856 : CollatzResearch.WordTrace tailWord_5418856 prefixEnd_5418856 927492575166718644893047 := by
  unfold tailWord_5418856
  simp only [CollatzResearch.WordTrace]
  refine ⟨98820957628208826884862211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131761276837611769179816281 98820957628208826884862211)
  ·
    refine ⟨148231436442313240327293317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98820957628208826884862211 148231436442313240327293317)
    ·
      refine ⟨27793394332933732561367497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148231436442313240327293317 27793394332933732561367497)
      ·
        refine ⟨20845045749700299421025623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27793394332933732561367497 20845045749700299421025623)
        ·
          refine ⟨31267568624550449131538435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20845045749700299421025623 31267568624550449131538435)
          ·
            refine ⟨46901352936825673697307653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31267568624550449131538435 46901352936825673697307653)
            ·
              refine ⟨8794003675654813818245185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46901352936825673697307653 8794003675654813818245185)
              ·
                refine ⟨6595502756741110363683889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8794003675654813818245185 6595502756741110363683889)
                ·
                  refine ⟨4946627067555832772762917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6595502756741110363683889 4946627067555832772762917)
                  ·
                    refine ⟨927492575166718644893047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946627067555832772762917 927492575166718644893047)
                    ·
                      rfl

theorem cell23_5418856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_5418856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418856 prefixEnd_5418856 := by exact prefixLift 5418856
  have htrace : WordTrace (prefixWord ++ tailWord_5418856) baseStart_5418856 baseEnd_5418856 := by
    simpa [prefixWord, tailWord_5418856, baseEnd_5418856] using wordTrace_append hprefix tailTrace_5418856
  have hstable : (prefixWord ++ tailWord_5418856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418856).length < 2 ^ (prefixWord ++ tailWord_5418856).sum := by decide
  have hdescent : baseEnd_5418856 < baseStart_5418856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418879 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_5418879 : Nat := 118140960795 + 5418879 * 2 ^ 59
def prefixEnd_5418879 : Nat := 4983230072969 + 3 ^ 40 * 5418879 * 2
def baseEnd_5418879 : Nat := 2782489535555209344691535

theorem tailTrace_5418879 : CollatzResearch.WordTrace tailWord_5418879 prefixEnd_5418879 2782489535555209344691535 := by
  unfold tailWord_5418879
  simp only [CollatzResearch.WordTrace]
  refine ⟨197642754135334328697811691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131761836090222885798541127 197642754135334328697811691)
  ·
    refine ⟨296464131203001493046717537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197642754135334328697811691 296464131203001493046717537)
    ·
      refine ⟨222348098402251119785038153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296464131203001493046717537 222348098402251119785038153)
      ·
        refine ⟨166761073801688339838778615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222348098402251119785038153 166761073801688339838778615)
        ·
          refine ⟨250141610702532509758167923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166761073801688339838778615 250141610702532509758167923)
          ·
            refine ⟨375212416053798764637251885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250141610702532509758167923 375212416053798764637251885)
            ·
              refine ⟨140704656020174536738969457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375212416053798764637251885 140704656020174536738969457)
              ·
                refine ⟨105528492015130902554227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140704656020174536738969457 105528492015130902554227093)
                ·
                  refine ⟨4946648063209261057229395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105528492015130902554227093 4946648063209261057229395)
                  ·
                    refine ⟨7419972094813891585844093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946648063209261057229395 7419972094813891585844093)
                    ·
                      refine ⟨2782489535555209344691535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7419972094813891585844093 2782489535555209344691535)
                      ·
                        rfl

theorem cell23_5418879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_5418879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418879 prefixEnd_5418879 := by exact prefixLift 5418879
  have htrace : WordTrace (prefixWord ++ tailWord_5418879) baseStart_5418879 baseEnd_5418879 := by
    simpa [prefixWord, tailWord_5418879, baseEnd_5418879] using wordTrace_append hprefix tailTrace_5418879
  have hstable : (prefixWord ++ tailWord_5418879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418879).length < 2 ^ (prefixWord ++ tailWord_5418879).sum := by decide
  have hdescent : baseEnd_5418879 < baseStart_5418879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418892 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5418892 : Nat := 118140960795 + 5418892 * 2 ^ 59
def prefixEnd_5418892 : Nat := 4983230072969 + 3 ^ 40 * 5418892 * 2
def baseEnd_5418892 : Nat := 2782496210803717793828975

theorem tailTrace_5418892 : CollatzResearch.WordTrace tailWord_5418892 prefixEnd_5418892 2782496210803717793828975 := by
  unfold tailWord_5418892
  simp only [CollatzResearch.WordTrace]
  refine ⟨98821614142143615959017465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131762152189524821278689953 98821614142143615959017465)
  ·
    refine ⟨74116210606607711969263099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98821614142143615959017465 74116210606607711969263099)
    ·
      refine ⟨111174315909911567953894649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74116210606607711969263099 111174315909911567953894649)
      ·
        refine ⟨83380736932433675965420987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111174315909911567953894649 83380736932433675965420987)
        ·
          refine ⟨125071105398650513948131481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83380736932433675965420987 125071105398650513948131481)
          ·
            refine ⟨93803329048987885461098611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125071105398650513948131481 93803329048987885461098611)
            ·
              refine ⟨140704993573481828191647917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93803329048987885461098611 140704993573481828191647917)
              ·
                refine ⟨52764372590055685571867969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140704993573481828191647917 52764372590055685571867969)
                ·
                  refine ⟨39573279442541764178900977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52764372590055685571867969 39573279442541764178900977)
                  ·
                    refine ⟨29679959581906323134175733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39573279442541764178900977 29679959581906323134175733)
                    ·
                      refine ⟨2782496210803717793828975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29679959581906323134175733 2782496210803717793828975)
                      ·
                        rfl

theorem cell23_5418892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5418892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418892 prefixEnd_5418892 := by exact prefixLift 5418892
  have htrace : WordTrace (prefixWord ++ tailWord_5418892) baseStart_5418892 baseEnd_5418892 := by
    simpa [prefixWord, tailWord_5418892, baseEnd_5418892] using wordTrace_append hprefix tailTrace_5418892
  have hstable : (prefixWord ++ tailWord_5418892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418892).length < 2 ^ (prefixWord ++ tailWord_5418892).sum := by decide
  have hdescent : baseEnd_5418892 < baseStart_5418892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418900 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5418900 : Nat := 118140960795 + 5418900 * 2 ^ 59
def prefixEnd_5418900 : Nat := 4983230072969 + 3 ^ 40 * 5418900 * 2
def baseEnd_5418900 : Nat := 2782500318648953762528939

theorem tailTrace_5418900 : CollatzResearch.WordTrace tailWord_5418900 prefixEnd_5418900 2782500318648953762528939 := by
  unfold tailWord_5418900
  simp only [CollatzResearch.WordTrace]
  refine ⟨98821760034129124642163077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131762346712172166189550769 98821760034129124642163077)
  ·
    refine ⟨18529080006399210870405577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98821760034129124642163077 18529080006399210870405577)
    ·
      refine ⟨13896810004799408152804183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18529080006399210870405577 13896810004799408152804183)
      ·
        refine ⟨20845215007199112229206275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896810004799408152804183 20845215007199112229206275)
        ·
          refine ⟨31267822510798668343809413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20845215007199112229206275 31267822510798668343809413)
          ·
            refine ⟨5862716720774750314464265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31267822510798668343809413 5862716720774750314464265)
            ·
              refine ⟨4397037540581062735848199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862716720774750314464265 4397037540581062735848199)
              ·
                refine ⟨6595556310871594103772299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397037540581062735848199 6595556310871594103772299)
                ·
                  refine ⟨9893334466307391155658449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595556310871594103772299 9893334466307391155658449)
                  ·
                    refine ⟨7420000849730543366743837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9893334466307391155658449 7420000849730543366743837)
                    ·
                      refine ⟨2782500318648953762528939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420000849730543366743837 2782500318648953762528939)
                      ·
                        rfl

theorem cell23_5418900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5418900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418900 prefixEnd_5418900 := by exact prefixLift 5418900
  have htrace : WordTrace (prefixWord ++ tailWord_5418900) baseStart_5418900 baseEnd_5418900 := by
    simpa [prefixWord, tailWord_5418900, baseEnd_5418900] using wordTrace_append hprefix tailTrace_5418900
  have hstable : (prefixWord ++ tailWord_5418900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418900).length < 2 ^ (prefixWord ++ tailWord_5418900).sum := by decide
  have hdescent : baseEnd_5418900 < baseStart_5418900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418913 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5418913 : Nat := 118140960795 + 5418913 * 2 ^ 59
def prefixEnd_5418913 : Nat := 4983230072969 + 3 ^ 40 * 5418913 * 2
def baseEnd_5418913 : Nat := 2782506993897462211666379

theorem tailTrace_5418913 : CollatzResearch.WordTrace tailWord_5418913 prefixEnd_5418913 2782506993897462211666379 := by
  unfold tailWord_5418913
  simp only [CollatzResearch.WordTrace]
  refine ⟨197643994217211152504549393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131762662811474101669699595 197643994217211152504549393)
  ·
    refine ⟨148232995662908364378412045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197643994217211152504549393 148232995662908364378412045)
    ·
      refine ⟨55587373373590636641904517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148232995662908364378412045 55587373373590636641904517)
      ·
        refine ⟨10422632507548244370357097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55587373373590636641904517 10422632507548244370357097)
        ·
          refine ⟨7816974380661183277767823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10422632507548244370357097 7816974380661183277767823)
          ·
            refine ⟨11725461570991774916651735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816974380661183277767823 11725461570991774916651735)
            ·
              refine ⟨17588192356487662374977603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11725461570991774916651735 17588192356487662374977603)
              ·
                refine ⟨26382288534731493562466405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17588192356487662374977603 26382288534731493562466405)
                ·
                  refine ⟨4946679100262155042962451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26382288534731493562466405 4946679100262155042962451)
                  ·
                    refine ⟨7420018650393232564443677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946679100262155042962451 7420018650393232564443677)
                    ·
                      refine ⟨2782506993897462211666379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420018650393232564443677 2782506993897462211666379)
                      ·
                        rfl

theorem cell23_5418913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5418913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418913 prefixEnd_5418913 := by exact prefixLift 5418913
  have htrace : WordTrace (prefixWord ++ tailWord_5418913) baseStart_5418913 baseEnd_5418913 := by
    simpa [prefixWord, tailWord_5418913, baseEnd_5418913] using wordTrace_append hprefix tailTrace_5418913
  have hstable : (prefixWord ++ tailWord_5418913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418913).length < 2 ^ (prefixWord ++ tailWord_5418913).sum := by decide
  have hdescent : baseEnd_5418913 < baseStart_5418913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5418929 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_5418929 : Nat := 118140960795 + 5418929 * 2 ^ 59
def prefixEnd_5418929 : Nat := 4983230072969 + 3 ^ 40 * 5418929 * 2
def baseEnd_5418929 : Nat := 927505069862644716355435

theorem tailTrace_5418929 : CollatzResearch.WordTrace tailWord_5418929 prefixEnd_5418929 927505069862644716355435 := by
  unfold tailWord_5418929
  simp only [CollatzResearch.WordTrace]
  refine ⟨197644577785153187237131841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131763051856768791491421227 197644577785153187237131841)
  ·
    refine ⟨148233433338864890427848881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197644577785153187237131841 148233433338864890427848881)
    ·
      refine ⟨111175075004148667820886661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148233433338864890427848881 111175075004148667820886661)
      ·
        refine ⟨20845326563277875216416249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111175075004148667820886661 20845326563277875216416249)
        ·
          refine ⟨15633994922458406412312187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20845326563277875216416249 15633994922458406412312187)
          ·
            refine ⟨23450992383687609618468281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15633994922458406412312187 23450992383687609618468281)
            ·
              refine ⟨17588244287765707213851211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23450992383687609618468281 17588244287765707213851211)
              ·
                refine ⟨26382366431648560820776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17588244287765707213851211 26382366431648560820776817)
                ·
                  refine ⟨19786774823736420615582613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26382366431648560820776817 19786774823736420615582613)
                  ·
                    refine ⟨927505069862644716355435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19786774823736420615582613 927505069862644716355435)
                    ·
                      rfl

theorem cell23_5418929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_5418929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5418929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5418929 prefixEnd_5418929 := by exact prefixLift 5418929
  have htrace : WordTrace (prefixWord ++ tailWord_5418929) baseStart_5418929 baseEnd_5418929 := by
    simpa [prefixWord, tailWord_5418929, baseEnd_5418929] using wordTrace_append hprefix tailTrace_5418929
  have hstable : (prefixWord ++ tailWord_5418929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5418929).length < 2 ^ (prefixWord ++ tailWord_5418929).sum := by decide
  have hdescent : baseEnd_5418929 < baseStart_5418929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5418929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419021 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5419021 : Nat := 118140960795 + 5419021 * 2 ^ 59
def prefixEnd_5419021 : Nat := 4983230072969 + 3 ^ 40 * 5419021 * 2
def baseEnd_5419021 : Nat := 2782562449808147789115883

theorem tailTrace_5419021 : CollatzResearch.WordTrace tailWord_5419021 prefixEnd_5419021 2782562449808147789115883 := by
  unfold tailWord_5419021
  simp only [CollatzResearch.WordTrace]
  refine ⟨197647933300819886949480917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131765288867213257966320611 197647933300819886949480917)
  ·
    refine ⟨4632373436737966100378459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 197647933300819886949480917 4632373436737966100378459)
    ·
      refine ⟨6948560155106949150567689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4632373436737966100378459 6948560155106949150567689)
      ·
        refine ⟨5211420116330211862925767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6948560155106949150567689 5211420116330211862925767)
        ·
          refine ⟨7817130174495317794388651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211420116330211862925767 7817130174495317794388651)
          ·
            refine ⟨11725695261742976691582977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817130174495317794388651 11725695261742976691582977)
            ·
              refine ⟨8794271446307232518687233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11725695261742976691582977 8794271446307232518687233)
              ·
                refine ⟨6595703584730424389015425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8794271446307232518687233 6595703584730424389015425)
                ·
                  refine ⟨4946777688547818291761569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6595703584730424389015425 4946777688547818291761569)
                  ·
                    refine ⟨3710083266410863718821177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4946777688547818291761569 3710083266410863718821177)
                    ·
                      refine ⟨2782562449808147789115883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710083266410863718821177 2782562449808147789115883)
                      ·
                        rfl

theorem cell23_5419021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5419021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419021 prefixEnd_5419021 := by exact prefixLift 5419021
  have htrace : WordTrace (prefixWord ++ tailWord_5419021) baseStart_5419021 baseEnd_5419021 := by
    simpa [prefixWord, tailWord_5419021, baseEnd_5419021] using wordTrace_append hprefix tailTrace_5419021
  have hstable : (prefixWord ++ tailWord_5419021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419021).length < 2 ^ (prefixWord ++ tailWord_5419021).sum := by decide
  have hdescent : baseEnd_5419021 < baseStart_5419021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419093 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_5419093 : Nat := 118140960795 + 5419093 * 2 ^ 59
def prefixEnd_5419093 : Nat := 4983230072969 + 3 ^ 40 * 5419093 * 2
def baseEnd_5419093 : Nat := 2782599420415271507415551

theorem tailTrace_5419093 : CollatzResearch.WordTrace tailWord_5419093 prefixEnd_5419093 2782599420415271507415551 := by
  unfold tailWord_5419093
  simp only [CollatzResearch.WordTrace]
  refine ⟨197650559356559043246101933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131767039571039362164067955 197650559356559043246101933)
  ·
    refine ⟨74118959758709641217288225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197650559356559043246101933 74118959758709641217288225)
    ·
      refine ⟨55589219819032230912966169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74118959758709641217288225 55589219819032230912966169)
      ·
        refine ⟨41691914864274173184724627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55589219819032230912966169 41691914864274173184724627)
        ·
          refine ⟨62537872296411259777086941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41691914864274173184724627 62537872296411259777086941)
          ·
            refine ⟨23451702111154222416407603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62537872296411259777086941 23451702111154222416407603)
            ·
              refine ⟨35177553166731333624611405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23451702111154222416407603 35177553166731333624611405)
              ·
                refine ⟨13191582437524250109229277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35177553166731333624611405 13191582437524250109229277)
                ·
                  refine ⟨4946843414071593790960979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13191582437524250109229277 4946843414071593790960979)
                  ·
                    refine ⟨7420265121107390686441469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946843414071593790960979 7420265121107390686441469)
                    ·
                      refine ⟨2782599420415271507415551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420265121107390686441469 2782599420415271507415551)
                      ·
                        rfl

theorem cell23_5419093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_5419093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419093 prefixEnd_5419093 := by exact prefixLift 5419093
  have htrace : WordTrace (prefixWord ++ tailWord_5419093) baseStart_5419093 baseEnd_5419093 := by
    simpa [prefixWord, tailWord_5419093, baseEnd_5419093] using wordTrace_append hprefix tailTrace_5419093
  have hstable : (prefixWord ++ tailWord_5419093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419093).length < 2 ^ (prefixWord ++ tailWord_5419093).sum := by decide
  have hdescent : baseEnd_5419093 < baseStart_5419093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419127 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_5419127 : Nat := 118140960795 + 5419127 * 2 ^ 59
def prefixEnd_5419127 : Nat := 4983230072969 + 3 ^ 40 * 5419127 * 2
def baseEnd_5419127 : Nat := 2782616878757524374390395

theorem tailTrace_5419127 : CollatzResearch.WordTrace tailWord_5419127 prefixEnd_5419127 2782616878757524374390395 := by
  unfold tailWord_5419127
  simp only [CollatzResearch.WordTrace]
  refine ⟨197651799438435867052839635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131767866292290578035226423 197651799438435867052839635)
  ·
    refine ⟨296477699157653800579259453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197651799438435867052839635 296477699157653800579259453)
    ·
      refine ⟨111179137184120175217222295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296477699157653800579259453 111179137184120175217222295)
      ·
        refine ⟨166768705776180262825833443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111179137184120175217222295 166768705776180262825833443)
        ·
          refine ⟨250153058664270394238750165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166768705776180262825833443 250153058664270394238750165)
          ·
            refine ⟨5862962312443837364970707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 250153058664270394238750165 5862962312443837364970707)
            ·
              refine ⟨8794443468665756047456061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862962312443837364970707 8794443468665756047456061)
              ·
                refine ⟨3297916300749658517796023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8794443468665756047456061 3297916300749658517796023)
                ·
                  refine ⟨4946874451124487776694035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297916300749658517796023 4946874451124487776694035)
                  ·
                    refine ⟨7420311676686731665041053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946874451124487776694035 7420311676686731665041053)
                    ·
                      refine ⟨2782616878757524374390395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420311676686731665041053 2782616878757524374390395)
                      ·
                        rfl

theorem cell23_5419127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_5419127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419127 prefixEnd_5419127 := by exact prefixLift 5419127
  have htrace : WordTrace (prefixWord ++ tailWord_5419127) baseStart_5419127 baseEnd_5419127 := by
    simpa [prefixWord, tailWord_5419127, baseEnd_5419127] using wordTrace_append hprefix tailTrace_5419127
  have hstable : (prefixWord ++ tailWord_5419127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419127).length < 2 ^ (prefixWord ++ tailWord_5419127).sum := by decide
  have hdescent : baseEnd_5419127 < baseStart_5419127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419133 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_5419133 : Nat := 118140960795 + 5419133 * 2 ^ 59
def prefixEnd_5419133 : Nat := 4983230072969 + 3 ^ 40 * 5419133 * 2
def baseEnd_5419133 : Nat := 2782619959641451350915367

theorem tailTrace_5419133 : CollatzResearch.WordTrace tailWord_5419133 prefixEnd_5419133 2782619959641451350915367 := by
  unfold tailWord_5419133
  simp only [CollatzResearch.WordTrace]
  refine ⟨197652018276414130077558053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131768012184276086718372035 197652018276414130077558053)
  ·
    refine ⟨37059753426827649389542135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197652018276414130077558053 37059753426827649389542135)
    ·
      refine ⟨55589630140241474084313203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37059753426827649389542135 55589630140241474084313203)
      ·
        refine ⟨83384445210362211126469805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55589630140241474084313203 83384445210362211126469805)
        ·
          refine ⟨31269166953885829172426177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83384445210362211126469805 31269166953885829172426177)
          ·
            refine ⟨23451875215414371879319633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31269166953885829172426177 23451875215414371879319633)
            ·
              refine ⟨17588906411560778909489725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23451875215414371879319633 17588906411560778909489725)
              ·
                refine ⟨6595839904335292091058647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17588906411560778909489725 6595839904335292091058647)
                ·
                  refine ⟨9893759856502938136587971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595839904335292091058647 9893759856502938136587971)
                  ·
                    refine ⟨14840639784754407204881957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9893759856502938136587971 14840639784754407204881957)
                    ·
                      refine ⟨2782619959641451350915367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14840639784754407204881957 2782619959641451350915367)
                      ·
                        rfl

theorem cell23_5419133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_5419133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419133 prefixEnd_5419133 := by exact prefixLift 5419133
  have htrace : WordTrace (prefixWord ++ tailWord_5419133) baseStart_5419133 baseEnd_5419133 := by
    simpa [prefixWord, tailWord_5419133, baseEnd_5419133] using wordTrace_append hprefix tailTrace_5419133
  have hstable : (prefixWord ++ tailWord_5419133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419133).length < 2 ^ (prefixWord ++ tailWord_5419133).sum := by decide
  have hdescent : baseEnd_5419133 < baseStart_5419133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419136 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_5419136 : Nat := 118140960795 + 5419136 * 2 ^ 59
def prefixEnd_5419136 : Nat := 4983230072969 + 3 ^ 40 * 5419136 * 2
def baseEnd_5419136 : Nat := 2782621500083414839177853

theorem tailTrace_5419136 : CollatzResearch.WordTrace tailWord_5419136 prefixEnd_5419136 2782621500083414839177853 := by
  unfold tailWord_5419136
  simp only [CollatzResearch.WordTrace]
  refine ⟨98826063847701630794958631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131768085130268841059944841 98826063847701630794958631)
  ·
    refine ⟨148239095771552446192437947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98826063847701630794958631 148239095771552446192437947)
    ·
      refine ⟨222358643657328669288656921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148239095771552446192437947 222358643657328669288656921)
      ·
        refine ⟨166768982742996501966492691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222358643657328669288656921 166768982742996501966492691)
        ·
          refine ⟨250153474114494752949739037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166768982742996501966492691 250153474114494752949739037)
          ·
            refine ⟨93807552792935532356152139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250153474114494752949739037 93807552792935532356152139)
            ·
              refine ⟨140711329189403298534228209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93807552792935532356152139 140711329189403298534228209)
              ·
                refine ⟨105533496892052473900671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140711329189403298534228209 105533496892052473900671157)
                ·
                  refine ⟨9893765333629919428187921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105533496892052473900671157 9893765333629919428187921)
                  ·
                    refine ⟨7420324000222439571140941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9893765333629919428187921 7420324000222439571140941)
                    ·
                      refine ⟨2782621500083414839177853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420324000222439571140941 2782621500083414839177853)
                      ·
                        rfl

theorem cell23_5419136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_5419136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419136 prefixEnd_5419136 := by exact prefixLift 5419136
  have htrace : WordTrace (prefixWord ++ tailWord_5419136) baseStart_5419136 baseEnd_5419136 := by
    simpa [prefixWord, tailWord_5419136, baseEnd_5419136] using wordTrace_append hprefix tailTrace_5419136
  have hstable : (prefixWord ++ tailWord_5419136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419136).length < 2 ^ (prefixWord ++ tailWord_5419136).sum := by decide
  have hdescent : baseEnd_5419136 < baseStart_5419136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419139 : List Nat := [1, 1, 1, 3, 3, 3, 11]
def baseStart_5419139 : Nat := 118140960795 + 5419139 * 2 ^ 59
def prefixEnd_5419139 : Nat := 4983230072969 + 3 ^ 40 * 5419139 * 2
def baseEnd_5419139 : Nat := 34353370870683683054819

theorem tailTrace_5419139 : CollatzResearch.WordTrace tailWord_5419139 prefixEnd_5419139 34353370870683683054819 := by
  unfold tailWord_5419139
  simp only [CollatzResearch.WordTrace]
  refine ⟨197652237114392393102276471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131768158076261595401517647 197652237114392393102276471)
  ·
    refine ⟨296478355671588589653414707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197652237114392393102276471 296478355671588589653414707)
    ·
      refine ⟨444717533507382884480122061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296478355671588589653414707 444717533507382884480122061)
      ·
        refine ⟨166769075065268581680045773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444717533507382884480122061 166769075065268581680045773)
        ·
          refine ⟨62538403149475718130017165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166769075065268581680045773 62538403149475718130017165)
          ·
            refine ⟨23451901181053394298756437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62538403149475718130017165 23451901181053394298756437)
            ·
              refine ⟨34353370870683683054819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23451901181053394298756437 34353370870683683054819)
              ·
                rfl

theorem cell23_5419139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 11].length) (baseStart_5419139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419139 prefixEnd_5419139 := by exact prefixLift 5419139
  have htrace : WordTrace (prefixWord ++ tailWord_5419139) baseStart_5419139 baseEnd_5419139 := by
    simpa [prefixWord, tailWord_5419139, baseEnd_5419139] using wordTrace_append hprefix tailTrace_5419139
  have hstable : (prefixWord ++ tailWord_5419139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419139).length < 2 ^ (prefixWord ++ tailWord_5419139).sum := by decide
  have hdescent : baseEnd_5419139 < baseStart_5419139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419144 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5419144 : Nat := 118140960795 + 5419144 * 2 ^ 59
def prefixEnd_5419144 : Nat := 4983230072969 + 3 ^ 40 * 5419144 * 2
def baseEnd_5419144 : Nat := 2782625607928650807877817

theorem tailTrace_5419144 : CollatzResearch.WordTrace tailWord_5419144 prefixEnd_5419144 2782625607928650807877817 := by
  unfold tailWord_5419144
  simp only [CollatzResearch.WordTrace]
  refine ⟨98826209739687139478104243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131768279652916185970805657 98826209739687139478104243)
  ·
    refine ⟨148239314609530709217156365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98826209739687139478104243 148239314609530709217156365)
    ·
      refine ⟨55589742978574015956433637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148239314609530709217156365 55589742978574015956433637)
      ·
        refine ⟨10423076808482627991831307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55589742978574015956433637 10423076808482627991831307)
        ·
          refine ⟨15634615212723941987746961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10423076808482627991831307 15634615212723941987746961)
          ·
            refine ⟨11725961409542956490810221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15634615212723941987746961 11725961409542956490810221)
            ·
              refine ⟨4397235528578608684053833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11725961409542956490810221 4397235528578608684053833)
              ·
                refine ⟨3297926646433956513040375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397235528578608684053833 3297926646433956513040375)
                ·
                  refine ⟨4946889969650934769560563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297926646433956513040375 4946889969650934769560563)
                  ·
                    refine ⟨7420334954476402154340845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946889969650934769560563 7420334954476402154340845)
                    ·
                      refine ⟨2782625607928650807877817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420334954476402154340845 2782625607928650807877817)
                      ·
                        rfl

theorem cell23_5419144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5419144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419144 prefixEnd_5419144 := by exact prefixLift 5419144
  have htrace : WordTrace (prefixWord ++ tailWord_5419144) baseStart_5419144 baseEnd_5419144 := by
    simpa [prefixWord, tailWord_5419144, baseEnd_5419144] using wordTrace_append hprefix tailTrace_5419144
  have hstable : (prefixWord ++ tailWord_5419144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419144).length < 2 ^ (prefixWord ++ tailWord_5419144).sum := by decide
  have hdescent : baseEnd_5419144 < baseStart_5419144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419146 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5419146 : Nat := 118140960795 + 5419146 * 2 ^ 59
def prefixEnd_5419146 : Nat := 4983230072969 + 3 ^ 40 * 5419146 * 2
def baseEnd_5419146 : Nat := 2782626634889959800052807

theorem tailTrace_5419146 : CollatzResearch.WordTrace tailWord_5419146 prefixEnd_5419146 2782626634889959800052807 := by
  unfold tailWord_5419146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413123106341758324445323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131768328283578022198520861 49413123106341758324445323)
  ·
    refine ⟨74119684659512637486667985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49413123106341758324445323 74119684659512637486667985)
    ·
      refine ⟨55589763494634478115000989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74119684659512637486667985 55589763494634478115000989)
      ·
        refine ⟨20846161310487929293125371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55589763494634478115000989 20846161310487929293125371)
        ·
          refine ⟨31269241965731893939688057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20846161310487929293125371 31269241965731893939688057)
          ·
            refine ⟨23451931474298920454766043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31269241965731893939688057 23451931474298920454766043)
            ·
              refine ⟨35177897211448380682149065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23451931474298920454766043 35177897211448380682149065)
              ·
                refine ⟨26383422908586285511611799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35177897211448380682149065 26383422908586285511611799)
                ·
                  refine ⟨39575134362879428267417699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26383422908586285511611799 39575134362879428267417699)
                  ·
                    refine ⟨59362701544319142401126549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39575134362879428267417699 59362701544319142401126549)
                    ·
                      refine ⟨2782626634889959800052807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59362701544319142401126549 2782626634889959800052807)
                      ·
                        rfl

theorem cell23_5419146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5419146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419146 prefixEnd_5419146 := by exact prefixLift 5419146
  have htrace : WordTrace (prefixWord ++ tailWord_5419146) baseStart_5419146 baseEnd_5419146 := by
    simpa [prefixWord, tailWord_5419146, baseEnd_5419146] using wordTrace_append hprefix tailTrace_5419146
  have hstable : (prefixWord ++ tailWord_5419146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419146).length < 2 ^ (prefixWord ++ tailWord_5419146).sum := by decide
  have hdescent : baseEnd_5419146 < baseStart_5419146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419160 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_5419160 : Nat := 118140960795 + 5419160 * 2 ^ 59
def prefixEnd_5419160 : Nat := 4983230072969 + 3 ^ 40 * 5419160 * 2
def baseEnd_5419160 : Nat := 927544607873040915092581

theorem tailTrace_5419160 : CollatzResearch.WordTrace tailWord_5419160 prefixEnd_5419160 927544607873040915092581 := by
  unfold tailWord_5419160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98826501523658156844395467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131768668698210875792527289 98826501523658156844395467)
  ·
    refine ⟨148239752285487235266593201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98826501523658156844395467 148239752285487235266593201)
    ·
      refine ⟨111179814214115426449944901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148239752285487235266593201 111179814214115426449944901)
      ·
        refine ⟨20846215165146642459364669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111179814214115426449944901 20846215165146642459364669)
        ·
          refine ⟨7817330686929990922261751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20846215165146642459364669 7817330686929990922261751)
          ·
            refine ⟨11725996030394986383392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817330686929990922261751 11725996030394986383392627)
            ·
              refine ⟨17588994045592479575088941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11725996030394986383392627 17588994045592479575088941)
              ·
                refine ⟨6595872767097179840658353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17588994045592479575088941 6595872767097179840658353)
                ·
                  refine ⟨4946904575322884880493765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6595872767097179840658353 4946904575322884880493765)
                  ·
                    refine ⟨927544607873040915092581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946904575322884880493765 927544607873040915092581)
                    ·
                      rfl

theorem cell23_5419160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_5419160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419160 prefixEnd_5419160 := by exact prefixLift 5419160
  have htrace : WordTrace (prefixWord ++ tailWord_5419160) baseStart_5419160 baseEnd_5419160 := by
    simpa [prefixWord, tailWord_5419160, baseEnd_5419160] using wordTrace_append hprefix tailTrace_5419160
  have hstable : (prefixWord ++ tailWord_5419160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419160).length < 2 ^ (prefixWord ++ tailWord_5419160).sum := by decide
  have hdescent : baseEnd_5419160 < baseStart_5419160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419170 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5419170 : Nat := 118140960795 + 5419170 * 2 ^ 59
def prefixEnd_5419170 : Nat := 4983230072969 + 3 ^ 40 * 5419170 * 2
def baseEnd_5419170 : Nat := 2782638958425667706152697

theorem tailTrace_5419170 : CollatzResearch.WordTrace tailWord_5419170 prefixEnd_5419170 2782638958425667706152697 := by
  unfold tailWord_5419170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413341944320021349163741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131768911851520056931103309 49413341944320021349163741)
  ·
    refine ⟨18530003229120008005936403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49413341944320021349163741 18530003229120008005936403)
    ·
      refine ⟨27795004843680012008904605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18530003229120008005936403 27795004843680012008904605)
      ·
        refine ⟨10423126816380004503339227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27795004843680012008904605 10423126816380004503339227)
        ·
          refine ⟨15634690224570006755008841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10423126816380004503339227 15634690224570006755008841)
          ·
            refine ⟨11726017668427505066256631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15634690224570006755008841 11726017668427505066256631)
            ·
              refine ⟨17589026502641257599384947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11726017668427505066256631 17589026502641257599384947)
              ·
                refine ⟨26383539753961886399077421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17589026502641257599384947 26383539753961886399077421)
                ·
                  refine ⟨9893827407735707399654033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26383539753961886399077421 9893827407735707399654033)
                  ·
                    refine ⟨7420370555801780549740525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9893827407735707399654033 7420370555801780549740525)
                    ·
                      refine ⟨2782638958425667706152697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420370555801780549740525 2782638958425667706152697)
                      ·
                        rfl

theorem cell23_5419170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5419170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419170 prefixEnd_5419170 := by exact prefixLift 5419170
  have htrace : WordTrace (prefixWord ++ tailWord_5419170) baseStart_5419170 baseEnd_5419170 := by
    simpa [prefixWord, tailWord_5419170, baseEnd_5419170] using wordTrace_append hprefix tailTrace_5419170
  have hstable : (prefixWord ++ tailWord_5419170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419170).length < 2 ^ (prefixWord ++ tailWord_5419170).sum := by decide
  have hdescent : baseEnd_5419170 < baseStart_5419170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419179 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_5419179 : Nat := 118140960795 + 5419179 * 2 ^ 59
def prefixEnd_5419179 : Nat := 4983230072969 + 3 ^ 40 * 5419179 * 2
def baseEnd_5419179 : Nat := 2782643579751558170940155

theorem tailTrace_5419179 : CollatzResearch.WordTrace tailWord_5419179 prefixEnd_5419179 2782643579751558170940155 := by
  unfold tailWord_5419179
  simp only [CollatzResearch.WordTrace]
  refine ⟨197653696034247479933732591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131769130689498319955821727 197653696034247479933732591)
  ·
    refine ⟨296480544051371219900598887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197653696034247479933732591 296480544051371219900598887)
    ·
      refine ⟨444720816077056829850898331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296480544051371219900598887 444720816077056829850898331)
      ·
        refine ⟨667081224115585244776347497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444720816077056829850898331 667081224115585244776347497)
        ·
          refine ⟨500310918086688933582260623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667081224115585244776347497 500310918086688933582260623)
          ·
            refine ⟨750466377130033400373390935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500310918086688933582260623 750466377130033400373390935)
            ·
              refine ⟨1125699565695050100560086403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750466377130033400373390935 1125699565695050100560086403)
              ·
                refine ⟨1688549348542575150840129605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125699565695050100560086403 1688549348542575150840129605)
                ·
                  refine ⟨316603002851732840782524301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688549348542575150840129605 316603002851732840782524301)
                  ·
                    refine ⟨118726126069399815293446613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316603002851732840782524301 118726126069399815293446613)
                    ·
                      refine ⟨2782643579751558170940155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118726126069399815293446613 2782643579751558170940155)
                      ·
                        rfl

theorem cell23_5419179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_5419179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419179 prefixEnd_5419179 := by exact prefixLift 5419179
  have htrace : WordTrace (prefixWord ++ tailWord_5419179) baseStart_5419179 baseEnd_5419179 := by
    simpa [prefixWord, tailWord_5419179, baseEnd_5419179] using wordTrace_append hprefix tailTrace_5419179
  have hstable : (prefixWord ++ tailWord_5419179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419179).length < 2 ^ (prefixWord ++ tailWord_5419179).sum := by decide
  have hdescent : baseEnd_5419179 < baseStart_5419179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419200 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_5419200 : Nat := 118140960795 + 5419200 * 2 ^ 59
def prefixEnd_5419200 : Nat := 4983230072969 + 3 ^ 40 * 5419200 * 2
def baseEnd_5419200 : Nat := 2782654362845302588777559

theorem tailTrace_5419200 : CollatzResearch.WordTrace tailWord_5419200 prefixEnd_5419200 2782654362845302588777559 := by
  unfold tailWord_5419200
  simp only [CollatzResearch.WordTrace]
  refine ⟨98827230983585700260123527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131769641311447600346831369 98827230983585700260123527)
  ·
    refine ⟨148240846475378550390185291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98827230983585700260123527 148240846475378550390185291)
    ·
      refine ⟨222361269713067825585277937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148240846475378550390185291 222361269713067825585277937)
      ·
        refine ⟨166770952284800869188958453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222361269713067825585277937 166770952284800869188958453)
        ·
          refine ⟨15634776776700081486464855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166770952284800869188958453 15634776776700081486464855)
          ·
            refine ⟨23452165165050122229697283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15634776776700081486464855 23452165165050122229697283)
            ·
              refine ⟨35178247747575183344545925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23452165165050122229697283 35178247747575183344545925)
              ·
                refine ⟨6595921452670346877102361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35178247747575183344545925 6595921452670346877102361)
                ·
                  refine ⟨4946941089502760157826771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6595921452670346877102361 4946941089502760157826771)
                  ·
                    refine ⟨7420411634254140236740157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946941089502760157826771 7420411634254140236740157)
                    ·
                      refine ⟨2782654362845302588777559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420411634254140236740157 2782654362845302588777559)
                      ·
                        rfl

theorem cell23_5419200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_5419200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419200 prefixEnd_5419200 := by exact prefixLift 5419200
  have htrace : WordTrace (prefixWord ++ tailWord_5419200) baseStart_5419200 baseEnd_5419200 := by
    simpa [prefixWord, tailWord_5419200, baseEnd_5419200] using wordTrace_append hprefix tailTrace_5419200
  have hstable : (prefixWord ++ tailWord_5419200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419200).length < 2 ^ (prefixWord ++ tailWord_5419200).sum := by decide
  have hdescent : baseEnd_5419200 < baseStart_5419200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419201 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5419201 : Nat := 118140960795 + 5419201 * 2 ^ 59
def prefixEnd_5419201 : Nat := 4983230072969 + 3 ^ 40 * 5419201 * 2
def baseEnd_5419201 : Nat := 2782654876325957084865055

theorem tailTrace_5419201 : CollatzResearch.WordTrace tailWord_5419201 prefixEnd_5419201 2782654876325957084865055 := by
  unfold tailWord_5419201
  simp only [CollatzResearch.WordTrace]
  refine ⟨197654498440167777691033457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131769665626778518460688971 197654498440167777691033457)
  ·
    refine ⟨148240873830125833268275093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197654498440167777691033457 148240873830125833268275093)
    ·
      refine ⟨6948790960787148434450395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148240873830125833268275093 6948790960787148434450395)
      ·
        refine ⟨10423186441180722651675593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948790960787148434450395 10423186441180722651675593)
        ·
          refine ⟨7817389830885541988756695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10423186441180722651675593 7817389830885541988756695)
          ·
            refine ⟨11726084746328312983135043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817389830885541988756695 11726084746328312983135043)
            ·
              refine ⟨17589127119492469474702565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11726084746328312983135043 17589127119492469474702565)
              ·
                refine ⟨3297961334904838026506731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17589127119492469474702565 3297961334904838026506731)
                ·
                  refine ⟨4946942002357257039760097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297961334904838026506731 4946942002357257039760097)
                  ·
                    refine ⟨3710206501767942779820073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4946942002357257039760097 3710206501767942779820073)
                    ·
                      refine ⟨2782654876325957084865055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710206501767942779820073 2782654876325957084865055)
                      ·
                        rfl

theorem cell23_5419201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5419201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419201 prefixEnd_5419201 := by exact prefixLift 5419201
  have htrace : WordTrace (prefixWord ++ tailWord_5419201) baseStart_5419201 baseEnd_5419201 := by
    simpa [prefixWord, tailWord_5419201, baseEnd_5419201] using wordTrace_append hprefix tailTrace_5419201
  have hstable : (prefixWord ++ tailWord_5419201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419201).length < 2 ^ (prefixWord ++ tailWord_5419201).sum := by decide
  have hdescent : baseEnd_5419201 < baseStart_5419201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419226 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5419226 : Nat := 118140960795 + 5419226 * 2 ^ 59
def prefixEnd_5419226 : Nat := 4983230072969 + 3 ^ 40 * 5419226 * 2
def baseEnd_5419226 : Nat := 2782667713342319487052439

theorem tailTrace_5419226 : CollatzResearch.WordTrace tailWord_5419226 prefixEnd_5419226 2782667713342319487052439 := by
  unfold tailWord_5419226
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413852566269301740173383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131770273510051471307129021 49413852566269301740173383)
  ·
    refine ⟨74120778849403952610260075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49413852566269301740173383 74120778849403952610260075)
    ·
      refine ⟨111181168274105928915390113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74120778849403952610260075 111181168274105928915390113)
      ·
        refine ⟨83385876205579446686542585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111181168274105928915390113 83385876205579446686542585)
        ·
          refine ⟨62539407154184585014906939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83385876205579446686542585 62539407154184585014906939)
          ·
            refine ⟨93809110731276877522360409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62539407154184585014906939 93809110731276877522360409)
            ·
              refine ⟨70356833048457658141770307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93809110731276877522360409 70356833048457658141770307)
              ·
                refine ⟨105535249572686487212655461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70356833048457658141770307 105535249572686487212655461)
                ·
                  refine ⟨19787859294878716352372899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105535249572686487212655461 19787859294878716352372899)
                  ·
                    refine ⟨29681788942318074528559349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19787859294878716352372899 29681788942318074528559349)
                    ·
                      refine ⟨2782667713342319487052439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29681788942318074528559349 2782667713342319487052439)
                      ·
                        rfl

theorem cell23_5419226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5419226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419226 prefixEnd_5419226 := by exact prefixLift 5419226
  have htrace : WordTrace (prefixWord ++ tailWord_5419226) baseStart_5419226 baseEnd_5419226 := by
    simpa [prefixWord, tailWord_5419226, baseEnd_5419226] using wordTrace_append hprefix tailTrace_5419226
  have hstable : (prefixWord ++ tailWord_5419226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419226).length < 2 ^ (prefixWord ++ tailWord_5419226).sum := by decide
  have hdescent : baseEnd_5419226 < baseStart_5419226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419236 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_5419236 : Nat := 118140960795 + 5419236 * 2 ^ 59
def prefixEnd_5419236 : Nat := 4983230072969 + 3 ^ 40 * 5419236 * 2
def baseEnd_5419236 : Nat := 2782672848148864447927393

theorem tailTrace_5419236 : CollatzResearch.WordTrace tailWord_5419236 prefixEnd_5419236 2782672848148864447927393 := by
  unfold tailWord_5419236
  simp only [CollatzResearch.WordTrace]
  refine ⟨98827887497520489334278781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131770516663360652445705041 98827887497520489334278781)
  ·
    refine ⟨37060457811570183500354543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98827887497520489334278781 37060457811570183500354543)
    ·
      refine ⟨55590686717355275250531815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37060457811570183500354543 55590686717355275250531815)
      ·
        refine ⟨83386030076032912875797723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55590686717355275250531815 83386030076032912875797723)
        ·
          refine ⟨125079045114049369313696585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83386030076032912875797723 125079045114049369313696585)
          ·
            refine ⟨93809283835537026985272439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125079045114049369313696585 93809283835537026985272439)
            ·
              refine ⟨140713925753305540477908659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93809283835537026985272439 140713925753305540477908659)
              ·
                refine ⟨211070888629958310716862989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140713925753305540477908659 211070888629958310716862989)
                ·
                  refine ⟨79151583236234366518823621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211070888629958310716862989 79151583236234366518823621)
                  ·
                    refine ⟨14840921856793943722279429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79151583236234366518823621 14840921856793943722279429)
                    ·
                      refine ⟨2782672848148864447927393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14840921856793943722279429 2782672848148864447927393)
                      ·
                        rfl

theorem cell23_5419236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_5419236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419236 prefixEnd_5419236 := by exact prefixLift 5419236
  have htrace : WordTrace (prefixWord ++ tailWord_5419236) baseStart_5419236 baseEnd_5419236 := by
    simpa [prefixWord, tailWord_5419236, baseEnd_5419236] using wordTrace_append hprefix tailTrace_5419236
  have hstable : (prefixWord ++ tailWord_5419236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419236).length < 2 ^ (prefixWord ++ tailWord_5419236).sum := by decide
  have hdescent : baseEnd_5419236 < baseStart_5419236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419240 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5419240 : Nat := 118140960795 + 5419240 * 2 ^ 59
def prefixEnd_5419240 : Nat := 4983230072969 + 3 ^ 40 * 5419240 * 2
def baseEnd_5419240 : Nat := 2782674902071482432277375

theorem tailTrace_5419240 : CollatzResearch.WordTrace tailWord_5419240 prefixEnd_5419240 2782674902071482432277375 := by
  unfold tailWord_5419240
  simp only [CollatzResearch.WordTrace]
  refine ⟨98827960443513243675851587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131770613924684324901135449 98827960443513243675851587)
  ·
    refine ⟨148241940665269865513777381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98827960443513243675851587 148241940665269865513777381)
    ·
      refine ⟨27795363874738099783833259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148241940665269865513777381 27795363874738099783833259)
      ·
        refine ⟨41693045812107149675749889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27795363874738099783833259 41693045812107149675749889)
        ·
          refine ⟨31269784359080362256812417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41693045812107149675749889 31269784359080362256812417)
          ·
            refine ⟨23452338269310271692609313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31269784359080362256812417 23452338269310271692609313)
            ·
              refine ⟨17589253701982703769456985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23452338269310271692609313 17589253701982703769456985)
              ·
                refine ⟨13191940276487027827092739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17589253701982703769456985 13191940276487027827092739)
                ·
                  refine ⟨19787910414730541740639109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13191940276487027827092739 19787910414730541740639109)
                  ·
                    refine ⟨3710233202761976576369833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19787910414730541740639109 3710233202761976576369833)
                    ·
                      refine ⟨2782674902071482432277375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710233202761976576369833 2782674902071482432277375)
                      ·
                        rfl

theorem cell23_5419240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5419240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419240 prefixEnd_5419240 := by exact prefixLift 5419240
  have htrace : WordTrace (prefixWord ++ tailWord_5419240) baseStart_5419240 baseEnd_5419240 := by
    simpa [prefixWord, tailWord_5419240, baseEnd_5419240] using wordTrace_append hprefix tailTrace_5419240
  have hstable : (prefixWord ++ tailWord_5419240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419240).length < 2 ^ (prefixWord ++ tailWord_5419240).sum := by decide
  have hdescent : baseEnd_5419240 < baseStart_5419240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419246 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_5419246 : Nat := 118140960795 + 5419246 * 2 ^ 59
def prefixEnd_5419246 : Nat := 4983230072969 + 3 ^ 40 * 5419246 * 2
def baseEnd_5419246 : Nat := 309186442550601045422483

theorem tailTrace_5419246 : CollatzResearch.WordTrace tailWord_5419246 prefixEnd_5419246 309186442550601045422483 := by
  unfold tailWord_5419246
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707017465625593797052699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131770759816669833584281061 24707017465625593797052699)
  ·
    refine ⟨37060526198438390695579049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24707017465625593797052699 37060526198438390695579049)
    ·
      refine ⟨27795394648828793021684287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37060526198438390695579049 27795394648828793021684287)
      ·
        refine ⟨41693091973243189532526431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27795394648828793021684287 41693091973243189532526431)
        ·
          refine ⟨62539637959864784298789647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41693091973243189532526431 62539637959864784298789647)
          ·
            refine ⟨93809456939797176448184471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62539637959864784298789647 93809456939797176448184471)
            ·
              refine ⟨140714185409695764672276707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93809456939797176448184471 140714185409695764672276707)
              ·
                refine ⟨211071278114543647008415061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140714185409695764672276707 211071278114543647008415061)
                ·
                  refine ⟨309186442550601045422483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 211071278114543647008415061 309186442550601045422483)
                  ·
                    rfl

theorem cell23_5419246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_5419246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419246 prefixEnd_5419246 := by exact prefixLift 5419246
  have htrace : WordTrace (prefixWord ++ tailWord_5419246) baseStart_5419246 baseEnd_5419246 := by
    simpa [prefixWord, tailWord_5419246, baseEnd_5419246] using wordTrace_append hprefix tailTrace_5419246
  have hstable : (prefixWord ++ tailWord_5419246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419246).length < 2 ^ (prefixWord ++ tailWord_5419246).sum := by decide
  have hdescent : baseEnd_5419246 < baseStart_5419246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419263 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 5]
def baseStart_5419263 : Nat := 118140960795 + 5419263 * 2 ^ 59
def prefixEnd_5419263 : Nat := 4983230072969 + 3 ^ 40 * 5419263 * 2
def baseEnd_5419263 : Nat := 309187412458503982476641

theorem tailTrace_5419263 : CollatzResearch.WordTrace tailWord_5419263 prefixEnd_5419263 309187412458503982476641 := by
  unfold tailWord_5419263
  simp only [CollatzResearch.WordTrace]
  refine ⟨197656759765943162279790443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131771173177295441519860295 197656759765943162279790443)
  ·
    refine ⟨296485139648914743419685665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197656759765943162279790443 296485139648914743419685665)
    ·
      refine ⟨222363854736686057564764249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296485139648914743419685665 222363854736686057564764249)
      ·
        refine ⟨166772891052514543173573187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222363854736686057564764249 166772891052514543173573187)
        ·
          refine ⟨250159336578771814760359781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166772891052514543173573187 250159336578771814760359781)
          ·
            refine ⟨46904875608519715267567459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250159336578771814760359781 46904875608519715267567459)
            ·
              refine ⟨70357313412779572901351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46904875608519715267567459 70357313412779572901351189)
              ·
                refine ⟨3297999066224042479750837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70357313412779572901351189 3297999066224042479750837)
                ·
                  refine ⟨309187412458503982476641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297999066224042479750837 309187412458503982476641)
                  ·
                    rfl

theorem cell23_5419263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 5].length) (baseStart_5419263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419263 prefixEnd_5419263 := by exact prefixLift 5419263
  have htrace : WordTrace (prefixWord ++ tailWord_5419263) baseStart_5419263 baseEnd_5419263 := by
    simpa [prefixWord, tailWord_5419263, baseEnd_5419263] using wordTrace_append hprefix tailTrace_5419263
  have hstable : (prefixWord ++ tailWord_5419263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419263).length < 2 ^ (prefixWord ++ tailWord_5419263).sum := by decide
  have hdescent : baseEnd_5419263 < baseStart_5419263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419273 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_5419273 : Nat := 118140960795 + 5419273 * 2 ^ 59
def prefixEnd_5419273 : Nat := 4983230072969 + 3 ^ 40 * 5419273 * 2
def baseEnd_5419273 : Nat := 2782691846933080803164723

theorem tailTrace_5419273 : CollatzResearch.WordTrace tailWord_5419273 prefixEnd_5419273 2782691846933080803164723 := by
  unfold tailWord_5419273
  simp only [CollatzResearch.WordTrace]
  refine ⟨197657124495906933987654473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131771416330604622658436315 197657124495906933987654473)
  ·
    refine ⟨148242843371930200490740855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197657124495906933987654473 148242843371930200490740855)
    ·
      refine ⟨222364265057895300736111283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148242843371930200490740855 222364265057895300736111283)
      ·
        refine ⟨333546397586842951104166925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222364265057895300736111283 333546397586842951104166925)
        ·
          refine ⟨125079899095066106664062597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333546397586842951104166925 125079899095066106664062597)
          ·
            refine ⟨23452481080324894999511737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125079899095066106664062597 23452481080324894999511737)
            ·
              refine ⟨17589360810243671249633803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23452481080324894999511737 17589360810243671249633803)
              ·
                refine ⟨26384041215365506874450705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17589360810243671249633803 26384041215365506874450705)
                ·
                  refine ⟨19788030911524130155838029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26384041215365506874450705 19788030911524130155838029)
                  ·
                    refine ⟨7420511591821548808439261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19788030911524130155838029 7420511591821548808439261)
                    ·
                      refine ⟨2782691846933080803164723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420511591821548808439261 2782691846933080803164723)
                      ·
                        rfl

theorem cell23_5419273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_5419273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419273 prefixEnd_5419273 := by exact prefixLift 5419273
  have htrace : WordTrace (prefixWord ++ tailWord_5419273) baseStart_5419273 baseEnd_5419273 := by
    simpa [prefixWord, tailWord_5419273, baseEnd_5419273] using wordTrace_append hprefix tailTrace_5419273
  have hstable : (prefixWord ++ tailWord_5419273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419273).length < 2 ^ (prefixWord ++ tailWord_5419273).sum := by decide
  have hdescent : baseEnd_5419273 < baseStart_5419273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419276 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_5419276 : Nat := 118140960795 + 5419276 * 2 ^ 59
def prefixEnd_5419276 : Nat := 4983230072969 + 3 ^ 40 * 5419276 * 2
def baseEnd_5419276 : Nat := 927564462458348097142403

theorem tailTrace_5419276 : CollatzResearch.WordTrace tailWord_5419276 prefixEnd_5419276 927564462458348097142403 := by
  unfold tailWord_5419276
  simp only [CollatzResearch.WordTrace]
  refine ⟨98828616957448032750006841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131771489276597377000009121 98828616957448032750006841)
  ·
    refine ⟨74121462718086024562505131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98828616957448032750006841 74121462718086024562505131)
    ·
      refine ⟨111182194077129036843757697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74121462718086024562505131 111182194077129036843757697)
      ·
        refine ⟨83386645557846777632818273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111182194077129036843757697 83386645557846777632818273)
        ·
          refine ⟨62539984168385083224613705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83386645557846777632818273 62539984168385083224613705)
          ·
            refine ⟨46904988126288812418460279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62539984168385083224613705 46904988126288812418460279)
            ·
              refine ⟨70357482189433218627690419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46904988126288812418460279 70357482189433218627690419)
              ·
                refine ⟨105536223284149827941535629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70357482189433218627690419 105536223284149827941535629)
                ·
                  refine ⟨39576083731556185478075861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105536223284149827941535629 39576083731556185478075861)
                  ·
                    refine ⟨927564462458348097142403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39576083731556185478075861 927564462458348097142403)
                    ·
                      rfl

theorem cell23_5419276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_5419276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419276 prefixEnd_5419276 := by exact prefixLift 5419276
  have htrace : WordTrace (prefixWord ++ tailWord_5419276) baseStart_5419276 baseEnd_5419276 := by
    simpa [prefixWord, tailWord_5419276, baseEnd_5419276] using wordTrace_append hprefix tailTrace_5419276
  have hstable : (prefixWord ++ tailWord_5419276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419276).length < 2 ^ (prefixWord ++ tailWord_5419276).sum := by decide
  have hdescent : baseEnd_5419276 < baseStart_5419276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419283 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 5, 2]
def baseStart_5419283 : Nat := 118140960795 + 5419283 * 2 ^ 59
def prefixEnd_5419283 : Nat := 4983230072969 + 3 ^ 40 * 5419283 * 2
def baseEnd_5419283 : Nat := 2782696981739625764039677

theorem tailTrace_5419283 : CollatzResearch.WordTrace tailWord_5419283 prefixEnd_5419283 2782696981739625764039677 := by
  unfold tailWord_5419283
  simp only [CollatzResearch.WordTrace]
  refine ⟨197657489225870705695518503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131771659483913803797012335 197657489225870705695518503)
  ·
    refine ⟨296486233838806058543277755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197657489225870705695518503 296486233838806058543277755)
    ·
      refine ⟨444729350758209087814916633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296486233838806058543277755 444729350758209087814916633)
      ·
        refine ⟨333547013068656815861187475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444729350758209087814916633 333547013068656815861187475)
        ·
          refine ⟨500320519602985223791781213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333547013068656815861187475 500320519602985223791781213)
          ·
            refine ⟨187620194851119458921917955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500320519602985223791781213 187620194851119458921917955)
            ·
              refine ⟨281430292276679188382876933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187620194851119458921917955 281430292276679188382876933)
              ·
                refine ⟨52768179801877347821789425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281430292276679188382876933 52768179801877347821789425)
                ·
                  refine ⟨39576134851408010866342069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52768179801877347821789425 39576134851408010866342069)
                  ·
                    refine ⟨3710262642319501018719569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39576134851408010866342069 3710262642319501018719569)
                    ·
                      refine ⟨2782696981739625764039677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710262642319501018719569 2782696981739625764039677)
                      ·
                        rfl

theorem cell23_5419283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5, 2].length) (baseStart_5419283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419283 prefixEnd_5419283 := by exact prefixLift 5419283
  have htrace : WordTrace (prefixWord ++ tailWord_5419283) baseStart_5419283 baseEnd_5419283 := by
    simpa [prefixWord, tailWord_5419283, baseEnd_5419283] using wordTrace_append hprefix tailTrace_5419283
  have hstable : (prefixWord ++ tailWord_5419283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419283).length < 2 ^ (prefixWord ++ tailWord_5419283).sum := by decide
  have hdescent : baseEnd_5419283 < baseStart_5419283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419370 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_5419370 : Nat := 118140960795 + 5419370 * 2 ^ 59
def prefixEnd_5419370 : Nat := 4983230072969 + 3 ^ 40 * 5419370 * 2
def baseEnd_5419370 : Nat := 309193517172951880405753

theorem tailTrace_5419370 : CollatzResearch.WordTrace tailWord_5419370 prefixEnd_5419370 309193517172951880405753 := by
  unfold tailWord_5419370
  simp only [CollatzResearch.WordTrace]
  refine ⟨49415165594138879888483891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131773774917703679702623709 49415165594138879888483891)
  ·
    refine ⟨74122748391208319832725837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49415165594138879888483891 74122748391208319832725837)
    ·
      refine ⟨27796030646703119937272189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74122748391208319832725837 27796030646703119937272189)
      ·
        refine ⟨10423511492513669976477071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27796030646703119937272189 10423511492513669976477071)
        ·
          refine ⟨15635267238770504964715607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10423511492513669976477071 15635267238770504964715607)
          ·
            refine ⟨23452900858155757447073411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15635267238770504964715607 23452900858155757447073411)
            ·
              refine ⟨35179351287233636170610117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23452900858155757447073411 35179351287233636170610117)
              ·
                refine ⟨6596128366356306781989397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35179351287233636170610117 6596128366356306781989397)
                ·
                  refine ⟨309193517172951880405753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6596128366356306781989397 309193517172951880405753)
                  ·
                    rfl

theorem cell23_5419370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_5419370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419370 prefixEnd_5419370 := by exact prefixLift 5419370
  have htrace : WordTrace (prefixWord ++ tailWord_5419370) baseStart_5419370 baseEnd_5419370 := by
    simpa [prefixWord, tailWord_5419370, baseEnd_5419370] using wordTrace_append hprefix tailTrace_5419370
  have hstable : (prefixWord ++ tailWord_5419370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419370).length < 2 ^ (prefixWord ++ tailWord_5419370).sum := by decide
  have hdescent : baseEnd_5419370 < baseStart_5419370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419373 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5419373 : Nat := 118140960795 + 5419373 * 2 ^ 59
def prefixEnd_5419373 : Nat := 4983230072969 + 3 ^ 40 * 5419373 * 2
def baseEnd_5419373 : Nat := 2782743194998530411914263

theorem tailTrace_5419373 : CollatzResearch.WordTrace tailWord_5419373 prefixEnd_5419373 2782743194998530411914263 := by
  unfold tailWord_5419373
  simp only [CollatzResearch.WordTrace]
  refine ⟨197660771795544651066294773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131773847863696434044196515 197660771795544651066294773)
  ·
    refine ⟨18530697355832311037465135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197660771795544651066294773 18530697355832311037465135)
    ·
      refine ⟨27796046033748466556197703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18530697355832311037465135 27796046033748466556197703)
      ·
        refine ⟨41694069050622699834296555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27796046033748466556197703 41694069050622699834296555)
        ·
          refine ⟨62541103575934049751444833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41694069050622699834296555 62541103575934049751444833)
          ·
            refine ⟨46905827681950537313583625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62541103575934049751444833 46905827681950537313583625)
            ·
              refine ⟨35179370761462902985187719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46905827681950537313583625 35179370761462902985187719)
              ·
                refine ⟨52769056142194354477781579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35179370761462902985187719 52769056142194354477781579)
                ·
                  refine ⟨79153584213291531716672369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52769056142194354477781579 79153584213291531716672369)
                  ·
                    refine ⟨59365188159968648787504277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79153584213291531716672369 59365188159968648787504277)
                    ·
                      refine ⟨2782743194998530411914263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59365188159968648787504277 2782743194998530411914263)
                      ·
                        rfl

theorem cell23_5419373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5419373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419373 prefixEnd_5419373 := by exact prefixLift 5419373
  have htrace : WordTrace (prefixWord ++ tailWord_5419373) baseStart_5419373 baseEnd_5419373 := by
    simpa [prefixWord, tailWord_5419373, baseEnd_5419373] using wordTrace_append hprefix tailTrace_5419373
  have hstable : (prefixWord ++ tailWord_5419373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419373).length < 2 ^ (prefixWord ++ tailWord_5419373).sum := by decide
  have hdescent : baseEnd_5419373 < baseStart_5419373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419400 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_5419400 : Nat := 118140960795 + 5419400 * 2 ^ 59
def prefixEnd_5419400 : Nat := 4983230072969 + 3 ^ 40 * 5419400 * 2
def baseEnd_5419400 : Nat := 927585686325400602092213

theorem tailTrace_5419400 : CollatzResearch.WordTrace tailWord_5419400 prefixEnd_5419400 927585686325400602092213 := by
  unfold tailWord_5419400
  simp only [CollatzResearch.WordTrace]
  refine ⟨98830878283223417338763827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131774504377631223118351769 98830878283223417338763827)
  ·
    refine ⟨148246317424835126008145741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98830878283223417338763827 148246317424835126008145741)
    ·
      refine ⟨55592369034313172253054653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148246317424835126008145741 55592369034313172253054653)
      ·
        refine ⟨20847138387867439594895495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55592369034313172253054653 20847138387867439594895495)
        ·
          refine ⟨31270707581801159392343243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20847138387867439594895495 31270707581801159392343243)
          ·
            refine ⟨46906061372701739088514865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31270707581801159392343243 46906061372701739088514865)
            ·
              refine ⟨35179546029526304316386149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46906061372701739088514865 35179546029526304316386149)
              ·
                refine ⟨6596164880536182059322403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35179546029526304316386149 6596164880536182059322403)
                ·
                  refine ⟨9894247320804273088983605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596164880536182059322403 9894247320804273088983605)
                  ·
                    refine ⟨927585686325400602092213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9894247320804273088983605 927585686325400602092213)
                    ·
                      rfl

theorem cell23_5419400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_5419400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419400 prefixEnd_5419400 := by exact prefixLift 5419400
  have htrace : WordTrace (prefixWord ++ tailWord_5419400) baseStart_5419400 baseEnd_5419400 := by
    simpa [prefixWord, tailWord_5419400, baseEnd_5419400] using wordTrace_append hprefix tailTrace_5419400
  have hstable : (prefixWord ++ tailWord_5419400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419400).length < 2 ^ (prefixWord ++ tailWord_5419400).sum := by decide
  have hdescent : baseEnd_5419400 < baseStart_5419400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419433 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_5419433 : Nat := 118140960795 + 5419433 * 2 ^ 59
def prefixEnd_5419433 : Nat := 4983230072969 + 3 ^ 40 * 5419433 * 2
def baseEnd_5419433 : Nat := 2782774003837800177163987

theorem tailTrace_5419433 : CollatzResearch.WordTrace tailWord_5419433 prefixEnd_5419433 2782774003837800177163987 := by
  unfold tailWord_5419433
  simp only [CollatzResearch.WordTrace]
  refine ⟨197662960175327281313478953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131775306783551520875652635 197662960175327281313478953)
  ·
    refine ⟨148247220131495460985109215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197662960175327281313478953 148247220131495460985109215)
    ·
      refine ⟨222370830197243191477663823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148247220131495460985109215 222370830197243191477663823)
      ·
        refine ⟨333556245295864787216495735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222370830197243191477663823 333556245295864787216495735)
        ·
          refine ⟨500334367943797180824743603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333556245295864787216495735 500334367943797180824743603)
          ·
            refine ⟨750501551915695771237115405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500334367943797180824743603 750501551915695771237115405)
            ·
              refine ⟨281438081968385914213918277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750501551915695771237115405 281438081968385914213918277)
              ·
                refine ⟨52769640369072358915109677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281438081968385914213918277 52769640369072358915109677)
                ·
                  refine ⟨19788615138402134593166129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52769640369072358915109677 19788615138402134593166129)
                  ·
                    refine ⟨14841461353801600944874597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19788615138402134593166129 14841461353801600944874597)
                    ·
                      refine ⟨2782774003837800177163987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14841461353801600944874597 2782774003837800177163987)
                      ·
                        rfl

theorem cell23_5419433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_5419433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419433 prefixEnd_5419433 := by exact prefixLift 5419433
  have htrace : WordTrace (prefixWord ++ tailWord_5419433) baseStart_5419433 baseEnd_5419433 := by
    simpa [prefixWord, tailWord_5419433, baseEnd_5419433] using wordTrace_append hprefix tailTrace_5419433
  have hstable : (prefixWord ++ tailWord_5419433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419433).length < 2 ^ (prefixWord ++ tailWord_5419433).sum := by decide
  have hdescent : baseEnd_5419433 < baseStart_5419433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419454 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_5419454 : Nat := 118140960795 + 5419454 * 2 ^ 59
def prefixEnd_5419454 : Nat := 4983230072969 + 3 ^ 40 * 5419454 * 2
def baseEnd_5419454 : Nat := 2782784786931544595001391

theorem tailTrace_5419454 : CollatzResearch.WordTrace tailWord_5419454 prefixEnd_5419454 2782784786931544595001391 := by
  unfold tailWord_5419454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707965763531400237499177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131775817405500801266662277 24707965763531400237499177)
  ·
    refine ⟨18530974322648550178124383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24707965763531400237499177 18530974322648550178124383)
    ·
      refine ⟨27796461483972825267186575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18530974322648550178124383 27796461483972825267186575)
      ·
        refine ⟨41694692225959237900779863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27796461483972825267186575 41694692225959237900779863)
        ·
          refine ⟨62542038338938856851169795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41694692225959237900779863 62542038338938856851169795)
          ·
            refine ⟨93813057508408285276754693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62542038338938856851169795 93813057508408285276754693)
            ·
              refine ⟨17589948282826553489391505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93813057508408285276754693 17589948282826553489391505)
              ·
                refine ⟨13192461212119915117043629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17589948282826553489391505 13192461212119915117043629)
                ·
                  refine ⟨4947172954544968168891361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13192461212119915117043629 4947172954544968168891361)
                  ·
                    refine ⟨3710379715908726126668521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947172954544968168891361 3710379715908726126668521)
                    ·
                      refine ⟨2782784786931544595001391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710379715908726126668521 2782784786931544595001391)
                      ·
                        rfl

theorem cell23_5419454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_5419454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419454 prefixEnd_5419454 := by exact prefixLift 5419454
  have htrace : WordTrace (prefixWord ++ tailWord_5419454) baseStart_5419454 baseEnd_5419454 := by
    simpa [prefixWord, tailWord_5419454, baseEnd_5419454] using wordTrace_append hprefix tailTrace_5419454
  have hstable : (prefixWord ++ tailWord_5419454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419454).length < 2 ^ (prefixWord ++ tailWord_5419454).sum := by decide
  have hdescent : baseEnd_5419454 < baseStart_5419454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419470 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_5419470 : Nat := 118140960795 + 5419470 * 2 ^ 59
def prefixEnd_5419470 : Nat := 4983230072969 + 3 ^ 40 * 5419470 * 2
def baseEnd_5419470 : Nat := 2782793002622016532401317

theorem tailTrace_5419470 : CollatzResearch.WordTrace tailWord_5419470 prefixEnd_5419470 2782793002622016532401317 := by
  unfold tailWord_5419470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708038709524154579071983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131776206450795491088383909 24708038709524154579071983)
  ·
    refine ⟨37062058064286231868607975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24708038709524154579071983 37062058064286231868607975)
    ·
      refine ⟨55593087096429347802911963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37062058064286231868607975 55593087096429347802911963)
      ·
        refine ⟨83389630644644021704367945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55593087096429347802911963 83389630644644021704367945)
        ·
          refine ⟨62542222983483016278275959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83389630644644021704367945 62542222983483016278275959)
          ·
            refine ⟨93813334475224524417413939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62542222983483016278275959 93813334475224524417413939)
            ·
              refine ⟨140720001712836786626120909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93813334475224524417413939 140720001712836786626120909)
              ·
                refine ⟨52770000642313794984795341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140720001712836786626120909 52770000642313794984795341)
                ·
                  refine ⟨19788750240867673119298253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52770000642313794984795341 19788750240867673119298253)
                  ·
                    refine ⟨7420781340325377419736845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19788750240867673119298253 7420781340325377419736845)
                    ·
                      refine ⟨2782793002622016532401317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420781340325377419736845 2782793002622016532401317)
                      ·
                        rfl

theorem cell23_5419470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_5419470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419470 prefixEnd_5419470 := by exact prefixLift 5419470
  have htrace : WordTrace (prefixWord ++ tailWord_5419470) baseStart_5419470 baseEnd_5419470 := by
    simpa [prefixWord, tailWord_5419470, baseEnd_5419470] using wordTrace_append hprefix tailTrace_5419470
  have hstable : (prefixWord ++ tailWord_5419470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419470).length < 2 ^ (prefixWord ++ tailWord_5419470).sum := by decide
  have hdescent : baseEnd_5419470 < baseStart_5419470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419474 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5419474 : Nat := 118140960795 + 5419474 * 2 ^ 59
def prefixEnd_5419474 : Nat := 4983230072969 + 3 ^ 40 * 5419474 * 2
def baseEnd_5419474 : Nat := 2782795056544634516751299

theorem tailTrace_5419474 : CollatzResearch.WordTrace tailWord_5419474 prefixEnd_5419474 2782795056544634516751299 := by
  unfold tailWord_5419474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49416113892044686328930369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131776303712119163543814317 49416113892044686328930369)
  ·
    refine ⟨37062085419033514746697777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49416113892044686328930369 37062085419033514746697777)
    ·
      refine ⟨27796564064275136060023333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37062085419033514746697777 27796564064275136060023333)
      ·
        refine ⟨5211855762051588011254375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27796564064275136060023333 5211855762051588011254375)
        ·
          refine ⟨7817783643077382016881563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211855762051588011254375 7817783643077382016881563)
          ·
            refine ⟨11726675464616073025322345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817783643077382016881563 11726675464616073025322345)
            ·
              refine ⟨8795006598462054768991759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11726675464616073025322345 8795006598462054768991759)
              ·
                refine ⟨13192509897693082153487639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8795006598462054768991759 13192509897693082153487639)
                ·
                  refine ⟨19788764846539623230231459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13192509897693082153487639 19788764846539623230231459)
                  ·
                    refine ⟨29683147269809434845347189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19788764846539623230231459 29683147269809434845347189)
                    ·
                      refine ⟨2782795056544634516751299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29683147269809434845347189 2782795056544634516751299)
                      ·
                        rfl

theorem cell23_5419474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5419474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419474 prefixEnd_5419474 := by exact prefixLift 5419474
  have htrace : WordTrace (prefixWord ++ tailWord_5419474) baseStart_5419474 baseEnd_5419474 := by
    simpa [prefixWord, tailWord_5419474, baseEnd_5419474] using wordTrace_append hprefix tailTrace_5419474
  have hstable : (prefixWord ++ tailWord_5419474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419474).length < 2 ^ (prefixWord ++ tailWord_5419474).sum := by decide
  have hdescent : baseEnd_5419474 < baseStart_5419474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419487 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_5419487 : Nat := 118140960795 + 5419487 * 2 ^ 59
def prefixEnd_5419487 : Nat := 4983230072969 + 3 ^ 40 * 5419487 * 2
def baseEnd_5419487 : Nat := 2782801731793142965888739

theorem tailTrace_5419487 : CollatzResearch.WordTrace tailWord_5419487 prefixEnd_5419487 2782801731793142965888739 := by
  unfold tailWord_5419487
  simp only [CollatzResearch.WordTrace]
  refine ⟨197664929717131648535944715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131776619811421099023963143 197664929717131648535944715)
  ·
    refine ⟨296497394575697472803917073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197664929717131648535944715 296497394575697472803917073)
    ·
      refine ⟨222373045931773104602937805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296497394575697472803917073 222373045931773104602937805)
      ·
        refine ⟨83389892224414914226101677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222373045931773104602937805 83389892224414914226101677)
        ·
          refine ⟨31271209584155592834788129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83389892224414914226101677 31271209584155592834788129)
          ·
            refine ⟨23453407188116694626091097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31271209584155592834788129 23453407188116694626091097)
            ·
              refine ⟨17590055391087520969568323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23453407188116694626091097 17590055391087520969568323)
              ·
                refine ⟨26385083086631281454352485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17590055391087520969568323 26385083086631281454352485)
                ·
                  refine ⟨4947203078743365272691091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26385083086631281454352485 4947203078743365272691091)
                  ·
                    refine ⟨7420804618115047909036637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4947203078743365272691091 7420804618115047909036637)
                    ·
                      refine ⟨2782801731793142965888739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7420804618115047909036637 2782801731793142965888739)
                      ·
                        rfl

theorem cell23_5419487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_5419487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419487 prefixEnd_5419487 := by exact prefixLift 5419487
  have htrace : WordTrace (prefixWord ++ tailWord_5419487) baseStart_5419487 baseEnd_5419487 := by
    simpa [prefixWord, tailWord_5419487, baseEnd_5419487] using wordTrace_append hprefix tailTrace_5419487
  have hstable : (prefixWord ++ tailWord_5419487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419487).length < 2 ^ (prefixWord ++ tailWord_5419487).sum := by decide
  have hdescent : baseEnd_5419487 < baseStart_5419487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419503 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 8]
def baseStart_5419503 : Nat := 118140960795 + 5419503 * 2 ^ 59
def prefixEnd_5419503 : Nat := 4983230072969 + 3 ^ 40 * 5419503 * 2
def baseEnd_5419503 : Nat := 927603315827871634429555

theorem tailTrace_5419503 : CollatzResearch.WordTrace tailWord_5419503 prefixEnd_5419503 927603315827871634429555 := by
  unfold tailWord_5419503
  simp only [CollatzResearch.WordTrace]
  refine ⟨197665513285073683268527163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131777008856715788845684775 197665513285073683268527163)
  ·
    refine ⟨296498269927610524902790745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197665513285073683268527163 296498269927610524902790745)
    ·
      refine ⟨222373702445707893677093059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296498269927610524902790745 222373702445707893677093059)
      ·
        refine ⟨333560553668561840515639589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222373702445707893677093059 333560553668561840515639589)
        ·
          refine ⟨62542603812855345096682423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333560553668561840515639589 62542603812855345096682423)
          ·
            refine ⟨93813905719283017645023635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62542603812855345096682423 93813905719283017645023635)
            ·
              refine ⟨140720858578924526467535453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93813905719283017645023635 140720858578924526467535453)
              ·
                refine ⟨52770321967096697425325795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140720858578924526467535453 52770321967096697425325795)
                ·
                  refine ⟨79155482950645046137988693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52770321967096697425325795 79155482950645046137988693)
                  ·
                    refine ⟨927603315827871634429555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79155482950645046137988693 927603315827871634429555)
                    ·
                      rfl

theorem cell23_5419503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_5419503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419503 prefixEnd_5419503 := by exact prefixLift 5419503
  have htrace : WordTrace (prefixWord ++ tailWord_5419503) baseStart_5419503 baseEnd_5419503 := by
    simpa [prefixWord, tailWord_5419503, baseEnd_5419503] using wordTrace_append hprefix tailTrace_5419503
  have hstable : (prefixWord ++ tailWord_5419503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419503).length < 2 ^ (prefixWord ++ tailWord_5419503).sum := by decide
  have hdescent : baseEnd_5419503 < baseStart_5419503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419530 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_5419530 : Nat := 118140960795 + 5419530 * 2 ^ 59
def prefixEnd_5419530 : Nat := 4983230072969 + 3 ^ 40 * 5419530 * 2
def baseEnd_5419530 : Nat := 2782823811461286297651041

theorem tailTrace_5419530 : CollatzResearch.WordTrace tailWord_5419530 prefixEnd_5419530 2782823811461286297651041 := by
  unfold tailWord_5419530
  simp only [CollatzResearch.WordTrace]
  refine ⟨49416624513993966719940011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131777665370650577919840029 49416624513993966719940011)
  ·
    refine ⟨74124936770990950079910017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49416624513993966719940011 74124936770990950079910017)
    ·
      refine ⟨55593702578243212559932513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74124936770990950079910017 55593702578243212559932513)
      ·
        refine ⟨41695276933682409419949385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55593702578243212559932513 41695276933682409419949385)
        ·
          refine ⟨31271457700261807064962039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41695276933682409419949385 31271457700261807064962039)
          ·
            refine ⟨46907186550392710597443059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31271457700261807064962039 46907186550392710597443059)
            ·
              refine ⟨70360779825589065896164589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46907186550392710597443059 70360779825589065896164589)
              ·
                refine ⟨26385292434595899711061721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70360779825589065896164589 26385292434595899711061721)
                ·
                  refine ⟨19788969325946924783296291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26385292434595899711061721 19788969325946924783296291)
                  ·
                    refine ⟨29683453988920387174944437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19788969325946924783296291 29683453988920387174944437)
                    ·
                      refine ⟨2782823811461286297651041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29683453988920387174944437 2782823811461286297651041)
                      ·
                        rfl

theorem cell23_5419530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_5419530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419530 prefixEnd_5419530 := by exact prefixLift 5419530
  have htrace : WordTrace (prefixWord ++ tailWord_5419530) baseStart_5419530 baseEnd_5419530 := by
    simpa [prefixWord, tailWord_5419530, baseEnd_5419530] using wordTrace_append hprefix tailTrace_5419530
  have hstable : (prefixWord ++ tailWord_5419530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419530).length < 2 ^ (prefixWord ++ tailWord_5419530).sum := by decide
  have hdescent : baseEnd_5419530 < baseStart_5419530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419531 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 1, 3, 2]
def baseStart_5419531 : Nat := 118140960795 + 5419531 * 2 ^ 59
def prefixEnd_5419531 : Nat := 4983230072969 + 3 ^ 40 * 5419531 * 2
def baseEnd_5419531 : Nat := 2782824324941940793738537

theorem tailTrace_5419531 : CollatzResearch.WordTrace tailWord_5419531 prefixEnd_5419531 2782824324941940793738537 := by
  unfold tailWord_5419531
  simp only [CollatzResearch.WordTrace]
  refine ⟨197666534528972244050546447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131777689685981496033697631 197666534528972244050546447)
  ·
    refine ⟨296499801793458366075819671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197666534528972244050546447 296499801793458366075819671)
    ·
      refine ⟨444749702690187549113729507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296499801793458366075819671 444749702690187549113729507)
      ·
        refine ⟨667124554035281323670594261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444749702690187549113729507 667124554035281323670594261)
        ·
          refine ⟨15635731735201906023529553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 667124554035281323670594261 15635731735201906023529553)
          ·
            refine ⟨11726798801401429517647165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15635731735201906023529553 11726798801401429517647165)
            ·
              refine ⟨4397549550525536069117687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11726798801401429517647165 4397549550525536069117687)
              ·
                refine ⟨6596324325788304103676531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397549550525536069117687 6596324325788304103676531)
                ·
                  refine ⟨9894486488682456155514797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596324325788304103676531 9894486488682456155514797)
                  ·
                    refine ⟨3710432433255921058318049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9894486488682456155514797 3710432433255921058318049)
                    ·
                      refine ⟨2782824324941940793738537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710432433255921058318049 2782824324941940793738537)
                      ·
                        rfl

theorem cell23_5419531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 3, 2].length) (baseStart_5419531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419531 prefixEnd_5419531 := by exact prefixLift 5419531
  have htrace : WordTrace (prefixWord ++ tailWord_5419531) baseStart_5419531 baseEnd_5419531 := by
    simpa [prefixWord, tailWord_5419531, baseEnd_5419531] using wordTrace_append hprefix tailTrace_5419531
  have hstable : (prefixWord ++ tailWord_5419531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419531).length < 2 ^ (prefixWord ++ tailWord_5419531).sum := by decide
  have hdescent : baseEnd_5419531 < baseStart_5419531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419582 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5419582 : Nat := 118140960795 + 5419582 * 2 ^ 59
def prefixEnd_5419582 : Nat := 4983230072969 + 3 ^ 40 * 5419582 * 2
def baseEnd_5419582 : Nat := 2782850512455320094200803

theorem tailTrace_5419582 : CollatzResearch.WordTrace tailWord_5419582 prefixEnd_5419582 2782850512455320094200803 := by
  unfold tailWord_5419582
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708549331473434970081625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131778929767858319840435333 24708549331473434970081625)
  ·
    refine ⟨18531411998605076227561219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24708549331473434970081625 18531411998605076227561219)
    ·
      refine ⟨27797117997907614341341829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18531411998605076227561219 27797117997907614341341829)
      ·
        refine ⟨5211959624607677689001593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27797117997907614341341829 5211959624607677689001593)
        ·
          refine ⟨3908969718455758266751195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5211959624607677689001593 3908969718455758266751195)
          ·
            refine ⟨5863454577683637400126793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908969718455758266751195 5863454577683637400126793)
            ·
              refine ⟨4397590933262728050095095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863454577683637400126793 4397590933262728050095095)
              ·
                refine ⟨6596386399894092075142643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397590933262728050095095 6596386399894092075142643)
                ·
                  refine ⟨9894579599841138112713965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596386399894092075142643 9894579599841138112713965)
                  ·
                    refine ⟨3710467349940426792267737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9894579599841138112713965 3710467349940426792267737)
                    ·
                      refine ⟨2782850512455320094200803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710467349940426792267737 2782850512455320094200803)
                      ·
                        rfl

theorem cell23_5419582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5419582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419582 prefixEnd_5419582 := by exact prefixLift 5419582
  have htrace : WordTrace (prefixWord ++ tailWord_5419582) baseStart_5419582 baseEnd_5419582 := by
    simpa [prefixWord, tailWord_5419582, baseEnd_5419582] using wordTrace_append hprefix tailTrace_5419582
  have hstable : (prefixWord ++ tailWord_5419582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419582).length < 2 ^ (prefixWord ++ tailWord_5419582).sum := by decide
  have hdescent : baseEnd_5419582 < baseStart_5419582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419660 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5419660 : Nat := 118140960795 + 5419660 * 2 ^ 59
def prefixEnd_5419660 : Nat := 4983230072969 + 3 ^ 40 * 5419660 * 2
def baseEnd_5419660 : Nat := 2782890563946370789025443

theorem tailTrace_5419660 : CollatzResearch.WordTrace tailWord_5419660 prefixEnd_5419660 2782890563946370789025443 := by
  unfold tailWord_5419660
  simp only [CollatzResearch.WordTrace]
  refine ⟨98835619772752449540996217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131780826363669932721328289 98835619772752449540996217)
  ·
    refine ⟨74126714829564337155747163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98835619772752449540996217 74126714829564337155747163)
    ·
      refine ⟨111190072244346505733620745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74126714829564337155747163 111190072244346505733620745)
      ·
        refine ⟨83392554183259879300215559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111190072244346505733620745 83392554183259879300215559)
        ·
          refine ⟨125088831274889818950323339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83392554183259879300215559 125088831274889818950323339)
          ·
            refine ⟨187633246912334728425485009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125088831274889818950323339 187633246912334728425485009)
            ·
              refine ⟨140724935184251046319113757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187633246912334728425485009 140724935184251046319113757)
              ·
                refine ⟨52771850694094142369667659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140724935184251046319113757 52771850694094142369667659)
                ·
                  refine ⟨79157776041141213554501489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52771850694094142369667659 79157776041141213554501489)
                  ·
                    refine ⟨59368332030855910165876117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79157776041141213554501489 59368332030855910165876117)
                    ·
                      refine ⟨2782890563946370789025443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59368332030855910165876117 2782890563946370789025443)
                      ·
                        rfl

theorem cell23_5419660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5419660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419660 prefixEnd_5419660 := by exact prefixLift 5419660
  have htrace : WordTrace (prefixWord ++ tailWord_5419660) baseStart_5419660 baseEnd_5419660 := by
    simpa [prefixWord, tailWord_5419660, baseEnd_5419660] using wordTrace_append hprefix tailTrace_5419660
  have hstable : (prefixWord ++ tailWord_5419660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419660).length < 2 ^ (prefixWord ++ tailWord_5419660).sum := by decide
  have hdescent : baseEnd_5419660 < baseStart_5419660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419684 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_5419684 : Nat := 118140960795 + 5419684 * 2 ^ 59
def prefixEnd_5419684 : Nat := 4983230072969 + 3 ^ 40 * 5419684 * 2
def baseEnd_5419684 : Nat := 2782902887482078695125333

theorem tailTrace_5419684 : CollatzResearch.WordTrace tailWord_5419684 prefixEnd_5419684 2782902887482078695125333 := by
  unfold tailWord_5419684
  simp only [CollatzResearch.WordTrace]
  refine ⟨98836057448708975590433053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131781409931611967453910737 98836057448708975590433053)
  ·
    refine ⟨37063521543265865846412395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98836057448708975590433053 37063521543265865846412395)
    ·
      refine ⟨55595282314898798769618593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37063521543265865846412395 55595282314898798769618593)
      ·
        refine ⟨41696461736174099077213945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55595282314898798769618593 41696461736174099077213945)
        ·
          refine ⟨31272346302130574307910459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41696461736174099077213945 31272346302130574307910459)
          ·
            refine ⟨46908519453195861461865689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31272346302130574307910459 46908519453195861461865689)
            ·
              refine ⟨35181389589896896096399267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46908519453195861461865689 35181389589896896096399267)
              ·
                refine ⟨52772084384845344144598901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35181389589896896096399267 52772084384845344144598901)
                ·
                  refine ⟨4947382911079251013556147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52772084384845344144598901 4947382911079251013556147)
                  ·
                    refine ⟨7421074366618876520334221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4947382911079251013556147 7421074366618876520334221)
                    ·
                      refine ⟨2782902887482078695125333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7421074366618876520334221 2782902887482078695125333)
                      ·
                        rfl

theorem cell23_5419684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_5419684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419684 prefixEnd_5419684 := by exact prefixLift 5419684
  have htrace : WordTrace (prefixWord ++ tailWord_5419684) baseStart_5419684 baseEnd_5419684 := by
    simpa [prefixWord, tailWord_5419684, baseEnd_5419684] using wordTrace_append hprefix tailTrace_5419684
  have hstable : (prefixWord ++ tailWord_5419684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419684).length < 2 ^ (prefixWord ++ tailWord_5419684).sum := by decide
  have hdescent : baseEnd_5419684 < baseStart_5419684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419724 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5419724 : Nat := 118140960795 + 5419724 * 2 ^ 59
def prefixEnd_5419724 : Nat := 4983230072969 + 3 ^ 40 * 5419724 * 2
def baseEnd_5419724 : Nat := 2782923426708258538625149

theorem tailTrace_5419724 : CollatzResearch.WordTrace tailWord_5419724 prefixEnd_5419724 2782923426708258538625149 := by
  unfold tailWord_5419724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98836786908636519006161113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131782382544848692008214817 98836786908636519006161113)
  ·
    refine ⟨74127590181477389254620835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98836786908636519006161113 74127590181477389254620835)
    ·
      refine ⟨111191385272216083881931253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74127590181477389254620835 111191385272216083881931253)
      ·
        refine ⟨10424192369270257863931055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111191385272216083881931253 10424192369270257863931055)
        ·
          refine ⟨15636288553905386795896583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424192369270257863931055 15636288553905386795896583)
          ·
            refine ⟨23454432830858080193844875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636288553905386795896583 23454432830858080193844875)
            ·
              refine ⟨35181649246287120290767313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23454432830858080193844875 35181649246287120290767313)
              ·
                refine ⟨26386236934715340218075485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35181649246287120290767313 26386236934715340218075485)
                ·
                  refine ⟨9894838850518252581778307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26386236934715340218075485 9894838850518252581778307)
                  ·
                    refine ⟨14842258275777378872667461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9894838850518252581778307 14842258275777378872667461)
                    ·
                      refine ⟨2782923426708258538625149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14842258275777378872667461 2782923426708258538625149)
                      ·
                        rfl

theorem cell23_5419724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5419724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419724 prefixEnd_5419724 := by exact prefixLift 5419724
  have htrace : WordTrace (prefixWord ++ tailWord_5419724) baseStart_5419724 baseEnd_5419724 := by
    simpa [prefixWord, tailWord_5419724, baseEnd_5419724] using wordTrace_append hprefix tailTrace_5419724
  have hstable : (prefixWord ++ tailWord_5419724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419724).length < 2 ^ (prefixWord ++ tailWord_5419724).sum := by decide
  have hdescent : baseEnd_5419724 < baseStart_5419724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419744 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_5419744 : Nat := 118140960795 + 5419744 * 2 ^ 59
def prefixEnd_5419744 : Nat := 4983230072969 + 3 ^ 40 * 5419744 * 2
def baseEnd_5419744 : Nat := 2782933696321348460375057

theorem tailTrace_5419744 : CollatzResearch.WordTrace tailWord_5419744 prefixEnd_5419744 2782933696321348460375057 := by
  unfold tailWord_5419744
  simp only [CollatzResearch.WordTrace]
  refine ⟨98837151638600290714025143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131782868851467054285366857 98837151638600290714025143)
  ·
    refine ⟨148255727457900436071037715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98837151638600290714025143 148255727457900436071037715)
    ·
      refine ⟨222383591186850654106556573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148255727457900436071037715 222383591186850654106556573)
      ·
        refine ⟨83393846695068995289958715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222383591186850654106556573 83393846695068995289958715)
        ·
          refine ⟨125090770042603492934938073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83393846695068995289958715 125090770042603492934938073)
          ·
            refine ⟨93818077531952619701203555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125090770042603492934938073 93818077531952619701203555)
            ·
              refine ⟨140727116297928929551805333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93818077531952619701203555 140727116297928929551805333)
              ·
                refine ⟨6596583576465418572740875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140727116297928929551805333 6596583576465418572740875)
                ·
                  refine ⟨9894875364698127859111313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596583576465418572740875 9894875364698127859111313)
                  ·
                    refine ⟨7421156523523595894333485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9894875364698127859111313 7421156523523595894333485)
                    ·
                      refine ⟨2782933696321348460375057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7421156523523595894333485 2782933696321348460375057)
                      ·
                        rfl

theorem cell23_5419744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_5419744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419744 prefixEnd_5419744 := by exact prefixLift 5419744
  have htrace : WordTrace (prefixWord ++ tailWord_5419744) baseStart_5419744 baseEnd_5419744 := by
    simpa [prefixWord, tailWord_5419744, baseEnd_5419744] using wordTrace_append hprefix tailTrace_5419744
  have hstable : (prefixWord ++ tailWord_5419744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419744).length < 2 ^ (prefixWord ++ tailWord_5419744).sum := by decide
  have hdescent : baseEnd_5419744 < baseStart_5419744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419758 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_5419758 : Nat := 118140960795 + 5419758 * 2 ^ 59
def prefixEnd_5419758 : Nat := 4983230072969 + 3 ^ 40 * 5419758 * 2
def baseEnd_5419758 : Nat := 2782940885050511405599993

theorem tailTrace_5419758 : CollatzResearch.WordTrace tailWord_5419758 prefixEnd_5419758 2782940885050511405599993 := by
  unfold tailWord_5419758
  simp only [CollatzResearch.WordTrace]
  refine ⟨24709351737393732727382491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131783209266099907879373285 24709351737393732727382491)
  ·
    refine ⟨37064027606090599091073737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24709351737393732727382491 37064027606090599091073737)
    ·
      refine ⟨27798020704567949318305303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37064027606090599091073737 27798020704567949318305303)
      ·
        refine ⟨41697031056851923977457955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27798020704567949318305303 41697031056851923977457955)
        ·
          refine ⟨62545546585277885966186933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41697031056851923977457955 62545546585277885966186933)
          ·
            refine ⟨5863644992369801809330025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62545546585277885966186933 5863644992369801809330025)
            ·
              refine ⟨4397733744277351356997519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863644992369801809330025 4397733744277351356997519)
              ·
                refine ⟨6596600616416027035496279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397733744277351356997519 6596600616416027035496279)
                ·
                  refine ⟨9894900924624040553244419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596600616416027035496279 9894900924624040553244419)
                  ·
                    refine ⟨14842351386936060829866629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9894900924624040553244419 14842351386936060829866629)
                    ·
                      refine ⟨2782940885050511405599993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14842351386936060829866629 2782940885050511405599993)
                      ·
                        rfl

theorem cell23_5419758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_5419758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419758 prefixEnd_5419758 := by exact prefixLift 5419758
  have htrace : WordTrace (prefixWord ++ tailWord_5419758) baseStart_5419758 baseEnd_5419758 := by
    simpa [prefixWord, tailWord_5419758, baseEnd_5419758] using wordTrace_append hprefix tailTrace_5419758
  have hstable : (prefixWord ++ tailWord_5419758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419758).length < 2 ^ (prefixWord ++ tailWord_5419758).sum := by decide
  have hdescent : baseEnd_5419758 < baseStart_5419758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_5419817 : Nat := 118140960795 + 5419817 * 2 ^ 59
def prefixEnd_5419817 : Nat := 4983230072969 + 3 ^ 40 * 5419817 * 2
def baseEnd_5419817 : Nat := 2782971180409126674762221

theorem tailTrace_5419817 : CollatzResearch.WordTrace tailWord_5419817 prefixEnd_5419817 2782971180409126674762221 := by
  unfold tailWord_5419817
  simp only [CollatzResearch.WordTrace]
  refine ⟨197676965805936114895457705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131784643870624076596971803 197676965805936114895457705)
  ·
    refine ⟨148257724354452086171593279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197676965805936114895457705 148257724354452086171593279)
    ·
      refine ⟨222386586531678129257389919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148257724354452086171593279 222386586531678129257389919)
      ·
        refine ⟨333579879797517193886084879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222386586531678129257389919 333579879797517193886084879)
        ·
          refine ⟨500369819696275790829127319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333579879797517193886084879 500369819696275790829127319)
          ·
            refine ⟨750554729544413686243690979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500369819696275790829127319 750554729544413686243690979)
            ·
              refine ⟨1125832094316620529365536469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750554729544413686243690979 1125832094316620529365536469)
              ·
                refine ⟨26386689710545793657004761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1125832094316620529365536469 26386689710545793657004761)
                ·
                  refine ⟨19790017282909345242753571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26386689710545793657004761 19790017282909345242753571)
                  ·
                    refine ⟨29685025924364017864130357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19790017282909345242753571 29685025924364017864130357)
                    ·
                      refine ⟨2782971180409126674762221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29685025924364017864130357 2782971180409126674762221)
                      ·
                        rfl

theorem cell23_5419817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_5419817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419817 prefixEnd_5419817 := by exact prefixLift 5419817
  have htrace : WordTrace (prefixWord ++ tailWord_5419817) baseStart_5419817 baseEnd_5419817 := by
    simpa [prefixWord, tailWord_5419817, baseEnd_5419817] using wordTrace_append hprefix tailTrace_5419817
  have hstable : (prefixWord ++ tailWord_5419817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419817).length < 2 ^ (prefixWord ++ tailWord_5419817).sum := by decide
  have hdescent : baseEnd_5419817 < baseStart_5419817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419831 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_5419831 : Nat := 118140960795 + 5419831 * 2 ^ 59
def prefixEnd_5419831 : Nat := 4983230072969 + 3 ^ 40 * 5419831 * 2
def baseEnd_5419831 : Nat := 2782978369138289619987157

theorem tailTrace_5419831 : CollatzResearch.WordTrace tailWord_5419831 prefixEnd_5419831 2782978369138289619987157 := by
  unfold tailWord_5419831
  simp only [CollatzResearch.WordTrace]
  refine ⟨197677476427885395286467347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131784984285256930190978231 197677476427885395286467347)
  ·
    refine ⟨296516214641828092929701021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197677476427885395286467347 296516214641828092929701021)
    ·
      refine ⟨111193580490685534848637883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296516214641828092929701021 111193580490685534848637883)
      ·
        refine ⟨166790370736028302272956825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111193580490685534848637883 166790370736028302272956825)
        ·
          refine ⟨125092778052021226704717619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166790370736028302272956825 125092778052021226704717619)
          ·
            refine ⟨187639167078031840057076429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125092778052021226704717619 187639167078031840057076429)
            ·
              refine ⟨70364687654261940021403661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187639167078031840057076429 70364687654261940021403661)
              ·
                refine ⟨26386757870348227508026373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70364687654261940021403661 26386757870348227508026373)
                ·
                  refine ⟨4947517100690292657754945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26386757870348227508026373 4947517100690292657754945)
                  ·
                    refine ⟨3710637825517719493316209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947517100690292657754945 3710637825517719493316209)
                    ·
                      refine ⟨2782978369138289619987157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710637825517719493316209 2782978369138289619987157)
                      ·
                        rfl

theorem cell23_5419831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_5419831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419831 prefixEnd_5419831 := by exact prefixLift 5419831
  have htrace : WordTrace (prefixWord ++ tailWord_5419831) baseStart_5419831 baseEnd_5419831 := by
    simpa [prefixWord, tailWord_5419831, baseEnd_5419831] using wordTrace_append hprefix tailTrace_5419831
  have hstable : (prefixWord ++ tailWord_5419831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419831).length < 2 ^ (prefixWord ++ tailWord_5419831).sum := by decide
  have hdescent : baseEnd_5419831 < baseStart_5419831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419848 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_5419848 : Nat := 118140960795 + 5419848 * 2 ^ 59
def prefixEnd_5419848 : Nat := 4983230072969 + 3 ^ 40 * 5419848 * 2
def baseEnd_5419848 : Nat := 2782987098309416053474579

theorem tailTrace_5419848 : CollatzResearch.WordTrace tailWord_5419848 prefixEnd_5419848 2782987098309416053474579 := by
  unfold tailWord_5419848
  simp only [CollatzResearch.WordTrace]
  refine ⟨98839048234411903594918099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131785397645882538126557465 98839048234411903594918099)
  ·
    refine ⟨148258572351617855392377149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98839048234411903594918099 148258572351617855392377149)
    ·
      refine ⟨55596964631856695772141431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148258572351617855392377149 55596964631856695772141431)
      ·
        refine ⟨83395446947785043658212147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55596964631856695772141431 83395446947785043658212147)
        ·
          refine ⟨125093170421677565487318221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83395446947785043658212147 125093170421677565487318221)
          ·
            refine ⟨46909938908129087057744333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125093170421677565487318221 46909938908129087057744333)
            ·
              refine ⟨17591227090548407646654125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46909938908129087057744333 17591227090548407646654125)
              ·
                refine ⟨6596710158955652867495297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17591227090548407646654125 6596710158955652867495297)
                ·
                  refine ⟨4947532619216739650621473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6596710158955652867495297 4947532619216739650621473)
                  ·
                    refine ⟨3710649464412554737966105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947532619216739650621473 3710649464412554737966105)
                    ·
                      refine ⟨2782987098309416053474579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710649464412554737966105 2782987098309416053474579)
                      ·
                        rfl

theorem cell23_5419848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_5419848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419848 prefixEnd_5419848 := by exact prefixLift 5419848
  have htrace : WordTrace (prefixWord ++ tailWord_5419848) baseStart_5419848 baseEnd_5419848 := by
    simpa [prefixWord, tailWord_5419848, baseEnd_5419848] using wordTrace_append hprefix tailTrace_5419848
  have hstable : (prefixWord ++ tailWord_5419848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419848).length < 2 ^ (prefixWord ++ tailWord_5419848).sum := by decide
  have hdescent : baseEnd_5419848 < baseStart_5419848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419884 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_5419884 : Nat := 118140960795 + 5419884 * 2 ^ 59
def prefixEnd_5419884 : Nat := 4983230072969 + 3 ^ 40 * 5419884 * 2
def baseEnd_5419884 : Nat := 927668527870992637541471

theorem tailTrace_5419884 : CollatzResearch.WordTrace tailWord_5419884 prefixEnd_5419884 927668527870992637541471 := by
  unfold tailWord_5419884
  simp only [CollatzResearch.WordTrace]
  refine ⟨98839704748346692669073353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131786272997795590225431137 98839704748346692669073353)
  ·
    refine ⟨74129778561260019501805015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98839704748346692669073353 74129778561260019501805015)
    ·
      refine ⟨111194667841890029252707523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74129778561260019501805015 111194667841890029252707523)
      ·
        refine ⟨166792001762835043879061285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111194667841890029252707523 166792001762835043879061285)
        ·
          refine ⟨31273500330531570727323991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166792001762835043879061285 31273500330531570727323991)
          ·
            refine ⟨46910250495797356090985987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31273500330531570727323991 46910250495797356090985987)
            ·
              refine ⟨70365375743696034136478981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46910250495797356090985987 70365375743696034136478981)
              ·
                refine ⟨13193507951943006400589809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70365375743696034136478981 13193507951943006400589809)
                ·
                  refine ⟨9895130963957254800442357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13193507951943006400589809 9895130963957254800442357)
                  ·
                    refine ⟨927668527870992637541471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9895130963957254800442357 927668527870992637541471)
                    ·
                      rfl

theorem cell23_5419884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_5419884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419884 prefixEnd_5419884 := by exact prefixLift 5419884
  have htrace : WordTrace (prefixWord ++ tailWord_5419884) baseStart_5419884 baseEnd_5419884 := by
    simpa [prefixWord, tailWord_5419884, baseEnd_5419884] using wordTrace_append hprefix tailTrace_5419884
  have hstable : (prefixWord ++ tailWord_5419884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419884).length < 2 ^ (prefixWord ++ tailWord_5419884).sum := by decide
  have hdescent : baseEnd_5419884 < baseStart_5419884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5419938 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_5419938 : Nat := 118140960795 + 5419938 * 2 ^ 59
def prefixEnd_5419938 : Nat := 4983230072969 + 3 ^ 40 * 5419938 * 2
def baseEnd_5419938 : Nat := 2783033311568320701349165

theorem tailTrace_5419938 : CollatzResearch.WordTrace tailWord_5419938 prefixEnd_5419938 2783033311568320701349165 := by
  unfold tailWord_5419938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49420344759624438140153117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131787586025665168373741645 49420344759624438140153117)
  ·
    refine ⟨18532629284859164302557419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49420344759624438140153117 18532629284859164302557419)
    ·
      refine ⟨27798943927288746453836129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18532629284859164302557419 27798943927288746453836129)
      ·
        refine ⟨20849207945466559840377097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27798943927288746453836129 20849207945466559840377097)
        ·
          refine ⟨15636905959099919880282823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20849207945466559840377097 15636905959099919880282823)
          ·
            refine ⟨23455358938649879820424235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636905959099919880282823 23455358938649879820424235)
            ·
              refine ⟨35183038407974819730636353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23455358938649879820424235 35183038407974819730636353)
              ·
                refine ⟨26387278805981114797977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35183038407974819730636353 26387278805981114797977265)
                ·
                  refine ⟨19790459104485836098482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26387278805981114797977265 19790459104485836098482949)
                  ·
                    refine ⟨3710711082091094268465553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19790459104485836098482949 3710711082091094268465553)
                    ·
                      refine ⟨2783033311568320701349165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710711082091094268465553 2783033311568320701349165)
                      ·
                        rfl

theorem cell23_5419938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_5419938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5419938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5419938 prefixEnd_5419938 := by exact prefixLift 5419938
  have htrace : WordTrace (prefixWord ++ tailWord_5419938) baseStart_5419938 baseEnd_5419938 := by
    simpa [prefixWord, tailWord_5419938, baseEnd_5419938] using wordTrace_append hprefix tailTrace_5419938
  have hstable : (prefixWord ++ tailWord_5419938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5419938).length < 2 ^ (prefixWord ++ tailWord_5419938).sum := by decide
  have hdescent : baseEnd_5419938 < baseStart_5419938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5419938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420004 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_5420004 : Nat := 118140960795 + 5420004 * 2 ^ 59
def prefixEnd_5420004 : Nat := 4983230072969 + 3 ^ 40 * 5420004 * 2
def baseEnd_5420004 : Nat := 927689067097172481041287

theorem tailTrace_5420004 : CollatzResearch.WordTrace tailWord_5420004 prefixEnd_5420004 927689067097172481041287 := by
  unfold tailWord_5420004
  simp only [CollatzResearch.WordTrace]
  refine ⟨98841893128129322916257533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131789190837505763888343377 98841893128129322916257533)
  ·
    refine ⟨37065709923048496093596575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98841893128129322916257533 37065709923048496093596575)
    ·
      refine ⟨55598564884572744140394863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37065709923048496093596575 55598564884572744140394863)
      ·
        refine ⟨83397847326859116210592295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55598564884572744140394863 83397847326859116210592295)
        ·
          refine ⟨125096770990288674315888443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83397847326859116210592295 125096770990288674315888443)
          ·
            refine ⟨187645156485433011473832665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125096770990288674315888443 187645156485433011473832665)
            ·
              refine ⟨140733867364074758605374499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187645156485433011473832665 140733867364074758605374499)
              ·
                refine ⟨211100801046112137908061749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140733867364074758605374499 211100801046112137908061749)
                ·
                  refine ⟨19790700098073012928880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211100801046112137908061749 19790700098073012928880789)
                  ·
                    refine ⟨927689067097172481041287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19790700098073012928880789 927689067097172481041287)
                    ·
                      rfl

theorem cell23_5420004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_5420004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420004 prefixEnd_5420004 := by exact prefixLift 5420004
  have htrace : WordTrace (prefixWord ++ tailWord_5420004) baseStart_5420004 baseEnd_5420004 := by
    simpa [prefixWord, tailWord_5420004, baseEnd_5420004] using wordTrace_append hprefix tailTrace_5420004
  have hstable : (prefixWord ++ tailWord_5420004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420004).length < 2 ^ (prefixWord ++ tailWord_5420004).sum := by decide
  have hdescent : baseEnd_5420004 < baseStart_5420004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420028 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_5420028 : Nat := 118140960795 + 5420028 * 2 ^ 59
def prefixEnd_5420028 : Nat := 4983230072969 + 3 ^ 40 * 5420028 * 2
def baseEnd_5420028 : Nat := 2783079524827225349223751

theorem tailTrace_5420028 : CollatzResearch.WordTrace tailWord_5420028 prefixEnd_5420028 2783079524827225349223751 := by
  unfold tailWord_5420028
  simp only [CollatzResearch.WordTrace]
  refine ⟨98842330804085848965694369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131789774405447798620925825 98842330804085848965694369)
  ·
    refine ⟨74131748103064386724270777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98842330804085848965694369 74131748103064386724270777)
    ·
      refine ⟨55598811077298290043203083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74131748103064386724270777 55598811077298290043203083)
      ·
        refine ⟨83398216615947435064804625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55598811077298290043203083 83398216615947435064804625)
        ·
          refine ⟨62548662461960576298603469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83398216615947435064804625 62548662461960576298603469)
          ·
            refine ⟨23455748423235216111976301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62548662461960576298603469 23455748423235216111976301)
            ·
              refine ⟨8795905658713206041991113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23455748423235216111976301 8795905658713206041991113)
              ·
                refine ⟨6596929244034904531493335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8795905658713206041991113 6596929244034904531493335)
                ·
                  refine ⟨9895393866052356797240003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596929244034904531493335 9895393866052356797240003)
                  ·
                    refine ⟨14843090799078535195860005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9895393866052356797240003 14843090799078535195860005)
                    ·
                      refine ⟨2783079524827225349223751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14843090799078535195860005 2783079524827225349223751)
                      ·
                        rfl

theorem cell23_5420028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_5420028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420028 prefixEnd_5420028 := by exact prefixLift 5420028
  have htrace : WordTrace (prefixWord ++ tailWord_5420028) baseStart_5420028 baseEnd_5420028 := by
    simpa [prefixWord, tailWord_5420028, baseEnd_5420028] using wordTrace_append hprefix tailTrace_5420028
  have hstable : (prefixWord ++ tailWord_5420028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420028).length < 2 ^ (prefixWord ++ tailWord_5420028).sum := by decide
  have hdescent : baseEnd_5420028 < baseStart_5420028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420055 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 2, 4]
def baseStart_5420055 : Nat := 118140960795 + 5420055 * 2 ^ 59
def prefixEnd_5420055 : Nat := 4983230072969 + 3 ^ 40 * 5420055 * 2
def baseEnd_5420055 : Nat := 927697796268298914528709

theorem tailTrace_5420055 : CollatzResearch.WordTrace tailWord_5420055 prefixEnd_5420055 927697796268298914528709 := by
  unfold tailWord_5420055
  simp only [CollatzResearch.WordTrace]
  refine ⟨197685646379073881542621619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131790430919382587695081079 197685646379073881542621619)
  ·
    refine ⟨296528469568610822313932429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197685646379073881542621619 296528469568610822313932429)
    ·
      refine ⟨111198176088229058367724661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296528469568610822313932429 111198176088229058367724661)
      ·
        refine ⟨10424829008271474221974187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111198176088229058367724661 10424829008271474221974187)
        ·
          refine ⟨15637243512407211332961281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424829008271474221974187 15637243512407211332961281)
          ·
            refine ⟨11727932634305408499720961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15637243512407211332961281 11727932634305408499720961)
            ·
              refine ⟨8795949475729056374790721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11727932634305408499720961 8795949475729056374790721)
              ·
                refine ⟨6596962106796792281093041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8795949475729056374790721 6596962106796792281093041)
                ·
                  refine ⟨4947721580097594210819781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6596962106796792281093041 4947721580097594210819781)
                  ·
                    refine ⟨927697796268298914528709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947721580097594210819781 927697796268298914528709)
                    ·
                      rfl

theorem cell23_5420055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_5420055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420055 prefixEnd_5420055 := by exact prefixLift 5420055
  have htrace : WordTrace (prefixWord ++ tailWord_5420055) baseStart_5420055 baseEnd_5420055 := by
    simpa [prefixWord, tailWord_5420055, baseEnd_5420055] using wordTrace_append hprefix tailTrace_5420055
  have hstable : (prefixWord ++ tailWord_5420055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420055).length < 2 ^ (prefixWord ++ tailWord_5420055).sum := by decide
  have hdescent : baseEnd_5420055 < baseStart_5420055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420068 : List Nat := [2, 3, 1, 4, 1, 3, 1, 8]
def baseStart_5420068 : Nat := 118140960795 + 5420068 * 2 ^ 59
def prefixEnd_5420068 : Nat := 4983230072969 + 3 ^ 40 * 5420068 * 2
def baseEnd_5420068 : Nat := 103077780150126118249021

theorem tailTrace_5420068 : CollatzResearch.WordTrace tailWord_5420068 prefixEnd_5420068 103077780150126118249021 := by
  unfold tailWord_5420068
  simp only [CollatzResearch.WordTrace]
  refine ⟨98843060264013392381422429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131790747018684523175229905 98843060264013392381422429)
  ·
    refine ⟨37066147599005022143033411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98843060264013392381422429 37066147599005022143033411)
    ·
      refine ⟨55599221398507533214550117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37066147599005022143033411 55599221398507533214550117)
      ·
        refine ⟨10424854012220162477728147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55599221398507533214550117 10424854012220162477728147)
        ·
          refine ⟨15637281018330243716592221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424854012220162477728147 15637281018330243716592221)
          ·
            refine ⟨5863980381873841393722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15637281018330243716592221 5863980381873841393722083)
            ·
              refine ⟨8795970572810762090583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863980381873841393722083 8795970572810762090583125)
              ·
                refine ⟨103077780150126118249021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8795970572810762090583125 103077780150126118249021)
                ·
                  rfl

theorem cell23_5420068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 8].length) (baseStart_5420068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420068 prefixEnd_5420068 := by exact prefixLift 5420068
  have htrace : WordTrace (prefixWord ++ tailWord_5420068) baseStart_5420068 baseEnd_5420068 := by
    simpa [prefixWord, tailWord_5420068, baseEnd_5420068] using wordTrace_append hprefix tailTrace_5420068
  have hstable : (prefixWord ++ tailWord_5420068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420068).length < 2 ^ (prefixWord ++ tailWord_5420068).sum := by decide
  have hdescent : baseEnd_5420068 < baseStart_5420068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420121 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_5420121 : Nat := 118140960795 + 5420121 * 2 ^ 59
def prefixEnd_5420121 : Nat := 4983230072969 + 3 ^ 40 * 5420121 * 2
def baseEnd_5420121 : Nat := 2783127278528093485360823

theorem tailTrace_5420121 : CollatzResearch.WordTrace tailWord_5420121 prefixEnd_5420121 2783127278528093485360823 := by
  unfold tailWord_5420121
  simp only [CollatzResearch.WordTrace]
  refine ⟨197688053596834774814524217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131792035731223183209682811 197688053596834774814524217)
  ·
    refine ⟨148266040197626081110893163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197688053596834774814524217 148266040197626081110893163)
    ·
      refine ⟨222399060296439121666339745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148266040197626081110893163 222399060296439121666339745)
      ·
        refine ⟨166799295222329341249754809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222399060296439121666339745 166799295222329341249754809)
        ·
          refine ⟨125099471416747005937316107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166799295222329341249754809 125099471416747005937316107)
          ·
            refine ⟨187649207125120508905974161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125099471416747005937316107 187649207125120508905974161)
            ·
              refine ⟨140736905343840381679480621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187649207125120508905974161 140736905343840381679480621)
              ·
                refine ⟨52776339503940143129805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140736905343840381679480621 52776339503940143129805233)
                ·
                  refine ⟨39582254627955107347353925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52776339503940143129805233 39582254627955107347353925)
                  ·
                    refine ⟨7421672742741582627628861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39582254627955107347353925 7421672742741582627628861)
                    ·
                      refine ⟨2783127278528093485360823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7421672742741582627628861 2783127278528093485360823)
                      ·
                        rfl

theorem cell23_5420121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_5420121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420121 prefixEnd_5420121 := by exact prefixLift 5420121
  have htrace : WordTrace (prefixWord ++ tailWord_5420121) baseStart_5420121 baseEnd_5420121 := by
    simpa [prefixWord, tailWord_5420121, baseEnd_5420121] using wordTrace_append hprefix tailTrace_5420121
  have hstable : (prefixWord ++ tailWord_5420121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420121).length < 2 ^ (prefixWord ++ tailWord_5420121).sum := by decide
  have hdescent : baseEnd_5420121 < baseStart_5420121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420135 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_5420135 : Nat := 118140960795 + 5420135 * 2 ^ 59
def prefixEnd_5420135 : Nat := 4983230072969 + 3 ^ 40 * 5420135 * 2
def baseEnd_5420135 : Nat := 2783134467257256430585759

theorem tailTrace_5420135 : CollatzResearch.WordTrace tailWord_5420135 prefixEnd_5420135 2783134467257256430585759 := by
  unfold tailWord_5420135
  simp only [CollatzResearch.WordTrace]
  refine ⟨197688564218784055205533859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131792376145856036803689239 197688564218784055205533859)
  ·
    refine ⟨296532846328176082808300789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197688564218784055205533859 296532846328176082808300789)
    ·
      refine ⟨27799954343266507763278199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296532846328176082808300789 27799954343266507763278199)
      ·
        refine ⟨41699931514899761644917299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27799954343266507763278199 41699931514899761644917299)
        ·
          refine ⟨62549897272349642467375949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41699931514899761644917299 62549897272349642467375949)
          ·
            refine ⟨23456211477131115925265981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62549897272349642467375949 23456211477131115925265981)
            ·
              refine ⟨8796079303924168471974743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23456211477131115925265981 8796079303924168471974743)
              ·
                refine ⟨13194118955886252707962115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796079303924168471974743 13194118955886252707962115)
                ·
                  refine ⟨19791178433829379061943173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13194118955886252707962115 19791178433829379061943173)
                  ·
                    refine ⟨3710845956343008574114345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19791178433829379061943173 3710845956343008574114345)
                    ·
                      refine ⟨2783134467257256430585759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710845956343008574114345 2783134467257256430585759)
                      ·
                        rfl

theorem cell23_5420135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_5420135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420135 prefixEnd_5420135 := by exact prefixLift 5420135
  have htrace : WordTrace (prefixWord ++ tailWord_5420135) baseStart_5420135 baseEnd_5420135 := by
    simpa [prefixWord, tailWord_5420135, baseEnd_5420135] using wordTrace_append hprefix tailTrace_5420135
  have hstable : (prefixWord ++ tailWord_5420135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420135).length < 2 ^ (prefixWord ++ tailWord_5420135).sum := by decide
  have hdescent : baseEnd_5420135 < baseStart_5420135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420186 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5420186 : Nat := 118140960795 + 5420186 * 2 ^ 59
def prefixEnd_5420186 : Nat := 4983230072969 + 3 ^ 40 * 5420186 * 2
def baseEnd_5420186 : Nat := 2783160654770635731048025

theorem tailTrace_5420186 : CollatzResearch.WordTrace tailWord_5420186 prefixEnd_5420186 2783160654770635731048025 := by
  unfold tailWord_5420186
  simp only [CollatzResearch.WordTrace]
  refine ⟨49422606085399822728910103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131793616227732860610426941 49422606085399822728910103)
  ·
    refine ⟨74133909128099734093365155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49422606085399822728910103 74133909128099734093365155)
    ·
      refine ⟨111200863692149601140047733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74133909128099734093365155 111200863692149601140047733)
      ·
        refine ⟨10425080971139025106879475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111200863692149601140047733 10425080971139025106879475)
        ·
          refine ⟨15637621456708537660319213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10425080971139025106879475 15637621456708537660319213)
          ·
            refine ⟨5864108046265701622619705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15637621456708537660319213 5864108046265701622619705)
            ·
              refine ⟨4398081034699276216964779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864108046265701622619705 4398081034699276216964779)
              ·
                refine ⟨6597121552048914325447169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398081034699276216964779 6597121552048914325447169)
                ·
                  refine ⟨4947841164036685744085377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597121552048914325447169 4947841164036685744085377)
                  ·
                    refine ⟨3710880873027514308064033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947841164036685744085377 3710880873027514308064033)
                    ·
                      refine ⟨2783160654770635731048025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710880873027514308064033 2783160654770635731048025)
                      ·
                        rfl

theorem cell23_5420186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5420186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420186 prefixEnd_5420186 := by exact prefixLift 5420186
  have htrace : WordTrace (prefixWord ++ tailWord_5420186) baseStart_5420186 baseEnd_5420186 := by
    simpa [prefixWord, tailWord_5420186, baseEnd_5420186] using wordTrace_append hprefix tailTrace_5420186
  have hstable : (prefixWord ++ tailWord_5420186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420186).length < 2 ^ (prefixWord ++ tailWord_5420186).sum := by decide
  have hdescent : baseEnd_5420186 < baseStart_5420186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420208 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2]
def baseStart_5420208 : Nat := 118140960795 + 5420208 * 2 ^ 59
def prefixEnd_5420208 : Nat := 4983230072969 + 3 ^ 40 * 5420208 * 2
def baseEnd_5420208 : Nat := 2783171951345034644972923

theorem tailTrace_5420208 : CollatzResearch.WordTrace tailWord_5420208 prefixEnd_5420208 2783171951345034644972923 := by
  unfold tailWord_5420208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98845613373759794336470639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131794151165013059115294185 98845613373759794336470639)
  ·
    refine ⟨148268420060639691504705959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98845613373759794336470639 148268420060639691504705959)
    ·
      refine ⟨222402630090959537257058939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148268420060639691504705959 222402630090959537257058939)
      ·
        refine ⟨333603945136439305885588409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222402630090959537257058939 333603945136439305885588409)
        ·
          refine ⟨250202958852329479414191307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333603945136439305885588409 250202958852329479414191307)
          ·
            refine ⟨375304438278494219121286961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250202958852329479414191307 375304438278494219121286961)
            ·
              refine ⟨281478328708870664340965221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375304438278494219121286961 281478328708870664340965221)
              ·
                refine ⟨52777186632913249563930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281478328708870664340965221 52777186632913249563930979)
                ·
                  refine ⟨79165779949369874345896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52777186632913249563930979 79165779949369874345896469)
                  ·
                    refine ⟨3710895935126712859963897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79165779949369874345896469 3710895935126712859963897)
                    ·
                      refine ⟨2783171951345034644972923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3710895935126712859963897 2783171951345034644972923)
                      ·
                        rfl

theorem cell23_5420208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2].length) (baseStart_5420208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420208 prefixEnd_5420208 := by exact prefixLift 5420208
  have htrace : WordTrace (prefixWord ++ tailWord_5420208) baseStart_5420208 baseEnd_5420208 := by
    simpa [prefixWord, tailWord_5420208, baseEnd_5420208] using wordTrace_append hprefix tailTrace_5420208
  have hstable : (prefixWord ++ tailWord_5420208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420208).length < 2 ^ (prefixWord ++ tailWord_5420208).sum := by decide
  have hdescent : baseEnd_5420208 < baseStart_5420208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420231 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 8]
def baseStart_5420231 : Nat := 118140960795 + 5420231 * 2 ^ 59
def prefixEnd_5420231 : Nat := 4983230072969 + 3 ^ 40 * 5420231 * 2
def baseEnd_5420231 : Nat := 309242640155565339442813

theorem tailTrace_5420231 : CollatzResearch.WordTrace tailWord_5420231 prefixEnd_5420231 309242640155565339442813 := by
  unfold tailWord_5420231
  simp only [CollatzResearch.WordTrace]
  refine ⟨197692065626436263601028547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131794710417624175734019031 197692065626436263601028547)
  ·
    refine ⟨296538098439654395401542821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197692065626436263601028547 296538098439654395401542821)
    ·
      refine ⟨55600893457435199137789279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296538098439654395401542821 55600893457435199137789279)
      ·
        refine ⟨83401340186152798706683919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55600893457435199137789279 83401340186152798706683919)
        ·
          refine ⟨125102010279229198060025879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83401340186152798706683919 125102010279229198060025879)
          ·
            refine ⟨187653015418843797090038819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125102010279229198060025879 187653015418843797090038819)
            ·
              refine ⟨281479523128265695635058229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187653015418843797090038819 281479523128265695635058229)
              ·
                refine ⟨26388705293274908965786709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281479523128265695635058229 26388705293274908965786709)
                ·
                  refine ⟨309242640155565339442813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26388705293274908965786709 309242640155565339442813)
                  ·
                    rfl

theorem cell23_5420231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 8].length) (baseStart_5420231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420231 prefixEnd_5420231 := by exact prefixLift 5420231
  have htrace : WordTrace (prefixWord ++ tailWord_5420231) baseStart_5420231 baseEnd_5420231 := by
    simpa [prefixWord, tailWord_5420231, baseEnd_5420231] using wordTrace_append hprefix tailTrace_5420231
  have hstable : (prefixWord ++ tailWord_5420231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420231).length < 2 ^ (prefixWord ++ tailWord_5420231).sum := by decide
  have hdescent : baseEnd_5420231 < baseStart_5420231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420269 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5420269 : Nat := 118140960795 + 5420269 * 2 ^ 59
def prefixEnd_5420269 : Nat := 4983230072969 + 3 ^ 40 * 5420269 * 2
def baseEnd_5420269 : Nat := 927734424554986302103381

theorem tailTrace_5420269 : CollatzResearch.WordTrace tailWord_5420269 prefixEnd_5420269 927734424554986302103381 := by
  unfold tailWord_5420269
  simp only [CollatzResearch.WordTrace]
  refine ⟨197693451600298596090911861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131795634400199064060607907 197693451600298596090911861)
  ·
    refine ⟨18533761087527993383522987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197693451600298596090911861 18533761087527993383522987)
    ·
      refine ⟨27800641631291990075284481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18533761087527993383522987 27800641631291990075284481)
      ·
        refine ⟨20850481223468992556463361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27800641631291990075284481 20850481223468992556463361)
        ·
          refine ⟨15637860917601744417347521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20850481223468992556463361 15637860917601744417347521)
          ·
            refine ⟨11728395688201308313010641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15637860917601744417347521 11728395688201308313010641)
            ·
              refine ⟨8796296766150981234757981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11728395688201308313010641 8796296766150981234757981)
              ·
                refine ⟨3298611287306617963034243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8796296766150981234757981 3298611287306617963034243)
                ·
                  refine ⟨4947916930959926944551365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298611287306617963034243 4947916930959926944551365)
                  ·
                    refine ⟨927734424554986302103381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947916930959926944551365 927734424554986302103381)
                    ·
                      rfl

theorem cell23_5420269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5420269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420269 prefixEnd_5420269 := by exact prefixLift 5420269
  have htrace : WordTrace (prefixWord ++ tailWord_5420269) baseStart_5420269 baseEnd_5420269 := by
    simpa [prefixWord, tailWord_5420269, baseEnd_5420269] using wordTrace_append hprefix tailTrace_5420269
  have hstable : (prefixWord ++ tailWord_5420269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420269).length < 2 ^ (prefixWord ++ tailWord_5420269).sum := by decide
  have hdescent : baseEnd_5420269 < baseStart_5420269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420292 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5420292 : Nat := 118140960795 + 5420292 * 2 ^ 59
def prefixEnd_5420292 : Nat := 4983230072969 + 3 ^ 40 * 5420292 * 2
def baseEnd_5420292 : Nat := 2783215083720012316322537

theorem tailTrace_5420292 : CollatzResearch.WordTrace tailWord_5420292 prefixEnd_5420292 2783215083720012316322537 := by
  unfold tailWord_5420292
  simp only [CollatzResearch.WordTrace]
  refine ⟨98847145239607635509499565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131796193652810180679332753 98847145239607635509499565)
  ·
    refine ⟨37067679464852863316062337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98847145239607635509499565 37067679464852863316062337)
    ·
      refine ⟨27800759598639647487046753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37067679464852863316062337 27800759598639647487046753)
      ·
        refine ⟨20850569698979735615285065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27800759598639647487046753 20850569698979735615285065)
        ·
          refine ⟨15637927274234801711463799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20850569698979735615285065 15637927274234801711463799)
          ·
            refine ⟨23456890911352202567195699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15637927274234801711463799 23456890911352202567195699)
            ·
              refine ⟨35185336367028303850793549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23456890911352202567195699 35185336367028303850793549)
              ·
                refine ⟨13194501137635613944047581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35185336367028303850793549 13194501137635613944047581)
                ·
                  refine ⟨4947937926613355229017843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13194501137635613944047581 4947937926613355229017843)
                  ·
                    refine ⟨7421906889920032843526765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4947937926613355229017843 7421906889920032843526765)
                    ·
                      refine ⟨2783215083720012316322537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7421906889920032843526765 2783215083720012316322537)
                      ·
                        rfl

theorem cell23_5420292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5420292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420292 prefixEnd_5420292 := by exact prefixLift 5420292
  have htrace : WordTrace (prefixWord ++ tailWord_5420292) baseStart_5420292 baseEnd_5420292 := by
    simpa [prefixWord, tailWord_5420292, baseEnd_5420292] using wordTrace_append hprefix tailTrace_5420292
  have hstable : (prefixWord ++ tailWord_5420292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420292).length < 2 ^ (prefixWord ++ tailWord_5420292).sum := by decide
  have hdescent : baseEnd_5420292 < baseStart_5420292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420325 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_5420325 : Nat := 118140960795 + 5420325 * 2 ^ 59
def prefixEnd_5420325 : Nat := 4983230072969 + 3 ^ 40 * 5420325 * 2
def baseEnd_5420325 : Nat := 927744009527203562403295

theorem tailTrace_5420325 : CollatzResearch.WordTrace tailWord_5420325 prefixEnd_5420325 927744009527203562403295 := by
  unfold tailWord_5420325
  simp only [CollatzResearch.WordTrace]
  refine ⟨197695494088095717654950429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131796996058730478436633619 197695494088095717654950429)
  ·
    refine ⟨74135810283035894120606411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197695494088095717654950429 74135810283035894120606411)
    ·
      refine ⟨111203715424553841180909617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74135810283035894120606411 111203715424553841180909617)
      ·
        refine ⟨83402786568415380885682213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111203715424553841180909617 83402786568415380885682213)
        ·
          refine ⟨15638022481577883916065415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83402786568415380885682213 15638022481577883916065415)
          ·
            refine ⟨23457033722366825874098123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15638022481577883916065415 23457033722366825874098123)
            ·
              refine ⟨35185550583550238811147185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23457033722366825874098123 35185550583550238811147185)
              ·
                refine ⟨26389162937662679108360389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35185550583550238811147185 26389162937662679108360389)
                ·
                  refine ⟨4947968050811752332817573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26389162937662679108360389 4947968050811752332817573)
                  ·
                    refine ⟨927744009527203562403295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947968050811752332817573 927744009527203562403295)
                    ·
                      rfl

theorem cell23_5420325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_5420325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420325 prefixEnd_5420325 := by exact prefixLift 5420325
  have htrace : WordTrace (prefixWord ++ tailWord_5420325) baseStart_5420325 baseEnd_5420325 := by
    simpa [prefixWord, tailWord_5420325, baseEnd_5420325] using wordTrace_append hprefix tailTrace_5420325
  have hstable : (prefixWord ++ tailWord_5420325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420325).length < 2 ^ (prefixWord ++ tailWord_5420325).sum := by decide
  have hdescent : baseEnd_5420325 < baseStart_5420325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420338 : List Nat := [3, 2, 1, 1, 4, 1, 11]
def baseStart_5420338 : Nat := 118140960795 + 5420338 * 2 ^ 59
def prefixEnd_5420338 : Nat := 4983230072969 + 3 ^ 40 * 5420338 * 2
def baseEnd_5420338 : Nat := 34360971652223693041325

theorem tailTrace_5420338 : CollatzResearch.WordTrace tailWord_5420338 prefixEnd_5420338 34360971652223693041325 := by
  unfold tailWord_5420338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49423992059262155218793417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131797312158032413916782445 49423992059262155218793417)
  ·
    refine ⟨37067994044446616414095063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49423992059262155218793417 37067994044446616414095063)
    ·
      refine ⟨55601991066669924621142595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37067994044446616414095063 55601991066669924621142595)
      ·
        refine ⟨83402986600004886931713893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55601991066669924621142595 83402986600004886931713893)
        ·
          refine ⟨15638059987500916299696355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83402986600004886931713893 15638059987500916299696355)
          ·
            refine ⟨23457089981251374449544533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15638059987500916299696355 23457089981251374449544533)
            ·
              refine ⟨34360971652223693041325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23457089981251374449544533 34360971652223693041325)
              ·
                rfl

theorem cell23_5420338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 11].length) (baseStart_5420338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420338 prefixEnd_5420338 := by exact prefixLift 5420338
  have htrace : WordTrace (prefixWord ++ tailWord_5420338) baseStart_5420338 baseEnd_5420338 := by
    simpa [prefixWord, tailWord_5420338, baseEnd_5420338] using wordTrace_append hprefix tailTrace_5420338
  have hstable : (prefixWord ++ tailWord_5420338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420338).length < 2 ^ (prefixWord ++ tailWord_5420338).sum := by decide
  have hdescent : baseEnd_5420338 < baseStart_5420338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420359 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 2, 4]
def baseStart_5420359 : Nat := 118140960795 + 5420359 * 2 ^ 59
def prefixEnd_5420359 : Nat := 4983230072969 + 3 ^ 40 * 5420359 * 2
def baseEnd_5420359 : Nat := 927749828974621184728243

theorem tailTrace_5420359 : CollatzResearch.WordTrace tailWord_5420359 prefixEnd_5420359 927749828974621184728243 := by
  unfold tailWord_5420359
  simp only [CollatzResearch.WordTrace]
  refine ⟨197696734169972541461688131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131797822779981694307792087 197696734169972541461688131)
  ·
    refine ⟨296545101254958812192532197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197696734169972541461688131 296545101254958812192532197)
    ·
      refine ⟨55602206485304777286099787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296545101254958812192532197 55602206485304777286099787)
      ·
        refine ⟨83403309727957165929149681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55602206485304777286099787 83403309727957165929149681)
        ·
          refine ⟨62552482295967874446862261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83403309727957165929149681 62552482295967874446862261)
          ·
            refine ⟨5864295215246988229393337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62552482295967874446862261 5864295215246988229393337)
            ·
              refine ⟨4398221411435241172045003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864295215246988229393337 4398221411435241172045003)
              ·
                refine ⟨6597332117152861758067505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398221411435241172045003 6597332117152861758067505)
                ·
                  refine ⟨4947999087864646318550629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597332117152861758067505 4947999087864646318550629)
                  ·
                    refine ⟨927749828974621184728243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947999087864646318550629 927749828974621184728243)
                    ·
                      rfl

theorem cell23_5420359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_5420359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420359 prefixEnd_5420359 := by exact prefixLift 5420359
  have htrace : WordTrace (prefixWord ++ tailWord_5420359) baseStart_5420359 baseEnd_5420359 := by
    simpa [prefixWord, tailWord_5420359, baseEnd_5420359] using wordTrace_append hprefix tailTrace_5420359
  have hstable : (prefixWord ++ tailWord_5420359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420359).length < 2 ^ (prefixWord ++ tailWord_5420359).sum := by decide
  have hdescent : baseEnd_5420359 < baseStart_5420359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420378 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5420378 : Nat := 118140960795 + 5420378 * 2 ^ 59
def prefixEnd_5420378 : Nat := 4983230072969 + 3 ^ 40 * 5420378 * 2
def baseEnd_5420378 : Nat := 2783259243056298979847141

theorem tailTrace_5420378 : CollatzResearch.WordTrace tailWord_5420378 prefixEnd_5420378 2783259243056298979847141 := by
  unfold tailWord_5420378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49424356789225926926657447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131798284771269138471086525 49424356789225926926657447)
  ·
    refine ⟨74136535183838890389986171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49424356789225926926657447 74136535183838890389986171)
    ·
      refine ⟨111204802775758335584979257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74136535183838890389986171 111204802775758335584979257)
      ·
        refine ⟨83403602081818751688734443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111204802775758335584979257 83403602081818751688734443)
        ·
          refine ⟨125105403122728127533101665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83403602081818751688734443 125105403122728127533101665)
          ·
            refine ⟨93829052342046095649826249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125105403122728127533101665 93829052342046095649826249)
            ·
              refine ⟨70371789256534571737369687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93829052342046095649826249 70371789256534571737369687)
              ·
                refine ⟨105557683884801857606054531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70371789256534571737369687 105557683884801857606054531)
                ·
                  refine ⟨158336525827202786409081797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105557683884801857606054531 158336525827202786409081797)
                  ·
                    refine ⟨29688098592600522451702837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158336525827202786409081797 29688098592600522451702837)
                    ·
                      refine ⟨2783259243056298979847141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29688098592600522451702837 2783259243056298979847141)
                      ·
                        rfl

theorem cell23_5420378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5420378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420378 prefixEnd_5420378 := by exact prefixLift 5420378
  have htrace : WordTrace (prefixWord ++ tailWord_5420378) baseStart_5420378 baseEnd_5420378 := by
    simpa [prefixWord, tailWord_5420378, baseEnd_5420378] using wordTrace_append hprefix tailTrace_5420378
  have hstable : (prefixWord ++ tailWord_5420378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420378).length < 2 ^ (prefixWord ++ tailWord_5420378).sum := by decide
  have hdescent : baseEnd_5420378 < baseStart_5420378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420473 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5420473 : Nat := 118140960795 + 5420473 * 2 ^ 59
def prefixEnd_5420473 : Nat := 4983230072969 + 3 ^ 40 * 5420473 * 2
def baseEnd_5420473 : Nat := 2783308023718476108159205

theorem tailTrace_5420473 : CollatzResearch.WordTrace tailWord_5420473 prefixEnd_5420473 2783308023718476108159205 := by
  unfold tailWord_5420473
  simp only [CollatzResearch.WordTrace]
  refine ⟨197700892091559538931338073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131800594727706359287558715 197700892091559538931338073)
  ·
    refine ⟨148275669068669654198503555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197700892091559538931338073 148275669068669654198503555)
    ·
      refine ⟨222413503603004481297755333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148275669068669654198503555 222413503603004481297755333)
      ·
        refine ⟨41702531925563340243329125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222413503603004481297755333 41702531925563340243329125)
        ·
          refine ⟨7819224736043126295624211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41702531925563340243329125 7819224736043126295624211)
          ·
            refine ⟨11728837104064689443436317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819224736043126295624211 11728837104064689443436317)
            ·
              refine ⟨4398313914024258541288619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11728837104064689443436317 4398313914024258541288619)
              ·
                refine ⟨6597470871036387811932929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398313914024258541288619 6597470871036387811932929)
                ·
                  refine ⟨4948103153277290858949697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597470871036387811932929 4948103153277290858949697)
                  ·
                    refine ⟨3711077364957968144212273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948103153277290858949697 3711077364957968144212273)
                    ·
                      refine ⟨2783308023718476108159205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711077364957968144212273 2783308023718476108159205)
                      ·
                        rfl

theorem cell23_5420473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5420473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420473 prefixEnd_5420473 := by exact prefixLift 5420473
  have htrace : WordTrace (prefixWord ++ tailWord_5420473) baseStart_5420473 baseEnd_5420473 := by
    simpa [prefixWord, tailWord_5420473, baseEnd_5420473] using wordTrace_append hprefix tailTrace_5420473
  have hstable : (prefixWord ++ tailWord_5420473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420473).length < 2 ^ (prefixWord ++ tailWord_5420473).sum := by decide
  have hdescent : baseEnd_5420473 < baseStart_5420473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420495 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_5420495 : Nat := 118140960795 + 5420495 * 2 ^ 59
def prefixEnd_5420495 : Nat := 4983230072969 + 3 ^ 40 * 5420495 * 2
def baseEnd_5420495 : Nat := 2783319320292875022084103

theorem tailTrace_5420495 : CollatzResearch.WordTrace tailWord_5420495 prefixEnd_5420495 2783319320292875022084103 := by
  unfold tailWord_5420495
  simp only [CollatzResearch.WordTrace]
  refine ⟨197701694497479836688638939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131801129664986557792425959 197701694497479836688638939)
  ·
    refine ⟨296552541746219755032958409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197701694497479836688638939 296552541746219755032958409)
    ·
      refine ⟨222414406309664816274718807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296552541746219755032958409 222414406309664816274718807)
      ·
        refine ⟨333621609464497224412078211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222414406309664816274718807 333621609464497224412078211)
        ·
          refine ⟨500432414196745836618117317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333621609464497224412078211 500432414196745836618117317)
          ·
            refine ⟨93831077661889844365896997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 500432414196745836618117317 93831077661889844365896997)
            ·
              refine ⟨17593327061604345818605687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93831077661889844365896997 17593327061604345818605687)
              ·
                refine ⟨26389990592406518727908531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17593327061604345818605687 26389990592406518727908531)
                ·
                  refine ⟨39584985888609778091862797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26389990592406518727908531 39584985888609778091862797)
                  ·
                    refine ⟨14844369708228666784448549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39584985888609778091862797 14844369708228666784448549)
                    ·
                      refine ⟨2783319320292875022084103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14844369708228666784448549 2783319320292875022084103)
                      ·
                        rfl

theorem cell23_5420495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_5420495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420495 prefixEnd_5420495 := by exact prefixLift 5420495
  have htrace : WordTrace (prefixWord ++ tailWord_5420495) baseStart_5420495 baseEnd_5420495 := by
    simpa [prefixWord, tailWord_5420495, baseEnd_5420495] using wordTrace_append hprefix tailTrace_5420495
  have hstable : (prefixWord ++ tailWord_5420495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420495).length < 2 ^ (prefixWord ++ tailWord_5420495).sum := by decide
  have hdescent : baseEnd_5420495 < baseStart_5420495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420512 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2]
def baseStart_5420512 : Nat := 118140960795 + 5420512 * 2 ^ 59
def prefixEnd_5420512 : Nat := 4983230072969 + 3 ^ 40 * 5420512 * 2
def baseEnd_5420512 : Nat := 2783328049464001455571525

theorem tailTrace_5420512 : CollatzResearch.WordTrace tailWord_5420512 prefixEnd_5420512 2783328049464001455571525 := by
  unfold tailWord_5420512
  simp only [CollatzResearch.WordTrace]
  refine ⟨98851157269209124296003895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131801543025612165728005193 98851157269209124296003895)
  ·
    refine ⟨148276735903813686444005843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98851157269209124296003895 148276735903813686444005843)
    ·
      refine ⟨222415103855720529666008765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148276735903813686444005843 222415103855720529666008765)
      ·
        refine ⟨83405663945895198624753287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222415103855720529666008765 83405663945895198624753287)
        ·
          refine ⟨125108495918842797937129931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83405663945895198624753287 125108495918842797937129931)
          ·
            refine ⟨187662743878264196905694897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125108495918842797937129931 187662743878264196905694897)
            ·
              refine ⟨140747057908698147679271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187662743878264196905694897 140747057908698147679271173)
              ·
                refine ⟨26390073357880902689863345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140747057908698147679271173 26390073357880902689863345)
                ·
                  refine ⟨19792555018410677017397509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26390073357880902689863345 19792555018410677017397509)
                  ·
                    refine ⟨3711104065952001940762033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19792555018410677017397509 3711104065952001940762033)
                    ·
                      refine ⟨2783328049464001455571525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711104065952001940762033 2783328049464001455571525)
                      ·
                        rfl

theorem cell23_5420512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_5420512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420512 prefixEnd_5420512 := by exact prefixLift 5420512
  have htrace : WordTrace (prefixWord ++ tailWord_5420512) baseStart_5420512 baseEnd_5420512 := by
    simpa [prefixWord, tailWord_5420512, baseEnd_5420512] using wordTrace_append hprefix tailTrace_5420512
  have hstable : (prefixWord ++ tailWord_5420512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420512).length < 2 ^ (prefixWord ++ tailWord_5420512).sum := by decide
  have hdescent : baseEnd_5420512 < baseStart_5420512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420546 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5420546 : Nat := 118140960795 + 5420546 * 2 ^ 59
def prefixEnd_5420546 : Nat := 4983230072969 + 3 ^ 40 * 5420546 * 2
def baseEnd_5420546 : Nat := 2783345507806254322546369

theorem tailTrace_5420546 : CollatzResearch.WordTrace tailWord_5420546 prefixEnd_5420546 2783345507806254322546369 := by
  unfold tailWord_5420546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49425888655073768099686373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131802369746863381599163661 49425888655073768099686373)
  ·
    refine ⟨9267354122826331518691195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49425888655073768099686373 9267354122826331518691195)
    ·
      refine ⟨13901031184239497278036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9267354122826331518691195 13901031184239497278036793)
      ·
        refine ⟨10425773388179622958527595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13901031184239497278036793 10425773388179622958527595)
        ·
          refine ⟨15638660082269434437791393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10425773388179622958527595 15638660082269434437791393)
          ·
            refine ⟨11728995061702075828343545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15638660082269434437791393 11728995061702075828343545)
            ·
              refine ⟨8796746296276556871257659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11728995061702075828343545 8796746296276556871257659)
              ·
                refine ⟨13195119444414835306886489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796746296276556871257659 13195119444414835306886489)
                ·
                  refine ⟨9896339583311126480164867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195119444414835306886489 9896339583311126480164867)
                  ·
                    refine ⟨14844509374966689720247301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9896339583311126480164867 14844509374966689720247301)
                    ·
                      refine ⟨2783345507806254322546369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14844509374966689720247301 2783345507806254322546369)
                      ·
                        rfl

theorem cell23_5420546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5420546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420546 prefixEnd_5420546 := by exact prefixLift 5420546
  have htrace : WordTrace (prefixWord ++ tailWord_5420546) baseStart_5420546 baseEnd_5420546 := by
    simpa [prefixWord, tailWord_5420546, baseEnd_5420546] using wordTrace_append hprefix tailTrace_5420546
  have hstable : (prefixWord ++ tailWord_5420546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420546).length < 2 ^ (prefixWord ++ tailWord_5420546).sum := by decide
  have hdescent : baseEnd_5420546 < baseStart_5420546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420602 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_5420602 : Nat := 118140960795 + 5420602 * 2 ^ 59
def prefixEnd_5420602 : Nat := 4983230072969 + 3 ^ 40 * 5420602 * 2
def baseEnd_5420602 : Nat := 2783374262722906103446111

theorem tailTrace_5420602 : CollatzResearch.WordTrace tailWord_5420602 prefixEnd_5420602 2783374262722906103446111 := by
  unfold tailWord_5420602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49426399277023048490696015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131803731405394795975189373 49426399277023048490696015)
  ·
    refine ⟨74139598915534572736044023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49426399277023048490696015 74139598915534572736044023)
    ·
      refine ⟨111209398373301859104066035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74139598915534572736044023 111209398373301859104066035)
      ·
        refine ⟨166814097559952788656099053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111209398373301859104066035 166814097559952788656099053)
        ·
          refine ⟨62555286584982295746037145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166814097559952788656099053 62555286584982295746037145)
          ·
            refine ⟨46916464938736721809527859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62555286584982295746037145 46916464938736721809527859)
            ·
              refine ⟨70374697408105082714291789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46916464938736721809527859 70374697408105082714291789)
              ·
                refine ⟨26390511528039406017859421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70374697408105082714291789 26390511528039406017859421)
                ·
                  refine ⟨9896441823014777256697283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26390511528039406017859421 9896441823014777256697283)
                  ·
                    refine ⟨14844662734522165885045925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9896441823014777256697283 14844662734522165885045925)
                    ·
                      refine ⟨2783374262722906103446111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14844662734522165885045925 2783374262722906103446111)
                      ·
                        rfl

theorem cell23_5420602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_5420602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420602 prefixEnd_5420602 := by exact prefixLift 5420602
  have htrace : WordTrace (prefixWord ++ tailWord_5420602) baseStart_5420602 baseEnd_5420602 := by
    simpa [prefixWord, tailWord_5420602, baseEnd_5420602] using wordTrace_append hprefix tailTrace_5420602
  have hstable : (prefixWord ++ tailWord_5420602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420602).length < 2 ^ (prefixWord ++ tailWord_5420602).sum := by decide
  have hdescent : baseEnd_5420602 < baseStart_5420602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420619 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 7, 2, 2]
def baseStart_5420619 : Nat := 118140960795 + 5420619 * 2 ^ 59
def prefixEnd_5420619 : Nat := 4983230072969 + 3 ^ 40 * 5420619 * 2
def baseEnd_5420619 : Nat := 2783382991894032536933533

theorem tailTrace_5420619 : CollatzResearch.WordTrace tailWord_5420619 prefixEnd_5420619 2783382991894032536933533 := by
  unfold tailWord_5420619
  simp only [CollatzResearch.WordTrace]
  refine ⟨197706217149030605866152911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131804144766020403910768607 197706217149030605866152911)
  ·
    refine ⟨296559325723545908799229367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197706217149030605866152911 296559325723545908799229367)
    ·
      refine ⟨444838988585318863198844051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296559325723545908799229367 444838988585318863198844051)
      ·
        refine ⟨667258482877978294798266077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444838988585318863198844051 667258482877978294798266077)
        ·
          refine ⟨250221931079241860549349779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 667258482877978294798266077 250221931079241860549349779)
          ·
            refine ⟨375332896618862790824024669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250221931079241860549349779 375332896618862790824024669)
            ·
              refine ⟨140749836232073546559009251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375332896618862790824024669 140749836232073546559009251)
              ·
                refine ⟨211124754348110319838513877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140749836232073546559009251 211124754348110319838513877)
                ·
                  refine ⟨4948236430033835621215169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211124754348110319838513877 4948236430033835621215169)
                  ·
                    refine ⟨3711177322525376715911377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948236430033835621215169 3711177322525376715911377)
                    ·
                      refine ⟨2783382991894032536933533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711177322525376715911377 2783382991894032536933533)
                      ·
                        rfl

theorem cell23_5420619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2, 2].length) (baseStart_5420619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420619 prefixEnd_5420619 := by exact prefixLift 5420619
  have htrace : WordTrace (prefixWord ++ tailWord_5420619) baseStart_5420619 baseEnd_5420619 := by
    simpa [prefixWord, tailWord_5420619, baseEnd_5420619] using wordTrace_append hprefix tailTrace_5420619
  have hstable : (prefixWord ++ tailWord_5420619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420619).length < 2 ^ (prefixWord ++ tailWord_5420619).sum := by decide
  have hdescent : baseEnd_5420619 < baseStart_5420619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420622 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5420622 : Nat := 118140960795 + 5420622 * 2 ^ 59
def prefixEnd_5420622 : Nat := 4983230072969 + 3 ^ 40 * 5420622 * 2
def baseEnd_5420622 : Nat := 2783384532335996025196019

theorem tailTrace_5420622 : CollatzResearch.WordTrace tailWord_5420622 prefixEnd_5420622 2783384532335996025196019 := by
  unfold tailWord_5420622
  simp only [CollatzResearch.WordTrace]
  refine ⟨24713290821002467172314015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131804217712013158252341413 24713290821002467172314015)
  ·
    refine ⟨37069936231503700758471023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24713290821002467172314015 37069936231503700758471023)
    ·
      refine ⟨55604904347255551137706535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37069936231503700758471023 55604904347255551137706535)
      ·
        refine ⟨83407356520883326706559803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55604904347255551137706535 83407356520883326706559803)
        ·
          refine ⟨125111034781324990059839705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83407356520883326706559803 125111034781324990059839705)
          ·
            refine ⟨93833276085993742544879779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125111034781324990059839705 93833276085993742544879779)
            ·
              refine ⟨140749914128990613817319669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93833276085993742544879779 140749914128990613817319669)
              ·
                refine ⟨13195304449592870045373719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140749914128990613817319669 13195304449592870045373719)
                ·
                  refine ⟨19792956674389305068060579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13195304449592870045373719 19792956674389305068060579)
                  ·
                    refine ⟨29689435011583957602090869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19792956674389305068060579 29689435011583957602090869)
                    ·
                      refine ⟨2783384532335996025196019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29689435011583957602090869 2783384532335996025196019)
                      ·
                        rfl

theorem cell23_5420622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5420622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420622 prefixEnd_5420622 := by exact prefixLift 5420622
  have htrace : WordTrace (prefixWord ++ tailWord_5420622) baseStart_5420622 baseEnd_5420622 := by
    simpa [prefixWord, tailWord_5420622, baseEnd_5420622] using wordTrace_append hprefix tailTrace_5420622
  have hstable : (prefixWord ++ tailWord_5420622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420622).length < 2 ^ (prefixWord ++ tailWord_5420622).sum := by decide
  have hdescent : baseEnd_5420622 < baseStart_5420622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420625 : List Nat := [1, 2, 2, 1, 3, 2, 12]
def baseStart_5420625 : Nat := 118140960795 + 5420625 * 2 ^ 59
def prefixEnd_5420625 : Nat := 4983230072969 + 3 ^ 40 * 5420625 * 2
def baseEnd_5420625 : Nat := 34362791021950117450105

theorem tailTrace_5420625 : CollatzResearch.WordTrace tailWord_5420625 prefixEnd_5420625 34362791021950117450105 := by
  unfold tailWord_5420625
  simp only [CollatzResearch.WordTrace]
  refine ⟨197706435987008868890871329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131804290658005912593914219 197706435987008868890871329)
  ·
    refine ⟨148279826990256651668153497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197706435987008868890871329 148279826990256651668153497)
    ·
      refine ⟨111209870242692488751115123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148279826990256651668153497 111209870242692488751115123)
      ·
        refine ⟨166814805364038733126672685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111209870242692488751115123 166814805364038733126672685)
        ·
          refine ⟨62555552011514524922502257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166814805364038733126672685 62555552011514524922502257)
          ·
            refine ⟨46916664008635893691876693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62555552011514524922502257 46916664008635893691876693)
            ·
              refine ⟨34362791021950117450105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46916664008635893691876693 34362791021950117450105)
              ·
                rfl

theorem cell23_5420625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 12].length) (baseStart_5420625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420625 prefixEnd_5420625 := by exact prefixLift 5420625
  have htrace : WordTrace (prefixWord ++ tailWord_5420625) baseStart_5420625 baseEnd_5420625 := by
    simpa [prefixWord, tailWord_5420625, baseEnd_5420625] using wordTrace_append hprefix tailTrace_5420625
  have hstable : (prefixWord ++ tailWord_5420625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420625).length < 2 ^ (prefixWord ++ tailWord_5420625).sum := by decide
  have hdescent : baseEnd_5420625 < baseStart_5420625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420656 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_5420656 : Nat := 118140960795 + 5420656 * 2 ^ 59
def prefixEnd_5420656 : Nat := 4983230072969 + 3 ^ 40 * 5420656 * 2
def baseEnd_5420656 : Nat := 2783401990678248892170863

theorem tailTrace_5420656 : CollatzResearch.WordTrace tailWord_5420656 prefixEnd_5420656 2783401990678248892170863 := by
  unfold tailWord_5420656
  simp only [CollatzResearch.WordTrace]
  refine ⟨98853783324948280592624911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131805044433264374123499881 98853783324948280592624911)
  ·
    refine ⟨148280674987422420888937367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98853783324948280592624911 148280674987422420888937367)
    ·
      refine ⟨222421012481133631333406051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148280674987422420888937367 222421012481133631333406051)
      ·
        refine ⟨333631518721700447000109077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222421012481133631333406051 333631518721700447000109077)
        ·
          refine ⟨15638977440079708453130113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 333631518721700447000109077 15638977440079708453130113)
          ·
            refine ⟨11729233080059781339847585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15638977440079708453130113 11729233080059781339847585)
            ·
              refine ⟨8796924810044836004885689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11729233080059781339847585 8796924810044836004885689)
              ·
                refine ⟨6597693607533627003664267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796924810044836004885689 6597693607533627003664267)
                ·
                  refine ⟨9896540411300440505496401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6597693607533627003664267 9896540411300440505496401)
                  ·
                    refine ⟨7422405308475330379122301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9896540411300440505496401 7422405308475330379122301)
                    ·
                      refine ⟨2783401990678248892170863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422405308475330379122301 2783401990678248892170863)
                      ·
                        rfl

theorem cell23_5420656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_5420656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420656 prefixEnd_5420656 := by exact prefixLift 5420656
  have htrace : WordTrace (prefixWord ++ tailWord_5420656) baseStart_5420656 baseEnd_5420656 := by
    simpa [prefixWord, tailWord_5420656, baseEnd_5420656] using wordTrace_append hprefix tailTrace_5420656
  have hstable : (prefixWord ++ tailWord_5420656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420656).length < 2 ^ (prefixWord ++ tailWord_5420656).sum := by decide
  have hdescent : baseEnd_5420656 < baseStart_5420656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420686 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5420686 : Nat := 118140960795 + 5420686 * 2 ^ 59
def prefixEnd_5420686 : Nat := 4983230072969 + 3 ^ 40 * 5420686 * 2
def baseEnd_5420686 : Nat := 2783417395097883774795725

theorem tailTrace_5420686 : CollatzResearch.WordTrace tailWord_5420686 prefixEnd_5420686 2783417395097883774795725 := by
  unfold tailWord_5420686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24713582604973484538605239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131805773893191917539227941 24713582604973484538605239)
  ·
    refine ⟨37070373907460226807907859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24713582604973484538605239 37070373907460226807907859)
    ·
      refine ⟨55605560861190340211861789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37070373907460226807907859 55605560861190340211861789)
      ·
        refine ⟨20852085322946377579448171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55605560861190340211861789 20852085322946377579448171)
        ·
          refine ⟨31278127984419566369172257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20852085322946377579448171 31278127984419566369172257)
          ·
            refine ⟨23458595988314674776879193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31278127984419566369172257 23458595988314674776879193)
            ·
              refine ⟨17593946991236006082659395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23458595988314674776879193 17593946991236006082659395)
              ·
                refine ⟨26390920486854009123989093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17593946991236006082659395 26390920486854009123989093)
                ·
                  refine ⟨4948297591285126710747955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26390920486854009123989093 4948297591285126710747955)
                  ·
                    refine ⟨7422446386927690066121933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4948297591285126710747955 7422446386927690066121933)
                    ·
                      refine ⟨2783417395097883774795725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422446386927690066121933 2783417395097883774795725)
                      ·
                        rfl

theorem cell23_5420686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5420686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420686 prefixEnd_5420686 := by exact prefixLift 5420686
  have htrace : WordTrace (prefixWord ++ tailWord_5420686) baseStart_5420686 baseEnd_5420686 := by
    simpa [prefixWord, tailWord_5420686, baseEnd_5420686] using wordTrace_append hprefix tailTrace_5420686
  have hstable : (prefixWord ++ tailWord_5420686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420686).length < 2 ^ (prefixWord ++ tailWord_5420686).sum := by decide
  have hdescent : baseEnd_5420686 < baseStart_5420686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420738 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5420738 : Nat := 118140960795 + 5420738 * 2 ^ 59
def prefixEnd_5420738 : Nat := 4983230072969 + 3 ^ 40 * 5420738 * 2
def baseEnd_5420738 : Nat := 2783444096091917571345487

theorem tailTrace_5420738 : CollatzResearch.WordTrace tailWord_5420738 prefixEnd_5420738 2783444096091917571345487 := by
  unfold tailWord_5420738
  simp only [CollatzResearch.WordTrace]
  refine ⟨49427639358899872297433717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131807038290399659459823245 49427639358899872297433717)
  ·
    refine ⟨4633841189896863027884411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49427639358899872297433717 4633841189896863027884411)
    ·
      refine ⟨6950761784845294541826617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633841189896863027884411 6950761784845294541826617)
      ·
        refine ⟨5213071338633970906369963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950761784845294541826617 5213071338633970906369963)
        ·
          refine ⟨7819607007950956359554945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213071338633970906369963 7819607007950956359554945)
          ·
            refine ⟨5864705255963217269666209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7819607007950956359554945 5864705255963217269666209)
            ·
              refine ⟨4398528941972412952249657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864705255963217269666209 4398528941972412952249657)
              ·
                refine ⟨3298896706479309714187243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398528941972412952249657 3298896706479309714187243)
                ·
                  refine ⟨4948345059718964571280865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298896706479309714187243 4948345059718964571280865)
                  ·
                    refine ⟨3711258794789223428460649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948345059718964571280865 3711258794789223428460649)
                    ·
                      refine ⟨2783444096091917571345487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711258794789223428460649 2783444096091917571345487)
                      ·
                        rfl

theorem cell23_5420738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5420738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420738 prefixEnd_5420738 := by exact prefixLift 5420738
  have htrace : WordTrace (prefixWord ++ tailWord_5420738) baseStart_5420738 baseEnd_5420738 := by
    simpa [prefixWord, tailWord_5420738, baseEnd_5420738] using wordTrace_append hprefix tailTrace_5420738
  have hstable : (prefixWord ++ tailWord_5420738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420738).length < 2 ^ (prefixWord ++ tailWord_5420738).sum := by decide
  have hdescent : baseEnd_5420738 < baseStart_5420738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420743 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_5420743 : Nat := 118140960795 + 5420743 * 2 ^ 59
def prefixEnd_5420743 : Nat := 4983230072969 + 3 ^ 40 * 5420743 * 2
def baseEnd_5420743 : Nat := 2783446663495190051782963

theorem tailTrace_5420743 : CollatzResearch.WordTrace tailWord_5420743 prefixEnd_5420743 2783446663495190051782963 := by
  unfold tailWord_5420743
  simp only [CollatzResearch.WordTrace]
  refine ⟨197710739800581375043666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131807159867054250029111255 197710739800581375043666883)
  ·
    refine ⟨296566109700872062565500325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197710739800581375043666883 296566109700872062565500325)
    ·
      refine ⟨55606145568913511731031311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296566109700872062565500325 55606145568913511731031311)
      ·
        refine ⟨83409218353370267596546967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55606145568913511731031311 83409218353370267596546967)
        ·
          refine ⟨125113827530055401394820451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83409218353370267596546967 125113827530055401394820451)
          ·
            refine ⟨187670741295083102092230677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125113827530055401394820451 187670741295083102092230677)
            ·
              refine ⟨8797065998207020410573313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187670741295083102092230677 8797065998207020410573313)
              ·
                refine ⟨6597799498655265307929985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8797065998207020410573313 6597799498655265307929985)
                ·
                  refine ⟨4948349623991448980947489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597799498655265307929985 4948349623991448980947489)
                  ·
                    refine ⟨3711262217993586735710617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948349623991448980947489 3711262217993586735710617)
                    ·
                      refine ⟨2783446663495190051782963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711262217993586735710617 2783446663495190051782963)
                      ·
                        rfl

theorem cell23_5420743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_5420743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420743 prefixEnd_5420743 := by exact prefixLift 5420743
  have htrace : WordTrace (prefixWord ++ tailWord_5420743) baseStart_5420743 baseEnd_5420743 := by
    simpa [prefixWord, tailWord_5420743, baseEnd_5420743] using wordTrace_append hprefix tailTrace_5420743
  have hstable : (prefixWord ++ tailWord_5420743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420743).length < 2 ^ (prefixWord ++ tailWord_5420743).sum := by decide
  have hdescent : baseEnd_5420743 < baseStart_5420743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420756 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5420756 : Nat := 118140960795 + 5420756 * 2 ^ 59
def prefixEnd_5420756 : Nat := 4983230072969 + 3 ^ 40 * 5420756 * 2
def baseEnd_5420756 : Nat := 2783453338743698500920403

theorem tailTrace_5420756 : CollatzResearch.WordTrace tailWord_5420756 prefixEnd_5420756 2783453338743698500920403 := by
  unfold tailWord_5420756
  simp only [CollatzResearch.WordTrace]
  refine ⟨98855606974767139131945061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131807475966356185509260081 98855606974767139131945061)
  ·
    refine ⟨18535426307768838587239699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98855606974767139131945061 18535426307768838587239699)
    ·
      refine ⟨27803139461653257880859549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535426307768838587239699 27803139461653257880859549)
      ·
        refine ⟨10426177298119971705322331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27803139461653257880859549 10426177298119971705322331)
        ·
          refine ⟨15639265947179957557983497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426177298119971705322331 15639265947179957557983497)
          ·
            refine ⟨11729449460384968168487623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15639265947179957557983497 11729449460384968168487623)
            ·
              refine ⟨17594174190577452252731435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11729449460384968168487623 17594174190577452252731435)
              ·
                refine ⟨26391261285866178379097153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17594174190577452252731435 26391261285866178379097153)
                ·
                  refine ⟨19793445964399633784322865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26391261285866178379097153 19793445964399633784322865)
                  ·
                    refine ⟨14845084473299725338242149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19793445964399633784322865 14845084473299725338242149)
                    ·
                      refine ⟨2783453338743698500920403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14845084473299725338242149 2783453338743698500920403)
                      ·
                        rfl

theorem cell23_5420756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5420756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420756 prefixEnd_5420756 := by exact prefixLift 5420756
  have htrace : WordTrace (prefixWord ++ tailWord_5420756) baseStart_5420756 baseEnd_5420756 := by
    simpa [prefixWord, tailWord_5420756, baseEnd_5420756] using wordTrace_append hprefix tailTrace_5420756
  have hstable : (prefixWord ++ tailWord_5420756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420756).length < 2 ^ (prefixWord ++ tailWord_5420756).sum := by decide
  have hdescent : baseEnd_5420756 < baseStart_5420756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420759 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_5420759 : Nat := 118140960795 + 5420759 * 2 ^ 59
def prefixEnd_5420759 : Nat := 4983230072969 + 3 ^ 40 * 5420759 * 2
def baseEnd_5420759 : Nat := 2783454879185661989182889

theorem tailTrace_5420759 : CollatzResearch.WordTrace tailWord_5420759 prefixEnd_5420759 2783454879185661989182889 := by
  unfold tailWord_5420759
  simp only [CollatzResearch.WordTrace]
  refine ⟨197711323368523409776249331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131807548912348939850832887 197711323368523409776249331)
  ·
    refine ⟨296566985052785114664373997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197711323368523409776249331 296566985052785114664373997)
    ·
      refine ⟨111212619394794417999140249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296566985052785114664373997 111212619394794417999140249)
      ·
        refine ⟨83409464546095813499355187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111212619394794417999140249 83409464546095813499355187)
        ·
          refine ⟨125114196819143720249032781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83409464546095813499355187 125114196819143720249032781)
          ·
            refine ⟨46917823807178895093387293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125114196819143720249032781 46917823807178895093387293)
            ·
              refine ⟨17594183927692085660020235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46917823807178895093387293 17594183927692085660020235)
              ·
                refine ⟨26391275891538128490030353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17594183927692085660020235 26391275891538128490030353)
                ·
                  refine ⟨19793456918653596367522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26391275891538128490030353 19793456918653596367522765)
                  ·
                    refine ⟨7422546344495098637821037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19793456918653596367522765 7422546344495098637821037)
                    ·
                      refine ⟨2783454879185661989182889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422546344495098637821037 2783454879185661989182889)
                      ·
                        rfl

theorem cell23_5420759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_5420759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420759 prefixEnd_5420759 := by exact prefixLift 5420759
  have htrace : WordTrace (prefixWord ++ tailWord_5420759) baseStart_5420759 baseEnd_5420759 := by
    simpa [prefixWord, tailWord_5420759, baseEnd_5420759] using wordTrace_append hprefix tailTrace_5420759
  have hstable : (prefixWord ++ tailWord_5420759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420759).length < 2 ^ (prefixWord ++ tailWord_5420759).sum := by decide
  have hdescent : baseEnd_5420759 < baseStart_5420759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420779 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 2, 5]
def baseStart_5420779 : Nat := 118140960795 + 5420779 * 2 ^ 59
def prefixEnd_5420779 : Nat := 4983230072969 + 3 ^ 40 * 5420779 * 2
def baseEnd_5420779 : Nat := 927821716266250636977599

theorem tailTrace_5420779 : CollatzResearch.WordTrace tailWord_5420779 prefixEnd_5420779 927821716266250636977599 := by
  unfold tailWord_5420779
  simp only [CollatzResearch.WordTrace]
  refine ⟨197712052828450953191977391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131808035218967302127984927 197712052828450953191977391)
  ·
    refine ⟨296568079242676429787966087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197712052828450953191977391 296568079242676429787966087)
    ·
      refine ⟨444852118864014644681949131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296568079242676429787966087 444852118864014644681949131)
      ·
        refine ⟨667278178296021967022923697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444852118864014644681949131 667278178296021967022923697)
        ·
          refine ⟨500458633722016475267192773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667278178296021967022923697 500458633722016475267192773)
          ·
            refine ⟨93835993822878089112598645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 500458633722016475267192773 93835993822878089112598645)
            ·
              refine ⟨8797124420894820854306123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93835993822878089112598645 8797124420894820854306123)
              ·
                refine ⟨13195686631342231281459185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797124420894820854306123 13195686631342231281459185)
                ·
                  refine ⟨9896764973506673461094389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195686631342231281459185 9896764973506673461094389)
                  ·
                    refine ⟨927821716266250636977599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9896764973506673461094389 927821716266250636977599)
                    ·
                      rfl

theorem cell23_5420779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].length) (baseStart_5420779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420779 prefixEnd_5420779 := by exact prefixLift 5420779
  have htrace : WordTrace (prefixWord ++ tailWord_5420779) baseStart_5420779 baseEnd_5420779 := by
    simpa [prefixWord, tailWord_5420779, baseEnd_5420779] using wordTrace_append hprefix tailTrace_5420779
  have hstable : (prefixWord ++ tailWord_5420779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420779).length < 2 ^ (prefixWord ++ tailWord_5420779).sum := by decide
  have hdescent : baseEnd_5420779 < baseStart_5420779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420799 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_5420799 : Nat := 118140960795 + 5420799 * 2 ^ 59
def prefixEnd_5420799 : Nat := 4983230072969 + 3 ^ 40 * 5420799 * 2
def baseEnd_5420799 : Nat := 2783475418411841832682705

theorem tailTrace_5420799 : CollatzResearch.WordTrace tailWord_5420799 prefixEnd_5420799 2783475418411841832682705 := by
  unfold tailWord_5420799
  simp only [CollatzResearch.WordTrace]
  refine ⟨197712782288378496607705451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131808521525585664405136967 197712782288378496607705451)
  ·
    refine ⟨296569173432567744911558177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197712782288378496607705451 296569173432567744911558177)
    ·
      refine ⟨222426880074425808683668633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296569173432567744911558177 222426880074425808683668633)
      ·
        refine ⟨166820160055819356512751475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222426880074425808683668633 166820160055819356512751475)
        ·
          refine ⟨250230240083729034769127213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166820160055819356512751475 250230240083729034769127213)
          ·
            refine ⟨93836340031398388038422705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250230240083729034769127213 93836340031398388038422705)
            ·
              refine ⟨70377255023548791028817029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93836340031398388038422705 70377255023548791028817029)
              ·
                refine ⟨13195735316915398317903193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70377255023548791028817029 13195735316915398317903193)
                ·
                  refine ⟨9896801487686548738427395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195735316915398317903193 9896801487686548738427395)
                  ·
                    refine ⟨14845202231529823107641093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9896801487686548738427395 14845202231529823107641093)
                    ·
                      refine ⟨2783475418411841832682705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14845202231529823107641093 2783475418411841832682705)
                      ·
                        rfl

theorem cell23_5420799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_5420799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420799 prefixEnd_5420799 := by exact prefixLift 5420799
  have htrace : WordTrace (prefixWord ++ tailWord_5420799) baseStart_5420799 baseEnd_5420799 := by
    simpa [prefixWord, tailWord_5420799, baseEnd_5420799] using wordTrace_append hprefix tailTrace_5420799
  have hstable : (prefixWord ++ tailWord_5420799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420799).length < 2 ^ (prefixWord ++ tailWord_5420799).sum := by decide
  have hdescent : baseEnd_5420799 < baseStart_5420799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420819 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3]
def baseStart_5420819 : Nat := 118140960795 + 5420819 * 2 ^ 59
def prefixEnd_5420819 : Nat := 4983230072969 + 3 ^ 40 * 5420819 * 2
def baseEnd_5420819 : Nat := 2783485688024931754432613

theorem tailTrace_5420819 : CollatzResearch.WordTrace tailWord_5420819 prefixEnd_5420819 2783485688024931754432613 := by
  unfold tailWord_5420819
  simp only [CollatzResearch.WordTrace]
  refine ⟨197713511748306040023433511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131809007832204026682289007 197713511748306040023433511)
  ·
    refine ⟨296570267622459060035150267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197713511748306040023433511 296570267622459060035150267)
    ·
      refine ⟨444855401433688590052725401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296570267622459060035150267 444855401433688590052725401)
      ·
        refine ⟨333641551075266442539544051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444855401433688590052725401 333641551075266442539544051)
        ·
          refine ⟨500462326612899663809316077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333641551075266442539544051 500462326612899663809316077)
          ·
            refine ⟨187673372479837373928493529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500462326612899663809316077 187673372479837373928493529)
            ·
              refine ⟨140755029359878030446370147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187673372479837373928493529 140755029359878030446370147)
              ·
                refine ⟨211132544039817045669555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140755029359878030446370147 211132544039817045669555221)
                ·
                  refine ⟨9896838001866424015760401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211132544039817045669555221 9896838001866424015760401)
                  ·
                    refine ⟨7422628501399818011820301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9896838001866424015760401 7422628501399818011820301)
                    ·
                      refine ⟨2783485688024931754432613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422628501399818011820301 2783485688024931754432613)
                      ·
                        rfl

theorem cell23_5420819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_5420819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420819 prefixEnd_5420819 := by exact prefixLift 5420819
  have htrace : WordTrace (prefixWord ++ tailWord_5420819) baseStart_5420819 baseEnd_5420819 := by
    simpa [prefixWord, tailWord_5420819, baseEnd_5420819] using wordTrace_append hprefix tailTrace_5420819
  have hstable : (prefixWord ++ tailWord_5420819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420819).length < 2 ^ (prefixWord ++ tailWord_5420819).sum := by decide
  have hdescent : baseEnd_5420819 < baseStart_5420819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420826 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_5420826 : Nat := 118140960795 + 5420826 * 2 ^ 59
def prefixEnd_5420826 : Nat := 4983230072969 + 3 ^ 40 * 5420826 * 2
def baseEnd_5420826 : Nat := 927829760796504409015027

theorem tailTrace_5420826 : CollatzResearch.WordTrace tailWord_5420826 prefixEnd_5420826 927829760796504409015027 := by
  unfold tailWord_5420826
  simp only [CollatzResearch.WordTrace]
  refine ⟨49428441764820170054734583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131809178039520453479292221 49428441764820170054734583)
  ·
    refine ⟨74142662647230255082101875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49428441764820170054734583 74142662647230255082101875)
    ·
      refine ⟨111213993970845382623152813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74142662647230255082101875 111213993970845382623152813)
      ·
        refine ⟨41705247739067018483682305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111213993970845382623152813 41705247739067018483682305)
        ·
          refine ⟨31278935804300263862761729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41705247739067018483682305 31278935804300263862761729)
          ·
            refine ⟨23459201853225197897071297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31278935804300263862761729 23459201853225197897071297)
            ·
              refine ⟨17594401389918898422803473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23459201853225197897071297 17594401389918898422803473)
              ·
                refine ⟨13195801042439173817102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17594401389918898422803473 13195801042439173817102605)
                ·
                  refine ⟨4948425390914690181413477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13195801042439173817102605 4948425390914690181413477)
                  ·
                    refine ⟨927829760796504409015027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4948425390914690181413477 927829760796504409015027)
                    ·
                      rfl

theorem cell23_5420826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_5420826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420826 prefixEnd_5420826 := by exact prefixLift 5420826
  have htrace : WordTrace (prefixWord ++ tailWord_5420826) baseStart_5420826 baseEnd_5420826 := by
    simpa [prefixWord, tailWord_5420826, baseEnd_5420826] using wordTrace_append hprefix tailTrace_5420826
  have hstable : (prefixWord ++ tailWord_5420826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420826).length < 2 ^ (prefixWord ++ tailWord_5420826).sum := by decide
  have hdescent : baseEnd_5420826 < baseStart_5420826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420836 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_5420836 : Nat := 118140960795 + 5420836 * 2 ^ 59
def prefixEnd_5420836 : Nat := 4983230072969 + 3 ^ 40 * 5420836 * 2
def baseEnd_5420836 : Nat := 2783494417196058187920035

theorem tailTrace_5420836 : CollatzResearch.WordTrace tailWord_5420836 prefixEnd_5420836 2783494417196058187920035 := by
  unfold tailWord_5420836
  simp only [CollatzResearch.WordTrace]
  refine ⟨98857065894622225963401181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131809421192829634617868241 98857065894622225963401181)
  ·
    refine ⟨37071399710483334736275443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98857065894622225963401181 37071399710483334736275443)
    ·
      refine ⟨55607099565725002104413165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37071399710483334736275443 55607099565725002104413165)
      ·
        refine ⟨20852662337146875789154937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55607099565725002104413165 20852662337146875789154937)
        ·
          refine ⟨15639496752860156841866203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20852662337146875789154937 15639496752860156841866203)
          ·
            refine ⟨23459245129290235262799305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639496752860156841866203 23459245129290235262799305)
            ·
              refine ⟨17594433846967676447099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23459245129290235262799305 17594433846967676447099479)
              ·
                refine ⟨26391650770451514670649219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17594433846967676447099479 26391650770451514670649219)
                ·
                  refine ⟨39587476155677272005973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26391650770451514670649219 39587476155677272005973829)
                  ·
                    refine ⟨7422651779189488501120093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39587476155677272005973829 7422651779189488501120093)
                    ·
                      refine ⟨2783494417196058187920035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422651779189488501120093 2783494417196058187920035)
                      ·
                        rfl

theorem cell23_5420836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_5420836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420836 prefixEnd_5420836 := by exact prefixLift 5420836
  have htrace : WordTrace (prefixWord ++ tailWord_5420836) baseStart_5420836 baseEnd_5420836 := by
    simpa [prefixWord, tailWord_5420836, baseEnd_5420836] using wordTrace_append hprefix tailTrace_5420836
  have hstable : (prefixWord ++ tailWord_5420836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420836).length < 2 ^ (prefixWord ++ tailWord_5420836).sum := by decide
  have hdescent : baseEnd_5420836 < baseStart_5420836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420853 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_5420853 : Nat := 118140960795 + 5420853 * 2 ^ 59
def prefixEnd_5420853 : Nat := 4983230072969 + 3 ^ 40 * 5420853 * 2
def baseEnd_5420853 : Nat := 2783503146367184621407457

theorem tailTrace_5420853 : CollatzResearch.WordTrace tailWord_5420853 prefixEnd_5420853 2783503146367184621407457 := by
  unfold tailWord_5420853
  simp only [CollatzResearch.WordTrace]
  refine ⟨197714751830182863830171213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131809834553455242553447475 197714751830182863830171213)
  ·
    refine ⟨74143031936318573936314205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197714751830182863830171213 74143031936318573936314205)
    ·
      refine ⟨27803636976119465226117827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74143031936318573936314205 27803636976119465226117827)
      ·
        refine ⟨41705455464179197839176741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27803636976119465226117827 41705455464179197839176741)
        ·
          refine ⟨7819772899533599594845639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41705455464179197839176741 7819772899533599594845639)
          ·
            refine ⟨11729659349300399392268459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819772899533599594845639 11729659349300399392268459)
            ·
              refine ⟨17594489023950599088402689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11729659349300399392268459 17594489023950599088402689)
              ·
                refine ⟨13195866767962949316302017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17594489023950599088402689 13195866767962949316302017)
                ·
                  refine ⟨9896900075972211987226513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195866767962949316302017 9896900075972211987226513)
                  ·
                    refine ⟨7422675056979158990419885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9896900075972211987226513 7422675056979158990419885)
                    ·
                      refine ⟨2783503146367184621407457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422675056979158990419885 2783503146367184621407457)
                      ·
                        rfl

theorem cell23_5420853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_5420853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420853 prefixEnd_5420853 := by exact prefixLift 5420853
  have htrace : WordTrace (prefixWord ++ tailWord_5420853) baseStart_5420853 baseEnd_5420853 := by
    simpa [prefixWord, tailWord_5420853, baseEnd_5420853] using wordTrace_append hprefix tailTrace_5420853
  have hstable : (prefixWord ++ tailWord_5420853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420853).length < 2 ^ (prefixWord ++ tailWord_5420853).sum := by decide
  have hdescent : baseEnd_5420853 < baseStart_5420853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420869 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_5420869 : Nat := 118140960795 + 5420869 * 2 ^ 59
def prefixEnd_5420869 : Nat := 4983230072969 + 3 ^ 40 * 5420869 * 2
def baseEnd_5420869 : Nat := 927837120685885519602461

theorem tailTrace_5420869 : CollatzResearch.WordTrace tailWord_5420869 prefixEnd_5420869 927837120685885519602461 := by
  unfold tailWord_5420869
  simp only [CollatzResearch.WordTrace]
  refine ⟨197715335398124898562753661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131810223598749932375169107 197715335398124898562753661)
  ·
    refine ⟨74143250774296836961032623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197715335398124898562753661 74143250774296836961032623)
    ·
      refine ⟨111214876161445255441548935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74143250774296836961032623 111214876161445255441548935)
      ·
        refine ⟨166822314242167883162323403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111214876161445255441548935 166822314242167883162323403)
        ·
          refine ⟨250233471363251824743485105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166822314242167883162323403 250233471363251824743485105)
          ·
            refine ⟨187675103522438868557613829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250233471363251824743485105 187675103522438868557613829)
            ·
              refine ⟨35189081910457287854552593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187675103522438868557613829 35189081910457287854552593)
              ·
                refine ⟨26391811432842965890914445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35189081910457287854552593 26391811432842965890914445)
                ·
                  refine ⟨9896929287316112209092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26391811432842965890914445 9896929287316112209092917)
                  ·
                    refine ⟨927837120685885519602461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9896929287316112209092917 927837120685885519602461)
                    ·
                      rfl

theorem cell23_5420869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_5420869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420869 prefixEnd_5420869 := by exact prefixLift 5420869
  have htrace : WordTrace (prefixWord ++ tailWord_5420869) baseStart_5420869 baseEnd_5420869 := by
    simpa [prefixWord, tailWord_5420869, baseEnd_5420869] using wordTrace_append hprefix tailTrace_5420869
  have hstable : (prefixWord ++ tailWord_5420869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420869).length < 2 ^ (prefixWord ++ tailWord_5420869).sum := by decide
  have hdescent : baseEnd_5420869 < baseStart_5420869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420903 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5420903 : Nat := 118140960795 + 5420903 * 2 ^ 59
def prefixEnd_5420903 : Nat := 4983230072969 + 3 ^ 40 * 5420903 * 2
def baseEnd_5420903 : Nat := 927842940133303141927409

theorem tailTrace_5420903 : CollatzResearch.WordTrace tailWord_5420903 prefixEnd_5420903 927842940133303141927409 := by
  unfold tailWord_5420903
  simp only [CollatzResearch.WordTrace]
  refine ⟨197716575480001722369491363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131811050320001148246327575 197716575480001722369491363)
  ·
    refine ⟨296574863220002583554237045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197716575480001722369491363 296574863220002583554237045)
    ·
      refine ⟨27803893426875242208209723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296574863220002583554237045 27803893426875242208209723)
      ·
        refine ⟨41705840140312863312314585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27803893426875242208209723 41705840140312863312314585)
        ·
          refine ⟨31279380105234647484235939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41705840140312863312314585 31279380105234647484235939)
          ·
            refine ⟨46919070157851971226353909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31279380105234647484235939 46919070157851971226353909)
            ·
              refine ⟨4398662827298622302470679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46919070157851971226353909 4398662827298622302470679)
              ·
                refine ⟨6597994240947933453706019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398662827298622302470679 6597994240947933453706019)
                ·
                  refine ⟨9896991361421900180559029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6597994240947933453706019 9896991361421900180559029)
                  ·
                    refine ⟨927842940133303141927409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9896991361421900180559029 927842940133303141927409)
                    ·
                      rfl

theorem cell23_5420903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5420903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420903 prefixEnd_5420903 := by exact prefixLift 5420903
  have htrace : WordTrace (prefixWord ++ tailWord_5420903) baseStart_5420903 baseEnd_5420903 := by
    simpa [prefixWord, tailWord_5420903, baseEnd_5420903] using wordTrace_append hprefix tailTrace_5420903
  have hstable : (prefixWord ++ tailWord_5420903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420903).length < 2 ^ (prefixWord ++ tailWord_5420903).sum := by decide
  have hdescent : baseEnd_5420903 < baseStart_5420903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420910 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5420910 : Nat := 118140960795 + 5420910 * 2 ^ 59
def prefixEnd_5420910 : Nat := 4983230072969 + 3 ^ 40 * 5420910 * 2
def baseEnd_5420910 : Nat := 2783532414764490898394695

theorem tailTrace_5420910 : CollatzResearch.WordTrace tailWord_5420910 prefixEnd_5420910 2783532414764490898394695 := by
  unfold tailWord_5420910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714603848872045320624523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131811220527317575043330789 24714603848872045320624523)
  ·
    refine ⟨37071905773308067980936785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24714603848872045320624523 37071905773308067980936785)
    ·
      refine ⟨27803929329981050985702589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37071905773308067980936785 27803929329981050985702589)
      ·
        refine ⟨10426473498742894119638471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27803929329981050985702589 10426473498742894119638471)
        ·
          refine ⟨15639710248114341179457707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426473498742894119638471 15639710248114341179457707)
          ·
            refine ⟨23459565372171511769186561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639710248114341179457707 23459565372171511769186561)
            ·
              refine ⟨17594674029128633826889921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23459565372171511769186561 17594674029128633826889921)
              ·
                refine ⟨13196005521846475370167441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17594674029128633826889921 13196005521846475370167441)
                ·
                  refine ⟨9897004141384856527625581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196005521846475370167441 9897004141384856527625581)
                  ·
                    refine ⟨3711376553019321197859593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9897004141384856527625581 3711376553019321197859593)
                    ·
                      refine ⟨2783532414764490898394695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711376553019321197859593 2783532414764490898394695)
                      ·
                        rfl

theorem cell23_5420910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5420910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420910 prefixEnd_5420910 := by exact prefixLift 5420910
  have htrace : WordTrace (prefixWord ++ tailWord_5420910) baseStart_5420910 baseEnd_5420910 := by
    simpa [prefixWord, tailWord_5420910, baseEnd_5420910] using wordTrace_append hprefix tailTrace_5420910
  have hstable : (prefixWord ++ tailWord_5420910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420910).length < 2 ^ (prefixWord ++ tailWord_5420910).sum := by decide
  have hdescent : baseEnd_5420910 < baseStart_5420910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420923 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 3, 2, 2]
def baseStart_5420923 : Nat := 118140960795 + 5420923 * 2 ^ 59
def prefixEnd_5420923 : Nat := 4983230072969 + 3 ^ 40 * 5420923 * 2
def baseEnd_5420923 : Nat := 2783539090012999347532135

theorem tailTrace_5420923 : CollatzResearch.WordTrace tailWord_5420923 prefixEnd_5420923 2783539090012999347532135 := by
  unfold tailWord_5420923
  simp only [CollatzResearch.WordTrace]
  refine ⟨197717304939929265785219423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131811536626619510523479615 197717304939929265785219423)
  ·
    refine ⟨296575957409893898677829135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197717304939929265785219423 296575957409893898677829135)
    ·
      refine ⟨444863936114840848016743703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296575957409893898677829135 444863936114840848016743703)
      ·
        refine ⟨667295904172261272025115555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444863936114840848016743703 667295904172261272025115555)
        ·
          refine ⟨1000943856258391908037673333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667295904172261272025115555 1000943856258391908037673333)
          ·
            refine ⟨93838486524224241378531875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1000943856258391908037673333 93838486524224241378531875)
            ·
              refine ⟨140757729786336362067797813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93838486524224241378531875 140757729786336362067797813)
              ·
                refine ⟨13196037167469033943856045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140757729786336362067797813 13196037167469033943856045)
                ·
                  refine ⟨4948513937800887728946017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13196037167469033943856045 4948513937800887728946017)
                  ·
                    refine ⟨3711385453350665796709513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948513937800887728946017 3711385453350665796709513)
                    ·
                      refine ⟨2783539090012999347532135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711385453350665796709513 2783539090012999347532135)
                      ·
                        rfl

theorem cell23_5420923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2, 2].length) (baseStart_5420923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420923 prefixEnd_5420923 := by exact prefixLift 5420923
  have htrace : WordTrace (prefixWord ++ tailWord_5420923) baseStart_5420923 baseEnd_5420923 := by
    simpa [prefixWord, tailWord_5420923, baseEnd_5420923] using wordTrace_append hprefix tailTrace_5420923
  have hstable : (prefixWord ++ tailWord_5420923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420923).length < 2 ^ (prefixWord ++ tailWord_5420923).sum := by decide
  have hdescent : baseEnd_5420923 < baseStart_5420923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420957 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_5420957 : Nat := 118140960795 + 5420957 * 2 ^ 59
def prefixEnd_5420957 : Nat := 4983230072969 + 3 ^ 40 * 5420957 * 2
def baseEnd_5420957 : Nat := 2783556548355252214506979

theorem tailTrace_5420957 : CollatzResearch.WordTrace tailWord_5420957 prefixEnd_5420957 2783556548355252214506979 := by
  unfold tailWord_5420957
  simp only [CollatzResearch.WordTrace]
  refine ⟨197718545021806089591957125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131812363347870726394638083 197718545021806089591957125)
  ·
    refine ⟨37072227191588641798491961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197718545021806089591957125 37072227191588641798491961)
    ·
      refine ⟨27804170393691481348868971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37072227191588641798491961 27804170393691481348868971)
      ·
        refine ⟨41706255590537222023303457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27804170393691481348868971 41706255590537222023303457)
        ·
          refine ⟨31279691692902916517477593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41706255590537222023303457 31279691692902916517477593)
          ·
            refine ⟨23459768769677187388108195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31279691692902916517477593 23459768769677187388108195)
            ·
              refine ⟨35189653154515781082162293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23459768769677187388108195 35189653154515781082162293)
              ·
                refine ⟨3299029983235854476452715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35189653154515781082162293 3299029983235854476452715)
                ·
                  refine ⟨4948544974853781714679073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299029983235854476452715 4948544974853781714679073)
                  ·
                    refine ⟨3711408731140336286009305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948544974853781714679073 3711408731140336286009305)
                    ·
                      refine ⟨2783556548355252214506979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711408731140336286009305 2783556548355252214506979)
                      ·
                        rfl

theorem cell23_5420957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_5420957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420957 prefixEnd_5420957 := by exact prefixLift 5420957
  have htrace : WordTrace (prefixWord ++ tailWord_5420957) baseStart_5420957 baseEnd_5420957 := by
    simpa [prefixWord, tailWord_5420957, baseEnd_5420957] using wordTrace_append hprefix tailTrace_5420957
  have hstable : (prefixWord ++ tailWord_5420957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420957).length < 2 ^ (prefixWord ++ tailWord_5420957).sum := by decide
  have hdescent : baseEnd_5420957 < baseStart_5420957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420969 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_5420969 : Nat := 118140960795 + 5420969 * 2 ^ 59
def prefixEnd_5420969 : Nat := 4983230072969 + 3 ^ 40 * 5420969 * 2
def baseEnd_5420969 : Nat := 2783562710123106167556923

theorem tailTrace_5420969 : CollatzResearch.WordTrace tailWord_5420969 prefixEnd_5420969 2783562710123106167556923 := by
  unfold tailWord_5420969
  simp only [CollatzResearch.WordTrace]
  refine ⟨197718982697762615641393961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131812655131841743760929307 197718982697762615641393961)
  ·
    refine ⟨148289237023321961731045471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197718982697762615641393961 148289237023321961731045471)
    ·
      refine ⟨222433855534982942596568207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148289237023321961731045471 222433855534982942596568207)
      ·
        refine ⟨333650783302474413894852311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222433855534982942596568207 333650783302474413894852311)
        ·
          refine ⟨500476174953711620842278467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333650783302474413894852311 500476174953711620842278467)
          ·
            refine ⟨750714262430567431263417701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500476174953711620842278467 750714262430567431263417701)
            ·
              refine ⟨140758924205731393361890819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750714262430567431263417701 140758924205731393361890819)
              ·
                refine ⟨211138386308597090042836229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140758924205731393361890819 211138386308597090042836229)
                ·
                  refine ⟨39588447432861954383031793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211138386308597090042836229 39588447432861954383031793)
                  ·
                    refine ⟨29691335574646465787273845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39588447432861954383031793 29691335574646465787273845)
                    ·
                      refine ⟨2783562710123106167556923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29691335574646465787273845 2783562710123106167556923)
                      ·
                        rfl

theorem cell23_5420969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_5420969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420969 prefixEnd_5420969 := by exact prefixLift 5420969
  have htrace : WordTrace (prefixWord ++ tailWord_5420969) baseStart_5420969 baseEnd_5420969 := by
    simpa [prefixWord, tailWord_5420969, baseEnd_5420969] using wordTrace_append hprefix tailTrace_5420969
  have hstable : (prefixWord ++ tailWord_5420969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420969).length < 2 ^ (prefixWord ++ tailWord_5420969).sum := by decide
  have hdescent : baseEnd_5420969 < baseStart_5420969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5420990 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_5420990 : Nat := 118140960795 + 5420990 * 2 ^ 59
def prefixEnd_5420990 : Nat := 4983230072969 + 3 ^ 40 * 5420990 * 2
def baseEnd_5420990 : Nat := 2783573493216850585394327

theorem tailTrace_5420990 : CollatzResearch.WordTrace tailWord_5420990 prefixEnd_5420990 2783573493216850585394327 := by
  unfold tailWord_5420990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714968578835817028488553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131813165753791024151938949 24714968578835817028488553)
  ·
    refine ⟨18536226434126862771366415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24714968578835817028488553 18536226434126862771366415)
    ·
      refine ⟨27804339651190294157049623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18536226434126862771366415 27804339651190294157049623)
      ·
        refine ⟨41706509476785441235574435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27804339651190294157049623 41706509476785441235574435)
        ·
          refine ⟨62559764215178161853361653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41706509476785441235574435 62559764215178161853361653)
          ·
            refine ⟨5864977895172952673752655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62559764215178161853361653 5864977895172952673752655)
            ·
              refine ⟨8797466842759429010628983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864977895172952673752655 8797466842759429010628983)
              ·
                refine ⟨13196200264139143515943475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797466842759429010628983 13196200264139143515943475)
                ·
                  refine ⟨19794300396208715273915213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13196200264139143515943475 19794300396208715273915213)
                  ·
                    refine ⟨7422862648578268227718205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19794300396208715273915213 7422862648578268227718205)
                    ·
                      refine ⟨2783573493216850585394327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7422862648578268227718205 2783573493216850585394327)
                      ·
                        rfl

theorem cell23_5420990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_5420990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5420990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5420990 prefixEnd_5420990 := by exact prefixLift 5420990
  have htrace : WordTrace (prefixWord ++ tailWord_5420990) baseStart_5420990 baseEnd_5420990 := by
    simpa [prefixWord, tailWord_5420990, baseEnd_5420990] using wordTrace_append hprefix tailTrace_5420990
  have hstable : (prefixWord ++ tailWord_5420990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5420990).length < 2 ^ (prefixWord ++ tailWord_5420990).sum := by decide
  have hdescent : baseEnd_5420990 < baseStart_5420990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5420990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421000 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_5421000 : Nat := 118140960795 + 5421000 * 2 ^ 59
def prefixEnd_5421000 : Nat := 4983230072969 + 3 ^ 40 * 5421000 * 2
def baseEnd_5421000 : Nat := 2783578628023395546269281

theorem tailTrace_5421000 : CollatzResearch.WordTrace tailWord_5421000 prefixEnd_5421000 2783578628023395546269281 := by
  unfold tailWord_5421000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98860056680325153967886227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131813408907100205290514969 98860056680325153967886227)
  ·
    refine ⟨148290085020487730951829341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98860056680325153967886227 148290085020487730951829341)
    ·
      refine ⟨55608781882682899106936003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148290085020487730951829341 55608781882682899106936003)
      ·
        refine ⟨83413172824024348660404005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55608781882682899106936003 83413172824024348660404005)
        ·
          refine ⟨15639969904504565373825751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83413172824024348660404005 15639969904504565373825751)
          ·
            refine ⟨23459954856756848060738627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639969904504565373825751 23459954856756848060738627)
            ·
              refine ⟨35189932285135272091107941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23459954856756848060738627 35189932285135272091107941)
              ·
                refine ⟨6598112303462863517082739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35189932285135272091107941 6598112303462863517082739)
                ·
                  refine ⟨9897168455194295275624109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598112303462863517082739 9897168455194295275624109)
                  ·
                    refine ⟨3711438170697860728359041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9897168455194295275624109 3711438170697860728359041)
                    ·
                      refine ⟨2783578628023395546269281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711438170697860728359041 2783578628023395546269281)
                      ·
                        rfl

theorem cell23_5421000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_5421000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421000 prefixEnd_5421000 := by exact prefixLift 5421000
  have htrace : WordTrace (prefixWord ++ tailWord_5421000) baseStart_5421000 baseEnd_5421000 := by
    simpa [prefixWord, tailWord_5421000, baseEnd_5421000] using wordTrace_append hprefix tailTrace_5421000
  have hstable : (prefixWord ++ tailWord_5421000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421000).length < 2 ^ (prefixWord ++ tailWord_5421000).sum := by decide
  have hdescent : baseEnd_5421000 < baseStart_5421000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421016 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5421016 : Nat := 118140960795 + 5421016 * 2 ^ 59
def prefixEnd_5421016 : Nat := 4983230072969 + 3 ^ 40 * 5421016 * 2
def baseEnd_5421016 : Nat := 2783586843713867483669207

theorem tailTrace_5421016 : CollatzResearch.WordTrace tailWord_5421016 prefixEnd_5421016 2783586843713867483669207 := by
  unfold tailWord_5421016
  simp only [CollatzResearch.WordTrace]
  refine ⟨98860348464296171334177451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131813797952394895112236601 98860348464296171334177451)
  ·
    refine ⟨148290522696444257001266177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98860348464296171334177451 148290522696444257001266177)
    ·
      refine ⟨111217892022333192750949633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148290522696444257001266177 111217892022333192750949633)
      ·
        refine ⟨83413419016749894563212225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111217892022333192750949633 83413419016749894563212225)
        ·
          refine ⟨62560064262562420922409169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83413419016749894563212225 62560064262562420922409169)
          ·
            refine ⟨46920048196921815691806877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62560064262562420922409169 46920048196921815691806877)
            ·
              refine ⟨17595018073845680884427579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46920048196921815691806877 17595018073845680884427579)
              ·
                refine ⟨26392527110768521326641369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17595018073845680884427579 26392527110768521326641369)
                ·
                  refine ⟨19794395333076390994981027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26392527110768521326641369 19794395333076390994981027)
                  ·
                    refine ⟨29691592999614586492471541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19794395333076390994981027 29691592999614586492471541)
                    ·
                      refine ⟨2783586843713867483669207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29691592999614586492471541 2783586843713867483669207)
                      ·
                        rfl

theorem cell23_5421016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5421016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421016 prefixEnd_5421016 := by exact prefixLift 5421016
  have htrace : WordTrace (prefixWord ++ tailWord_5421016) baseStart_5421016 baseEnd_5421016 := by
    simpa [prefixWord, tailWord_5421016, baseEnd_5421016] using wordTrace_append hprefix tailTrace_5421016
  have hstable : (prefixWord ++ tailWord_5421016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421016).length < 2 ^ (prefixWord ++ tailWord_5421016).sum := by decide
  have hdescent : baseEnd_5421016 < baseStart_5421016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421120 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_5421120 : Nat := 118140960795 + 5421120 * 2 ^ 59
def prefixEnd_5421120 : Nat := 4983230072969 + 3 ^ 40 * 5421120 * 2
def baseEnd_5421120 : Nat := 2783640245701935076768729

theorem tailTrace_5421120 : CollatzResearch.WordTrace tailWord_5421120 prefixEnd_5421120 2783640245701935076768729 := by
  unfold tailWord_5421120
  simp only [CollatzResearch.WordTrace]
  refine ⟨98862245060107784215070407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131816326746810378953427209 98862245060107784215070407)
  ·
    refine ⟨148293367590161676322605611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98862245060107784215070407 148293367590161676322605611)
    ·
      refine ⟨222440051385242514483908417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148293367590161676322605611 222440051385242514483908417)
      ·
        refine ⟨166830038538931885862931313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222440051385242514483908417 166830038538931885862931313)
        ·
          refine ⟨125122528904198914397198485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166830038538931885862931313 125122528904198914397198485)
          ·
            refine ⟨5865118542384324112368679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125122528904198914397198485 5865118542384324112368679)
            ·
              refine ⟨8797677813576486168553019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5865118542384324112368679 8797677813576486168553019)
              ·
                refine ⟨13196516720364729252829529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797677813576486168553019 13196516720364729252829529)
                ·
                  refine ⟨9897387540273546939622147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196516720364729252829529 9897387540273546939622147)
                  ·
                    refine ⟨14846081310410320409433221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9897387540273546939622147 14846081310410320409433221)
                    ·
                      refine ⟨2783640245701935076768729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14846081310410320409433221 2783640245701935076768729)
                      ·
                        rfl

theorem cell23_5421120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_5421120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421120 prefixEnd_5421120 := by exact prefixLift 5421120
  have htrace : WordTrace (prefixWord ++ tailWord_5421120) baseStart_5421120 baseEnd_5421120 := by
    simpa [prefixWord, tailWord_5421120, baseEnd_5421120] using wordTrace_append hprefix tailTrace_5421120
  have hstable : (prefixWord ++ tailWord_5421120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421120).length < 2 ^ (prefixWord ++ tailWord_5421120).sum := by decide
  have hdescent : baseEnd_5421120 < baseStart_5421120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421123 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3]
def baseStart_5421123 : Nat := 118140960795 + 5421123 * 2 ^ 59
def prefixEnd_5421123 : Nat := 4983230072969 + 3 ^ 40 * 5421123 * 2
def baseEnd_5421123 : Nat := 2783641786143898565031215

theorem tailTrace_5421123 : CollatzResearch.WordTrace tailWord_5421123 prefixEnd_5421123 2783641786143898565031215 := by
  unfold tailWord_5421123
  simp only [CollatzResearch.WordTrace]
  refine ⟨197724599539204699942500023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131816399692803133295000015 197724599539204699942500023)
  ·
    refine ⟨296586899308807049913750035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197724599539204699942500023 296586899308807049913750035)
    ·
      refine ⟨444880348963210574870625053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296586899308807049913750035 444880348963210574870625053)
      ·
        refine ⟨166830130861203965576484395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444880348963210574870625053 166830130861203965576484395)
        ·
          refine ⟨250245196291805948364726593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166830130861203965576484395 250245196291805948364726593)
          ·
            refine ⟨187683897218854461273544945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250245196291805948364726593 187683897218854461273544945)
            ·
              refine ⟨140762922914140845955158709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187683897218854461273544945 140762922914140845955158709)
              ·
                refine ⟨13196524023200704308296129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140762922914140845955158709 13196524023200704308296129)
                ·
                  refine ⟨9897393017400528231222097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196524023200704308296129 9897393017400528231222097)
                  ·
                    refine ⟨7423044763050396173416573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9897393017400528231222097 7423044763050396173416573)
                    ·
                      refine ⟨2783641786143898565031215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7423044763050396173416573 2783641786143898565031215)
                      ·
                        rfl

theorem cell23_5421123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_5421123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421123 prefixEnd_5421123 := by exact prefixLift 5421123
  have htrace : WordTrace (prefixWord ++ tailWord_5421123) baseStart_5421123 baseEnd_5421123 := by
    simpa [prefixWord, tailWord_5421123, baseEnd_5421123] using wordTrace_append hprefix tailTrace_5421123
  have hstable : (prefixWord ++ tailWord_5421123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421123).length < 2 ^ (prefixWord ++ tailWord_5421123).sum := by decide
  have hdescent : baseEnd_5421123 < baseStart_5421123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421133 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5421133 : Nat := 118140960795 + 5421133 * 2 ^ 59
def prefixEnd_5421133 : Nat := 4983230072969 + 3 ^ 40 * 5421133 * 2
def baseEnd_5421133 : Nat := 2783646920950443525906169

theorem tailTrace_5421133 : CollatzResearch.WordTrace tailWord_5421133 prefixEnd_5421133 2783646920950443525906169 := by
  unfold tailWord_5421133
  simp only [CollatzResearch.WordTrace]
  refine ⟨197724964269168471650364053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131816642846112314433576035 197724964269168471650364053)
  ·
    refine ⟨9268357700117272108610815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197724964269168471650364053 9268357700117272108610815)
    ·
      refine ⟨13902536550175908162916223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268357700117272108610815 13902536550175908162916223)
      ·
        refine ⟨20853804825263862244374335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13902536550175908162916223 20853804825263862244374335)
        ·
          refine ⟨31280707237895793366561503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20853804825263862244374335 31280707237895793366561503)
          ·
            refine ⟨46921060856843690049842255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31280707237895793366561503 46921060856843690049842255)
            ·
              refine ⟨70381591285265535074763383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46921060856843690049842255 70381591285265535074763383)
              ·
                refine ⟨105572386927898302612145075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70381591285265535074763383 105572386927898302612145075)
                ·
                  refine ⟨158358580391847453918217613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105572386927898302612145075 158358580391847453918217613)
                  ·
                    refine ⟨59384467646942795219331605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158358580391847453918217613 59384467646942795219331605)
                    ·
                      refine ⟨2783646920950443525906169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59384467646942795219331605 2783646920950443525906169)
                      ·
                        rfl

theorem cell23_5421133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5421133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421133 prefixEnd_5421133 := by exact prefixLift 5421133
  have htrace : WordTrace (prefixWord ++ tailWord_5421133) baseStart_5421133 baseEnd_5421133 := by
    simpa [prefixWord, tailWord_5421133, baseEnd_5421133] using wordTrace_append hprefix tailTrace_5421133
  have hstable : (prefixWord ++ tailWord_5421133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421133).length < 2 ^ (prefixWord ++ tailWord_5421133).sum := by decide
  have hdescent : baseEnd_5421133 < baseStart_5421133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421143 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 6]
def baseStart_5421143 : Nat := 118140960795 + 5421143 * 2 ^ 59
def prefixEnd_5421143 : Nat := 4983230072969 + 3 ^ 40 * 5421143 * 2
def baseEnd_5421143 : Nat := 309294672861887609642347

theorem tailTrace_5421143 : CollatzResearch.WordTrace tailWord_5421143 prefixEnd_5421143 309294672861887609642347 := by
  unfold tailWord_5421143
  simp only [CollatzResearch.WordTrace]
  refine ⟨197725328999132243358228083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131816885999421495572152055 197725328999132243358228083)
  ·
    refine ⟨296587993498698365037342125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197725328999132243358228083 296587993498698365037342125)
    ·
      refine ⟨111220497562011886889003297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296587993498698365037342125 111220497562011886889003297)
      ·
        refine ⟨83415373171508915166752473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111220497562011886889003297 83415373171508915166752473)
        ·
          refine ⟨62561529878631686375064355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83415373171508915166752473 62561529878631686375064355)
          ·
            refine ⟨93842294817947529562596533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62561529878631686375064355 93842294817947529562596533)
            ·
              refine ⟨8797715139182580896493425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93842294817947529562596533 8797715139182580896493425)
              ·
                refine ⟨6598286354386935672370069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8797715139182580896493425 6598286354386935672370069)
                ·
                  refine ⟨309294672861887609642347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6598286354386935672370069 309294672861887609642347)
                  ·
                    rfl

theorem cell23_5421143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 6].length) (baseStart_5421143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421143 prefixEnd_5421143 := by exact prefixLift 5421143
  have htrace : WordTrace (prefixWord ++ tailWord_5421143) baseStart_5421143 baseEnd_5421143 := by
    simpa [prefixWord, tailWord_5421143, baseEnd_5421143] using wordTrace_append hprefix tailTrace_5421143
  have hstable : (prefixWord ++ tailWord_5421143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421143).length < 2 ^ (prefixWord ++ tailWord_5421143).sum := by decide
  have hdescent : baseEnd_5421143 < baseStart_5421143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421146 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5421146 : Nat := 118140960795 + 5421146 * 2 ^ 59
def prefixEnd_5421146 : Nat := 4983230072969 + 3 ^ 40 * 5421146 * 2
def baseEnd_5421146 : Nat := 2783653596198951975043609

theorem tailTrace_5421146 : CollatzResearch.WordTrace tailWord_5421146 prefixEnd_5421146 2783653596198951975043609 := by
  unfold tailWord_5421146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49431359604530343717646823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131816958945414249913724861 49431359604530343717646823)
  ·
    refine ⟨74147039406795515576470235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49431359604530343717646823 74147039406795515576470235)
    ·
      refine ⟨111220559110193273364705353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74147039406795515576470235 111220559110193273364705353)
      ·
        refine ⟨83415419332644955023529015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111220559110193273364705353 83415419332644955023529015)
        ·
          refine ⟨125123128998967432535293523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83415419332644955023529015 125123128998967432535293523)
          ·
            refine ⟨187684693498451148802940285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125123128998967432535293523 187684693498451148802940285)
            ·
              refine ⟨70381760061919180801102607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187684693498451148802940285 70381760061919180801102607)
              ·
                refine ⟨105572640092878771201653911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70381760061919180801102607 105572640092878771201653911)
                ·
                  refine ⟨158358960139318156802480867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105572640092878771201653911 158358960139318156802480867)
                  ·
                    refine ⟨237538440208977235203721301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158358960139318156802480867 237538440208977235203721301)
                    ·
                      refine ⟨2783653596198951975043609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237538440208977235203721301 2783653596198951975043609)
                      ·
                        rfl

theorem cell23_5421146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5421146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421146 prefixEnd_5421146 := by exact prefixLift 5421146
  have htrace : WordTrace (prefixWord ++ tailWord_5421146) baseStart_5421146 baseEnd_5421146 := by
    simpa [prefixWord, tailWord_5421146, baseEnd_5421146] using wordTrace_append hprefix tailTrace_5421146
  have hstable : (prefixWord ++ tailWord_5421146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421146).length < 2 ^ (prefixWord ++ tailWord_5421146).sum := by decide
  have hdescent : baseEnd_5421146 < baseStart_5421146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421180 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_5421180 : Nat := 118140960795 + 5421180 * 2 ^ 59
def prefixEnd_5421180 : Nat := 4983230072969 + 3 ^ 40 * 5421180 * 2
def baseEnd_5421180 : Nat := 2783671054541204842018453

theorem tailTrace_5421180 : CollatzResearch.WordTrace tailWord_5421180 prefixEnd_5421180 2783671054541204842018453 := by
  unfold tailWord_5421180
  simp only [CollatzResearch.WordTrace]
  refine ⟨98863339249999099338662497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131817785666665465784883329 98863339249999099338662497)
  ·
    refine ⟨74147504437499324503996873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98863339249999099338662497 74147504437499324503996873)
    ·
      refine ⟨55610628328124493377997655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74147504437499324503996873 55610628328124493377997655)
      ·
        refine ⟨83415942492186740066996483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55610628328124493377997655 83415942492186740066996483)
        ·
          refine ⟨125123913738280110100494725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83415942492186740066996483 125123913738280110100494725)
          ·
            refine ⟨23460733825927520643842761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125123913738280110100494725 23460733825927520643842761)
            ·
              refine ⟨17595550369445640482882071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23460733825927520643842761 17595550369445640482882071)
              ·
                refine ⟨26393325554168460724323107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17595550369445640482882071 26393325554168460724323107)
                ·
                  refine ⟨39589988331252691086484661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26393325554168460724323107 39589988331252691086484661)
                  ·
                    refine ⟨3711561406054939789357937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39589988331252691086484661 3711561406054939789357937)
                    ·
                      refine ⟨2783671054541204842018453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3711561406054939789357937 2783671054541204842018453)
                      ·
                        rfl

theorem cell23_5421180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_5421180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421180 prefixEnd_5421180 := by exact prefixLift 5421180
  have htrace : WordTrace (prefixWord ++ tailWord_5421180) baseStart_5421180 baseEnd_5421180 := by
    simpa [prefixWord, tailWord_5421180, baseEnd_5421180] using wordTrace_append hprefix tailTrace_5421180
  have hstable : (prefixWord ++ tailWord_5421180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421180).length < 2 ^ (prefixWord ++ tailWord_5421180).sum := by decide
  have hdescent : baseEnd_5421180 < baseStart_5421180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421237 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5421237 : Nat := 118140960795 + 5421237 * 2 ^ 59
def prefixEnd_5421237 : Nat := 4983230072969 + 3 ^ 40 * 5421237 * 2
def baseEnd_5421237 : Nat := 927900107646170373001897

theorem tailTrace_5421237 : CollatzResearch.WordTrace tailWord_5421237 prefixEnd_5421237 927900107646170373001897 := by
  unfold tailWord_5421237
  simp only [CollatzResearch.WordTrace]
  refine ⟨197728757460791697412149965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131819171640527798274766643 197728757460791697412149965)
  ·
    refine ⟨74148284047796886529556237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197728757460791697412149965 74148284047796886529556237)
    ·
      refine ⟨27805606517923832448583589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74148284047796886529556237 27805606517923832448583589)
      ·
        refine ⟨5213551222110718584109423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27805606517923832448583589 5213551222110718584109423)
        ·
          refine ⟨7820326833166077876164135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213551222110718584109423 7820326833166077876164135)
          ·
            refine ⟨11730490249749116814246203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820326833166077876164135 11730490249749116814246203)
            ·
              refine ⟨17595735374623675221369305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11730490249749116814246203 17595735374623675221369305)
              ·
                refine ⟨13196801530967756416026979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17595735374623675221369305 13196801530967756416026979)
                ·
                  refine ⟨19795202296451634624040469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13196801530967756416026979 19795202296451634624040469)
                  ·
                    refine ⟨927900107646170373001897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19795202296451634624040469 927900107646170373001897)
                    ·
                      rfl

theorem cell23_5421237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5421237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421237 prefixEnd_5421237 := by exact prefixLift 5421237
  have htrace : WordTrace (prefixWord ++ tailWord_5421237) baseStart_5421237 baseEnd_5421237 := by
    simpa [prefixWord, tailWord_5421237, baseEnd_5421237] using wordTrace_append hprefix tailTrace_5421237
  have hstable : (prefixWord ++ tailWord_5421237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421237).length < 2 ^ (prefixWord ++ tailWord_5421237).sum := by decide
  have hdescent : baseEnd_5421237 < baseStart_5421237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421244 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_5421244 : Nat := 118140960795 + 5421244 * 2 ^ 59
def prefixEnd_5421244 : Nat := 4983230072969 + 3 ^ 40 * 5421244 * 2
def baseEnd_5421244 : Nat := 2783703917303092591618159

theorem tailTrace_5421244 : CollatzResearch.WordTrace tailWord_5421244 prefixEnd_5421244 2783703917303092591618159 := by
  unfold tailWord_5421244
  simp only [CollatzResearch.WordTrace]
  refine ⟨98864506385883168803827393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131819341847844225071769857 98864506385883168803827393)
  ·
    refine ⟨74148379789412376602870545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98864506385883168803827393 74148379789412376602870545)
    ·
      refine ⟨55611284842059282452152909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74148379789412376602870545 55611284842059282452152909)
      ·
        refine ⟨20854231815772230919557341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55611284842059282452152909 20854231815772230919557341)
        ·
          refine ⟨7820336930914586594834003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20854231815772230919557341 7820336930914586594834003)
          ·
            refine ⟨11730505396371879892251005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820336930914586594834003 11730505396371879892251005)
            ·
              refine ⟨4398939523639454959594127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11730505396371879892251005 4398939523639454959594127)
              ·
                refine ⟨6598409285459182439391191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398939523639454959594127 6598409285459182439391191)
                ·
                  refine ⟨9897613928188773659086787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598409285459182439391191 9897613928188773659086787)
                  ·
                    refine ⟨14846420892283160488630181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9897613928188773659086787 14846420892283160488630181)
                    ·
                      refine ⟨2783703917303092591618159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14846420892283160488630181 2783703917303092591618159)
                      ·
                        rfl

theorem cell23_5421244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_5421244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421244 prefixEnd_5421244 := by exact prefixLift 5421244
  have htrace : WordTrace (prefixWord ++ tailWord_5421244) baseStart_5421244 baseEnd_5421244 := by
    simpa [prefixWord, tailWord_5421244, baseEnd_5421244] using wordTrace_append hprefix tailTrace_5421244
  have hstable : (prefixWord ++ tailWord_5421244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421244).length < 2 ^ (prefixWord ++ tailWord_5421244).sum := by decide
  have hdescent : baseEnd_5421244 < baseStart_5421244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421277 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5421277 : Nat := 118140960795 + 5421277 * 2 ^ 59
def prefixEnd_5421277 : Nat := 4983230072969 + 3 ^ 40 * 5421277 * 2
def baseEnd_5421277 : Nat := 2783720862164690962505507

theorem tailTrace_5421277 : CollatzResearch.WordTrace tailWord_5421277 prefixEnd_5421277 2783720862164690962505507 := by
  unfold tailWord_5421277
  simp only [CollatzResearch.WordTrace]
  refine ⟨197730216380646784243606085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131820144253764522829070723 197730216380646784243606085)
  ·
    refine ⟨37074415571371272045676141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197730216380646784243606085 37074415571371272045676141)
    ·
      refine ⟨13902905839264227017128553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37074415571371272045676141 13902905839264227017128553)
      ·
        refine ⟨10427179379448170262846415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13902905839264227017128553 10427179379448170262846415)
        ·
          refine ⟨15640769069172255394269623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10427179379448170262846415 15640769069172255394269623)
          ·
            refine ⟨23461153603758383091404435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15640769069172255394269623 23461153603758383091404435)
            ·
              refine ⟨35191730405637574637106653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23461153603758383091404435 35191730405637574637106653)
              ·
                refine ⟨13196898902114090488914995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35191730405637574637106653 13196898902114090488914995)
                ·
                  refine ⟨19795348353171135733372493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13196898902114090488914995 19795348353171135733372493)
                  ·
                    refine ⟨7423255632439175900014685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19795348353171135733372493 7423255632439175900014685)
                    ·
                      refine ⟨2783720862164690962505507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7423255632439175900014685 2783720862164690962505507)
                      ·
                        rfl

theorem cell23_5421277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5421277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421277 prefixEnd_5421277 := by exact prefixLift 5421277
  have htrace : WordTrace (prefixWord ++ tailWord_5421277) baseStart_5421277 baseEnd_5421277 := by
    simpa [prefixWord, tailWord_5421277, baseEnd_5421277] using wordTrace_append hprefix tailTrace_5421277
  have hstable : (prefixWord ++ tailWord_5421277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421277).length < 2 ^ (prefixWord ++ tailWord_5421277).sum := by decide
  have hdescent : baseEnd_5421277 < baseStart_5421277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421310 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5421310 : Nat := 118140960795 + 5421310 * 2 ^ 59
def prefixEnd_5421310 : Nat := 4983230072969 + 3 ^ 40 * 5421310 * 2
def baseEnd_5421310 : Nat := 927912602342096444464285

theorem tailTrace_5421310 : CollatzResearch.WordTrace tailWord_5421310 prefixEnd_5421310 927912602342096444464285 := by
  unfold tailWord_5421310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716427498690903859944673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131820946659684820586371589 24716427498690903859944673)
  ·
    refine ⟨18537320624018177894958505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24716427498690903859944673 18537320624018177894958505)
    ·
      refine ⟨13902990468013633421218879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18537320624018177894958505 13902990468013633421218879)
      ·
        refine ⟨20854485702020450131828319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13902990468013633421218879 20854485702020450131828319)
        ·
          refine ⟨31281728553030675197742479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20854485702020450131828319 31281728553030675197742479)
          ·
            refine ⟨46922592829546012796613719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31281728553030675197742479 46922592829546012796613719)
            ·
              refine ⟨70383889244319019194920579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46922592829546012796613719 70383889244319019194920579)
              ·
                refine ⟨105575833866478528792380869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70383889244319019194920579 105575833866478528792380869)
                ·
                  refine ⟨19795468849964724148571413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105575833866478528792380869 19795468849964724148571413)
                  ·
                    refine ⟨927912602342096444464285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19795468849964724148571413 927912602342096444464285)
                    ·
                      rfl

theorem cell23_5421310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5421310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421310 prefixEnd_5421310 := by exact prefixLift 5421310
  have htrace : WordTrace (prefixWord ++ tailWord_5421310) baseStart_5421310 baseEnd_5421310 := by
    simpa [prefixWord, tailWord_5421310, baseEnd_5421310] using wordTrace_append hprefix tailTrace_5421310
  have hstable : (prefixWord ++ tailWord_5421310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421310).length < 2 ^ (prefixWord ++ tailWord_5421310).sum := by decide
  have hdescent : baseEnd_5421310 < baseStart_5421310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5421370 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_5421370 : Nat := 118140960795 + 5421370 * 2 ^ 59
def prefixEnd_5421370 : Nat := 4983230072969 + 3 ^ 40 * 5421370 * 2
def baseEnd_5421370 : Nat := 927922871955186366214193

theorem tailTrace_5421370 : CollatzResearch.WordTrace tailWord_5421370 prefixEnd_5421370 927922871955186366214193 := by
  unfold tailWord_5421370
  simp only [CollatzResearch.WordTrace]
  refine ⟨49433402092327465281685391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131822405579539907417827709 49433402092327465281685391)
  ·
    refine ⟨74150103138491197922528087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49433402092327465281685391 74150103138491197922528087)
    ·
      refine ⟨111225154707736796883792131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74150103138491197922528087 111225154707736796883792131)
      ·
        refine ⟨166837732061605195325688197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111225154707736796883792131 166837732061605195325688197)
        ·
          refine ⟨31282074761550974123566537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166837732061605195325688197 31282074761550974123566537)
          ·
            refine ⟨23461556071163230592674903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31282074761550974123566537 23461556071163230592674903)
            ·
              refine ⟨35192334106744845889012355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23461556071163230592674903 35192334106744845889012355)
              ·
                refine ⟨52788501160117268833518533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35192334106744845889012355 52788501160117268833518533)
                ·
                  refine ⟨9897843967521987906284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52788501160117268833518533 9897843967521987906284725)
                  ·
                    refine ⟨927922871955186366214193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9897843967521987906284725 927922871955186366214193)
                    ·
                      rfl

theorem cell23_5421370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_5421370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5421370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5421370 prefixEnd_5421370 := by exact prefixLift 5421370
  have htrace : WordTrace (prefixWord ++ tailWord_5421370) baseStart_5421370 baseEnd_5421370 := by
    simpa [prefixWord, tailWord_5421370, baseEnd_5421370] using wordTrace_append hprefix tailTrace_5421370
  have hstable : (prefixWord ++ tailWord_5421370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5421370).length < 2 ^ (prefixWord ++ tailWord_5421370).sum := by decide
  have hdescent : baseEnd_5421370 < baseStart_5421370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5421370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
