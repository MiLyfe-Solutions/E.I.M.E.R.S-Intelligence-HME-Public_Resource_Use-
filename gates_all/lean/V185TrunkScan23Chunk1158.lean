import V185TrunkScan23Chunk1157

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6859885 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6859885 : Nat := 118140960795 + 6859885 * 2 ^ 59
def prefixEnd_6859885 : Nat := 4983230072969 + 3 ^ 40 * 6859885 * 2
def baseEnd_6859885 : Nat := 3522418239567998402089469

theorem tailTrace_6859885 : CollatzResearch.WordTrace tailWord_6859885 prefixEnd_6859885 3522418239567998402089469 := by
  unfold tailWord_6859885
  simp only [CollatzResearch.WordTrace]
  refine ⟨250200560752815694929253109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166800373835210463286168739 250200560752815694929253109)
  ·
    refine ⟨23456302570576471399617479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250200560752815694929253109 23456302570576471399617479)
    ·
      refine ⟨35184453855864707099426219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23456302570576471399617479 35184453855864707099426219)
      ·
        refine ⟨52776680783797060649139329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35184453855864707099426219 52776680783797060649139329)
        ·
          refine ⟨39582510587847795486854497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52776680783797060649139329 39582510587847795486854497)
          ·
            refine ⟨29686882940885846615140873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39582510587847795486854497 29686882940885846615140873)
            ·
              refine ⟨22265162205664384961355655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29686882940885846615140873 22265162205664384961355655)
              ·
                refine ⟨33397743308496577442033483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22265162205664384961355655 33397743308496577442033483)
                ·
                  refine ⟨50096614962744866163050225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33397743308496577442033483 50096614962744866163050225)
                  ·
                    refine ⟨37572461222058649622287669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50096614962744866163050225 37572461222058649622287669)
                    ·
                      refine ⟨3522418239567998402089469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37572461222058649622287669 3522418239567998402089469)
                      ·
                        rfl

theorem cell23_6859885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6859885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859885 prefixEnd_6859885 := by exact prefixLift 6859885
  have htrace : WordTrace (prefixWord ++ tailWord_6859885) baseStart_6859885 baseEnd_6859885 := by
    simpa [prefixWord, tailWord_6859885, baseEnd_6859885] using wordTrace_append hprefix tailTrace_6859885
  have hstable : (prefixWord ++ tailWord_6859885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859885).length < 2 ^ (prefixWord ++ tailWord_6859885).sum := by decide
  have hdescent : baseEnd_6859885 < baseStart_6859885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859909 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_6859909 : Nat := 118140960795 + 6859909 * 2 ^ 59
def prefixEnd_6859909 : Nat := 4983230072969 + 3 ^ 40 * 6859909 * 2
def baseEnd_6859909 : Nat := 1174143521034568769396453

theorem tailTrace_6859909 : CollatzResearch.WordTrace tailWord_6859909 prefixEnd_6859909 1174143521034568769396453 := by
  unfold tailWord_6859909
  simp only [CollatzResearch.WordTrace]
  refine ⟨250201436104728747028126781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166800957403152498018751187 250201436104728747028126781)
  ·
    refine ⟨93825538539273280135547543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250201436104728747028126781 93825538539273280135547543)
    ·
      refine ⟨140738307808909920203321315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93825538539273280135547543 140738307808909920203321315)
      ·
        refine ⟨211107461713364880304981973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140738307808909920203321315 211107461713364880304981973)
        ·
          refine ⟨4947831133906989382148015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211107461713364880304981973 4947831133906989382148015)
          ·
            refine ⟨7421746700860484073222023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947831133906989382148015 7421746700860484073222023)
            ·
              refine ⟨11132620051290726109833035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421746700860484073222023 11132620051290726109833035)
              ·
                refine ⟨16698930076936089164749553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11132620051290726109833035 16698930076936089164749553)
                ·
                  refine ⟨12524197557702066873562165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16698930076936089164749553 12524197557702066873562165)
                  ·
                    refine ⟨1174143521034568769396453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12524197557702066873562165 1174143521034568769396453)
                    ·
                      rfl

theorem cell23_6859909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_6859909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859909 prefixEnd_6859909 := by exact prefixLift 6859909
  have htrace : WordTrace (prefixWord ++ tailWord_6859909) baseStart_6859909 baseEnd_6859909 := by
    simpa [prefixWord, tailWord_6859909, baseEnd_6859909] using wordTrace_append hprefix tailTrace_6859909
  have hstable : (prefixWord ++ tailWord_6859909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859909).length < 2 ^ (prefixWord ++ tailWord_6859909).sum := by decide
  have hdescent : baseEnd_6859909 < baseStart_6859909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859912 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6859912 : Nat := 118140960795 + 6859912 * 2 ^ 59
def prefixEnd_6859912 : Nat := 4983230072969 + 3 ^ 40 * 6859912 * 2
def baseEnd_6859912 : Nat := 3522432103545669796451845

theorem tailTrace_6859912 : CollatzResearch.WordTrace tailWord_6859912 prefixEnd_6859912 3522432103545669796451845 := by
  unfold tailWord_6859912
  simp only [CollatzResearch.WordTrace]
  refine ⟨125100772761858939270242995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166801030349145252360323993 125100772761858939270242995)
  ·
    refine ⟨187651159142788408905364493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125100772761858939270242995 187651159142788408905364493)
    ·
      refine ⟨70369184678545653339511685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187651159142788408905364493 70369184678545653339511685)
      ·
        refine ⟨13194222127227310001158441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70369184678545653339511685 13194222127227310001158441)
        ·
          refine ⟨9895666595420482500868831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13194222127227310001158441 9895666595420482500868831)
          ·
            refine ⟨14843499893130723751303247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895666595420482500868831 14843499893130723751303247)
            ·
              refine ⟨22265249839696085626954871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14843499893130723751303247 22265249839696085626954871)
              ·
                refine ⟨33397874759544128440432307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22265249839696085626954871 33397874759544128440432307)
                ·
                  refine ⟨50096812139316192660648461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33397874759544128440432307 50096812139316192660648461)
                  ·
                    refine ⟨18786304552243572247743173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50096812139316192660648461 18786304552243572247743173)
                    ·
                      refine ⟨3522432103545669796451845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18786304552243572247743173 3522432103545669796451845)
                      ·
                        rfl

theorem cell23_6859912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6859912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859912 prefixEnd_6859912 := by exact prefixLift 6859912
  have htrace : WordTrace (prefixWord ++ tailWord_6859912) baseStart_6859912 baseEnd_6859912 := by
    simpa [prefixWord, tailWord_6859912, baseEnd_6859912] using wordTrace_append hprefix tailTrace_6859912
  have hstable : (prefixWord ++ tailWord_6859912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859912).length < 2 ^ (prefixWord ++ tailWord_6859912).sum := by decide
  have hdescent : baseEnd_6859912 < baseStart_6859912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859948 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_6859948 : Nat := 118140960795 + 6859948 * 2 ^ 59
def prefixEnd_6859948 : Nat := 4983230072969 + 3 ^ 40 * 6859948 * 2
def baseEnd_6859948 : Nat := 1174150196283077218533893

theorem tailTrace_6859948 : CollatzResearch.WordTrace tailWord_6859948 prefixEnd_6859948 1174150196283077218533893 := by
  unfold tailWord_6859948
  simp only [CollatzResearch.WordTrace]
  refine ⟨125101429275793728344398249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166801905701058304459197665 125101429275793728344398249)
  ·
    refine ⟨93826071956845296258298687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125101429275793728344398249 93826071956845296258298687)
    ·
      refine ⟨140739107935267944387448031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93826071956845296258298687 140739107935267944387448031)
      ·
        refine ⟨211108661902901916581172047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140739107935267944387448031 211108661902901916581172047)
        ·
          refine ⟨316662992854352874871758071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211108661902901916581172047 316662992854352874871758071)
          ·
            refine ⟨474994489281529312307637107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316662992854352874871758071 474994489281529312307637107)
            ·
              refine ⟨712491733922293968461455661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474994489281529312307637107 712491733922293968461455661)
              ·
                refine ⟨267184400220860238173045873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 712491733922293968461455661 267184400220860238173045873)
                ·
                  refine ⟨200388300165645178629784405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267184400220860238173045873 200388300165645178629784405)
                  ·
                    refine ⟨1174150196283077218533893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 200388300165645178629784405 1174150196283077218533893)
                    ·
                      rfl

theorem cell23_6859948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_6859948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859948 prefixEnd_6859948 := by exact prefixLift 6859948
  have htrace : WordTrace (prefixWord ++ tailWord_6859948) baseStart_6859948 baseEnd_6859948 := by
    simpa [prefixWord, tailWord_6859948, baseEnd_6859948] using wordTrace_append hprefix tailTrace_6859948
  have hstable : (prefixWord ++ tailWord_6859948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859948).length < 2 ^ (prefixWord ++ tailWord_6859948).sum := by decide
  have hdescent : baseEnd_6859948 < baseStart_6859948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859965 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6859965 : Nat := 118140960795 + 6859965 * 2 ^ 59
def prefixEnd_6859965 : Nat := 4983230072969 + 3 ^ 40 * 6859965 * 2
def baseEnd_6859965 : Nat := 1174153106006786029696367

theorem tailTrace_6859965 : CollatzResearch.WordTrace tailWord_6859965 prefixEnd_6859965 1174153106006786029696367 := by
  unfold tailWord_6859965
  simp only [CollatzResearch.WordTrace]
  refine ⟨250203478592525868592165349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166802319061683912394776899 250203478592525868592165349)
  ·
    refine ⟨46913152236098600361031003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250203478592525868592165349 46913152236098600361031003)
    ·
      refine ⟨70369728354147900541546505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46913152236098600361031003 70369728354147900541546505)
      ·
        refine ⟨52777296265610925406159879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70369728354147900541546505 52777296265610925406159879)
        ·
          refine ⟨79165944398416388109239819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52777296265610925406159879 79165944398416388109239819)
          ·
            refine ⟨118748916597624582163859729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79165944398416388109239819 118748916597624582163859729)
            ·
              refine ⟨89061687448218436622894797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118748916597624582163859729 89061687448218436622894797)
              ·
                refine ⟨33398132793081913733585549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89061687448218436622894797 33398132793081913733585549)
                ·
                  refine ⟨12524299797405717650094581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33398132793081913733585549 12524299797405717650094581)
                  ·
                    refine ⟨1174153106006786029696367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12524299797405717650094581 1174153106006786029696367)
                    ·
                      rfl

theorem cell23_6859965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6859965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859965 prefixEnd_6859965 := by exact prefixLift 6859965
  have htrace : WordTrace (prefixWord ++ tailWord_6859965) baseStart_6859965 baseEnd_6859965 := by
    simpa [prefixWord, tailWord_6859965, baseEnd_6859965] using wordTrace_append hprefix tailTrace_6859965
  have hstable : (prefixWord ++ tailWord_6859965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859965).length < 2 ^ (prefixWord ++ tailWord_6859965).sum := by decide
  have hdescent : baseEnd_6859965 < baseStart_6859965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859979 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 1, 1, 3]
def baseStart_6859979 : Nat := 118140960795 + 6859979 * 2 ^ 59
def prefixEnd_6859979 : Nat := 4983230072969 + 3 ^ 40 * 6859979 * 2
def baseEnd_6859979 : Nat := 3522466506749521034314037

theorem tailTrace_6859979 : CollatzResearch.WordTrace tailWord_6859979 prefixEnd_6859979 3522466506749521034314037 := by
  unfold tailWord_6859979
  simp only [CollatzResearch.WordTrace]
  refine ⟨250203989214475148983174991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166802659476316765988783327 250203989214475148983174991)
  ·
    refine ⟨375305983821712723474762487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250203989214475148983174991 375305983821712723474762487)
    ·
      refine ⟨562958975732569085212143731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375305983821712723474762487 562958975732569085212143731)
      ·
        refine ⟨844438463598853627818215597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562958975732569085212143731 844438463598853627818215597)
        ·
          refine ⟨316664423849570110431830849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 844438463598853627818215597 316664423849570110431830849)
          ·
            refine ⟨237498317887177582823873137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316664423849570110431830849 237498317887177582823873137)
            ·
              refine ⟨178123738415383187117904853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237498317887177582823873137 178123738415383187117904853)
              ·
                refine ⟨4174775119110543448075895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178123738415383187117904853 4174775119110543448075895)
                ·
                  refine ⟨6262162678665815172113843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174775119110543448075895 6262162678665815172113843)
                  ·
                    refine ⟨9393244017998722758170765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6262162678665815172113843 9393244017998722758170765)
                    ·
                      refine ⟨3522466506749521034314037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9393244017998722758170765 3522466506749521034314037)
                      ·
                        rfl

theorem cell23_6859979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 1, 3].length) (baseStart_6859979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859979 prefixEnd_6859979 := by exact prefixLift 6859979
  have htrace : WordTrace (prefixWord ++ tailWord_6859979) baseStart_6859979 baseEnd_6859979 := by
    simpa [prefixWord, tailWord_6859979, baseEnd_6859979] using wordTrace_append hprefix tailTrace_6859979
  have hstable : (prefixWord ++ tailWord_6859979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859979).length < 2 ^ (prefixWord ++ tailWord_6859979).sum := by decide
  have hdescent : baseEnd_6859979 < baseStart_6859979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859985 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_6859985 : Nat := 118140960795 + 6859985 * 2 ^ 59
def prefixEnd_6859985 : Nat := 4983230072969 + 3 ^ 40 * 6859985 * 2
def baseEnd_6859985 : Nat := 3522469587633448010839009

theorem tailTrace_6859985 : CollatzResearch.WordTrace tailWord_6859985 prefixEnd_6859985 3522469587633448010839009 := by
  unfold tailWord_6859985
  simp only [CollatzResearch.WordTrace]
  refine ⟨250204208052453412007893409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166802805368302274671928939 250204208052453412007893409)
  ·
    refine ⟨187653156039340059005920057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250204208052453412007893409 187653156039340059005920057)
    ·
      refine ⟨140739867029505044254440043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187653156039340059005920057 140739867029505044254440043)
      ·
        refine ⟨211109800544257566381660065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140739867029505044254440043 211109800544257566381660065)
        ·
          refine ⟨158332350408193174786245049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211109800544257566381660065 158332350408193174786245049)
          ·
            refine ⟨118749262806144881089683787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158332350408193174786245049 118749262806144881089683787)
            ·
              refine ⟨178123894209217321634525681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118749262806144881089683787 178123894209217321634525681)
              ·
                refine ⟨133592920656912991225894261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178123894209217321634525681 133592920656912991225894261)
                ·
                  refine ⟨12524336311585592927427587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133592920656912991225894261 12524336311585592927427587)
                  ·
                    refine ⟨18786504467378389391141381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12524336311585592927427587 18786504467378389391141381)
                    ·
                      refine ⟨3522469587633448010839009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18786504467378389391141381 3522469587633448010839009)
                      ·
                        rfl

theorem cell23_6859985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_6859985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859985 prefixEnd_6859985 := by exact prefixLift 6859985
  have htrace : WordTrace (prefixWord ++ tailWord_6859985) baseStart_6859985 baseEnd_6859985 := by
    simpa [prefixWord, tailWord_6859985, baseEnd_6859985] using wordTrace_append hprefix tailTrace_6859985
  have hstable : (prefixWord ++ tailWord_6859985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859985).length < 2 ^ (prefixWord ++ tailWord_6859985).sum := by decide
  have hdescent : baseEnd_6859985 < baseStart_6859985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859989 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6859989 : Nat := 118140960795 + 6859989 * 2 ^ 59
def prefixEnd_6859989 : Nat := 4983230072969 + 3 ^ 40 * 6859989 * 2
def baseEnd_6859989 : Nat := 3522471641556065995188991

theorem tailTrace_6859989 : CollatzResearch.WordTrace tailWord_6859989 prefixEnd_6859989 3522471641556065995188991 := by
  unfold tailWord_6859989
  simp only [CollatzResearch.WordTrace]
  refine ⟨250204353944438920691039021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166802902629625947127359347 250204353944438920691039021)
  ·
    refine ⟨93826632729164595259139633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250204353944438920691039021 93826632729164595259139633)
    ·
      refine ⟨70369974546873446444354725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93826632729164595259139633 70369974546873446444354725)
      ·
        refine ⟨13194370227538771208316511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70369974546873446444354725 13194370227538771208316511)
        ·
          refine ⟨19791555341308156812474767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13194370227538771208316511 19791555341308156812474767)
          ·
            refine ⟨29687333011962235218712151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19791555341308156812474767 29687333011962235218712151)
            ·
              refine ⟨44530999517943352828068227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29687333011962235218712151 44530999517943352828068227)
              ·
                refine ⟨66796499276915029242102341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44530999517943352828068227 66796499276915029242102341)
                ·
                  refine ⟨12524343614421567982894189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66796499276915029242102341 12524343614421567982894189)
                  ·
                    refine ⟨4696628855408087993585321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12524343614421567982894189 4696628855408087993585321)
                    ·
                      refine ⟨3522471641556065995188991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696628855408087993585321 3522471641556065995188991)
                      ·
                        rfl

theorem cell23_6859989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6859989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859989 prefixEnd_6859989 := by exact prefixLift 6859989
  have htrace : WordTrace (prefixWord ++ tailWord_6859989) baseStart_6859989 baseEnd_6859989 := by
    simpa [prefixWord, tailWord_6859989, baseEnd_6859989] using wordTrace_append hprefix tailTrace_6859989
  have hstable : (prefixWord ++ tailWord_6859989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859989).length < 2 ^ (prefixWord ++ tailWord_6859989).sum := by decide
  have hdescent : baseEnd_6859989 < baseStart_6859989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859990 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6859990 : Nat := 118140960795 + 6859990 * 2 ^ 59
def prefixEnd_6859990 : Nat := 4983230072969 + 3 ^ 40 * 6859990 * 2
def baseEnd_6859990 : Nat := 1174157385012240163758829

theorem tailTrace_6859990 : CollatzResearch.WordTrace tailWord_6859990 prefixEnd_6859990 1174157385012240163758829 := by
  unfold tailWord_6859990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637774401089706116364089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166802926944956865241216949 15637774401089706116364089)
  ·
    refine ⟨11728330800817279587273067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15637774401089706116364089 11728330800817279587273067)
    ·
      refine ⟨17592496201225919380909601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11728330800817279587273067 17592496201225919380909601)
      ·
        refine ⟨13194372150919439535682201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17592496201225919380909601 13194372150919439535682201)
        ·
          refine ⟨9895779113189579651761651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13194372150919439535682201 9895779113189579651761651)
          ·
            refine ⟨14843668669784369477642477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895779113189579651761651 14843668669784369477642477)
            ·
              refine ⟨5566375751169138554115929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14843668669784369477642477 5566375751169138554115929)
              ·
                refine ⟨4174781813376853915586947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5566375751169138554115929 4174781813376853915586947)
                ·
                  refine ⟨6262172720065280873380421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174781813376853915586947 6262172720065280873380421)
                  ·
                    refine ⟨1174157385012240163758829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6262172720065280873380421 1174157385012240163758829)
                    ·
                      rfl

theorem cell23_6859990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6859990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859990 prefixEnd_6859990 := by exact prefixLift 6859990
  have htrace : WordTrace (prefixWord ++ tailWord_6859990) baseStart_6859990 baseEnd_6859990 := by
    simpa [prefixWord, tailWord_6859990, baseEnd_6859990] using wordTrace_append hprefix tailTrace_6859990
  have hstable : (prefixWord ++ tailWord_6859990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859990).length < 2 ^ (prefixWord ++ tailWord_6859990).sum := by decide
  have hdescent : baseEnd_6859990 < baseStart_6859990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6859995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 8, 4]
def baseStart_6859995 : Nat := 118140960795 + 6859995 * 2 ^ 59
def prefixEnd_6859995 : Nat := 4983230072969 + 3 ^ 40 * 6859995 * 2
def baseEnd_6859995 : Nat := 1174158240813330990571321

theorem tailTrace_6859995 : CollatzResearch.WordTrace tailWord_6859995 prefixEnd_6859995 1174158240813330990571321 := by
  unfold tailWord_6859995
  simp only [CollatzResearch.WordTrace]
  refine ⟨250204572782417183715757439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166803048521611455810504959 250204572782417183715757439)
  ·
    refine ⟨375306859173625775573636159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250204572782417183715757439 375306859173625775573636159)
    ·
      refine ⟨562960288760438663360454239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375306859173625775573636159 562960288760438663360454239)
      ·
        refine ⟨844440433140657995040681359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562960288760438663360454239 844440433140657995040681359)
        ·
          refine ⟨1266660649710986992561022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844440433140657995040681359 1266660649710986992561022039)
          ·
            refine ⟨1899990974566480488841533059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266660649710986992561022039 1899990974566480488841533059)
            ·
              refine ⟨2849986461849720733262299589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899990974566480488841533059 2849986461849720733262299589)
              ·
                refine ⟨534372461596822637486681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2849986461849720733262299589 534372461596822637486681173)
                ·
                  refine ⟨6262177284337765283047045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 534372461596822637486681173 6262177284337765283047045)
                  ·
                    refine ⟨1174158240813330990571321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6262177284337765283047045 1174158240813330990571321)
                    ·
                      rfl

theorem cell23_6859995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 4].length) (baseStart_6859995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6859995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6859995 prefixEnd_6859995 := by exact prefixLift 6859995
  have htrace : WordTrace (prefixWord ++ tailWord_6859995) baseStart_6859995 baseEnd_6859995 := by
    simpa [prefixWord, tailWord_6859995, baseEnd_6859995] using wordTrace_append hprefix tailTrace_6859995
  have hstable : (prefixWord ++ tailWord_6859995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6859995).length < 2 ^ (prefixWord ++ tailWord_6859995).sum := by decide
  have hdescent : baseEnd_6859995 < baseStart_6859995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6859995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860019 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 4]
def baseStart_6860019 : Nat := 118140960795 + 6860019 * 2 ^ 59
def prefixEnd_6860019 : Nat := 4983230072969 + 3 ^ 40 * 6860019 * 2
def baseEnd_6860019 : Nat := 3522487045975700877813853

theorem tailTrace_6860019 : CollatzResearch.WordTrace tailWord_6860019 prefixEnd_6860019 3522487045975700877813853 := by
  unfold tailWord_6860019
  simp only [CollatzResearch.WordTrace]
  refine ⟨250205448134330235814631111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166803632089553490543087407 250205448134330235814631111)
  ·
    refine ⟨375308172201495353721946667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250205448134330235814631111 375308172201495353721946667)
    ·
      refine ⟨562962258302243030582920001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375308172201495353721946667 562962258302243030582920001)
      ·
        refine ⟨422221693726682272937190001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562962258302243030582920001 422221693726682272937190001)
        ·
          refine ⟨316666270295011704702892501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422221693726682272937190001 316666270295011704702892501)
          ·
            refine ⟨7421865710039336828974043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 316666270295011704702892501 7421865710039336828974043)
            ·
              refine ⟨11132798565059005243461065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421865710039336828974043 11132798565059005243461065)
              ·
                refine ⟨8349598923794253932595799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11132798565059005243461065 8349598923794253932595799)
                ·
                  refine ⟨12524398385691380898893699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349598923794253932595799 12524398385691380898893699)
                  ·
                    refine ⟨18786597578537071348340549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12524398385691380898893699 18786597578537071348340549)
                    ·
                      refine ⟨3522487045975700877813853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18786597578537071348340549 3522487045975700877813853)
                      ·
                        rfl

theorem cell23_6860019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_6860019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860019 prefixEnd_6860019 := by exact prefixLift 6860019
  have htrace : WordTrace (prefixWord ++ tailWord_6860019) baseStart_6860019 baseEnd_6860019 := by
    simpa [prefixWord, tailWord_6860019, baseEnd_6860019] using wordTrace_append hprefix tailTrace_6860019
  have hstable : (prefixWord ++ tailWord_6860019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860019).length < 2 ^ (prefixWord ++ tailWord_6860019).sum := by decide
  have hdescent : baseEnd_6860019 < baseStart_6860019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860036 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6860036 : Nat := 118140960795 + 6860036 * 2 ^ 59
def prefixEnd_6860036 : Nat := 4983230072969 + 3 ^ 40 * 6860036 * 2
def baseEnd_6860036 : Nat := 3522495775146827311301275

theorem tailTrace_6860036 : CollatzResearch.WordTrace tailWord_6860036 prefixEnd_6860036 3522495775146827311301275 := by
  unfold tailWord_6860036
  simp only [CollatzResearch.WordTrace]
  refine ⟨125103034087634323858999981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166804045450179098478666641 125103034087634323858999981)
  ·
    refine ⟨46913637782862871447124993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125103034087634323858999981 46913637782862871447124993)
    ·
      refine ⟨35185228337147153585343745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46913637782862871447124993 35185228337147153585343745)
      ·
        refine ⟨26388921252860365189007809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35185228337147153585343745 26388921252860365189007809)
        ·
          refine ⟨19791690939645273891755857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26388921252860365189007809 19791690939645273891755857)
          ·
            refine ⟨14843768204733955418816893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19791690939645273891755857 14843768204733955418816893)
            ·
              refine ⟨5566413076775233282056335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14843768204733955418816893 5566413076775233282056335)
              ·
                refine ⟨8349619615162849923084503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566413076775233282056335 8349619615162849923084503)
                ·
                  refine ⟨12524429422744274884626755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349619615162849923084503 12524429422744274884626755)
                  ·
                    refine ⟨18786644134116412326940133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12524429422744274884626755 18786644134116412326940133)
                    ·
                      refine ⟨3522495775146827311301275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18786644134116412326940133 3522495775146827311301275)
                      ·
                        rfl

theorem cell23_6860036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6860036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860036 prefixEnd_6860036 := by exact prefixLift 6860036
  have htrace : WordTrace (prefixWord ++ tailWord_6860036) baseStart_6860036 baseEnd_6860036 := by
    simpa [prefixWord, tailWord_6860036, baseEnd_6860036] using wordTrace_append hprefix tailTrace_6860036
  have hstable : (prefixWord ++ tailWord_6860036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860036).length < 2 ^ (prefixWord ++ tailWord_6860036).sum := by decide
  have hdescent : baseEnd_6860036 < baseStart_6860036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860055 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 9]
def baseStart_6860055 : Nat := 118140960795 + 6860055 * 2 ^ 59
def prefixEnd_6860055 : Nat := 4983230072969 + 3 ^ 40 * 6860055 * 2
def baseEnd_6860055 : Nat := 1174168510426420912321229

theorem tailTrace_6860055 : CollatzResearch.WordTrace tailWord_6860055 prefixEnd_6860055 1174168510426420912321229 := by
  unfold tailWord_6860055
  simp only [CollatzResearch.WordTrace]
  refine ⟨250206761162199813962941619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166804507441466542641961079 250206761162199813962941619)
  ·
    refine ⟨375310141743299720944412429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250206761162199813962941619 375310141743299720944412429)
    ·
      refine ⟨140741303153737395354154661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375310141743299720944412429 140741303153737395354154661)
      ·
        refine ⟨26388994341325761628903999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140741303153737395354154661 26388994341325761628903999)
        ·
          refine ⟨39583491511988642443355999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26388994341325761628903999 39583491511988642443355999)
          ·
            refine ⟨59375237267982963665033999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39583491511988642443355999 59375237267982963665033999)
            ·
              refine ⟨89062855901974445497550999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59375237267982963665033999 89062855901974445497550999)
              ·
                refine ⟨133594283852961668246326499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89062855901974445497550999 133594283852961668246326499)
                ·
                  refine ⟨200391425779442502369489749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133594283852961668246326499 200391425779442502369489749)
                  ·
                    refine ⟨1174168510426420912321229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 200391425779442502369489749 1174168510426420912321229)
                    ·
                      rfl

theorem cell23_6860055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_6860055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860055 prefixEnd_6860055 := by exact prefixLift 6860055
  have htrace : WordTrace (prefixWord ++ tailWord_6860055) baseStart_6860055 baseEnd_6860055 := by
    simpa [prefixWord, tailWord_6860055, baseEnd_6860055] using wordTrace_append hprefix tailTrace_6860055
  have hstable : (prefixWord ++ tailWord_6860055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860055).length < 2 ^ (prefixWord ++ tailWord_6860055).sum := by decide
  have hdescent : baseEnd_6860055 < baseStart_6860055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860065 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6860065 : Nat := 118140960795 + 6860065 * 2 ^ 59
def prefixEnd_6860065 : Nat := 4983230072969 + 3 ^ 40 * 6860065 * 2
def baseEnd_6860065 : Nat := 3522510666085807697838641

theorem tailTrace_6860065 : CollatzResearch.WordTrace tailWord_6860065 prefixEnd_6860065 3522510666085807697838641 := by
  unfold tailWord_6860065
  simp only [CollatzResearch.WordTrace]
  refine ⟨250207125892163585670805649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166804750594775723780537099 250207125892163585670805649)
  ·
    refine ⟨187655344419122689253104237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250207125892163585670805649 187655344419122689253104237)
    ·
      refine ⟨70370754157171008469914089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187655344419122689253104237 70370754157171008469914089)
      ·
        refine ⟨52778065617878256352435567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70370754157171008469914089 52778065617878256352435567)
        ·
          refine ⟨79167098426817384528653351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52778065617878256352435567 79167098426817384528653351)
          ·
            refine ⟨118750647640226076792980027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79167098426817384528653351 118750647640226076792980027)
            ·
              refine ⟨178125971460339115189470041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118750647640226076792980027 178125971460339115189470041)
              ·
                refine ⟨133594478595254336392102531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178125971460339115189470041 133594478595254336392102531)
                ·
                  refine ⟨200391717892881504588153797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133594478595254336392102531 200391717892881504588153797)
                  ·
                    refine ⟨37573447104915282110278837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200391717892881504588153797 37573447104915282110278837)
                    ·
                      refine ⟨3522510666085807697838641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37573447104915282110278837 3522510666085807697838641)
                      ·
                        rfl

theorem cell23_6860065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6860065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860065 prefixEnd_6860065 := by exact prefixLift 6860065
  have htrace : WordTrace (prefixWord ++ tailWord_6860065) baseStart_6860065 baseEnd_6860065 := by
    simpa [prefixWord, tailWord_6860065, baseEnd_6860065] using wordTrace_append hprefix tailTrace_6860065
  have hstable : (prefixWord ++ tailWord_6860065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860065).length < 2 ^ (prefixWord ++ tailWord_6860065).sum := by decide
  have hdescent : baseEnd_6860065 < baseStart_6860065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860069 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_6860069 : Nat := 118140960795 + 6860069 * 2 ^ 59
def prefixEnd_6860069 : Nat := 4983230072969 + 3 ^ 40 * 6860069 * 2
def baseEnd_6860069 : Nat := 3522512720008425682188623

theorem tailTrace_6860069 : CollatzResearch.WordTrace tailWord_6860069 prefixEnd_6860069 3522512720008425682188623 := by
  unfold tailWord_6860069
  simp only [CollatzResearch.WordTrace]
  refine ⟨250207271784149094353951261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166804847856099396235967507 250207271784149094353951261)
  ·
    refine ⟨93827726919055910382731723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250207271784149094353951261 93827726919055910382731723)
    ·
      refine ⟨140741590378583865574097585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93827726919055910382731723 140741590378583865574097585)
      ·
        refine ⟨105556192783937899180573189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140741590378583865574097585 105556192783937899180573189)
        ·
          refine ⟨19791786146988356096357473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105556192783937899180573189 19791786146988356096357473)
          ·
            refine ⟨14843839610241267072268105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19791786146988356096357473 14843839610241267072268105)
            ·
              refine ⟨11132879707680950304201079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14843839610241267072268105 11132879707680950304201079)
              ·
                refine ⟨16699319561521425456301619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11132879707680950304201079 16699319561521425456301619)
                ·
                  refine ⟨25048979342282138184452429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16699319561521425456301619 25048979342282138184452429)
                  ·
                    refine ⟨9393367253355801819169661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25048979342282138184452429 9393367253355801819169661)
                    ·
                      refine ⟨3522512720008425682188623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9393367253355801819169661 3522512720008425682188623)
                      ·
                        rfl

theorem cell23_6860069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_6860069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860069 prefixEnd_6860069 := by exact prefixLift 6860069
  have htrace : WordTrace (prefixWord ++ tailWord_6860069) baseStart_6860069 baseEnd_6860069 := by
    simpa [prefixWord, tailWord_6860069, baseEnd_6860069] using wordTrace_append hprefix tailTrace_6860069
  have hstable : (prefixWord ++ tailWord_6860069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860069).length < 2 ^ (prefixWord ++ tailWord_6860069).sum := by decide
  have hdescent : baseEnd_6860069 < baseStart_6860069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860079 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 1, 3, 2]
def baseStart_6860079 : Nat := 118140960795 + 6860079 * 2 ^ 59
def prefixEnd_6860079 : Nat := 4983230072969 + 3 ^ 40 * 6860079 * 2
def baseEnd_6860079 : Nat := 3522517854814970643063577

theorem tailTrace_6860079 : CollatzResearch.WordTrace tailWord_6860079 prefixEnd_6860079 3522517854814970643063577 := by
  unfold tailWord_6860079
  simp only [CollatzResearch.WordTrace]
  refine ⟨250207636514112866061815291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166805091009408577374543527 250207636514112866061815291)
  ·
    refine ⟨375311454771169299092722937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250207636514112866061815291 375311454771169299092722937)
    ·
      refine ⟨281483591078376974319542203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375311454771169299092722937 281483591078376974319542203)
      ·
        refine ⟨422225386617565461479313305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281483591078376974319542203 422225386617565461479313305)
        ·
          refine ⟨316669039963174096109484979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422225386617565461479313305 316669039963174096109484979)
          ·
            refine ⟨475003559944761144164227469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316669039963174096109484979 475003559944761144164227469)
            ·
              refine ⟨178126334979285429061585301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475003559944761144164227469 178126334979285429061585301)
              ·
                refine ⟨8349671952154004487261811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178126334979285429061585301 8349671952154004487261811)
                ·
                  refine ⟨12524507928231006730892717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349671952154004487261811 12524507928231006730892717)
                  ·
                    refine ⟨4696690473086627524084769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12524507928231006730892717 4696690473086627524084769)
                    ·
                      refine ⟨3522517854814970643063577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696690473086627524084769 3522517854814970643063577)
                      ·
                        rfl

theorem cell23_6860079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 3, 2].length) (baseStart_6860079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860079 prefixEnd_6860079 := by exact prefixLift 6860079
  have htrace : WordTrace (prefixWord ++ tailWord_6860079) baseStart_6860079 baseEnd_6860079 := by
    simpa [prefixWord, tailWord_6860079, baseEnd_6860079] using wordTrace_append hprefix tailTrace_6860079
  have hstable : (prefixWord ++ tailWord_6860079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860079).length < 2 ^ (prefixWord ++ tailWord_6860079).sum := by decide
  have hdescent : baseEnd_6860079 < baseStart_6860079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860122 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_6860122 : Nat := 118140960795 + 6860122 * 2 ^ 59
def prefixEnd_6860122 : Nat := 4983230072969 + 3 ^ 40 * 6860122 * 2
def baseEnd_6860122 : Nat := 3522539934483113974825879

theorem tailTrace_6860122 : CollatzResearch.WordTrace tailWord_6860122 prefixEnd_6860122 3522539934483113974825879 := by
  unfold tailWord_6860122
  simp only [CollatzResearch.WordTrace]
  refine ⟨62552301213239271101407655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166806136568638056270420413 62552301213239271101407655)
  ·
    refine ⟨93828451819858906652111483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62552301213239271101407655 93828451819858906652111483)
    ·
      refine ⟨140742677729788359978167225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93828451819858906652111483 140742677729788359978167225)
      ·
        refine ⟨105557008297341269983625419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140742677729788359978167225 105557008297341269983625419)
        ·
          refine ⟨158335512446011904975438129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105557008297341269983625419 158335512446011904975438129)
          ·
            refine ⟨118751634334508928731578597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158335512446011904975438129 118751634334508928731578597)
            ·
              refine ⟨22265931437720424137170987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118751634334508928731578597 22265931437720424137170987)
              ·
                refine ⟨33398897156580636205756481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22265931437720424137170987 33398897156580636205756481)
                ·
                  refine ⟨25049172867435477154317361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33398897156580636205756481 25049172867435477154317361)
                  ·
                    refine ⟨18786879650576607865738021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25049172867435477154317361 18786879650576607865738021)
                    ·
                      refine ⟨3522539934483113974825879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18786879650576607865738021 3522539934483113974825879)
                      ·
                        rfl

theorem cell23_6860122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_6860122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860122 prefixEnd_6860122 := by exact prefixLift 6860122
  have htrace : WordTrace (prefixWord ++ tailWord_6860122) baseStart_6860122 baseEnd_6860122 := by
    simpa [prefixWord, tailWord_6860122, baseEnd_6860122] using wordTrace_append hprefix tailTrace_6860122
  have hstable : (prefixWord ++ tailWord_6860122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860122).length < 2 ^ (prefixWord ++ tailWord_6860122).sum := by decide
  have hdescent : baseEnd_6860122 < baseStart_6860122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860132 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 7]
def baseStart_6860132 : Nat := 118140960795 + 6860132 * 2 ^ 59
def prefixEnd_6860132 : Nat := 4983230072969 + 3 ^ 40 * 6860132 * 2
def baseEnd_6860132 : Nat := 391393896587739881744537

theorem tailTrace_6860132 : CollatzResearch.WordTrace tailWord_6860132 prefixEnd_6860132 391393896587739881744537 := by
  unfold tailWord_6860132
  simp only [CollatzResearch.WordTrace]
  refine ⟨125104784791460428056747325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166806379721947237408996433 125104784791460428056747325)
  ·
    refine ⟨46914294296797660521280247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125104784791460428056747325 46914294296797660521280247)
    ·
      refine ⟨70371441445196490781920371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46914294296797660521280247 70371441445196490781920371)
      ·
        refine ⟨105557162167794736172880557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70371441445196490781920371 105557162167794736172880557)
        ·
          refine ⟨39583935812923026064830209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105557162167794736172880557 39583935812923026064830209)
          ·
            refine ⟨29687951859692269548622657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39583935812923026064830209 29687951859692269548622657)
            ·
              refine ⟨22265963894769202161466993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29687951859692269548622657 22265963894769202161466993)
              ·
                refine ⟨16699472921076901621100245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22265963894769202161466993 16699472921076901621100245)
                ·
                  refine ⟨391393896587739881744537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16699472921076901621100245 391393896587739881744537)
                  ·
                    rfl

theorem cell23_6860132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_6860132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860132 prefixEnd_6860132 := by exact prefixLift 6860132
  have htrace : WordTrace (prefixWord ++ tailWord_6860132) baseStart_6860132 baseEnd_6860132 := by
    simpa [prefixWord, tailWord_6860132, baseEnd_6860132] using wordTrace_append hprefix tailTrace_6860132
  have hstable : (prefixWord ++ tailWord_6860132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860132).length < 2 ^ (prefixWord ++ tailWord_6860132).sum := by decide
  have hdescent : baseEnd_6860132 < baseStart_6860132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860172 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6860172 : Nat := 118140960795 + 6860172 * 2 ^ 59
def prefixEnd_6860172 : Nat := 4983230072969 + 3 ^ 40 * 6860172 * 2
def baseEnd_6860172 : Nat := 3522565608515838779200649

theorem tailTrace_6860172 : CollatzResearch.WordTrace tailWord_6860172 prefixEnd_6860172 3522565608515838779200649 := by
  unfold tailWord_6860172
  simp only [CollatzResearch.WordTrace]
  refine ⟨125105514251387971472475385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166807352335183961963300513 125105514251387971472475385)
  ·
    refine ⟨93829135688540978604356539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125105514251387971472475385 93829135688540978604356539)
    ·
      refine ⟨140743703532811467906534809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93829135688540978604356539 140743703532811467906534809)
      ·
        refine ⟨105557777649608600929901107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140743703532811467906534809 105557777649608600929901107)
        ·
          refine ⟨158336666474412901394851661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105557777649608600929901107 158336666474412901394851661)
          ·
            refine ⟨59376249927904838023069373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158336666474412901394851661 59376249927904838023069373)
            ·
              refine ⟨22266093722964314258651015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59376249927904838023069373 22266093722964314258651015)
              ·
                refine ⟨33399140584446471387976523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22266093722964314258651015 33399140584446471387976523)
                ·
                  refine ⟨50098710876669707081964785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33399140584446471387976523 50098710876669707081964785)
                  ·
                    refine ⟨37574033157502280311473589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50098710876669707081964785 37574033157502280311473589)
                    ·
                      refine ⟨3522565608515838779200649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37574033157502280311473589 3522565608515838779200649)
                      ·
                        rfl

theorem cell23_6860172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6860172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860172 prefixEnd_6860172 := by exact prefixLift 6860172
  have htrace : WordTrace (prefixWord ++ tailWord_6860172) baseStart_6860172 baseEnd_6860172 := by
    simpa [prefixWord, tailWord_6860172, baseEnd_6860172] using wordTrace_append hprefix tailTrace_6860172
  have hstable : (prefixWord ++ tailWord_6860172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860172).length < 2 ^ (prefixWord ++ tailWord_6860172).sum := by decide
  have hdescent : baseEnd_6860172 < baseStart_6860172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860253 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6860253 : Nat := 118140960795 + 6860253 * 2 ^ 59
def prefixEnd_6860253 : Nat := 4983230072969 + 3 ^ 40 * 6860253 * 2
def baseEnd_6860253 : Nat := 3522607200448852962287777

theorem tailTrace_6860253 : CollatzResearch.WordTrace tailWord_6860253 prefixEnd_6860253 3522607200448852962287777 := by
  unfold tailWord_6860253
  simp only [CollatzResearch.WordTrace]
  refine ⟨250213982815482493778649413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166809321876988329185766275 250213982815482493778649413)
  ·
    refine ⟨46915121777902967583496765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250213982815482493778649413 46915121777902967583496765)
    ·
      refine ⟨17593170666713612843811287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46915121777902967583496765 17593170666713612843811287)
      ·
        refine ⟨26389756000070419265716931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593170666713612843811287 26389756000070419265716931)
        ·
          refine ⟨39584634000105628898575397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26389756000070419265716931 39584634000105628898575397)
          ·
            refine ⟨7422118875019805418482887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39584634000105628898575397 7422118875019805418482887)
            ·
              refine ⟨11133178312529708127724331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422118875019805418482887 11133178312529708127724331)
              ·
                refine ⟨16699767468794562191586497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133178312529708127724331 16699767468794562191586497)
                ·
                  refine ⟨12524825601595921643689873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16699767468794562191586497 12524825601595921643689873)
                  ·
                    refine ⟨9393619201196941232767405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12524825601595921643689873 9393619201196941232767405)
                    ·
                      refine ⟨3522607200448852962287777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9393619201196941232767405 3522607200448852962287777)
                      ·
                        rfl

theorem cell23_6860253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6860253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860253 prefixEnd_6860253 := by exact prefixLift 6860253
  have htrace : WordTrace (prefixWord ++ tailWord_6860253) baseStart_6860253 baseEnd_6860253 := by
    simpa [prefixWord, tailWord_6860253, baseEnd_6860253] using wordTrace_append hprefix tailTrace_6860253
  have hstable : (prefixWord ++ tailWord_6860253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860253).length < 2 ^ (prefixWord ++ tailWord_6860253).sum := by decide
  have hdescent : baseEnd_6860253 < baseStart_6860253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860319 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_6860319 : Nat := 118140960795 + 6860319 * 2 ^ 59
def prefixEnd_6860319 : Nat := 4983230072969 + 3 ^ 40 * 6860319 * 2
def baseEnd_6860319 : Nat := 3522641090172049704062473

theorem tailTrace_6860319 : CollatzResearch.WordTrace tailWord_6860319 prefixEnd_6860319 3522641090172049704062473 := by
  unfold tailWord_6860319
  simp only [CollatzResearch.WordTrace]
  refine ⟨250216390033243387050552011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166810926688828924700368007 250216390033243387050552011)
  ·
    refine ⟨375324585049865080575828017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250216390033243387050552011 375324585049865080575828017)
    ·
      refine ⟨281493438787398810431871013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375324585049865080575828017 281493438787398810431871013)
      ·
        refine ⟨52780019772637276955975815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281493438787398810431871013 52780019772637276955975815)
        ·
          refine ⟨79170029658955915433963723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52780019772637276955975815 79170029658955915433963723)
          ·
            refine ⟨118755044488433873150945585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79170029658955915433963723 118755044488433873150945585)
            ·
              refine ⟨89066283366325404863209189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118755044488433873150945585 89066283366325404863209189)
              ·
                refine ⟨16699928131186013411851723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89066283366325404863209189 16699928131186013411851723)
                ·
                  refine ⟨25049892196779020117777585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16699928131186013411851723 25049892196779020117777585)
                  ·
                    refine ⟨18787419147584265088333189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25049892196779020117777585 18787419147584265088333189)
                    ·
                      refine ⟨3522641090172049704062473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18787419147584265088333189 3522641090172049704062473)
                      ·
                        rfl

theorem cell23_6860319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_6860319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860319 prefixEnd_6860319 := by exact prefixLift 6860319
  have htrace : WordTrace (prefixWord ++ tailWord_6860319) baseStart_6860319 baseEnd_6860319 := by
    simpa [prefixWord, tailWord_6860319, baseEnd_6860319] using wordTrace_append hprefix tailTrace_6860319
  have hstable : (prefixWord ++ tailWord_6860319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860319).length < 2 ^ (prefixWord ++ tailWord_6860319).sum := by decide
  have hdescent : baseEnd_6860319 < baseStart_6860319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860374 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6860374 : Nat := 118140960795 + 6860374 * 2 ^ 59
def prefixEnd_6860374 : Nat := 4983230072969 + 3 ^ 40 * 6860374 * 2
def baseEnd_6860374 : Nat := 3522669331608046988874721

theorem tailTrace_6860374 : CollatzResearch.WordTrace tailWord_6860374 prefixEnd_6860374 3522669331608046988874721 := by
  unfold tailWord_6860374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638649753002758215237761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166812264032029420962536117 15638649753002758215237761)
  ·
    refine ⟨11728987314752068661428321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15638649753002758215237761 11728987314752068661428321)
    ·
      refine ⟨8796740486064051496071241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11728987314752068661428321 8796740486064051496071241)
      ·
        refine ⟨6597555364548038622053431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796740486064051496071241 6597555364548038622053431)
        ·
          refine ⟨9896333046822057933080147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597555364548038622053431 9896333046822057933080147)
          ·
            refine ⟨14844499570233086899620221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896333046822057933080147 14844499570233086899620221)
            ·
              refine ⟨5566687338837407587357583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14844499570233086899620221 5566687338837407587357583)
              ·
                refine ⟨8350031008256111381036375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566687338837407587357583 8350031008256111381036375)
                ·
                  refine ⟨12525046512384167071554563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350031008256111381036375 12525046512384167071554563)
                  ·
                    refine ⟨18787569768576250607331845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12525046512384167071554563 18787569768576250607331845)
                    ·
                      refine ⟨3522669331608046988874721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18787569768576250607331845 3522669331608046988874721)
                      ·
                        rfl

theorem cell23_6860374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6860374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860374 prefixEnd_6860374 := by exact prefixLift 6860374
  have htrace : WordTrace (prefixWord ++ tailWord_6860374) baseStart_6860374 baseEnd_6860374 := by
    simpa [prefixWord, tailWord_6860374, baseEnd_6860374] using wordTrace_append hprefix tailTrace_6860374
  have hstable : (prefixWord ++ tailWord_6860374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860374).length < 2 ^ (prefixWord ++ tailWord_6860374).sum := by decide
  have hdescent : baseEnd_6860374 < baseStart_6860374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_6860396 : Nat := 118140960795 + 6860396 * 2 ^ 59
def prefixEnd_6860396 : Nat := 4983230072969 + 3 ^ 40 * 6860396 * 2
def baseEnd_6860396 : Nat := 3522680628182445902799619

theorem tailTrace_6860396 : CollatzResearch.WordTrace tailWord_6860396 prefixEnd_6860396 3522680628182445902799619 := by
  unfold tailWord_6860396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125109599226982214600552521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166812798969309619467403361 125109599226982214600552521)
  ·
    refine ⟨93832199420236660950414391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125109599226982214600552521 93832199420236660950414391)
    ·
      refine ⟨140748299130354991425621587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93832199420236660950414391 140748299130354991425621587)
      ·
        refine ⟨211122448695532487138432381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140748299130354991425621587 211122448695532487138432381)
        ·
          refine ⟨79170918260824682676912143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211122448695532487138432381 79170918260824682676912143)
          ·
            refine ⟨118756377391237024015368215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79170918260824682676912143 118756377391237024015368215)
            ·
              refine ⟨178134566086855536023052323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118756377391237024015368215 178134566086855536023052323)
              ·
                refine ⟨267201849130283304034578485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178134566086855536023052323 267201849130283304034578485)
                ·
                  refine ⟨25050173355964059753241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267201849130283304034578485 25050173355964059753241733)
                  ·
                    refine ⟨4696907504243261203732825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25050173355964059753241733 4696907504243261203732825)
                    ·
                      refine ⟨3522680628182445902799619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696907504243261203732825 3522680628182445902799619)
                      ·
                        rfl

theorem cell23_6860396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_6860396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860396 prefixEnd_6860396 := by exact prefixLift 6860396
  have htrace : WordTrace (prefixWord ++ tailWord_6860396) baseStart_6860396 baseEnd_6860396 := by
    simpa [prefixWord, tailWord_6860396, baseEnd_6860396] using wordTrace_append hprefix tailTrace_6860396
  have hstable : (prefixWord ++ tailWord_6860396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860396).length < 2 ^ (prefixWord ++ tailWord_6860396).sum := by decide
  have hdescent : baseEnd_6860396 < baseStart_6860396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860406 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_6860406 : Nat := 118140960795 + 6860406 * 2 ^ 59
def prefixEnd_6860406 : Nat := 4983230072969 + 3 ^ 40 * 6860406 * 2
def baseEnd_6860406 : Nat := 1174228587662996954558191

theorem tailTrace_6860406 : CollatzResearch.WordTrace tailWord_6860406 prefixEnd_6860406 1174228587662996954558191 := by
  unfold tailWord_6860406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638722698995512556810567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166813042122618800605979381 15638722698995512556810567)
  ·
    refine ⟨23458084048493268835215851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15638722698995512556810567 23458084048493268835215851)
    ·
      refine ⟨35187126072739903252823777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23458084048493268835215851 35187126072739903252823777)
      ·
        refine ⟨26390344554554927439617833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35187126072739903252823777 26390344554554927439617833)
        ·
          refine ⟨19792758415916195579713375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26390344554554927439617833 19792758415916195579713375)
          ·
            refine ⟨29689137623874293369570063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19792758415916195579713375 29689137623874293369570063)
            ·
              refine ⟨44533706435811440054355095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29689137623874293369570063 44533706435811440054355095)
              ·
                refine ⟨66800559653717160081532643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44533706435811440054355095 66800559653717160081532643)
                ·
                  refine ⟨100200839480575740122298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66800559653717160081532643 100200839480575740122298965)
                  ·
                    refine ⟨1174228587662996954558191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100200839480575740122298965 1174228587662996954558191)
                    ·
                      rfl

theorem cell23_6860406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_6860406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860406 prefixEnd_6860406 := by exact prefixLift 6860406
  have htrace : WordTrace (prefixWord ++ tailWord_6860406) baseStart_6860406 baseEnd_6860406 := by
    simpa [prefixWord, tailWord_6860406, baseEnd_6860406] using wordTrace_append hprefix tailTrace_6860406
  have hstable : (prefixWord ++ tailWord_6860406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860406).length < 2 ^ (prefixWord ++ tailWord_6860406).sum := by decide
  have hdescent : baseEnd_6860406 < baseStart_6860406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860413 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_6860413 : Nat := 118140960795 + 6860413 * 2 ^ 59
def prefixEnd_6860413 : Nat := 4983230072969 + 3 ^ 40 * 6860413 * 2
def baseEnd_6860413 : Nat := 3522689357353572336287041

theorem tailTrace_6860413 : CollatzResearch.WordTrace tailWord_6860413 prefixEnd_6860413 3522689357353572336287041 := by
  unfold tailWord_6860413
  simp only [CollatzResearch.WordTrace]
  refine ⟨250219818494902841104473893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166813212329935227402982595 250219818494902841104473893)
  ·
    refine ⟨46916215967794282707088855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250219818494902841104473893 46916215967794282707088855)
    ·
      refine ⟨70374323951691424060633283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46916215967794282707088855 70374323951691424060633283)
      ·
        refine ⟨105561485927537136090949925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70374323951691424060633283 105561485927537136090949925)
        ·
          refine ⟨19792778611413213017053111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105561485927537136090949925 19792778611413213017053111)
          ·
            refine ⟨29689167917119819525579667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19792778611413213017053111 29689167917119819525579667)
            ·
              refine ⟨44533751875679729288369501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29689167917119819525579667 44533751875679729288369501)
              ·
                refine ⟨16700156953379898483138563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44533751875679729288369501 16700156953379898483138563)
                ·
                  refine ⟨25050235430069847724707845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16700156953379898483138563 25050235430069847724707845)
                  ·
                    refine ⟨4696919143138096448382721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25050235430069847724707845 4696919143138096448382721)
                    ·
                      refine ⟨3522689357353572336287041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696919143138096448382721 3522689357353572336287041)
                      ·
                        rfl

theorem cell23_6860413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_6860413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860413 prefixEnd_6860413 := by exact prefixLift 6860413
  have htrace : WordTrace (prefixWord ++ tailWord_6860413) baseStart_6860413 baseEnd_6860413 := by
    simpa [prefixWord, tailWord_6860413, baseEnd_6860413] using wordTrace_append hprefix tailTrace_6860413
  have hstable : (prefixWord ++ tailWord_6860413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860413).length < 2 ^ (prefixWord ++ tailWord_6860413).sum := by decide
  have hdescent : baseEnd_6860413 < baseStart_6860413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860434 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6860434 : Nat := 118140960795 + 6860434 * 2 ^ 59
def prefixEnd_6860434 : Nat := 4983230072969 + 3 ^ 40 * 6860434 * 2
def baseEnd_6860434 : Nat := 3522700140447316754124445

theorem tailTrace_6860434 : CollatzResearch.WordTrace tailWord_6860434 prefixEnd_6860434 3522700140447316754124445 := by
  unfold tailWord_6860434
  simp only [CollatzResearch.WordTrace]
  refine ⟨62555146106956690422747089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166813722951884507793992237 62555146106956690422747089)
  ·
    refine ⟨46916359580217517817060317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62555146106956690422747089 46916359580217517817060317)
    ·
      refine ⟨17593634842581569181397619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46916359580217517817060317 17593634842581569181397619)
      ·
        refine ⟨26390452263872353772096429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593634842581569181397619 26390452263872353772096429)
        ·
          refine ⟨9896419598952132664536161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26390452263872353772096429 9896419598952132664536161)
          ·
            refine ⟨7422314699214099498402121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9896419598952132664536161 7422314699214099498402121)
            ·
              refine ⟨5566736024410574623801591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422314699214099498402121 5566736024410574623801591)
              ·
                refine ⟨8350104036615861935702387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566736024410574623801591 8350104036615861935702387)
                ·
                  refine ⟨12525156054923792903553581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350104036615861935702387 12525156054923792903553581)
                  ·
                    refine ⟨4696933520596422338832593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12525156054923792903553581 4696933520596422338832593)
                    ·
                      refine ⟨3522700140447316754124445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696933520596422338832593 3522700140447316754124445)
                      ·
                        rfl

theorem cell23_6860434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6860434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860434 prefixEnd_6860434 := by exact prefixLift 6860434
  have htrace : WordTrace (prefixWord ++ tailWord_6860434) baseStart_6860434 baseEnd_6860434 := by
    simpa [prefixWord, tailWord_6860434, baseEnd_6860434] using wordTrace_append hprefix tailTrace_6860434
  have hstable : (prefixWord ++ tailWord_6860434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860434).length < 2 ^ (prefixWord ++ tailWord_6860434).sum := by decide
  have hdescent : baseEnd_6860434 < baseStart_6860434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860447 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6860447 : Nat := 118140960795 + 6860447 * 2 ^ 59
def prefixEnd_6860447 : Nat := 4983230072969 + 3 ^ 40 * 6860447 * 2
def baseEnd_6860447 : Nat := 3522706815695825203261885

theorem tailTrace_6860447 : CollatzResearch.WordTrace tailWord_6860447 prefixEnd_6860447 3522706815695825203261885 := by
  unfold tailWord_6860447
  simp only [CollatzResearch.WordTrace]
  refine ⟨250221058576779664911211595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166814039051186443274141063 250221058576779664911211595)
  ·
    refine ⟨375331587865169497366817393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250221058576779664911211595 375331587865169497366817393)
    ·
      refine ⟨281498690898877123025113045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375331587865169497366817393 281498690898877123025113045)
      ·
        refine ⟨6597625567942432570901087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 281498690898877123025113045 6597625567942432570901087)
        ·
          refine ⟨9896438351913648856351631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597625567942432570901087 9896438351913648856351631)
          ·
            refine ⟨14844657527870473284527447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896438351913648856351631 14844657527870473284527447)
            ·
              refine ⟨22266986291805709926791171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14844657527870473284527447 22266986291805709926791171)
              ·
                refine ⟨33400479437708564890186757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22266986291805709926791171 33400479437708564890186757)
                ·
                  refine ⟨6262589894570355916910017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33400479437708564890186757 6262589894570355916910017)
                  ·
                    refine ⟨4696942420927766937682513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6262589894570355916910017 4696942420927766937682513)
                    ·
                      refine ⟨3522706815695825203261885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4696942420927766937682513 3522706815695825203261885)
                      ·
                        rfl

theorem cell23_6860447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6860447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860447 prefixEnd_6860447 := by exact prefixLift 6860447
  have htrace : WordTrace (prefixWord ++ tailWord_6860447) baseStart_6860447 baseEnd_6860447 := by
    simpa [prefixWord, tailWord_6860447, baseEnd_6860447] using wordTrace_append hprefix tailTrace_6860447
  have hstable : (prefixWord ++ tailWord_6860447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860447).length < 2 ^ (prefixWord ++ tailWord_6860447).sum := by decide
  have hdescent : baseEnd_6860447 < baseStart_6860447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860479 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 8]
def baseStart_6860479 : Nat := 118140960795 + 6860479 * 2 ^ 59
def prefixEnd_6860479 : Nat := 4983230072969 + 3 ^ 40 * 6860479 * 2
def baseEnd_6860479 : Nat := 1174241082358923026020579

theorem tailTrace_6860479 : CollatzResearch.WordTrace tailWord_6860479 prefixEnd_6860479 1174241082358923026020579 := by
  unfold tailWord_6860479
  simp only [CollatzResearch.WordTrace]
  refine ⟨250222225712663734376376491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166814817141775822917584327 250222225712663734376376491)
  ·
    refine ⟨375333338568995601564564737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250222225712663734376376491 375333338568995601564564737)
    ·
      refine ⟨281500003926746701173423553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375333338568995601564564737 281500003926746701173423553)
      ·
        refine ⟨211125002945060025880067665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281500003926746701173423553 211125002945060025880067665)
        ·
          refine ⟨158343752208795019410050749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211125002945060025880067665 158343752208795019410050749)
          ·
            refine ⟨59378907078298132278769031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158343752208795019410050749 59378907078298132278769031)
            ·
              refine ⟨89068360617447198418153547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59378907078298132278769031 89068360617447198418153547)
              ·
                refine ⟨133602540926170797627230321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89068360617447198418153547 133602540926170797627230321)
                ·
                  refine ⟨100201905694628098220422741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133602540926170797627230321 100201905694628098220422741)
                  ·
                    refine ⟨1174241082358923026020579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100201905694628098220422741 1174241082358923026020579)
                    ·
                      rfl

theorem cell23_6860479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_6860479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860479 prefixEnd_6860479 := by exact prefixLift 6860479
  have htrace : WordTrace (prefixWord ++ tailWord_6860479) baseStart_6860479 baseEnd_6860479 := by
    simpa [prefixWord, tailWord_6860479, baseEnd_6860479] using wordTrace_append hprefix tailTrace_6860479
  have hstable : (prefixWord ++ tailWord_6860479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860479).length < 2 ^ (prefixWord ++ tailWord_6860479).sum := by decide
  have hdescent : baseEnd_6860479 < baseStart_6860479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860499 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_6860499 : Nat := 118140960795 + 6860499 * 2 ^ 59
def prefixEnd_6860499 : Nat := 4983230072969 + 3 ^ 40 * 6860499 * 2
def baseEnd_6860499 : Nat := 3522733516689858999811645

theorem tailTrace_6860499 : CollatzResearch.WordTrace tailWord_6860499 prefixEnd_6860499 3522733516689858999811645 := by
  unfold tailWord_6860499
  simp only [CollatzResearch.WordTrace]
  refine ⟨250222955172591277792104551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166815303448394185194736367 250222955172591277792104551)
  ·
    refine ⟨375334432758886916688156827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250222955172591277792104551 375334432758886916688156827)
    ·
      refine ⟨563001649138330375032235241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375334432758886916688156827 563001649138330375032235241)
      ·
        refine ⟨422251236853747781274176431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563001649138330375032235241 422251236853747781274176431)
        ·
          refine ⟨633376855280621671911264647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422251236853747781274176431 633376855280621671911264647)
          ·
            refine ⟨950065282920932507866896971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633376855280621671911264647 950065282920932507866896971)
            ·
              refine ⟨1425097924381398761800345457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950065282920932507866896971 1425097924381398761800345457)
              ·
                refine ⟨1068823443286049071350259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425097924381398761800345457 1068823443286049071350259093)
                ·
                  refine ⟨50101098904033550219543395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1068823443286049071350259093 50101098904033550219543395)
                  ·
                    refine ⟨75151648356050325329315093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50101098904033550219543395 75151648356050325329315093)
                    ·
                      refine ⟨3522733516689858999811645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75151648356050325329315093 3522733516689858999811645)
                      ·
                        rfl

theorem cell23_6860499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_6860499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860499 prefixEnd_6860499 := by exact prefixLift 6860499
  have htrace : WordTrace (prefixWord ++ tailWord_6860499) baseStart_6860499 baseEnd_6860499 := by
    simpa [prefixWord, tailWord_6860499, baseEnd_6860499] using wordTrace_append hprefix tailTrace_6860499
  have hstable : (prefixWord ++ tailWord_6860499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860499).length < 2 ^ (prefixWord ++ tailWord_6860499).sum := by decide
  have hdescent : baseEnd_6860499 < baseStart_6860499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860563 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 4, 3, 2]
def baseStart_6860563 : Nat := 118140960795 + 6860563 * 2 ^ 59
def prefixEnd_6860563 : Nat := 4983230072969 + 3 ^ 40 * 6860563 * 2
def baseEnd_6860563 : Nat := 3522766379451746749411351

theorem tailTrace_6860563 : CollatzResearch.WordTrace tailWord_6860563 prefixEnd_6860563 3522766379451746749411351 := by
  unfold tailWord_6860563
  simp only [CollatzResearch.WordTrace]
  refine ⟨250225289444359416722434343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166816859629572944481622895 250225289444359416722434343)
  ·
    refine ⟨375337934166539125083651515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250225289444359416722434343 375337934166539125083651515)
    ·
      refine ⟨563006901249808687625477273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375337934166539125083651515 563006901249808687625477273)
      ·
        refine ⟨422255175937356515719107955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563006901249808687625477273 422255175937356515719107955)
        ·
          refine ⟨633382763906034773578661933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422255175937356515719107955 633382763906034773578661933)
          ·
            refine ⟨237518536464763040091998225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633382763906034773578661933 237518536464763040091998225)
            ·
              refine ⟨178138902348572280068998669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237518536464763040091998225 178138902348572280068998669)
              ·
                refine ⟨66802088380714605025874501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178138902348572280068998669 66802088380714605025874501)
                ·
                  refine ⟨12525391571383988442351469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66802088380714605025874501 12525391571383988442351469)
                  ·
                    refine ⟨4697021839268995665881801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12525391571383988442351469 4697021839268995665881801)
                    ·
                      refine ⟨3522766379451746749411351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697021839268995665881801 3522766379451746749411351)
                      ·
                        rfl

theorem cell23_6860563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3, 2].length) (baseStart_6860563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860563 prefixEnd_6860563 := by exact prefixLift 6860563
  have htrace : WordTrace (prefixWord ++ tailWord_6860563) baseStart_6860563 baseEnd_6860563 := by
    simpa [prefixWord, tailWord_6860563, baseEnd_6860563] using wordTrace_append hprefix tailTrace_6860563
  have hstable : (prefixWord ++ tailWord_6860563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860563).length < 2 ^ (prefixWord ++ tailWord_6860563).sum := by decide
  have hdescent : baseEnd_6860563 < baseStart_6860563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860593 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_6860593 : Nat := 118140960795 + 6860593 * 2 ^ 59
def prefixEnd_6860593 : Nat := 4983230072969 + 3 ^ 40 * 6860593 * 2
def baseEnd_6860593 : Nat := 3522781783871381632036213

theorem tailTrace_6860593 : CollatzResearch.WordTrace tailWord_6860593 prefixEnd_6860593 3522781783871381632036213 := by
  unfold tailWord_6860593
  simp only [CollatzResearch.WordTrace]
  refine ⟨250226383634250731846026433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166817589089500487897350955 250226383634250731846026433)
  ·
    refine ⟨187669787725688048884519825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250226383634250731846026433 187669787725688048884519825)
    ·
      refine ⟨140752340794266036663389869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187669787725688048884519825 140752340794266036663389869)
      ·
        refine ⟨52782127797849763748771201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140752340794266036663389869 52782127797849763748771201)
        ·
          refine ⟨39586595848387322811578401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52782127797849763748771201 39586595848387322811578401)
          ·
            refine ⟨29689946886290492108683801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39586595848387322811578401 29689946886290492108683801)
            ·
              refine ⟨22267460164717869081512851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29689946886290492108683801 22267460164717869081512851)
              ·
                refine ⟨33401190247076803622269277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22267460164717869081512851 33401190247076803622269277)
                ·
                  refine ⟨12525446342653801358350979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33401190247076803622269277 12525446342653801358350979)
                  ·
                    refine ⟨18788169513980702037526469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12525446342653801358350979 18788169513980702037526469)
                    ·
                      refine ⟨3522781783871381632036213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18788169513980702037526469 3522781783871381632036213)
                      ·
                        rfl

theorem cell23_6860593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_6860593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860593 prefixEnd_6860593 := by exact prefixLift 6860593
  have htrace : WordTrace (prefixWord ++ tailWord_6860593) baseStart_6860593 baseEnd_6860593 := by
    simpa [prefixWord, tailWord_6860593, baseEnd_6860593] using wordTrace_append hprefix tailTrace_6860593
  have hstable : (prefixWord ++ tailWord_6860593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860593).length < 2 ^ (prefixWord ++ tailWord_6860593).sum := by decide
  have hdescent : baseEnd_6860593 < baseStart_6860593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860607 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 1, 5]
def baseStart_6860607 : Nat := 118140960795 + 6860607 * 2 ^ 59
def prefixEnd_6860607 : Nat := 4983230072969 + 3 ^ 40 * 6860607 * 2
def baseEnd_6860607 : Nat := 1174262990866848192420383

theorem tailTrace_6860607 : CollatzResearch.WordTrace tailWord_6860607 prefixEnd_6860607 1174262990866848192420383 := by
  unfold tailWord_6860607
  simp only [CollatzResearch.WordTrace]
  refine ⟨250226894256200012237036075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166817929504133341491357383 250226894256200012237036075)
  ·
    refine ⟨375340341384300018355554113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250226894256200012237036075 375340341384300018355554113)
    ·
      refine ⟨281505256038225013766665585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375340341384300018355554113 281505256038225013766665585)
      ·
        refine ⟨211128942028668760324999189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281505256038225013766665585 211128942028668760324999189)
        ·
          refine ⟨9896669157593848140234337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211128942028668760324999189 9896669157593848140234337)
          ·
            refine ⟨7422501868195386105175753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9896669157593848140234337 7422501868195386105175753)
            ·
              refine ⟨5566876401146539578881815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422501868195386105175753 5566876401146539578881815)
              ·
                refine ⟨8350314601719809368322723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566876401146539578881815 8350314601719809368322723)
                ·
                  refine ⟨12525471902579714052484085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350314601719809368322723 12525471902579714052484085)
                  ·
                    refine ⟨1174262990866848192420383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12525471902579714052484085 1174262990866848192420383)
                    ·
                      rfl

theorem cell23_6860607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_6860607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860607 prefixEnd_6860607 := by exact prefixLift 6860607
  have htrace : WordTrace (prefixWord ++ tailWord_6860607) baseStart_6860607 baseEnd_6860607 := by
    simpa [prefixWord, tailWord_6860607, baseEnd_6860607] using wordTrace_append hprefix tailTrace_6860607
  have hstable : (prefixWord ++ tailWord_6860607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860607).length < 2 ^ (prefixWord ++ tailWord_6860607).sum := by decide
  have hdescent : baseEnd_6860607 < baseStart_6860607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860616 : List Nat := [2, 1, 3, 1, 1, 5, 10]
def baseStart_6860616 : Nat := 118140960795 + 6860616 * 2 ^ 59
def prefixEnd_6860616 : Nat := 4983230072969 + 3 ^ 40 * 6860616 * 2
def baseEnd_6860616 : Nat := 43491278937363395580847

theorem tailTrace_6860616 : CollatzResearch.WordTrace tailWord_6860616 prefixEnd_6860616 43491278937363395580847 := by
  unfold tailWord_6860616
  simp only [CollatzResearch.WordTrace]
  refine ⟨125113611256583703387056851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166818148342111604516075801 125113611256583703387056851)
  ·
    refine ⟨187670416884875555080585277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125113611256583703387056851 187670416884875555080585277)
    ·
      refine ⟨70376406331828333155219479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187670416884875555080585277 70376406331828333155219479)
      ·
        refine ⟨105564609497742499732829219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70376406331828333155219479 105564609497742499732829219)
        ·
          refine ⟨158346914246613749599243829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105564609497742499732829219 158346914246613749599243829)
          ·
            refine ⟨14845023210620039024929109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158346914246613749599243829 14845023210620039024929109)
            ·
              refine ⟨43491278937363395580847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14845023210620039024929109 43491278937363395580847)
              ·
                rfl

theorem cell23_6860616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 10].length) (baseStart_6860616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860616 prefixEnd_6860616 := by exact prefixLift 6860616
  have htrace : WordTrace (prefixWord ++ tailWord_6860616) baseStart_6860616 baseEnd_6860616 := by
    simpa [prefixWord, tailWord_6860616, baseEnd_6860616] using wordTrace_append hprefix tailTrace_6860616
  have hstable : (prefixWord ++ tailWord_6860616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860616).length < 2 ^ (prefixWord ++ tailWord_6860616).sum := by decide
  have hdescent : baseEnd_6860616 < baseStart_6860616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860620 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_6860620 : Nat := 118140960795 + 6860620 * 2 ^ 59
def prefixEnd_6860620 : Nat := 4983230072969 + 3 ^ 40 * 6860620 * 2
def baseEnd_6860620 : Nat := 1174265215949684342132863

theorem tailTrace_6860620 : CollatzResearch.WordTrace tailWord_6860620 prefixEnd_6860620 1174265215949684342132863 := by
  unfold tailWord_6860620
  simp only [CollatzResearch.WordTrace]
  refine ⟨125113684202576457728629657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166818245603435276971506209 125113684202576457728629657)
  ·
    refine ⟨93835263151932343296472243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125113684202576457728629657 93835263151932343296472243)
    ·
      refine ⟨140752894727898514944708365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93835263151932343296472243 140752894727898514944708365)
      ·
        refine ⟨52782335522961943104265637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140752894727898514944708365 52782335522961943104265637)
        ·
          refine ⟨9896687910555364332049807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52782335522961943104265637 9896687910555364332049807)
          ·
            refine ⟨14845031865833046498074711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896687910555364332049807 14845031865833046498074711)
            ·
              refine ⟨22267547798749569747112067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14845031865833046498074711 22267547798749569747112067)
              ·
                refine ⟨33401321698124354620668101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22267547798749569747112067 33401321698124354620668101)
                ·
                  refine ⟨6262747818398316491375269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33401321698124354620668101 6262747818398316491375269)
                  ·
                    refine ⟨1174265215949684342132863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6262747818398316491375269 1174265215949684342132863)
                    ·
                      rfl

theorem cell23_6860620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_6860620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860620 prefixEnd_6860620 := by exact prefixLift 6860620
  have htrace : WordTrace (prefixWord ++ tailWord_6860620) baseStart_6860620 baseEnd_6860620 := by
    simpa [prefixWord, tailWord_6860620, baseEnd_6860620] using wordTrace_append hprefix tailTrace_6860620
  have hstable : (prefixWord ++ tailWord_6860620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860620).length < 2 ^ (prefixWord ++ tailWord_6860620).sum := by decide
  have hdescent : baseEnd_6860620 < baseStart_6860620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860640 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_6860640 : Nat := 118140960795 + 6860640 * 2 ^ 59
def prefixEnd_6860640 : Nat := 4983230072969 + 3 ^ 40 * 6860640 * 2
def baseEnd_6860640 : Nat := 3522805917462142948148497

theorem tailTrace_6860640 : CollatzResearch.WordTrace tailWord_6860640 prefixEnd_6860640 3522805917462142948148497 := by
  unfold tailWord_6860640
  simp only [CollatzResearch.WordTrace]
  refine ⟨125114048932540229436493687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166818731910053639248658249 125114048932540229436493687)
  ·
    refine ⟨187671073398810344154740531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125114048932540229436493687 187671073398810344154740531)
    ·
      refine ⟨281506610098215516232110797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187671073398810344154740531 281506610098215516232110797)
      ·
        refine ⟨105564978786830818587041549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281506610098215516232110797 105564978786830818587041549)
        ·
          refine ⟨39586867045061556970140581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105564978786830818587041549 39586867045061556970140581)
          ·
            refine ⟨7422537570949041931901359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39586867045061556970140581 7422537570949041931901359)
            ·
              refine ⟨11133806356423562897852039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422537570949041931901359 11133806356423562897852039)
              ·
                refine ⟨16700709534635344346778059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133806356423562897852039 16700709534635344346778059)
                ·
                  refine ⟨25051064301953016520167089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16700709534635344346778059 25051064301953016520167089)
                  ·
                    refine ⟨18788298226464762390125317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25051064301953016520167089 18788298226464762390125317)
                    ·
                      refine ⟨3522805917462142948148497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18788298226464762390125317 3522805917462142948148497)
                      ·
                        rfl

theorem cell23_6860640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_6860640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860640 prefixEnd_6860640 := by exact prefixLift 6860640
  have htrace : WordTrace (prefixWord ++ tailWord_6860640) baseStart_6860640 baseEnd_6860640 := by
    simpa [prefixWord, tailWord_6860640, baseEnd_6860640] using wordTrace_append hprefix tailTrace_6860640
  have hstable : (prefixWord ++ tailWord_6860640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860640).length < 2 ^ (prefixWord ++ tailWord_6860640).sum := by decide
  have hdescent : baseEnd_6860640 < baseStart_6860640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860650 : List Nat := [3, 1, 3, 4, 1, 1, 1, 9]
def baseStart_6860650 : Nat := 118140960795 + 6860650 * 2 ^ 59
def prefixEnd_6860650 : Nat := 4983230072969 + 3 ^ 40 * 6860650 * 2
def baseEnd_6860650 : Nat := 130474483417358811445313

theorem tailTrace_6860650 : CollatzResearch.WordTrace tailWord_6860650 prefixEnd_6860650 130474483417358811445313 := by
  unfold tailWord_6860650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62557115648761057645212851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166818975063362820387234269 62557115648761057645212851)
  ·
    refine ⟨93835673473141586467819277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62557115648761057645212851 93835673473141586467819277)
    ·
      refine ⟨35188377552428094925432229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93835673473141586467819277 35188377552428094925432229)
      ·
        refine ⟨6597820791080267798518543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35188377552428094925432229 6597820791080267798518543)
        ·
          refine ⟨9896731186620401697777815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597820791080267798518543 9896731186620401697777815)
          ·
            refine ⟨14845096779930602546666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896731186620401697777815 14845096779930602546666723)
            ·
              refine ⟨22267645169895903820000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14845096779930602546666723 22267645169895903820000085)
              ·
                refine ⟨130474483417358811445313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22267645169895903820000085 130474483417358811445313)
                ·
                  rfl

theorem cell23_6860650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_6860650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860650 prefixEnd_6860650 := by exact prefixLift 6860650
  have htrace : WordTrace (prefixWord ++ tailWord_6860650) baseStart_6860650 baseEnd_6860650 := by
    simpa [prefixWord, tailWord_6860650, baseEnd_6860650] using wordTrace_append hprefix tailTrace_6860650
  have hstable : (prefixWord ++ tailWord_6860650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860650).length < 2 ^ (prefixWord ++ tailWord_6860650).sum := by decide
  have hdescent : baseEnd_6860650 < baseStart_6860650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860734 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_6860734 : Nat := 118140960795 + 6860734 * 2 ^ 59
def prefixEnd_6860734 : Nat := 4983230072969 + 3 ^ 40 * 6860734 * 2
def baseEnd_6860734 : Nat := 3522854184643665580373065

theorem tailTrace_6860734 : CollatzResearch.WordTrace tailWord_6860734 prefixEnd_6860734 3522854184643665580373065 := by
  unfold tailWord_6860734
  simp only [CollatzResearch.WordTrace]
  refine ⟨31278940790842489115863657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166821017551159941951272837 31278940790842489115863657)
  ·
    refine ⟨23459205593131866836897743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31278940790842489115863657 23459205593131866836897743)
    ·
      refine ⟨35188808389697800255346615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23459205593131866836897743 35188808389697800255346615)
      ·
        refine ⟨52783212584546700383019923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35188808389697800255346615 52783212584546700383019923)
        ·
          refine ⟨79174818876820050574529885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52783212584546700383019923 79174818876820050574529885)
          ·
            refine ⟨29690557078807518965448707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79174818876820050574529885 29690557078807518965448707)
            ·
              refine ⟨44535835618211278448173061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29690557078807518965448707 44535835618211278448173061)
              ·
                refine ⟨8350469178414614709032449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44535835618211278448173061 8350469178414614709032449)
                ·
                  refine ⟨6262851883810961031774337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8350469178414614709032449 6262851883810961031774337)
                  ·
                    refine ⟨4697138912858220773830753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6262851883810961031774337 4697138912858220773830753)
                    ·
                      refine ⟨3522854184643665580373065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697138912858220773830753 3522854184643665580373065)
                      ·
                        rfl

theorem cell23_6860734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_6860734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860734 prefixEnd_6860734 := by exact prefixLift 6860734
  have htrace : WordTrace (prefixWord ++ tailWord_6860734) baseStart_6860734 baseEnd_6860734 := by
    simpa [prefixWord, tailWord_6860734, baseEnd_6860734] using wordTrace_append hprefix tailTrace_6860734
  have hstable : (prefixWord ++ tailWord_6860734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860734).length < 2 ^ (prefixWord ++ tailWord_6860734).sum := by decide
  have hdescent : baseEnd_6860734 < baseStart_6860734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860750 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_6860750 : Nat := 118140960795 + 6860750 * 2 ^ 59
def prefixEnd_6860750 : Nat := 4983230072969 + 3 ^ 40 * 6860750 * 2
def baseEnd_6860750 : Nat := 3522862400334137517772991

theorem tailTrace_6860750 : CollatzResearch.WordTrace tailWord_6860750 prefixEnd_6860750 3522862400334137517772991 := by
  unfold tailWord_6860750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279013736835243457436463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166821406596454631772994469 31279013736835243457436463)
  ·
    refine ⟨46918520605252865186154695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31279013736835243457436463 46918520605252865186154695)
    ·
      refine ⟨70377780907879297779232043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46918520605252865186154695 70377780907879297779232043)
      ·
        refine ⟨105566671361818946668848065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70377780907879297779232043 105566671361818946668848065)
        ·
          refine ⟨79175003521364210001636049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105566671361818946668848065 79175003521364210001636049)
          ·
            refine ⟨59381252641023157501227037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79175003521364210001636049 59381252641023157501227037)
            ·
              refine ⟨22267969740383684062960139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59381252641023157501227037 22267969740383684062960139)
              ·
                refine ⟨33401954610575526094440209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22267969740383684062960139 33401954610575526094440209)
                ·
                  refine ⟨25051465957931644570830157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33401954610575526094440209 25051465957931644570830157)
                  ·
                    refine ⟨9394299734224366714061309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25051465957931644570830157 9394299734224366714061309)
                    ·
                      refine ⟨3522862400334137517772991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9394299734224366714061309 3522862400334137517772991)
                      ·
                        rfl

theorem cell23_6860750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_6860750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860750 prefixEnd_6860750 := by exact prefixLift 6860750
  have htrace : WordTrace (prefixWord ++ tailWord_6860750) baseStart_6860750 baseEnd_6860750 := by
    simpa [prefixWord, tailWord_6860750, baseEnd_6860750] using wordTrace_append hprefix tailTrace_6860750
  have hstable : (prefixWord ++ tailWord_6860750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860750).length < 2 ^ (prefixWord ++ tailWord_6860750).sum := by decide
  have hdescent : baseEnd_6860750 < baseStart_6860750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860760 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_6860760 : Nat := 118140960795 + 6860760 * 2 ^ 59
def prefixEnd_6860760 : Nat := 4983230072969 + 3 ^ 40 * 6860760 * 2
def baseEnd_6860760 : Nat := 3522867535140682478647945

theorem tailTrace_6860760 : CollatzResearch.WordTrace tailWord_6860760 prefixEnd_6860760 3522867535140682478647945 := by
  unfold tailWord_6860760
  simp only [CollatzResearch.WordTrace]
  refine ⟨125116237312322859683677867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166821649749763812911570489 125116237312322859683677867)
  ·
    refine ⟨187674355968484289525516801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125116237312322859683677867 187674355968484289525516801)
    ·
      refine ⟨140755766976363217144137601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187674355968484289525516801 140755766976363217144137601)
      ·
        refine ⟨105566825232272412858103201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140755766976363217144137601 105566825232272412858103201)
        ·
          refine ⟨79175118924204309643577401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105566825232272412858103201 79175118924204309643577401)
          ·
            refine ⟨59381339193153232232683051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79175118924204309643577401 59381339193153232232683051)
            ·
              refine ⟨89072008789729848349024577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59381339193153232232683051 89072008789729848349024577)
              ·
                refine ⟨66804006592297386261768433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89072008789729848349024577 66804006592297386261768433)
                ·
                  refine ⟨50103004944223039696326325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66804006592297386261768433 50103004944223039696326325)
                  ·
                    refine ⟨4697156713520909971530593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50103004944223039696326325 4697156713520909971530593)
                    ·
                      refine ⟨3522867535140682478647945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697156713520909971530593 3522867535140682478647945)
                      ·
                        rfl

theorem cell23_6860760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_6860760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860760 prefixEnd_6860760 := by exact prefixLift 6860760
  have htrace : WordTrace (prefixWord ++ tailWord_6860760) baseStart_6860760 baseEnd_6860760 := by
    simpa [prefixWord, tailWord_6860760, baseEnd_6860760] using wordTrace_append hprefix tailTrace_6860760
  have hstable : (prefixWord ++ tailWord_6860760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860760).length < 2 ^ (prefixWord ++ tailWord_6860760).sum := by decide
  have hdescent : baseEnd_6860760 < baseStart_6860760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860807 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6860807 : Nat := 118140960795 + 6860807 * 2 ^ 59
def prefixEnd_6860807 : Nat := 4983230072969 + 3 ^ 40 * 6860807 * 2
def baseEnd_6860807 : Nat := 3522891668731443794760229

theorem tailTrace_6860807 : CollatzResearch.WordTrace tailWord_6860807 prefixEnd_6860807 3522891668731443794760229 := by
  unfold tailWord_6860807
  simp only [CollatzResearch.WordTrace]
  refine ⟨250234188855475446394316675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166822792570316964262877783 250234188855475446394316675)
  ·
    refine ⟨375351283283213169591475013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250234188855475446394316675 375351283283213169591475013)
    ·
      refine ⟨70378365615602469298401565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375351283283213169591475013 70378365615602469298401565)
      ·
        refine ⟨26391887105850925986900587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70378365615602469298401565 26391887105850925986900587)
        ·
          refine ⟨39587830658776388980350881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26391887105850925986900587 39587830658776388980350881)
          ·
            refine ⟨29690872994082291735263161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39587830658776388980350881 29690872994082291735263161)
            ·
              refine ⟨22268154745561718801447371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29690872994082291735263161 22268154745561718801447371)
              ·
                refine ⟨33402232118342578202171057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22268154745561718801447371 33402232118342578202171057)
                ·
                  refine ⟨25051674088756933651628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33402232118342578202171057 25051674088756933651628293)
                  ·
                    refine ⟨4697188891641925059680305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25051674088756933651628293 4697188891641925059680305)
                    ·
                      refine ⟨3522891668731443794760229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697188891641925059680305 3522891668731443794760229)
                      ·
                        rfl

theorem cell23_6860807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6860807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860807 prefixEnd_6860807 := by exact prefixLift 6860807
  have htrace : WordTrace (prefixWord ++ tailWord_6860807) baseStart_6860807 baseEnd_6860807 := by
    simpa [prefixWord, tailWord_6860807, baseEnd_6860807] using wordTrace_append hprefix tailTrace_6860807
  have hstable : (prefixWord ++ tailWord_6860807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860807).length < 2 ^ (prefixWord ++ tailWord_6860807).sum := by decide
  have hdescent : baseEnd_6860807 < baseStart_6860807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860860 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_6860860 : Nat := 118140960795 + 6860860 * 2 ^ 59
def prefixEnd_6860860 : Nat := 4983230072969 + 3 ^ 40 * 6860860 * 2
def baseEnd_6860860 : Nat := 1174306294402044029132495

theorem tailTrace_6860860 : CollatzResearch.WordTrace tailWord_6860860 prefixEnd_6860860 1174306294402044029132495 := by
  unfold tailWord_6860860
  simp only [CollatzResearch.WordTrace]
  refine ⟨125118060962141718222998017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166824081282855624297330689 125118060962141718222998017)
  ·
    refine ⟨93838545721606288667248513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125118060962141718222998017 93838545721606288667248513)
    ·
      refine ⟨70378909291204716500436385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93838545721606288667248513 70378909291204716500436385)
      ·
        refine ⟨52784181968403537375327289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70378909291204716500436385 52784181968403537375327289)
        ·
          refine ⟨39588136476302653031495467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52784181968403537375327289 39588136476302653031495467)
          ·
            refine ⟨59382204714453979547243201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39588136476302653031495467 59382204714453979547243201)
            ·
              refine ⟨44536653535840484660432401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59382204714453979547243201 44536653535840484660432401)
              ·
                refine ⟨33402490151880363495324301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44536653535840484660432401 33402490151880363495324301)
                ·
                  refine ⟨12525933806955136310746613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33402490151880363495324301 12525933806955136310746613)
                  ·
                    refine ⟨1174306294402044029132495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12525933806955136310746613 1174306294402044029132495)
                    ·
                      rfl

theorem cell23_6860860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_6860860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860860 prefixEnd_6860860 := by exact prefixLift 6860860
  have htrace : WordTrace (prefixWord ++ tailWord_6860860) baseStart_6860860 baseEnd_6860860 := by
    simpa [prefixWord, tailWord_6860860, baseEnd_6860860] using wordTrace_append hprefix tailTrace_6860860
  have hstable : (prefixWord ++ tailWord_6860860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860860).length < 2 ^ (prefixWord ++ tailWord_6860860).sum := by decide
  have hdescent : baseEnd_6860860 < baseStart_6860860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860877 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6860877 : Nat := 118140960795 + 6860877 * 2 ^ 59
def prefixEnd_6860877 : Nat := 4983230072969 + 3 ^ 40 * 6860877 * 2
def baseEnd_6860877 : Nat := 1174309204125752840294969

theorem tailTrace_6860877 : CollatzResearch.WordTrace tailWord_6860877 prefixEnd_6860877 1174309204125752840294969 := by
  unfold tailWord_6860877
  simp only [CollatzResearch.WordTrace]
  refine ⟨250236741965221848349364885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166824494643481232232909923 250236741965221848349364885)
  ·
    refine ⟨11729847279619774141376479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250236741965221848349364885 11729847279619774141376479)
    ·
      refine ⟨17594770919429661212064719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11729847279619774141376479 17594770919429661212064719)
      ·
        refine ⟨26392156379144491818097079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17594770919429661212064719 26392156379144491818097079)
        ·
          refine ⟨39588234568716737727145619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26392156379144491818097079 39588234568716737727145619)
          ·
            refine ⟨59382351853075106590718429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39588234568716737727145619 59382351853075106590718429)
            ·
              refine ⟨22268381944903164971519411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59382351853075106590718429 22268381944903164971519411)
              ·
                refine ⟨33402572917354747457279117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22268381944903164971519411 33402572917354747457279117)
                ·
                  refine ⟨12525964844008030296479669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33402572917354747457279117 12525964844008030296479669)
                  ·
                    refine ⟨1174309204125752840294969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12525964844008030296479669 1174309204125752840294969)
                    ·
                      rfl

theorem cell23_6860877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6860877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860877 prefixEnd_6860877 := by exact prefixLift 6860877
  have htrace : WordTrace (prefixWord ++ tailWord_6860877) baseStart_6860877 baseEnd_6860877 := by
    simpa [prefixWord, tailWord_6860877, baseEnd_6860877] using wordTrace_append hprefix tailTrace_6860877
  have hstable : (prefixWord ++ tailWord_6860877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860877).length < 2 ^ (prefixWord ++ tailWord_6860877).sum := by decide
  have hdescent : baseEnd_6860877 < baseStart_6860877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860890 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_6860890 : Nat := 118140960795 + 6860890 * 2 ^ 59
def prefixEnd_6860890 : Nat := 4983230072969 + 3 ^ 40 * 6860890 * 2
def baseEnd_6860890 : Nat := 1174311429208588990007449

theorem tailTrace_6860890 : CollatzResearch.WordTrace tailWord_6860890 prefixEnd_6860890 1174311429208588990007449 := by
  unfold tailWord_6860890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62559304028543687892397031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166824810742783167713058749 62559304028543687892397031)
  ·
    refine ⟨93838956042815531838595547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62559304028543687892397031 93838956042815531838595547)
    ·
      refine ⟨140758434064223297757893321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93838956042815531838595547 140758434064223297757893321)
      ·
        refine ⟨105568825548167473318419991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140758434064223297757893321 105568825548167473318419991)
        ·
          refine ⟨158353238322251209977629987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105568825548167473318419991 158353238322251209977629987)
          ·
            refine ⟨237529857483376814966444981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158353238322251209977629987 237529857483376814966444981)
            ·
              refine ⟨22268424139066576403104217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237529857483376814966444981 22268424139066576403104217)
              ·
                refine ⟨16701318104299932302328163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22268424139066576403104217 16701318104299932302328163)
                ·
                  refine ⟨25051977156449898453492245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16701318104299932302328163 25051977156449898453492245)
                  ·
                    refine ⟨1174311429208588990007449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25051977156449898453492245 1174311429208588990007449)
                    ·
                      rfl

theorem cell23_6860890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_6860890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860890 prefixEnd_6860890 := by exact prefixLift 6860890
  have htrace : WordTrace (prefixWord ++ tailWord_6860890) baseStart_6860890 baseEnd_6860890 := by
    simpa [prefixWord, tailWord_6860890, baseEnd_6860890] using wordTrace_append hprefix tailTrace_6860890
  have hstable : (prefixWord ++ tailWord_6860890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860890).length < 2 ^ (prefixWord ++ tailWord_6860890).sum := by decide
  have hdescent : baseEnd_6860890 < baseStart_6860890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860908 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_6860908 : Nat := 118140960795 + 6860908 * 2 ^ 59
def prefixEnd_6860908 : Nat := 4983230072969 + 3 ^ 40 * 6860908 * 2
def baseEnd_6860908 : Nat := 3522943530277547899597265

theorem tailTrace_6860908 : CollatzResearch.WordTrace tailWord_6860908 prefixEnd_6860908 3522943530277547899597265 := by
  unfold tailWord_6860908
  simp only [CollatzResearch.WordTrace]
  refine ⟨125118936314054770321871689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166825248418739693762495585 125118936314054770321871689)
  ·
    refine ⟨93839202235541077741403767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125118936314054770321871689 93839202235541077741403767)
    ·
      refine ⟨140758803353311616612105651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93839202235541077741403767 140758803353311616612105651)
      ·
        refine ⟨211138205029967424918158477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140758803353311616612105651 211138205029967424918158477)
        ·
          refine ⟨79176826886237784344309429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211138205029967424918158477 79176826886237784344309429)
          ·
            refine ⟨7422827520584792282279009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79176826886237784344309429 7422827520584792282279009)
            ·
              refine ⟨5567120640438594211709257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422827520584792282279009 5567120640438594211709257)
              ·
                refine ⟨4175340480328945658781943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567120640438594211709257 4175340480328945658781943)
                ·
                  refine ⟨6263010720493418488172915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175340480328945658781943 6263010720493418488172915)
                  ·
                    refine ⟨9394516080740127732259373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6263010720493418488172915 9394516080740127732259373)
                    ·
                      refine ⟨3522943530277547899597265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9394516080740127732259373 3522943530277547899597265)
                      ·
                        rfl

theorem cell23_6860908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_6860908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860908 prefixEnd_6860908 := by exact prefixLift 6860908
  have htrace : WordTrace (prefixWord ++ tailWord_6860908) baseStart_6860908 baseEnd_6860908 := by
    simpa [prefixWord, tailWord_6860908, baseEnd_6860908] using wordTrace_append hprefix tailTrace_6860908
  have hstable : (prefixWord ++ tailWord_6860908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860908).length < 2 ^ (prefixWord ++ tailWord_6860908).sum := by decide
  have hdescent : baseEnd_6860908 < baseStart_6860908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860947 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 3]
def baseStart_6860947 : Nat := 118140960795 + 6860947 * 2 ^ 59
def prefixEnd_6860947 : Nat := 4983230072969 + 3 ^ 40 * 6860947 * 2
def baseEnd_6860947 : Nat := 3522963556023073247009585

theorem tailTrace_6860947 : CollatzResearch.WordTrace tailWord_6860947 prefixEnd_6860947 3522963556023073247009585 := by
  unfold tailWord_6860947
  simp only [CollatzResearch.WordTrace]
  refine ⟨250239295074968250304413095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166826196716645500202942063 250239295074968250304413095)
  ·
    refine ⟨375358942612452375456619643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250239295074968250304413095 375358942612452375456619643)
    ·
      refine ⟨563038413918678563184929465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375358942612452375456619643 563038413918678563184929465)
      ·
        refine ⟨422278810439008922388697099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563038413918678563184929465 422278810439008922388697099)
        ·
          refine ⟨633418215658513383583045649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422278810439008922388697099 633418215658513383583045649)
          ·
            refine ⟨475063661743885037687284237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633418215658513383583045649 475063661743885037687284237)
            ·
              refine ⟨178148873153956889132731589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475063661743885037687284237 178148873153956889132731589)
              ·
                refine ⟨33402913716366916712387173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178148873153956889132731589 33402913716366916712387173)
                ·
                  refine ⟨6263046321818796883572595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33402913716366916712387173 6263046321818796883572595)
                  ·
                    refine ⟨9394569482728195325358893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6263046321818796883572595 9394569482728195325358893)
                    ·
                      refine ⟨3522963556023073247009585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9394569482728195325358893 3522963556023073247009585)
                      ·
                        rfl

theorem cell23_6860947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_6860947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860947 prefixEnd_6860947 := by exact prefixLift 6860947
  have htrace : WordTrace (prefixWord ++ tailWord_6860947) baseStart_6860947 baseEnd_6860947 := by
    simpa [prefixWord, tailWord_6860947, baseEnd_6860947] using wordTrace_append hprefix tailTrace_6860947
  have hstable : (prefixWord ++ tailWord_6860947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860947).length < 2 ^ (prefixWord ++ tailWord_6860947).sum := by decide
  have hdescent : baseEnd_6860947 < baseStart_6860947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6860958 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6860958 : Nat := 118140960795 + 6860958 * 2 ^ 59
def prefixEnd_6860958 : Nat := 4983230072969 + 3 ^ 40 * 6860958 * 2
def baseEnd_6860958 : Nat := 1174323068103424234657345

theorem tailTrace_6860958 : CollatzResearch.WordTrace tailWord_6860958 prefixEnd_6860958 1174323068103424234657345 := by
  unfold tailWord_6860958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279962034741049897882941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166826464185285599455375685 31279962034741049897882941)
  ·
    refine ⟨11729985763027893711706103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31279962034741049897882941 11729985763027893711706103)
    ·
      refine ⟨17594978644541840567559155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11729985763027893711706103 17594978644541840567559155)
      ·
        refine ⟨26392467966812760851338733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17594978644541840567559155 26392467966812760851338733)
        ·
          refine ⟨9897175487554785319252025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26392467966812760851338733 9897175487554785319252025)
          ·
            refine ⟨7422881615666088989439019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897175487554785319252025 7422881615666088989439019)
            ·
              refine ⟨11134322423499133484158529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422881615666088989439019 11134322423499133484158529)
              ·
                refine ⟨8350741817624350113118897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11134322423499133484158529 8350741817624350113118897)
                ·
                  refine ⟨6263056363218262584839173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8350741817624350113118897 6263056363218262584839173)
                  ·
                    refine ⟨1174323068103424234657345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6263056363218262584839173 1174323068103424234657345)
                    ·
                      rfl

theorem cell23_6860958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6860958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6860958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6860958 prefixEnd_6860958 := by exact prefixLift 6860958
  have htrace : WordTrace (prefixWord ++ tailWord_6860958) baseStart_6860958 baseEnd_6860958 := by
    simpa [prefixWord, tailWord_6860958, baseEnd_6860958] using wordTrace_append hprefix tailTrace_6860958
  have hstable : (prefixWord ++ tailWord_6860958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6860958).length < 2 ^ (prefixWord ++ tailWord_6860958).sum := by decide
  have hdescent : baseEnd_6860958 < baseStart_6860958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6860958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861040 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_6861040 : Nat := 118140960795 + 6861040 * 2 ^ 59
def prefixEnd_6861040 : Nat := 4983230072969 + 3 ^ 40 * 6861040 * 2
def baseEnd_6861040 : Nat := 1174337103241313794382219

theorem tailTrace_6861040 : CollatzResearch.WordTrace tailWord_6861040 prefixEnd_6861040 1174337103241313794382219 := by
  unfold tailWord_6861040
  simp only [CollatzResearch.WordTrace]
  refine ⟨125121343531815663593774287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166828458042420884791699049 125121343531815663593774287)
  ·
    refine ⟨187682015297723495390661431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125121343531815663593774287 187682015297723495390661431)
    ·
      refine ⟨281523022946585243085992147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187682015297723495390661431 281523022946585243085992147)
      ·
        refine ⟨422284534419877864628988221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281523022946585243085992147 422284534419877864628988221)
        ·
          refine ⟨158356700407454199235870583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422284534419877864628988221 158356700407454199235870583)
          ·
            refine ⟨237535050611181298853805875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158356700407454199235870583 237535050611181298853805875)
            ·
              refine ⟨356302575916771948280708813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237535050611181298853805875 356302575916771948280708813)
              ·
                refine ⟨133613465968789480605265805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356302575916771948280708813 133613465968789480605265805)
                ·
                  refine ⟨50105049738296055226974677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133613465968789480605265805 50105049738296055226974677)
                  ·
                    refine ⟨1174337103241313794382219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50105049738296055226974677 1174337103241313794382219)
                    ·
                      rfl

theorem cell23_6861040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_6861040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861040 prefixEnd_6861040 := by exact prefixLift 6861040
  have htrace : WordTrace (prefixWord ++ tailWord_6861040) baseStart_6861040 baseEnd_6861040 := by
    simpa [prefixWord, tailWord_6861040, baseEnd_6861040] using wordTrace_append hprefix tailTrace_6861040
  have hstable : (prefixWord ++ tailWord_6861040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861040).length < 2 ^ (prefixWord ++ tailWord_6861040).sum := by decide
  have hdescent : baseEnd_6861040 < baseStart_6861040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861114 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_6861114 : Nat := 118140960795 + 6861114 * 2 ^ 59
def prefixEnd_6861114 : Nat := 4983230072969 + 3 ^ 40 * 6861114 * 2
def baseEnd_6861114 : Nat := 3523049307292374093621317

theorem tailTrace_6861114 : CollatzResearch.WordTrace tailWord_6861114 prefixEnd_6861114 3523049307292374093621317 := by
  unfold tailWord_6861114
  simp only [CollatzResearch.WordTrace]
  refine ⟨62561346516340809456435599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166830257376908825217161597 62561346516340809456435599)
  ·
    refine ⟨93842019774511214184653399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62561346516340809456435599 93842019774511214184653399)
    ·
      refine ⟨140763029661766821276980099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93842019774511214184653399 140763029661766821276980099)
      ·
        refine ⟨211144544492650231915470149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140763029661766821276980099 211144544492650231915470149)
        ·
          refine ⟨39589602092371918484150653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211144544492650231915470149 39589602092371918484150653)
          ·
            refine ⟨14846100784639469431556495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39589602092371918484150653 14846100784639469431556495)
            ·
              refine ⟨22269151176959204147334743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14846100784639469431556495 22269151176959204147334743)
              ·
                refine ⟨33403726765438806221002115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22269151176959204147334743 33403726765438806221002115)
                ·
                  refine ⟨50105590148158209331503173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33403726765438806221002115 50105590148158209331503173)
                  ·
                    refine ⟨9394798152779664249656845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50105590148158209331503173 9394798152779664249656845)
                    ·
                      refine ⟨3523049307292374093621317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9394798152779664249656845 3523049307292374093621317)
                      ·
                        rfl

theorem cell23_6861114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_6861114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861114 prefixEnd_6861114 := by exact prefixLift 6861114
  have htrace : WordTrace (prefixWord ++ tailWord_6861114) baseStart_6861114 baseEnd_6861114 := by
    simpa [prefixWord, tailWord_6861114, baseEnd_6861114] using wordTrace_append hprefix tailTrace_6861114
  have hstable : (prefixWord ++ tailWord_6861114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861114).length < 2 ^ (prefixWord ++ tailWord_6861114).sum := by decide
  have hdescent : baseEnd_6861114 < baseStart_6861114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861137 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_6861137 : Nat := 118140960795 + 6861137 * 2 ^ 59
def prefixEnd_6861137 : Nat := 4983230072969 + 3 ^ 40 * 6861137 * 2
def baseEnd_6861137 : Nat := 3523061117347427503633711

theorem tailTrace_6861137 : CollatzResearch.WordTrace tailWord_6861137 prefixEnd_6861137 3523061117347427503633711 := by
  unfold tailWord_6861137
  simp only [CollatzResearch.WordTrace]
  refine ⟨250246224944279912753829665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166830816629519941835886443 250246224944279912753829665)
  ·
    refine ⟨187684668708209934565372249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250246224944279912753829665 187684668708209934565372249)
    ·
      refine ⟨140763501531157450924029187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187684668708209934565372249 140763501531157450924029187)
      ·
        refine ⟨211145252296736176386043781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140763501531157450924029187 211145252296736176386043781)
        ·
          refine ⟨39589734805638033072383209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211145252296736176386043781 39589734805638033072383209)
          ·
            refine ⟨29692301104228524804287407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39589734805638033072383209 29692301104228524804287407)
            ·
              refine ⟨44538451656342787206431111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29692301104228524804287407 44538451656342787206431111)
              ·
                refine ⟨66807677484514180809646667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44538451656342787206431111 66807677484514180809646667)
                ·
                  refine ⟨100211516226771271214470001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66807677484514180809646667 100211516226771271214470001)
                  ·
                    refine ⟨75158637170078453410852501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100211516226771271214470001 75158637170078453410852501)
                    ·
                      refine ⟨3523061117347427503633711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75158637170078453410852501 3523061117347427503633711)
                      ·
                        rfl

theorem cell23_6861137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_6861137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861137 prefixEnd_6861137 := by exact prefixLift 6861137
  have htrace : WordTrace (prefixWord ++ tailWord_6861137) baseStart_6861137 baseEnd_6861137 := by
    simpa [prefixWord, tailWord_6861137, baseEnd_6861137] using wordTrace_append hprefix tailTrace_6861137
  have hstable : (prefixWord ++ tailWord_6861137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861137).length < 2 ^ (prefixWord ++ tailWord_6861137).sum := by decide
  have hdescent : baseEnd_6861137 < baseStart_6861137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861177 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_6861177 : Nat := 118140960795 + 6861177 * 2 ^ 59
def prefixEnd_6861177 : Nat := 4983230072969 + 3 ^ 40 * 6861177 * 2
def baseEnd_6861177 : Nat := 1174360552191202449044509

theorem tailTrace_6861177 : CollatzResearch.WordTrace tailWord_6861177 prefixEnd_6861177 1174360552191202449044509 := by
  unfold tailWord_6861177
  simp only [CollatzResearch.WordTrace]
  refine ⟨250247683864134999585285785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166831789242756666390190523 250247683864134999585285785)
  ·
    refine ⟨187685762898101249688964339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250247683864134999585285785 187685762898101249688964339)
    ·
      refine ⟨281528644347151874533446509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187685762898101249688964339 281528644347151874533446509)
      ·
        refine ⟨105573241630181952950042441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281528644347151874533446509 105573241630181952950042441)
        ·
          refine ⟨79179931222636464712531831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105573241630181952950042441 79179931222636464712531831)
          ·
            refine ⟨118769896833954697068797747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79179931222636464712531831 118769896833954697068797747)
            ·
              refine ⟨178154845250932045603196621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118769896833954697068797747 178154845250932045603196621)
              ·
                refine ⟨66808066969099517101198733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178154845250932045603196621 66808066969099517101198733)
                ·
                  refine ⟨25053025113412318912949525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66808066969099517101198733 25053025113412318912949525)
                  ·
                    refine ⟨1174360552191202449044509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25053025113412318912949525 1174360552191202449044509)
                    ·
                      rfl

theorem cell23_6861177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_6861177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861177 prefixEnd_6861177 := by exact prefixLift 6861177
  have htrace : WordTrace (prefixWord ++ tailWord_6861177) baseStart_6861177 baseEnd_6861177 := by
    simpa [prefixWord, tailWord_6861177, baseEnd_6861177] using wordTrace_append hprefix tailTrace_6861177
  have hstable : (prefixWord ++ tailWord_6861177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861177).length < 2 ^ (prefixWord ++ tailWord_6861177).sum := by decide
  have hdescent : baseEnd_6861177 < baseStart_6861177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861195 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 1, 1, 3]
def baseStart_6861195 : Nat := 118140960795 + 6861195 * 2 ^ 59
def prefixEnd_6861195 : Nat := 4983230072969 + 3 ^ 40 * 6861195 * 2
def baseEnd_6861195 : Nat := 3523090899225388276708445

theorem tailTrace_6861195 : CollatzResearch.WordTrace tailWord_6861195 prefixEnd_6861195 3523090899225388276708445 := by
  unfold tailWord_6861195
  simp only [CollatzResearch.WordTrace]
  refine ⟨250248340378069788659441039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166832226918713192439627359 250248340378069788659441039)
  ·
    refine ⟨375372510567104682989161559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250248340378069788659441039 375372510567104682989161559)
    ·
      refine ⟨563058765850657024483742339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375372510567104682989161559 563058765850657024483742339)
      ·
        refine ⟨844588148775985536725613509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563058765850657024483742339 844588148775985536725613509)
        ·
          refine ⟨158360277895497288136052533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 844588148775985536725613509 158360277895497288136052533)
          ·
            refine ⟨14846276052702870762754925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158360277895497288136052533 14846276052702870762754925)
            ·
              refine ⟨5567353519763576536033097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14846276052702870762754925 5567353519763576536033097)
              ·
                refine ⟨4175515139822682402024823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567353519763576536033097 4175515139822682402024823)
                ·
                  refine ⟨6263272709734023603037235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175515139822682402024823 6263272709734023603037235)
                  ·
                    refine ⟨9394909064601035404555853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6263272709734023603037235 9394909064601035404555853)
                    ·
                      refine ⟨3523090899225388276708445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9394909064601035404555853 3523090899225388276708445)
                      ·
                        rfl

theorem cell23_6861195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 1, 3].length) (baseStart_6861195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861195 prefixEnd_6861195 := by exact prefixLift 6861195
  have htrace : WordTrace (prefixWord ++ tailWord_6861195) baseStart_6861195 baseEnd_6861195 := by
    simpa [prefixWord, tailWord_6861195, baseEnd_6861195] using wordTrace_append hprefix tailTrace_6861195
  have hstable : (prefixWord ++ tailWord_6861195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861195).length < 2 ^ (prefixWord ++ tailWord_6861195).sum := by decide
  have hdescent : baseEnd_6861195 < baseStart_6861195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861207 : List Nat := [1, 1, 3, 3, 1, 1, 3, 10]
def baseStart_6861207 : Nat := 118140960795 + 6861207 * 2 ^ 59
def prefixEnd_6861207 : Nat := 4983230072969 + 3 ^ 40 * 6861207 * 2
def baseEnd_6861207 : Nat := 130485076333083045546607

theorem tailTrace_6861207 : CollatzResearch.WordTrace tailWord_6861207 prefixEnd_6861207 130485076333083045546607 := by
  unfold tailWord_6861207
  simp only [CollatzResearch.WordTrace]
  refine ⟨250248778054026314708877875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166832518702684209805918583 250248778054026314708877875)
  ·
    refine ⟨375373167081039472063316813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250248778054026314708877875 375373167081039472063316813)
    ·
      refine ⟨140764937655389802023743805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375373167081039472063316813 140764937655389802023743805)
      ·
        refine ⟨52786851620771175758903927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140764937655389802023743805 52786851620771175758903927)
        ·
          refine ⟨79180277431156763638355891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52786851620771175758903927 79180277431156763638355891)
          ·
            refine ⟨118770416146735145457533837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79180277431156763638355891 118770416146735145457533837)
            ·
              refine ⟨44538906055025679546575189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118770416146735145457533837 44538906055025679546575189)
              ·
                refine ⟨130485076333083045546607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44538906055025679546575189 130485076333083045546607)
                ·
                  rfl

theorem cell23_6861207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 10].length) (baseStart_6861207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861207 prefixEnd_6861207 := by exact prefixLift 6861207
  have htrace : WordTrace (prefixWord ++ tailWord_6861207) baseStart_6861207 baseEnd_6861207 := by
    simpa [prefixWord, tailWord_6861207, baseEnd_6861207] using wordTrace_append hprefix tailTrace_6861207
  have hstable : (prefixWord ++ tailWord_6861207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861207).length < 2 ^ (prefixWord ++ tailWord_6861207).sum := by decide
  have hdescent : baseEnd_6861207 < baseStart_6861207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861218 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6861218 : Nat := 118140960795 + 6861218 * 2 ^ 59
def prefixEnd_6861218 : Nat := 4983230072969 + 3 ^ 40 * 6861218 * 2
def baseEnd_6861218 : Nat := 3523102709280441686720839

theorem tailTrace_6861218 : CollatzResearch.WordTrace tailWord_6861218 prefixEnd_6861218 3523102709280441686720839 := by
  unfold tailWord_6861218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62562294814246615896882077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166832786171324309058352205 62562294814246615896882077)
  ·
    refine ⟨23460860555342480961330779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62562294814246615896882077 23460860555342480961330779)
    ·
      refine ⟨35191290833013721441996169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23460860555342480961330779 35191290833013721441996169)
      ·
        refine ⟨26393468124760291081497127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35191290833013721441996169 26393468124760291081497127)
        ·
          refine ⟨39590202187140436622245691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26393468124760291081497127 39590202187140436622245691)
          ·
            refine ⟨59385303280710654933368537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39590202187140436622245691 59385303280710654933368537)
            ·
              refine ⟨44538977460532991200026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59385303280710654933368537 44538977460532991200026403)
              ·
                refine ⟨66808466190799486800039605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44538977460532991200026403 66808466190799486800039605)
                ·
                  refine ⟨6263293705387451887503713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66808466190799486800039605 6263293705387451887503713)
                  ·
                    refine ⟨4697470279040588915627785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263293705387451887503713 4697470279040588915627785)
                    ·
                      refine ⟨3523102709280441686720839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697470279040588915627785 3523102709280441686720839)
                      ·
                        rfl

theorem cell23_6861218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6861218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861218 prefixEnd_6861218 := by exact prefixLift 6861218
  have htrace : WordTrace (prefixWord ++ tailWord_6861218) baseStart_6861218 baseEnd_6861218 := by
    simpa [prefixWord, tailWord_6861218, baseEnd_6861218] using wordTrace_append hprefix tailTrace_6861218
  have hstable : (prefixWord ++ tailWord_6861218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861218).length < 2 ^ (prefixWord ++ tailWord_6861218).sum := by decide
  have hdescent : baseEnd_6861218 < baseStart_6861218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861247 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_6861247 : Nat := 118140960795 + 6861247 * 2 ^ 59
def prefixEnd_6861247 : Nat := 4983230072969 + 3 ^ 40 * 6861247 * 2
def baseEnd_6861247 : Nat := 3523117600219422073258205

theorem tailTrace_6861247 : CollatzResearch.WordTrace tailWord_6861247 prefixEnd_6861247 3523117600219422073258205 := by
  unfold tailWord_6861247
  simp only [CollatzResearch.WordTrace]
  refine ⟨250250236973881401540333995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166833491315920934360222663 250250236973881401540333995)
  ·
    refine ⟨375375355460822102310500993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250250236973881401540333995 375375355460822102310500993)
    ·
      refine ⟨281531516595616576732875745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375375355460822102310500993 281531516595616576732875745)
      ·
        refine ⟨211148637446712432549656809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281531516595616576732875745 211148637446712432549656809)
        ·
          refine ⟨158361478085034324412242607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211148637446712432549656809 158361478085034324412242607)
          ·
            refine ⟨237542217127551486618363911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158361478085034324412242607 237542217127551486618363911)
            ·
              refine ⟨356313325691327229927545867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237542217127551486618363911 356313325691327229927545867)
              ·
                refine ⟨534469988536990844891318801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356313325691327229927545867 534469988536990844891318801)
                ·
                  refine ⟨400852491402743133668489101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534469988536990844891318801 400852491402743133668489101)
                  ·
                    refine ⟨150319684276028675125683413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400852491402743133668489101 150319684276028675125683413)
                    ·
                      refine ⟨3523117600219422073258205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150319684276028675125683413 3523117600219422073258205)
                      ·
                        rfl

theorem cell23_6861247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_6861247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861247 prefixEnd_6861247 := by exact prefixLift 6861247
  have htrace : WordTrace (prefixWord ++ tailWord_6861247) baseStart_6861247 baseEnd_6861247 := by
    simpa [prefixWord, tailWord_6861247, baseEnd_6861247] using wordTrace_append hprefix tailTrace_6861247
  have hstable : (prefixWord ++ tailWord_6861247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861247).length < 2 ^ (prefixWord ++ tailWord_6861247).sum := by decide
  have hdescent : baseEnd_6861247 < baseStart_6861247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861268 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6861268 : Nat := 118140960795 + 6861268 * 2 ^ 59
def prefixEnd_6861268 : Nat := 4983230072969 + 3 ^ 40 * 6861268 * 2
def baseEnd_6861268 : Nat := 3523128383313166491095609

theorem tailTrace_6861268 : CollatzResearch.WordTrace tailWord_6861268 prefixEnd_6861268 3523128383313166491095609 := by
  unfold tailWord_6861268
  simp only [CollatzResearch.WordTrace]
  refine ⟨125125501453402661063424229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166834001937870214751232305 125125501453402661063424229)
  ·
    refine ⟨23461031522512998949392043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125125501453402661063424229 23461031522512998949392043)
    ·
      refine ⟨35191547283769498424088065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23461031522512998949392043 35191547283769498424088065)
      ·
        refine ⟨26393660462827123818066049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35191547283769498424088065 26393660462827123818066049)
        ·
          refine ⟨19795245347120342863549537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26393660462827123818066049 19795245347120342863549537)
          ·
            refine ⟨14846434010340257147662153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19795245347120342863549537 14846434010340257147662153)
            ·
              refine ⟨11134825507755192860746615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14846434010340257147662153 11134825507755192860746615)
              ·
                refine ⟨16702238261632789291119923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134825507755192860746615 16702238261632789291119923)
                ·
                  refine ⟨25053357392449183936679885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16702238261632789291119923 25053357392449183936679885)
                  ·
                    refine ⟨9395009022168443976254957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25053357392449183936679885 9395009022168443976254957)
                    ·
                      refine ⟨3523128383313166491095609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395009022168443976254957 3523128383313166491095609)
                      ·
                        rfl

theorem cell23_6861268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6861268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861268 prefixEnd_6861268 := by exact prefixLift 6861268
  have htrace : WordTrace (prefixWord ++ tailWord_6861268) baseStart_6861268 baseEnd_6861268 := by
    simpa [prefixWord, tailWord_6861268, baseEnd_6861268] using wordTrace_append hprefix tailTrace_6861268
  have hstable : (prefixWord ++ tailWord_6861268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861268).length < 2 ^ (prefixWord ++ tailWord_6861268).sum := by decide
  have hdescent : baseEnd_6861268 < baseStart_6861268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861274 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_6861274 : Nat := 118140960795 + 6861274 * 2 ^ 59
def prefixEnd_6861274 : Nat := 4983230072969 + 3 ^ 40 * 6861274 * 2
def baseEnd_6861274 : Nat := 3523131464197093467620581

theorem tailTrace_6861274 : CollatzResearch.WordTrace tailWord_6861274 prefixEnd_6861274 3523131464197093467620581 := by
  unfold tailWord_6861274
  simp only [CollatzResearch.WordTrace]
  refine ⟨62562805436195896287891719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166834147829855723434377917 62562805436195896287891719)
  ·
    refine ⟨93844208154293844431837579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62562805436195896287891719 93844208154293844431837579)
    ·
      refine ⟨140766312231440766647756369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93844208154293844431837579 140766312231440766647756369)
      ·
        refine ⟨105574734173580574985817277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140766312231440766647756369 105574734173580574985817277)
        ·
          refine ⟨39590525315092715619681479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105574734173580574985817277 39590525315092715619681479)
          ·
            refine ⟨59385787972639073429522219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39590525315092715619681479 59385787972639073429522219)
            ·
              refine ⟨89078681958958610144283329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59385787972639073429522219 89078681958958610144283329)
              ·
                refine ⟨66809011469218957608212497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89078681958958610144283329 66809011469218957608212497)
                ·
                  refine ⟨50106758601914218206159373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66809011469218957608212497 50106758601914218206159373)
                  ·
                    refine ⟨18790034475717831827309765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50106758601914218206159373 18790034475717831827309765)
                    ·
                      refine ⟨3523131464197093467620581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18790034475717831827309765 3523131464197093467620581)
                      ·
                        rfl

theorem cell23_6861274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_6861274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861274 prefixEnd_6861274 := by exact prefixLift 6861274
  have htrace : WordTrace (prefixWord ++ tailWord_6861274) baseStart_6861274 baseEnd_6861274 := by
    simpa [prefixWord, tailWord_6861274, baseEnd_6861274] using wordTrace_append hprefix tailTrace_6861274
  have hstable : (prefixWord ++ tailWord_6861274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861274).length < 2 ^ (prefixWord ++ tailWord_6861274).sum := by decide
  have hdescent : baseEnd_6861274 < baseStart_6861274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861291 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 4, 2]
def baseStart_6861291 : Nat := 118140960795 + 6861291 * 2 ^ 59
def prefixEnd_6861291 : Nat := 4983230072969 + 3 ^ 40 * 6861291 * 2
def baseEnd_6861291 : Nat := 3523140193368219901108003

theorem tailTrace_6861291 : CollatzResearch.WordTrace tailWord_6861291 prefixEnd_6861291 3523140193368219901108003 := by
  unfold tailWord_6861291
  simp only [CollatzResearch.WordTrace]
  refine ⟨250251841785721997054935727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166834561190481331369957151 250251841785721997054935727)
  ·
    refine ⟨375377762678582995582403591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250251841785721997054935727 375377762678582995582403591)
    ·
      refine ⟨563066644017874493373605387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375377762678582995582403591 563066644017874493373605387)
      ·
        refine ⟨844599966026811740060408081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563066644017874493373605387 844599966026811740060408081)
        ·
          refine ⟨633449974520108805045306061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844599966026811740060408081 633449974520108805045306061)
          ·
            refine ⟨237543740445040801891989773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633449974520108805045306061 237543740445040801891989773)
            ·
              refine ⟨89078902666890300709496165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237543740445040801891989773 89078902666890300709496165)
              ·
                refine ⟨16702294250041931383030531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89078902666890300709496165 16702294250041931383030531)
                ·
                  refine ⟨25053441375062897074545797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16702294250041931383030531 25053441375062897074545797)
                  ·
                    refine ⟨4697520257824293201477337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25053441375062897074545797 4697520257824293201477337)
                    ·
                      refine ⟨3523140193368219901108003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697520257824293201477337 3523140193368219901108003)
                      ·
                        rfl

theorem cell23_6861291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4, 2].length) (baseStart_6861291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861291 prefixEnd_6861291 := by exact prefixLift 6861291
  have htrace : WordTrace (prefixWord ++ tailWord_6861291) baseStart_6861291 baseEnd_6861291 := by
    simpa [prefixWord, tailWord_6861291, baseEnd_6861291] using wordTrace_append hprefix tailTrace_6861291
  have hstable : (prefixWord ++ tailWord_6861291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861291).length < 2 ^ (prefixWord ++ tailWord_6861291).sum := by decide
  have hdescent : baseEnd_6861291 < baseStart_6861291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861304 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_6861304 : Nat := 118140960795 + 6861304 * 2 ^ 59
def prefixEnd_6861304 : Nat := 4983230072969 + 3 ^ 40 * 6861304 * 2
def baseEnd_6861304 : Nat := 3523146868616728350245443

theorem tailTrace_6861304 : CollatzResearch.WordTrace tailWord_6861304 prefixEnd_6861304 3523146868616728350245443 := by
  unfold tailWord_6861304
  simp only [CollatzResearch.WordTrace]
  refine ⟨125126157967337450137579483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166834877289783266850105977 125126157967337450137579483)
  ·
    refine ⟨187689236951006175206369225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125126157967337450137579483 187689236951006175206369225)
    ·
      refine ⟨140766927713254631404776919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187689236951006175206369225 140766927713254631404776919)
      ·
        refine ⟨211150391569881947107165379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140766927713254631404776919 211150391569881947107165379)
        ·
          refine ⟨316725587354822920660748069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211150391569881947107165379 316725587354822920660748069)
          ·
            refine ⟨59386047629029297623890263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316725587354822920660748069 59386047629029297623890263)
            ·
              refine ⟨89079071443543946435835395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59386047629029297623890263 89079071443543946435835395)
              ·
                refine ⟨133618607165315919653753093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89079071443543946435835395 133618607165315919653753093)
                ·
                  refine ⟨25053488843496734935078705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133618607165315919653753093 25053488843496734935078705)
                  ·
                    refine ⟨18790116632622551201309029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25053488843496734935078705 18790116632622551201309029)
                    ·
                      refine ⟨3523146868616728350245443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18790116632622551201309029 3523146868616728350245443)
                      ·
                        rfl

theorem cell23_6861304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_6861304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861304 prefixEnd_6861304 := by exact prefixLift 6861304
  have htrace : WordTrace (prefixWord ++ tailWord_6861304) baseStart_6861304 baseEnd_6861304 := by
    simpa [prefixWord, tailWord_6861304, baseEnd_6861304] using wordTrace_append hprefix tailTrace_6861304
  have hstable : (prefixWord ++ tailWord_6861304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861304).length < 2 ^ (prefixWord ++ tailWord_6861304).sum := by decide
  have hdescent : baseEnd_6861304 < baseStart_6861304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861384 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6861384 : Nat := 118140960795 + 6861384 * 2 ^ 59
def prefixEnd_6861384 : Nat := 4983230072969 + 3 ^ 40 * 6861384 * 2
def baseEnd_6861384 : Nat := 3523187947069088037245075

theorem tailTrace_6861384 : CollatzResearch.WordTrace tailWord_6861384 prefixEnd_6861384 3523187947069088037245075 := by
  unfold tailWord_6861384
  simp only [CollatzResearch.WordTrace]
  refine ⟨125127616887192536969035603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166836822516256715958714137 125127616887192536969035603)
  ·
    refine ⟨187691425330788805453553405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125127616887192536969035603 187691425330788805453553405)
    ·
      refine ⟨70384284499045802045082527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187691425330788805453553405 70384284499045802045082527)
      ·
        refine ⟨105576426748568703067623791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70384284499045802045082527 105576426748568703067623791)
        ·
          refine ⟨158364640122853054601435687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105576426748568703067623791 158364640122853054601435687)
          ·
            refine ⟨237546960184279581902153531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158364640122853054601435687 237546960184279581902153531)
            ·
              refine ⟨356320440276419372853230297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237546960184279581902153531 356320440276419372853230297)
              ·
                refine ⟨267240330207314529639922723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356320440276419372853230297 267240330207314529639922723)
                ·
                  refine ⟨400860495310971794459884085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267240330207314529639922723 400860495310971794459884085)
                  ·
                    refine ⟨37580671435403605730614133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400860495310971794459884085 37580671435403605730614133)
                    ·
                      refine ⟨3523187947069088037245075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37580671435403605730614133 3523187947069088037245075)
                      ·
                        rfl

theorem cell23_6861384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6861384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861384 prefixEnd_6861384 := by exact prefixLift 6861384
  have htrace : WordTrace (prefixWord ++ tailWord_6861384) baseStart_6861384 baseEnd_6861384 := by
    simpa [prefixWord, tailWord_6861384, baseEnd_6861384] using wordTrace_append hprefix tailTrace_6861384
  have hstable : (prefixWord ++ tailWord_6861384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861384).length < 2 ^ (prefixWord ++ tailWord_6861384).sum := by decide
  have hdescent : baseEnd_6861384 < baseStart_6861384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861391 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 3, 4]
def baseStart_6861391 : Nat := 118140960795 + 6861391 * 2 ^ 59
def prefixEnd_6861391 : Nat := 4983230072969 + 3 ^ 40 * 6861391 * 2
def baseEnd_6861391 : Nat := 1174397180477889836619181

theorem tailTrace_6861391 : CollatzResearch.WordTrace tailWord_6861391 prefixEnd_6861391 1174397180477889836619181 := by
  unfold tailWord_6861391
  simp only [CollatzResearch.WordTrace]
  refine ⟨250255489085359714133576027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166836992723573142755717351 250255489085359714133576027)
  ·
    refine ⟨375383233628039571200364041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250255489085359714133576027 375383233628039571200364041)
    ·
      refine ⟨281537425221029678400273031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375383233628039571200364041 281537425221029678400273031)
      ·
        refine ⟨422306137831544517600409547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281537425221029678400273031 422306137831544517600409547)
        ·
          refine ⟨633459206747316776400614321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422306137831544517600409547 633459206747316776400614321)
          ·
            refine ⟨475094405060487582300460741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633459206747316776400614321 475094405060487582300460741)
            ·
              refine ⟨89080200948841421681336389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475094405060487582300460741 89080200948841421681336389)
              ·
                refine ⟨16702537677907766565250573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89080200948841421681336389 16702537677907766565250573)
                ·
                  refine ⟨6263451629215412461968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16702537677907766565250573 6263451629215412461968965)
                  ·
                    refine ⟨1174397180477889836619181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6263451629215412461968965 1174397180477889836619181)
                    ·
                      rfl

theorem cell23_6861391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_6861391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861391 prefixEnd_6861391 := by exact prefixLift 6861391
  have htrace : WordTrace (prefixWord ++ tailWord_6861391) baseStart_6861391 baseEnd_6861391 := by
    simpa [prefixWord, tailWord_6861391, baseEnd_6861391] using wordTrace_append hprefix tailTrace_6861391
  have hstable : (prefixWord ++ tailWord_6861391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861391).length < 2 ^ (prefixWord ++ tailWord_6861391).sum := by decide
  have hdescent : baseEnd_6861391 < baseStart_6861391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861418 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6861418 : Nat := 118140960795 + 6861418 * 2 ^ 59
def prefixEnd_6861418 : Nat := 4983230072969 + 3 ^ 40 * 6861418 * 2
def baseEnd_6861418 : Nat := 3523205405411340904219919

theorem tailTrace_6861418 : CollatzResearch.WordTrace tailWord_6861418 prefixEnd_6861418 3523205405411340904219919 := by
  unfold tailWord_6861418
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564118464065474436202227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166837649237507931829872605 62564118464065474436202227)
  ·
    refine ⟨93846177696098211654303341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62564118464065474436202227 93846177696098211654303341)
    ·
      refine ⟨35192316636036829370363753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93846177696098211654303341 35192316636036829370363753)
      ·
        refine ⟨26394237477027622027772815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35192316636036829370363753 26394237477027622027772815)
        ·
          refine ⟨39591356215541433041659223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26394237477027622027772815 39591356215541433041659223)
          ·
            refine ⟨59387034323312149562488835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39591356215541433041659223 59387034323312149562488835)
            ·
              refine ⟨89080551484968224343733253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59387034323312149562488835 89080551484968224343733253)
              ·
                refine ⟨16702603403431542064449985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89080551484968224343733253 16702603403431542064449985)
                ·
                  refine ⟨12526952552573656548337489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16702603403431542064449985 12526952552573656548337489)
                  ·
                    refine ⟨9395214414430242411253117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12526952552573656548337489 9395214414430242411253117)
                    ·
                      refine ⟨3523205405411340904219919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395214414430242411253117 3523205405411340904219919)
                      ·
                        rfl

theorem cell23_6861418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6861418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861418 prefixEnd_6861418 := by exact prefixLift 6861418
  have htrace : WordTrace (prefixWord ++ tailWord_6861418) baseStart_6861418 baseEnd_6861418 := by
    simpa [prefixWord, tailWord_6861418, baseEnd_6861418] using wordTrace_append hprefix tailTrace_6861418
  have hstable : (prefixWord ++ tailWord_6861418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861418).length < 2 ^ (prefixWord ++ tailWord_6861418).sum := by decide
  have hdescent : baseEnd_6861418 < baseStart_6861418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861491 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_6861491 : Nat := 118140960795 + 6861491 * 2 ^ 59
def prefixEnd_6861491 : Nat := 4983230072969 + 3 ^ 40 * 6861491 * 2
def baseEnd_6861491 : Nat := 3523242889499119118607083

theorem tailTrace_6861491 : CollatzResearch.WordTrace tailWord_6861491 prefixEnd_6861491 3523242889499119118607083 := by
  unfold tailWord_6861491
  simp only [CollatzResearch.WordTrace]
  refine ⟨250259136384997431212216327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166839424256664954141477551 250259136384997431212216327)
  ·
    refine ⟨375388704577496146818324491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250259136384997431212216327 375388704577496146818324491)
    ·
      refine ⟨563083056866244220227486737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375388704577496146818324491 563083056866244220227486737)
      ·
        refine ⟨422312292649683165170615053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563083056866244220227486737 422312292649683165170615053)
        ·
          refine ⟨158367109743631186938980645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422312292649683165170615053 158367109743631186938980645)
          ·
            refine ⟨29693833076930847551058871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158367109743631186938980645 29693833076930847551058871)
            ·
              refine ⟨44540749615396271326588307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29693833076930847551058871 44540749615396271326588307)
              ·
                refine ⟨66811124423094406989882461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44540749615396271326588307 66811124423094406989882461)
                ·
                  refine ⟨25054171658660402621205923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66811124423094406989882461 25054171658660402621205923)
                  ·
                    refine ⟨37581257487990603931808885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25054171658660402621205923 37581257487990603931808885)
                    ·
                      refine ⟨3523242889499119118607083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37581257487990603931808885 3523242889499119118607083)
                      ·
                        rfl

theorem cell23_6861491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_6861491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861491 prefixEnd_6861491 := by exact prefixLift 6861491
  have htrace : WordTrace (prefixWord ++ tailWord_6861491) baseStart_6861491 baseEnd_6861491 := by
    simpa [prefixWord, tailWord_6861491, baseEnd_6861491] using wordTrace_append hprefix tailTrace_6861491
  have hstable : (prefixWord ++ tailWord_6861491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861491).length < 2 ^ (prefixWord ++ tailWord_6861491).sum := by decide
  have hdescent : baseEnd_6861491 < baseStart_6861491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861539 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6861539 : Nat := 118140960795 + 6861539 * 2 ^ 59
def prefixEnd_6861539 : Nat := 4983230072969 + 3 ^ 40 * 6861539 * 2
def baseEnd_6861539 : Nat := 3523267536570534930806863

theorem tailTrace_6861539 : CollatzResearch.WordTrace tailWord_6861539 prefixEnd_6861539 3523267536570534930806863 := by
  unfold tailWord_6861539
  simp only [CollatzResearch.WordTrace]
  refine ⟨250260887088823535409963671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166840591392549023606642447 250260887088823535409963671)
  ·
    refine ⟨375391330633235303114945507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250260887088823535409963671 375391330633235303114945507)
    ·
      refine ⟨563086995949852954672418261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375391330633235303114945507 563086995949852954672418261)
      ·
        refine ⟨13197351467574678625134803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 563086995949852954672418261 13197351467574678625134803)
        ·
          refine ⟨19796027201362017937702205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197351467574678625134803 19796027201362017937702205)
          ·
            refine ⟨7423510200510756726638327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19796027201362017937702205 7423510200510756726638327)
            ·
              refine ⟨11135265300766135089957491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423510200510756726638327 11135265300766135089957491)
              ·
                refine ⟨16702897951149202634936237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11135265300766135089957491 16702897951149202634936237)
                ·
                  refine ⟨6263586731680950988101089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16702897951149202634936237 6263586731680950988101089)
                  ·
                    refine ⟨4697690048760713241075817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263586731680950988101089 4697690048760713241075817)
                    ·
                      refine ⟨3523267536570534930806863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697690048760713241075817 3523267536570534930806863)
                      ·
                        rfl

theorem cell23_6861539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6861539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861539 prefixEnd_6861539 := by exact prefixLift 6861539
  have htrace : WordTrace (prefixWord ++ tailWord_6861539) baseStart_6861539 baseEnd_6861539 := by
    simpa [prefixWord, tailWord_6861539, baseEnd_6861539] using wordTrace_append hprefix tailTrace_6861539
  have hstable : (prefixWord ++ tailWord_6861539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861539).length < 2 ^ (prefixWord ++ tailWord_6861539).sum := by decide
  have hdescent : baseEnd_6861539 < baseStart_6861539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861548 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_6861548 : Nat := 118140960795 + 6861548 * 2 ^ 59
def prefixEnd_6861548 : Nat := 4983230072969 + 3 ^ 40 * 6861548 * 2
def baseEnd_6861548 : Nat := 3523272157896425395594321

theorem tailTrace_6861548 : CollatzResearch.WordTrace tailWord_6861548 prefixEnd_6861548 3523272157896425395594321 := by
  unfold tailWord_6861548
  simp only [CollatzResearch.WordTrace]
  refine ⟨125130607672895464973520649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166840810230527286631360865 125130607672895464973520649)
  ·
    refine ⟨93847955754671598730140487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125130607672895464973520649 93847955754671598730140487)
    ·
      refine ⟨140771933632007398095210731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93847955754671598730140487 140771933632007398095210731)
      ·
        refine ⟨211157900448011097142816097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140771933632007398095210731 211157900448011097142816097)
        ·
          refine ⟨158368425336008322857112073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211157900448011097142816097 158368425336008322857112073)
          ·
            refine ⟨118776319002006242142834055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158368425336008322857112073 118776319002006242142834055)
            ·
              refine ⟨178164478503009363214251083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118776319002006242142834055 178164478503009363214251083)
              ·
                refine ⟨267246717754514044821376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178164478503009363214251083 267246717754514044821376625)
                ·
                  refine ⟨200435038315885533616032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267246717754514044821376625 200435038315885533616032469)
                  ·
                    refine ⟨4697696210528567194125761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200435038315885533616032469 4697696210528567194125761)
                    ·
                      refine ⟨3523272157896425395594321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697696210528567194125761 3523272157896425395594321)
                      ·
                        rfl

theorem cell23_6861548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_6861548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861548 prefixEnd_6861548 := by exact prefixLift 6861548
  have htrace : WordTrace (prefixWord ++ tailWord_6861548) baseStart_6861548 baseEnd_6861548 := by
    simpa [prefixWord, tailWord_6861548, baseEnd_6861548] using wordTrace_append hprefix tailTrace_6861548
  have hstable : (prefixWord ++ tailWord_6861548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861548).length < 2 ^ (prefixWord ++ tailWord_6861548).sum := by decide
  have hdescent : baseEnd_6861548 < baseStart_6861548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861556 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6861556 : Nat := 118140960795 + 6861556 * 2 ^ 59
def prefixEnd_6861556 : Nat := 4983230072969 + 3 ^ 40 * 6861556 * 2
def baseEnd_6861556 : Nat := 3523276265741661364294285

theorem tailTrace_6861556 : CollatzResearch.WordTrace tailWord_6861556 prefixEnd_6861556 3523276265741661364294285 := by
  unfold tailWord_6861556
  simp only [CollatzResearch.WordTrace]
  refine ⟨125130753564880973656666261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166841004753174631542221681 125130753564880973656666261)
  ·
    refine ⟨5865504073353795640156231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125130753564880973656666261 5865504073353795640156231)
    ·
      refine ⟨8798256110030693460234347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865504073353795640156231 8798256110030693460234347)
      ·
        refine ⟨13197384165046040190351521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798256110030693460234347 13197384165046040190351521)
        ·
          refine ⟨9898038123784530142763641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13197384165046040190351521 9898038123784530142763641)
          ·
            refine ⟨7423528592838397607072731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9898038123784530142763641 7423528592838397607072731)
            ·
              refine ⟨11135292889257596410609097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423528592838397607072731 11135292889257596410609097)
              ·
                refine ⟨8351469666943197307956823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11135292889257596410609097 8351469666943197307956823)
                ·
                  refine ⟨12527204500414795961935235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351469666943197307956823 12527204500414795961935235)
                  ·
                    refine ⟨18790806750622193942902853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12527204500414795961935235 18790806750622193942902853)
                    ·
                      refine ⟨3523276265741661364294285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18790806750622193942902853 3523276265741661364294285)
                      ·
                        rfl

theorem cell23_6861556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6861556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861556 prefixEnd_6861556 := by exact prefixLift 6861556
  have htrace : WordTrace (prefixWord ++ tailWord_6861556) baseStart_6861556 baseEnd_6861556 := by
    simpa [prefixWord, tailWord_6861556, baseEnd_6861556] using wordTrace_append hprefix tailTrace_6861556
  have hstable : (prefixWord ++ tailWord_6861556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861556).length < 2 ^ (prefixWord ++ tailWord_6861556).sum := by decide
  have hdescent : baseEnd_6861556 < baseStart_6861556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861565 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_6861565 : Nat := 118140960795 + 6861565 * 2 ^ 59
def prefixEnd_6861565 : Nat := 4983230072969 + 3 ^ 40 * 6861565 * 2
def baseEnd_6861565 : Nat := 3523280887067551829081743

theorem tailTrace_6861565 : CollatzResearch.WordTrace tailWord_6861565 prefixEnd_6861565 3523280887067551829081743 := by
  unfold tailWord_6861565
  simp only [CollatzResearch.WordTrace]
  refine ⟨250261835386729341850410149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166841223591152894566940099 250261835386729341850410149)
  ·
    refine ⟨46924094135011751596951903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250261835386729341850410149 46924094135011751596951903)
    ·
      refine ⟨70386141202517627395427855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46924094135011751596951903 70386141202517627395427855)
      ·
        refine ⟨105579211803776441093141783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70386141202517627395427855 105579211803776441093141783)
        ·
          refine ⟨158368817705664661639712675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105579211803776441093141783 158368817705664661639712675)
          ·
            refine ⟨237553226558496992459569013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158368817705664661639712675 237553226558496992459569013)
            ·
              refine ⟨22270614989859093043084595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237553226558496992459569013 22270614989859093043084595)
              ·
                refine ⟨33405922484788639564626893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22270614989859093043084595 33405922484788639564626893)
                ·
                  refine ⟨12527220931795739836735085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33405922484788639564626893 12527220931795739836735085)
                  ·
                    refine ⟨4697707849423402438775657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12527220931795739836735085 4697707849423402438775657)
                    ·
                      refine ⟨3523280887067551829081743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697707849423402438775657 3523280887067551829081743)
                      ·
                        rfl

theorem cell23_6861565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_6861565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861565 prefixEnd_6861565 := by exact prefixLift 6861565
  have htrace : WordTrace (prefixWord ++ tailWord_6861565) baseStart_6861565 baseEnd_6861565 := by
    simpa [prefixWord, tailWord_6861565, baseEnd_6861565] using wordTrace_append hprefix tailTrace_6861565
  have hstable : (prefixWord ++ tailWord_6861565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861565).length < 2 ^ (prefixWord ++ tailWord_6861565).sum := by decide
  have hdescent : baseEnd_6861565 < baseStart_6861565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861571 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 6]
def baseStart_6861571 : Nat := 118140960795 + 6861571 * 2 ^ 59
def prefixEnd_6861571 : Nat := 4983230072969 + 3 ^ 40 * 6861571 * 2
def baseEnd_6861571 : Nat := 1174427989317159601868905

theorem tailTrace_6861571 : CollatzResearch.WordTrace tailWord_6861571 prefixEnd_6861571 1174427989317159601868905 := by
  unfold tailWord_6861571
  simp only [CollatzResearch.WordTrace]
  refine ⟨250262054224707604875128567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166841369483138403250085711 250262054224707604875128567)
  ·
    refine ⟨375393081337061407312692851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250262054224707604875128567 375393081337061407312692851)
    ·
      refine ⟨563089622005592110969039277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375393081337061407312692851 563089622005592110969039277)
      ·
        refine ⟨211158608252097041613389729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563089622005592110969039277 211158608252097041613389729)
        ·
          refine ⟨158368956189072781210042297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211158608252097041613389729 158368956189072781210042297)
          ·
            refine ⟨118776717141804585907531723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158368956189072781210042297 118776717141804585907531723)
            ·
              refine ⟨178165075712706878861297585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118776717141804585907531723 178165075712706878861297585)
              ·
                refine ⟨133623806784530159145973189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178165075712706878861297585 133623806784530159145973189)
                ·
                  refine ⟨25054463772099404839869973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133623806784530159145973189 25054463772099404839869973)
                  ·
                    refine ⟨1174427989317159601868905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25054463772099404839869973 1174427989317159601868905)
                    ·
                      rfl

theorem cell23_6861571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_6861571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861571 prefixEnd_6861571 := by exact prefixLift 6861571
  have htrace : WordTrace (prefixWord ++ tailWord_6861571) baseStart_6861571 baseEnd_6861571 := by
    simpa [prefixWord, tailWord_6861571, baseEnd_6861571] using wordTrace_append hprefix tailTrace_6861571
  have hstable : (prefixWord ++ tailWord_6861571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861571).length < 2 ^ (prefixWord ++ tailWord_6861571).sum := by decide
  have hdescent : baseEnd_6861571 < baseStart_6861571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861612 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_6861612 : Nat := 118140960795 + 6861612 * 2 ^ 59
def prefixEnd_6861612 : Nat := 4983230072969 + 3 ^ 40 * 6861612 * 2
def baseEnd_6861612 : Nat := 3523305020658313145194027

theorem tailTrace_6861612 : CollatzResearch.WordTrace tailWord_6861612 prefixEnd_6861612 3523305020658313145194027 := by
  unfold tailWord_6861612
  simp only [CollatzResearch.WordTrace]
  refine ⟨125131774808779534438685545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166842366411706045918247393 125131774808779534438685545)
  ·
    refine ⟨93848831106584650829014159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125131774808779534438685545 93848831106584650829014159)
    ·
      refine ⟨140773246659876976243521239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93848831106584650829014159 140773246659876976243521239)
      ·
        refine ⟨211159869989815464365281859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140773246659876976243521239 211159869989815464365281859)
        ·
          refine ⟨316739804984723196547922789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211159869989815464365281859 316739804984723196547922789)
          ·
            refine ⟨59388713434635599352735523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316739804984723196547922789 59388713434635599352735523)
            ·
              refine ⟨89083070151953399029103285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59388713434635599352735523 89083070151953399029103285)
              ·
                refine ⟨8351537826745631158978433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89083070151953399029103285 8351537826745631158978433)
                ·
                  refine ⟨6263653370059223369233825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351537826745631158978433 6263653370059223369233825)
                  ·
                    refine ⟨4697740027544417526925369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263653370059223369233825 4697740027544417526925369)
                    ·
                      refine ⟨3523305020658313145194027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697740027544417526925369 3523305020658313145194027)
                      ·
                        rfl

theorem cell23_6861612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_6861612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861612 prefixEnd_6861612 := by exact prefixLift 6861612
  have htrace : WordTrace (prefixWord ++ tailWord_6861612) baseStart_6861612 baseEnd_6861612 := by
    simpa [prefixWord, tailWord_6861612, baseEnd_6861612] using wordTrace_append hprefix tailTrace_6861612
  have hstable : (prefixWord ++ tailWord_6861612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861612).length < 2 ^ (prefixWord ++ tailWord_6861612).sum := by decide
  have hdescent : baseEnd_6861612 < baseStart_6861612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861618 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_6861618 : Nat := 118140960795 + 6861618 * 2 ^ 59
def prefixEnd_6861618 : Nat := 4983230072969 + 3 ^ 40 * 6861618 * 2
def baseEnd_6861618 : Nat := 391478677949137791302111

theorem tailTrace_6861618 : CollatzResearch.WordTrace tailWord_6861618 prefixEnd_6861618 391478677949137791302111 := by
  unfold tailWord_6861618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62565942113884332975522377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166842512303691554601393005 62565942113884332975522377)
  ·
    refine ⟨46924456585413249731641783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62565942113884332975522377 46924456585413249731641783)
    ·
      refine ⟨70386684878119874597462675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46924456585413249731641783 70386684878119874597462675)
      ·
        refine ⟨105580027317179811896194013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70386684878119874597462675 105580027317179811896194013)
        ·
          refine ⟨39592510243942429461072755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105580027317179811896194013 39592510243942429461072755)
          ·
            refine ⟨59388765365913644191609133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39592510243942429461072755 59388765365913644191609133)
            ·
              refine ⟨22270787012217616571853425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59388765365913644191609133 22270787012217616571853425)
              ·
                refine ⟨16703090259163212428890069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22270787012217616571853425 16703090259163212428890069)
                ·
                  refine ⟨391478677949137791302111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16703090259163212428890069 391478677949137791302111)
                  ·
                    rfl

theorem cell23_6861618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_6861618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861618 prefixEnd_6861618 := by exact prefixLift 6861618
  have htrace : WordTrace (prefixWord ++ tailWord_6861618) baseStart_6861618 baseEnd_6861618 := by
    simpa [prefixWord, tailWord_6861618, baseEnd_6861618] using wordTrace_append hprefix tailTrace_6861618
  have hstable : (prefixWord ++ tailWord_6861618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861618).length < 2 ^ (prefixWord ++ tailWord_6861618).sum := by decide
  have hdescent : baseEnd_6861618 < baseStart_6861618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861628 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_6861628 : Nat := 118140960795 + 6861628 * 2 ^ 59
def prefixEnd_6861628 : Nat := 4983230072969 + 3 ^ 40 * 6861628 * 2
def baseEnd_6861628 : Nat := 3523313236348785082593953

theorem tailTrace_6861628 : CollatzResearch.WordTrace tailWord_6861628 prefixEnd_6861628 3523313236348785082593953 := by
  unfold tailWord_6861628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125132066592750551804976769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166842755457000735739969025 125132066592750551804976769)
  ·
    refine ⟨93849049944562913853732577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125132066592750551804976769 93849049944562913853732577)
    ·
      refine ⟨70386787458422185390299433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93849049944562913853732577 70386787458422185390299433)
      ·
        refine ⟨52790090593816639042724575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70386787458422185390299433 52790090593816639042724575)
        ·
          refine ⟨79185135890724958564086863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52790090593816639042724575 79185135890724958564086863)
          ·
            refine ⟨118777703836087437846130295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79185135890724958564086863 118777703836087437846130295)
            ·
              refine ⟨178166555754131156769195443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118777703836087437846130295 178166555754131156769195443)
              ·
                refine ⟨267249833631196735153793165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178166555754131156769195443 267249833631196735153793165)
                ·
                  refine ⟨100218687611698775682672437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267249833631196735153793165 100218687611698775682672437)
                  ·
                    refine ⟨9395501963596760220250541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100218687611698775682672437 9395501963596760220250541)
                    ·
                      refine ⟨3523313236348785082593953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395501963596760220250541 3523313236348785082593953)
                      ·
                        rfl

theorem cell23_6861628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_6861628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861628 prefixEnd_6861628 := by exact prefixLift 6861628
  have htrace : WordTrace (prefixWord ++ tailWord_6861628) baseStart_6861628 baseEnd_6861628 := by
    simpa [prefixWord, tailWord_6861628, baseEnd_6861628] using wordTrace_append hprefix tailTrace_6861628
  have hstable : (prefixWord ++ tailWord_6861628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861628).length < 2 ^ (prefixWord ++ tailWord_6861628).sum := by decide
  have hdescent : baseEnd_6861628 < baseStart_6861628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861633 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6861633 : Nat := 118140960795 + 6861633 * 2 ^ 59
def prefixEnd_6861633 : Nat := 4983230072969 + 3 ^ 40 * 6861633 * 2
def baseEnd_6861633 : Nat := 3523315803752057563031431

theorem tailTrace_6861633 : CollatzResearch.WordTrace tailWord_6861633 prefixEnd_6861633 3523315803752057563031431 := by
  unfold tailWord_6861633
  simp only [CollatzResearch.WordTrace]
  refine ⟨250264315550482989463885553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166842877033655326309257035 250264315550482989463885553)
  ·
    refine ⟨187698236662862242097914165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250264315550482989463885553 187698236662862242097914165)
    ·
      refine ⟨17596709687143335196679453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187698236662862242097914165 17596709687143335196679453)
      ·
        refine ⟨6598766132678750698754795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17596709687143335196679453 6598766132678750698754795)
        ·
          refine ⟨9898149199018126048132193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598766132678750698754795 9898149199018126048132193)
          ·
            refine ⟨7423611899263594536099145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9898149199018126048132193 7423611899263594536099145)
            ·
              refine ⟨5567708924447695902074359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7423611899263594536099145 5567708924447695902074359)
              ·
                refine ⟨8351563386671543853111539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567708924447695902074359 8351563386671543853111539)
                ·
                  refine ⟨12527345080007315779667309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351563386671543853111539 12527345080007315779667309)
                  ·
                    refine ⟨4697754405002743417375241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12527345080007315779667309 4697754405002743417375241)
                    ·
                      refine ⟨3523315803752057563031431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697754405002743417375241 3523315803752057563031431)
                      ·
                        rfl

theorem cell23_6861633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6861633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861633 prefixEnd_6861633 := by exact prefixLift 6861633
  have htrace : WordTrace (prefixWord ++ tailWord_6861633) baseStart_6861633 baseEnd_6861633 := by
    simpa [prefixWord, tailWord_6861633, baseEnd_6861633] using wordTrace_append hprefix tailTrace_6861633
  have hstable : (prefixWord ++ tailWord_6861633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861633).length < 2 ^ (prefixWord ++ tailWord_6861633).sum := by decide
  have hdescent : baseEnd_6861633 < baseStart_6861633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861635 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 5]
def baseStart_6861635 : Nat := 118140960795 + 6861635 * 2 ^ 59
def prefixEnd_6861635 : Nat := 4983230072969 + 3 ^ 40 * 6861635 * 2
def baseEnd_6861635 : Nat := 391479647857040728356269

theorem tailTrace_6861635 : CollatzResearch.WordTrace tailWord_6861635 prefixEnd_6861635 391479647857040728356269 := by
  unfold tailWord_6861635
  simp only [CollatzResearch.WordTrace]
  refine ⟨250264388496475743805458359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166842925664317162536972239 250264388496475743805458359)
  ·
    refine ⟨375396582744713615708187539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250264388496475743805458359 375396582744713615708187539)
    ·
      refine ⟨563094874117070423562281309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375396582744713615708187539 563094874117070423562281309)
      ·
        refine ⟨211160577793901408835855491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563094874117070423562281309 211160577793901408835855491)
        ·
          refine ⟨316740866690852113253783237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211160577793901408835855491 316740866690852113253783237)
          ·
            refine ⟨59388912504534771235084357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316740866690852113253783237 59388912504534771235084357)
            ·
              refine ⟨11135421094600269606578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59388912504534771235084357 11135421094600269606578317)
              ·
                refine ⟨4175782910475101102466869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11135421094600269606578317 4175782910475101102466869)
                ·
                  refine ⟨391479647857040728356269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175782910475101102466869 391479647857040728356269)
                  ·
                    rfl

theorem cell23_6861635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 5].length) (baseStart_6861635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861635 prefixEnd_6861635 := by exact prefixLift 6861635
  have htrace : WordTrace (prefixWord ++ tailWord_6861635) baseStart_6861635 baseEnd_6861635 := by
    simpa [prefixWord, tailWord_6861635, baseEnd_6861635] using wordTrace_append hprefix tailTrace_6861635
  have hstable : (prefixWord ++ tailWord_6861635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861635).length < 2 ^ (prefixWord ++ tailWord_6861635).sum := by decide
  have hdescent : baseEnd_6861635 < baseStart_6861635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861648 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_6861648 : Nat := 118140960795 + 6861648 * 2 ^ 59
def prefixEnd_6861648 : Nat := 4983230072969 + 3 ^ 40 * 6861648 * 2
def baseEnd_6861648 : Nat := 1174441168653958334781287

theorem tailTrace_6861648 : CollatzResearch.WordTrace tailWord_6861648 prefixEnd_6861648 1174441168653958334781287 := by
  unfold tailWord_6861648
  simp only [CollatzResearch.WordTrace]
  refine ⟨125132431322714323512840799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166843241763619098017121065 125132431322714323512840799)
  ·
    refine ⟨187698646984071485269261199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125132431322714323512840799 187698646984071485269261199)
    ·
      refine ⟨281547970476107227903891799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187698646984071485269261199 281547970476107227903891799)
      ·
        refine ⟨422321955714160841855837699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281547970476107227903891799 422321955714160841855837699)
        ·
          refine ⟨633482933571241262783756549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422321955714160841855837699 633482933571241262783756549)
          ·
            refine ⟨118778050044607736771954353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 633482933571241262783756549 118778050044607736771954353)
            ·
              refine ⟨89083537533455802578965765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118778050044607736771954353 89083537533455802578965765)
              ·
                refine ⟨16703163287522962983556081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89083537533455802578965765 16703163287522962983556081)
                ·
                  refine ⟨12527372465642222237667061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16703163287522962983556081 12527372465642222237667061)
                  ·
                    refine ⟨1174441168653958334781287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12527372465642222237667061 1174441168653958334781287)
                    ·
                      rfl

theorem cell23_6861648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_6861648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861648 prefixEnd_6861648 := by exact prefixLift 6861648
  have htrace : WordTrace (prefixWord ++ tailWord_6861648) baseStart_6861648 baseEnd_6861648 := by
    simpa [prefixWord, tailWord_6861648, baseEnd_6861648] using wordTrace_append hprefix tailTrace_6861648
  have hstable : (prefixWord ++ tailWord_6861648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861648).length < 2 ^ (prefixWord ++ tailWord_6861648).sum := by decide
  have hdescent : baseEnd_6861648 < baseStart_6861648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861685 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6861685 : Nat := 118140960795 + 6861685 * 2 ^ 59
def prefixEnd_6861685 : Nat := 4983230072969 + 3 ^ 40 * 6861685 * 2
def baseEnd_6861685 : Nat := 3523342504746091359581191

theorem tailTrace_6861685 : CollatzResearch.WordTrace tailWord_6861685 prefixEnd_6861685 3523342504746091359581191 := by
  unfold tailWord_6861685
  simp only [CollatzResearch.WordTrace]
  refine ⟨250266212146294602344778509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166844141430863068229852339 250266212146294602344778509)
  ·
    refine ⟨93849829554860475879291941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250266212146294602344778509 93849829554860475879291941)
    ·
      refine ⟨17596843041536339227367239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93849829554860475879291941 17596843041536339227367239)
      ·
        refine ⟨26395264562304508841050859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17596843041536339227367239 26395264562304508841050859)
        ·
          refine ⟨39592896843456763261576289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26395264562304508841050859 39592896843456763261576289)
          ·
            refine ⟨29694672632592572446182217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39592896843456763261576289 29694672632592572446182217)
            ·
              refine ⟨22271004474444429334636663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29694672632592572446182217 22271004474444429334636663)
              ·
                refine ⟨33406506711666644001954995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22271004474444429334636663 33406506711666644001954995)
                ·
                  refine ⟨50109760067499966002932493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33406506711666644001954995 50109760067499966002932493)
                  ·
                    refine ⟨18791160025312487251099685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50109760067499966002932493 18791160025312487251099685)
                    ·
                      refine ⟨3523342504746091359581191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18791160025312487251099685 3523342504746091359581191)
                      ·
                        rfl

theorem cell23_6861685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6861685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861685 prefixEnd_6861685 := by exact prefixLift 6861685
  have htrace : WordTrace (prefixWord ++ tailWord_6861685) baseStart_6861685 baseEnd_6861685 := by
    simpa [prefixWord, tailWord_6861685, baseEnd_6861685] using wordTrace_append hprefix tailTrace_6861685
  have hstable : (prefixWord ++ tailWord_6861685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861685).length < 2 ^ (prefixWord ++ tailWord_6861685).sum := by decide
  have hdescent : baseEnd_6861685 < baseStart_6861685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861705 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_6861705 : Nat := 118140960795 + 6861705 * 2 ^ 59
def prefixEnd_6861705 : Nat := 4983230072969 + 3 ^ 40 * 6861705 * 2
def baseEnd_6861705 : Nat := 3523352774359181281331099

theorem tailTrace_6861705 : CollatzResearch.WordTrace tailWord_6861705 prefixEnd_6861705 3523352774359181281331099 := by
  unfold tailWord_6861705
  simp only [CollatzResearch.WordTrace]
  refine ⟨250266941606222145760506569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166844627737481430507004379 250266941606222145760506569)
  ·
    refine ⟨187700206204666609320379927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250266941606222145760506569 187700206204666609320379927)
    ·
      refine ⟨281550309306999913980569891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187700206204666609320379927 281550309306999913980569891)
      ·
        refine ⟨422325463960499870970854837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281550309306999913980569891 422325463960499870970854837)
        ·
          refine ⟨39593012246296862903517641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 422325463960499870970854837 39593012246296862903517641)
          ·
            refine ⟨29694759184722647177638231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39593012246296862903517641 29694759184722647177638231)
            ·
              refine ⟨44542138777083970766457347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29694759184722647177638231 44542138777083970766457347)
              ·
                refine ⟨66813208165625956149686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44542138777083970766457347 66813208165625956149686021)
                ·
                  refine ⟨12527476531054866778066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66813208165625956149686021 12527476531054866778066129)
                  ·
                    refine ⟨9395607398291150083549597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12527476531054866778066129 9395607398291150083549597)
                    ·
                      refine ⟨3523352774359181281331099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395607398291150083549597 3523352774359181281331099)
                      ·
                        rfl

theorem cell23_6861705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_6861705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861705 prefixEnd_6861705 := by exact prefixLift 6861705
  have htrace : WordTrace (prefixWord ++ tailWord_6861705) baseStart_6861705 baseEnd_6861705 := by
    simpa [prefixWord, tailWord_6861705, baseEnd_6861705] using wordTrace_append hprefix tailTrace_6861705
  have hstable : (prefixWord ++ tailWord_6861705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861705).length < 2 ^ (prefixWord ++ tailWord_6861705).sum := by decide
  have hdescent : baseEnd_6861705 < baseStart_6861705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861708 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 8]
def baseStart_6861708 : Nat := 118140960795 + 6861708 * 2 ^ 59
def prefixEnd_6861708 : Nat := 4983230072969 + 3 ^ 40 * 6861708 * 2
def baseEnd_6861708 : Nat := 391483812755682752177065

theorem tailTrace_6861708 : CollatzResearch.WordTrace tailWord_6861708 prefixEnd_6861708 391483812755682752177065 := by
  unfold tailWord_6861708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125133525512605638636432889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166844700683474184848577185 125133525512605638636432889)
  ·
    refine ⟨93850144134454228977324667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125133525512605638636432889 93850144134454228977324667)
    ·
      refine ⟨140775216201681343465987001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93850144134454228977324667 140775216201681343465987001)
      ·
        refine ⟨105581412151261007599490251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140775216201681343465987001 105581412151261007599490251)
        ·
          refine ⟨158372118226891511399235377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105581412151261007599490251 158372118226891511399235377)
          ·
            refine ⟨118779088670168633549426533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158372118226891511399235377 118779088670168633549426533)
            ·
              refine ⟨22271079125656618790517475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118779088670168633549426533 22271079125656618790517475)
              ·
                refine ⟨33406618688484928185776213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22271079125656618790517475 33406618688484928185776213)
                ·
                  refine ⟨391483812755682752177065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33406618688484928185776213 391483812755682752177065)
                  ·
                    rfl

theorem cell23_6861708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_6861708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861708 prefixEnd_6861708 := by exact prefixLift 6861708
  have htrace : WordTrace (prefixWord ++ tailWord_6861708) baseStart_6861708 baseEnd_6861708 := by
    simpa [prefixWord, tailWord_6861708, baseEnd_6861708] using wordTrace_append hprefix tailTrace_6861708
  have hstable : (prefixWord ++ tailWord_6861708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861708).length < 2 ^ (prefixWord ++ tailWord_6861708).sum := by decide
  have hdescent : baseEnd_6861708 < baseStart_6861708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861725 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 6]
def baseStart_6861725 : Nat := 118140960795 + 6861725 * 2 ^ 59
def prefixEnd_6861725 : Nat := 4983230072969 + 3 ^ 40 * 6861725 * 2
def baseEnd_6861725 : Nat := 391484782663585689231223

theorem tailTrace_6861725 : CollatzResearch.WordTrace tailWord_6861725 prefixEnd_6861725 391484782663585689231223 := by
  unfold tailWord_6861725
  simp only [CollatzResearch.WordTrace]
  refine ⟨250267671066149689176234629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166845114044099792784156419 250267671066149689176234629)
  ·
    refine ⟨46925188324903066720543993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250267671066149689176234629 46925188324903066720543993)
    ·
      refine ⟨35193891243677300040407995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46925188324903066720543993 35193891243677300040407995)
      ·
        refine ⟨52790836865515950060611993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35193891243677300040407995 52790836865515950060611993)
        ·
          refine ⟨39593127649136962545458995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52790836865515950060611993 39593127649136962545458995)
          ·
            refine ⟨59389691473705443818188493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39593127649136962545458995 59389691473705443818188493)
            ·
              refine ⟨22271134302639541431820685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59389691473705443818188493 22271134302639541431820685)
              ·
                refine ⟨8351675363489828036932757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22271134302639541431820685 8351675363489828036932757)
                ·
                  refine ⟨391484782663585689231223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8351675363489828036932757 391484782663585689231223)
                  ·
                    rfl

theorem cell23_6861725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_6861725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861725 prefixEnd_6861725 := by exact prefixLift 6861725
  have htrace : WordTrace (prefixWord ++ tailWord_6861725) baseStart_6861725 baseEnd_6861725 := by
    simpa [prefixWord, tailWord_6861725, baseEnd_6861725] using wordTrace_append hprefix tailTrace_6861725
  have hstable : (prefixWord ++ tailWord_6861725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861725).length < 2 ^ (prefixWord ++ tailWord_6861725).sum := by decide
  have hdescent : baseEnd_6861725 < baseStart_6861725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861728 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6861728 : Nat := 118140960795 + 6861728 * 2 ^ 59
def prefixEnd_6861728 : Nat := 4983230072969 + 3 ^ 40 * 6861728 * 2
def baseEnd_6861728 : Nat := 3523364584414234691343493

theorem tailTrace_6861728 : CollatzResearch.WordTrace tailWord_6861728 prefixEnd_6861728 3523364584414234691343493 := by
  unfold tailWord_6861728
  simp only [CollatzResearch.WordTrace]
  refine ⟨125133890242569410344296919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166845186990092547125729225 125133890242569410344296919)
  ·
    refine ⟨187700835363854115516445379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125133890242569410344296919 187700835363854115516445379)
    ·
      refine ⟨281551253045781173274668069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187700835363854115516445379 281551253045781173274668069)
      ·
        refine ⟨52790859946083969989000263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281551253045781173274668069 52790859946083969989000263)
        ·
          refine ⟨79186289919125954983500395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52790859946083969989000263 79186289919125954983500395)
          ·
            refine ⟨118779434878688932475250593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79186289919125954983500395 118779434878688932475250593)
            ·
              refine ⟨89084576159016699356437945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118779434878688932475250593 89084576159016699356437945)
              ·
                refine ⟨66813432119262524517328459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89084576159016699356437945 66813432119262524517328459)
                ·
                  refine ⟨100220148178893786775992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66813432119262524517328459 100220148178893786775992689)
                  ·
                    refine ⟨75165111134170340081994517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100220148178893786775992689 75165111134170340081994517)
                    ·
                      refine ⟨3523364584414234691343493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75165111134170340081994517 3523364584414234691343493)
                      ·
                        rfl

theorem cell23_6861728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6861728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861728 prefixEnd_6861728 := by exact prefixLift 6861728
  have htrace : WordTrace (prefixWord ++ tailWord_6861728) baseStart_6861728 baseEnd_6861728 := by
    simpa [prefixWord, tailWord_6861728, baseEnd_6861728] using wordTrace_append hprefix tailTrace_6861728
  have hstable : (prefixWord ++ tailWord_6861728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861728).length < 2 ^ (prefixWord ++ tailWord_6861728).sum := by decide
  have hdescent : baseEnd_6861728 < baseStart_6861728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861775 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_6861775 : Nat := 118140960795 + 6861775 * 2 ^ 59
def prefixEnd_6861775 : Nat := 4983230072969 + 3 ^ 40 * 6861775 * 2
def baseEnd_6861775 : Nat := 3523388718004996007455777

theorem tailTrace_6861775 : CollatzResearch.WordTrace tailWord_6861775 prefixEnd_6861775 3523388718004996007455777 := by
  unfold tailWord_6861775
  simp only [CollatzResearch.WordTrace]
  refine ⟨250269494715968547715554779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166846329810645698477036519 250269494715968547715554779)
  ·
    refine ⟨375404242073952821573332169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250269494715968547715554779 375404242073952821573332169)
    ·
      refine ⟨281553181555464616179999127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375404242073952821573332169 281553181555464616179999127)
      ·
        refine ⟨422329772333196924269998691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281553181555464616179999127 422329772333196924269998691)
        ·
          refine ⟨633494658499795386404998037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422329772333196924269998691 633494658499795386404998037)
          ·
            refine ⟨29695062117177908737734283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 633494658499795386404998037 29695062117177908737734283)
            ·
              refine ⟨44542593175766863106601425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29695062117177908737734283 44542593175766863106601425)
              ·
                refine ⟨33406944881825147329951069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44542593175766863106601425 33406944881825147329951069)
                ·
                  refine ⟨12527604330684430248731651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33406944881825147329951069 12527604330684430248731651)
                  ·
                    refine ⟨18791406496026645373097477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12527604330684430248731651 18791406496026645373097477)
                    ·
                      refine ⟨3523388718004996007455777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18791406496026645373097477 3523388718004996007455777)
                      ·
                        rfl

theorem cell23_6861775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_6861775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861775 prefixEnd_6861775 := by exact prefixLift 6861775
  have htrace : WordTrace (prefixWord ++ tailWord_6861775) baseStart_6861775 baseEnd_6861775 := by
    simpa [prefixWord, tailWord_6861775, baseEnd_6861775] using wordTrace_append hprefix tailTrace_6861775
  have hstable : (prefixWord ++ tailWord_6861775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861775).length < 2 ^ (prefixWord ++ tailWord_6861775).sum := by decide
  have hdescent : baseEnd_6861775 < baseStart_6861775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861785 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_6861785 : Nat := 118140960795 + 6861785 * 2 ^ 59
def prefixEnd_6861785 : Nat := 4983230072969 + 3 ^ 40 * 6861785 * 2
def baseEnd_6861785 : Nat := 1174464617603846989443577

theorem tailTrace_6861785 : CollatzResearch.WordTrace tailWord_6861785 prefixEnd_6861785 1174464617603846989443577 := by
  unfold tailWord_6861785
  simp only [CollatzResearch.WordTrace]
  refine ⟨250269859445932319423418809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166846572963954879615612539 250269859445932319423418809)
  ·
    refine ⟨187702394584449239567564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250269859445932319423418809 187702394584449239567564107)
    ·
      refine ⟨281553591876673859351346161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187702394584449239567564107 281553591876673859351346161)
      ·
        refine ⟨211165193907505394513509621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281553591876673859351346161 211165193907505394513509621)
        ·
          refine ⟨19796736928828630735641527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211165193907505394513509621 19796736928828630735641527)
          ·
            refine ⟨29695105393242946103462291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796736928828630735641527 29695105393242946103462291)
            ·
              refine ⟨44542658089864419155193437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29695105393242946103462291 44542658089864419155193437)
              ·
                refine ⟨16703496783699157183197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44542658089864419155193437 16703496783699157183197539)
                ·
                  refine ⟨25055245175548735774796309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16703496783699157183197539 25055245175548735774796309)
                  ·
                    refine ⟨1174464617603846989443577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25055245175548735774796309 1174464617603846989443577)
                    ·
                      rfl

theorem cell23_6861785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_6861785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861785 prefixEnd_6861785 := by exact prefixLift 6861785
  have htrace : WordTrace (prefixWord ++ tailWord_6861785) baseStart_6861785 baseEnd_6861785 := by
    simpa [prefixWord, tailWord_6861785, baseEnd_6861785] using wordTrace_append hprefix tailTrace_6861785
  have hstable : (prefixWord ++ tailWord_6861785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861785).length < 2 ^ (prefixWord ++ tailWord_6861785).sum := by decide
  have hdescent : baseEnd_6861785 < baseStart_6861785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861806 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_6861806 : Nat := 118140960795 + 6861806 * 2 ^ 59
def prefixEnd_6861806 : Nat := 4983230072969 + 3 ^ 40 * 6861806 * 2
def baseEnd_6861806 : Nat := 1174468211968428462056045

theorem tailTrace_6861806 : CollatzResearch.WordTrace tailWord_6861806 prefixEnd_6861806 1174468211968428462056045 := by
  unfold tailWord_6861806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31283828172357030001241659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166847083585904160006622181 31283828172357030001241659)
  ·
    refine ⟨46925742258535545001862489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31283828172357030001241659 46925742258535545001862489)
    ·
      refine ⟨35194306693901658751396867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46925742258535545001862489 35194306693901658751396867)
      ·
        refine ⟨52791460040852488127095301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35194306693901658751396867 52791460040852488127095301)
        ·
          refine ⟨9898398757659841523830369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52791460040852488127095301 9898398757659841523830369)
          ·
            refine ⟨7423799068244881142872777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9898398757659841523830369 7423799068244881142872777)
            ·
              refine ⟨5567849301183660857154583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7423799068244881142872777 5567849301183660857154583)
              ·
                refine ⟨8351773951775491285731875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567849301183660857154583 8351773951775491285731875)
                ·
                  refine ⟨12527660927663236928597813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351773951775491285731875 12527660927663236928597813)
                  ·
                    refine ⟨1174468211968428462056045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12527660927663236928597813 1174468211968428462056045)
                    ·
                      rfl

theorem cell23_6861806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_6861806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861806 prefixEnd_6861806 := by exact prefixLift 6861806
  have htrace : WordTrace (prefixWord ++ tailWord_6861806) baseStart_6861806 baseEnd_6861806 := by
    simpa [prefixWord, tailWord_6861806, baseEnd_6861806] using wordTrace_append hprefix tailTrace_6861806
  have hstable : (prefixWord ++ tailWord_6861806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861806).length < 2 ^ (prefixWord ++ tailWord_6861806).sum := by decide
  have hdescent : baseEnd_6861806 < baseStart_6861806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861809 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_6861809 : Nat := 118140960795 + 6861809 * 2 ^ 59
def prefixEnd_6861809 : Nat := 4983230072969 + 3 ^ 40 * 6861809 * 2
def baseEnd_6861809 : Nat := 3523406176347248874430621

theorem tailTrace_6861809 : CollatzResearch.WordTrace tailWord_6861809 prefixEnd_6861809 3523406176347248874430621 := by
  unfold tailWord_6861809
  simp only [CollatzResearch.WordTrace]
  refine ⟨250270734797845371522292481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166847156531896914348194987 250270734797845371522292481)
  ·
    refine ⟨187703051098384028641719361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250270734797845371522292481 187703051098384028641719361)
    ·
      refine ⟨140777288323788021481289521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187703051098384028641719361 140777288323788021481289521)
      ·
        refine ⟨105582966242841016110967141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140777288323788021481289521 105582966242841016110967141)
        ·
          refine ⟨19796806170532690520806339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105582966242841016110967141 19796806170532690520806339)
          ·
            refine ⟨29695209255799035781209509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796806170532690520806339 29695209255799035781209509)
            ·
              refine ⟨5567851735462319208976783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29695209255799035781209509 5567851735462319208976783)
              ·
                refine ⟨8351777603193478813465175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567851735462319208976783 8351777603193478813465175)
                ·
                  refine ⟨12527666404790218220197763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351777603193478813465175 12527666404790218220197763)
                  ·
                    refine ⟨18791499607185327330296645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12527666404790218220197763 18791499607185327330296645)
                    ·
                      refine ⟨3523406176347248874430621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18791499607185327330296645 3523406176347248874430621)
                      ·
                        rfl

theorem cell23_6861809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_6861809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861809 prefixEnd_6861809 := by exact prefixLift 6861809
  have htrace : WordTrace (prefixWord ++ tailWord_6861809) baseStart_6861809 baseEnd_6861809 := by
    simpa [prefixWord, tailWord_6861809, baseEnd_6861809] using wordTrace_append hprefix tailTrace_6861809
  have hstable : (prefixWord ++ tailWord_6861809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861809).length < 2 ^ (prefixWord ++ tailWord_6861809).sum := by decide
  have hdescent : baseEnd_6861809 < baseStart_6861809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861855 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_6861855 : Nat := 118140960795 + 6861855 * 2 ^ 59
def prefixEnd_6861855 : Nat := 4983230072969 + 3 ^ 40 * 6861855 * 2
def baseEnd_6861855 : Nat := 3523429796457355694455409

theorem tailTrace_6861855 : CollatzResearch.WordTrace tailWord_6861855 prefixEnd_6861855 3523429796457355694455409 := by
  unfold tailWord_6861855
  simp only [CollatzResearch.WordTrace]
  refine ⟨250272412555678721378467019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166848275037119147585644679 250272412555678721378467019)
  ·
    refine ⟨375408618833518082067700529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250272412555678721378467019 375408618833518082067700529)
    ·
      refine ⟨281556464125138561550775397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375408618833518082067700529 281556464125138561550775397)
      ·
        refine ⟨52791837023463480290770387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281556464125138561550775397 52791837023463480290770387)
        ·
          refine ⟨79187755535195220436155581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52791837023463480290770387 79187755535195220436155581)
          ·
            refine ⟨29695408325698207663558343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79187755535195220436155581 29695408325698207663558343)
            ·
              refine ⟨44543112488547311495337515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29695408325698207663558343 44543112488547311495337515)
              ·
                refine ⟨66814668732820967243006273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44543112488547311495337515 66814668732820967243006273)
                ·
                  refine ⟨50111001549615725432254705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66814668732820967243006273 50111001549615725432254705)
                  ·
                    refine ⟨37583251162211794074191029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50111001549615725432254705 37583251162211794074191029)
                    ·
                      refine ⟨3523429796457355694455409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37583251162211794074191029 3523429796457355694455409)
                      ·
                        rfl

theorem cell23_6861855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_6861855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861855 prefixEnd_6861855 := by exact prefixLift 6861855
  have htrace : WordTrace (prefixWord ++ tailWord_6861855) baseStart_6861855 baseEnd_6861855 := by
    simpa [prefixWord, tailWord_6861855, baseEnd_6861855] using wordTrace_append hprefix tailTrace_6861855
  have hstable : (prefixWord ++ tailWord_6861855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861855).length < 2 ^ (prefixWord ++ tailWord_6861855).sum := by decide
  have hdescent : baseEnd_6861855 < baseStart_6861855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861860 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6861860 : Nat := 118140960795 + 6861860 * 2 ^ 59
def prefixEnd_6861860 : Nat := 4983230072969 + 3 ^ 40 * 6861860 * 2
def baseEnd_6861860 : Nat := 3523432363860628174892887

theorem tailTrace_6861860 : CollatzResearch.WordTrace tailWord_6861860 prefixEnd_6861860 3523432363860628174892887 := by
  unfold tailWord_6861860
  simp only [CollatzResearch.WordTrace]
  refine ⟨125136297460330303616199517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166848396613773738154932689 125136297460330303616199517)
  ·
    refine ⟨46926111547623863856074819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125136297460330303616199517 46926111547623863856074819)
    ·
      refine ⟨70389167321435795784112229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46926111547623863856074819 70389167321435795784112229)
      ·
        refine ⟨13197968872769211709521043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70389167321435795784112229 13197968872769211709521043)
        ·
          refine ⟨19796953309153817564281565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197968872769211709521043 19796953309153817564281565)
          ·
            refine ⟨7423857490932681586605587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19796953309153817564281565 7423857490932681586605587)
            ·
              refine ⟨11135786236399022379908381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423857490932681586605587 11135786236399022379908381)
              ·
                refine ⟨4175919838649633392465643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11135786236399022379908381 4175919838649633392465643)
                ·
                  refine ⟨6263879757974450088698465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175919838649633392465643 6263879757974450088698465)
                  ·
                    refine ⟨4697909818480837566523849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263879757974450088698465 4697909818480837566523849)
                    ·
                      refine ⟨3523432363860628174892887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697909818480837566523849 3523432363860628174892887)
                      ·
                        rfl

theorem cell23_6861860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6861860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861860 prefixEnd_6861860 := by exact prefixLift 6861860
  have htrace : WordTrace (prefixWord ++ tailWord_6861860) baseStart_6861860 baseEnd_6861860 := by
    simpa [prefixWord, tailWord_6861860, baseEnd_6861860] using wordTrace_append hprefix tailTrace_6861860
  have hstable : (prefixWord ++ tailWord_6861860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861860).length < 2 ^ (prefixWord ++ tailWord_6861860).sum := by decide
  have hdescent : baseEnd_6861860 < baseStart_6861860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861876 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6861876 : Nat := 118140960795 + 6861876 * 2 ^ 59
def prefixEnd_6861876 : Nat := 4983230072969 + 3 ^ 40 * 6861876 * 2
def baseEnd_6861876 : Nat := 3523440579551100112292813

theorem tailTrace_6861876 : CollatzResearch.WordTrace tailWord_6861876 prefixEnd_6861876 3523440579551100112292813 := by
  unfold tailWord_6861876
  simp only [CollatzResearch.WordTrace]
  refine ⟨125136589244301320982490741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166848785659068427976654321 125136589244301320982490741)
  ·
    refine ⟨11731555241653248842108507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125136589244301320982490741 11731555241653248842108507)
    ·
      refine ⟨17597332862479873263162761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731555241653248842108507 17597332862479873263162761)
      ·
        refine ⟨13197999646859904947372071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17597332862479873263162761 13197999646859904947372071)
        ·
          refine ⟨19796999470289857421058107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197999646859904947372071 19796999470289857421058107)
          ·
            refine ⟨29695499205434786131587161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796999470289857421058107 29695499205434786131587161)
            ·
              refine ⟨22271624404076089598690371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29695499205434786131587161 22271624404076089598690371)
              ·
                refine ⟨33407436606114134398035557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22271624404076089598690371 33407436606114134398035557)
                ·
                  refine ⟨6263894363646400199631667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33407436606114134398035557 6263894363646400199631667)
                  ·
                    refine ⟨9395841545469600299447501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6263894363646400199631667 9395841545469600299447501)
                    ·
                      refine ⟨3523440579551100112292813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395841545469600299447501 3523440579551100112292813)
                      ·
                        rfl

theorem cell23_6861876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6861876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861876 prefixEnd_6861876 := by exact prefixLift 6861876
  have htrace : WordTrace (prefixWord ++ tailWord_6861876) baseStart_6861876 baseEnd_6861876 := by
    simpa [prefixWord, tailWord_6861876, baseEnd_6861876] using wordTrace_append hprefix tailTrace_6861876
  have hstable : (prefixWord ++ tailWord_6861876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861876).length < 2 ^ (prefixWord ++ tailWord_6861876).sum := by decide
  have hdescent : baseEnd_6861876 < baseStart_6861876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861905 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 7]
def baseStart_6861905 : Nat := 118140960795 + 6861905 * 2 ^ 59
def prefixEnd_6861905 : Nat := 4983230072969 + 3 ^ 40 * 6861905 * 2
def baseEnd_6861905 : Nat := 391495052276675610981131

theorem tailTrace_6861905 : CollatzResearch.WordTrace tailWord_6861905 prefixEnd_6861905 391495052276675610981131 := by
  unfold tailWord_6861905
  simp only [CollatzResearch.WordTrace]
  refine ⟨250274236205497579917787169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166849490803665053278524779 250274236205497579917787169)
  ·
    refine ⟨187705677154123184938340377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250274236205497579917787169 187705677154123184938340377)
    ·
      refine ⟨140779257865592388703755283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187705677154123184938340377 140779257865592388703755283)
      ·
        refine ⟨211168886798388583055632925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140779257865592388703755283 211168886798388583055632925)
        ·
          refine ⟨79188332549395718645862347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211168886798388583055632925 79188332549395718645862347)
          ·
            refine ⟨118782498824093577968793521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79188332549395718645862347 118782498824093577968793521)
            ·
              refine ⟨89086874118070183476595141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118782498824093577968793521 89086874118070183476595141)
              ·
                refine ⟨16703788897138159401861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89086874118070183476595141 16703788897138159401861589)
                ·
                  refine ⟨391495052276675610981131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16703788897138159401861589 391495052276675610981131)
                  ·
                    rfl

theorem cell23_6861905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_6861905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861905 prefixEnd_6861905 := by exact prefixLift 6861905
  have htrace : WordTrace (prefixWord ++ tailWord_6861905) baseStart_6861905 baseEnd_6861905 := by
    simpa [prefixWord, tailWord_6861905, baseEnd_6861905] using wordTrace_append hprefix tailTrace_6861905
  have hstable : (prefixWord ++ tailWord_6861905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861905).length < 2 ^ (prefixWord ++ tailWord_6861905).sum := by decide
  have hdescent : baseEnd_6861905 < baseStart_6861905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861932 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_6861932 : Nat := 118140960795 + 6861932 * 2 ^ 59
def prefixEnd_6861932 : Nat := 4983230072969 + 3 ^ 40 * 6861932 * 2
def baseEnd_6861932 : Nat := 3523469334467751893192555

theorem tailTrace_6861932 : CollatzResearch.WordTrace tailWord_6861932 prefixEnd_6861932 3523469334467751893192555 := by
  unfold tailWord_6861932
  simp only [CollatzResearch.WordTrace]
  refine ⟨125137610488199881764510025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166850147317599842352680033 125137610488199881764510025)
  ·
    refine ⟨93853207866149911323382519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125137610488199881764510025 93853207866149911323382519)
    ·
      refine ⟨140779811799224866985073779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93853207866149911323382519 140779811799224866985073779)
      ·
        refine ⟨211169717698837300477610669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140779811799224866985073779 211169717698837300477610669)
        ·
          refine ⟨79188644137063987679104001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211169717698837300477610669 79188644137063987679104001)
          ·
            refine ⟨59391483102797990759328001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79188644137063987679104001 59391483102797990759328001)
            ·
              refine ⟨44543612327098493069496001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59391483102797990759328001 44543612327098493069496001)
              ·
                refine ⟨33407709245323869802122001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44543612327098493069496001 33407709245323869802122001)
                ·
                  refine ⟨25055781933992902351591501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33407709245323869802122001 25055781933992902351591501)
                  ·
                    refine ⟨9395918225247338381846813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25055781933992902351591501 9395918225247338381846813)
                    ·
                      refine ⟨3523469334467751893192555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9395918225247338381846813 3523469334467751893192555)
                      ·
                        rfl

theorem cell23_6861932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_6861932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861932 prefixEnd_6861932 := by exact prefixLift 6861932
  have htrace : WordTrace (prefixWord ++ tailWord_6861932) baseStart_6861932 baseEnd_6861932 := by
    simpa [prefixWord, tailWord_6861932, baseEnd_6861932] using wordTrace_append hprefix tailTrace_6861932
  have hstable : (prefixWord ++ tailWord_6861932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861932).length < 2 ^ (prefixWord ++ tailWord_6861932).sum := by decide
  have hdescent : baseEnd_6861932 < baseStart_6861932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861933 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_6861933 : Nat := 118140960795 + 6861933 * 2 ^ 59
def prefixEnd_6861933 : Nat := 4983230072969 + 3 ^ 40 * 6861933 * 2
def baseEnd_6861933 : Nat := 3523469847948406389280051

theorem tailTrace_6861933 : CollatzResearch.WordTrace tailWord_6861933 prefixEnd_6861933 3523469847948406389280051 := by
  unfold tailWord_6861933
  simp only [CollatzResearch.WordTrace]
  refine ⟨250275257449396140699806453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166850171632930760466537635 250275257449396140699806453)
  ·
    refine ⟨23463305385880888190606855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250275257449396140699806453 23463305385880888190606855)
    ·
      refine ⟨35194958078821332285910283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23463305385880888190606855 35194958078821332285910283)
      ·
        refine ⟨52792437118231998428865425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35194958078821332285910283 52792437118231998428865425)
        ·
          refine ⟨39594327838673998821649069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52792437118231998428865425 39594327838673998821649069)
          ·
            refine ⟨14847872939502749558118401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39594327838673998821649069 14847872939502749558118401)
            ·
              refine ⟨11135904704627062168588801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14847872939502749558118401 11135904704627062168588801)
              ·
                refine ⟨8351928528470296626441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11135904704627062168588801 8351928528470296626441601)
                ·
                  refine ⟨6263946396352722469831201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351928528470296626441601 6263946396352722469831201)
                  ·
                    refine ⟨4697959797264541852373401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263946396352722469831201 4697959797264541852373401)
                    ·
                      refine ⟨3523469847948406389280051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697959797264541852373401 3523469847948406389280051)
                      ·
                        rfl

theorem cell23_6861933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_6861933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861933 prefixEnd_6861933 := by exact prefixLift 6861933
  have htrace : WordTrace (prefixWord ++ tailWord_6861933) baseStart_6861933 baseEnd_6861933 := by
    simpa [prefixWord, tailWord_6861933, baseEnd_6861933] using wordTrace_append hprefix tailTrace_6861933
  have hstable : (prefixWord ++ tailWord_6861933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861933).length < 2 ^ (prefixWord ++ tailWord_6861933).sum := by decide
  have hdescent : baseEnd_6861933 < baseStart_6861933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861989 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_6861989 : Nat := 118140960795 + 6861989 * 2 ^ 59
def prefixEnd_6861989 : Nat := 4983230072969 + 3 ^ 40 * 6861989 * 2
def baseEnd_6861989 : Nat := 3523498602865058170179793

theorem tailTrace_6861989 : CollatzResearch.WordTrace tailWord_6861989 prefixEnd_6861989 3523498602865058170179793 := by
  unfold tailWord_6861989
  simp only [CollatzResearch.WordTrace]
  refine ⟨250277299937193262263845021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166851533291462174842563347 250277299937193262263845021)
  ·
    refine ⟨93853987476447473348941883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250277299937193262263845021 93853987476447473348941883)
    ·
      refine ⟨140780981214671210023412825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93853987476447473348941883 140780981214671210023412825)
      ·
        refine ⟨105585735911003407517559619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140780981214671210023412825 105585735911003407517559619)
        ·
          refine ⟨158378603866505111276339429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105585735911003407517559619 158378603866505111276339429)
          ·
            refine ⟨29695988224969708364313643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158378603866505111276339429 29695988224969708364313643)
            ·
              refine ⟨44543982337454562546470465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29695988224969708364313643 44543982337454562546470465)
              ·
                refine ⟨33407986753090921909852849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44543982337454562546470465 33407986753090921909852849)
                ·
                  refine ⟨25055990064818191432389637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33407986753090921909852849 25055990064818191432389637)
                  ·
                    refine ⟨4697998137153410893573057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25055990064818191432389637 4697998137153410893573057)
                    ·
                      refine ⟨3523498602865058170179793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4697998137153410893573057 3523498602865058170179793)
                      ·
                        rfl

theorem cell23_6861989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_6861989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6861989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6861989 prefixEnd_6861989 := by exact prefixLift 6861989
  have htrace : WordTrace (prefixWord ++ tailWord_6861989) baseStart_6861989 baseEnd_6861989 := by
    simpa [prefixWord, tailWord_6861989, baseEnd_6861989] using wordTrace_append hprefix tailTrace_6861989
  have hstable : (prefixWord ++ tailWord_6861989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861989).length < 2 ^ (prefixWord ++ tailWord_6861989).sum := by decide
  have hdescent : baseEnd_6861989 < baseStart_6861989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862039 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_6862039 : Nat := 118140960795 + 6862039 * 2 ^ 59
def prefixEnd_6862039 : Nat := 4983230072969 + 3 ^ 40 * 6862039 * 2
def baseEnd_6862039 : Nat := 3523524276897782974554563

theorem tailTrace_6862039 : CollatzResearch.WordTrace tailWord_6862039 prefixEnd_6862039 3523524276897782974554563 := by
  unfold tailWord_6862039
  simp only [CollatzResearch.WordTrace]
  refine ⟨250279123587012120803165171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166852749058008080535443447 250279123587012120803165171)
  ·
    refine ⟨375418685380518181204747757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250279123587012120803165171 375418685380518181204747757)
    ·
      refine ⟨140782007017694317951780409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375418685380518181204747757 140782007017694317951780409)
      ·
        refine ⟨105586505263270738463835307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140782007017694317951780409 105586505263270738463835307)
        ·
          refine ⟨158379757894906107695752961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105586505263270738463835307 158379757894906107695752961)
          ·
            refine ⟨118784818421179580771814721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158379757894906107695752961 118784818421179580771814721)
            ·
              refine ⟨89088613815884685578861041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118784818421179580771814721 89088613815884685578861041)
              ·
                refine ⟨66816460361913514184145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89088613815884685578861041 66816460361913514184145781)
                ·
                  refine ⟨6264043158929391954763667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66816460361913514184145781 6264043158929391954763667)
                  ·
                    refine ⟨9396064738394087932145501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264043158929391954763667 9396064738394087932145501)
                    ·
                      refine ⟨3523524276897782974554563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396064738394087932145501 3523524276897782974554563)
                      ·
                        rfl

theorem cell23_6862039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_6862039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862039 prefixEnd_6862039 := by exact prefixLift 6862039
  have htrace : WordTrace (prefixWord ++ tailWord_6862039) baseStart_6862039 baseEnd_6862039 := by
    simpa [prefixWord, tailWord_6862039, baseEnd_6862039] using wordTrace_append hprefix tailTrace_6862039
  have hstable : (prefixWord ++ tailWord_6862039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862039).length < 2 ^ (prefixWord ++ tailWord_6862039).sum := by decide
  have hdescent : baseEnd_6862039 < baseStart_6862039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862042 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_6862042 : Nat := 118140960795 + 6862042 * 2 ^ 59
def prefixEnd_6862042 : Nat := 4983230072969 + 3 ^ 40 * 6862042 * 2
def baseEnd_6862042 : Nat := 1174508605779915487605683

theorem tailTrace_6862042 : CollatzResearch.WordTrace tailWord_6862042 prefixEnd_6862042 1174508605779915487605683 := by
  unfold tailWord_6862042
  simp only [CollatzResearch.WordTrace]
  refine ⟨62569808251500313078881095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166852822004000834877016253 62569808251500313078881095)
  ·
    refine ⟨93854712377250469618321643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62569808251500313078881095 93854712377250469618321643)
    ·
      refine ⟨140782068565875704427482465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93854712377250469618321643 140782068565875704427482465)
      ·
        refine ⟨105586551424406778320611849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140782068565875704427482465 105586551424406778320611849)
        ·
          refine ⟨79189913568305083740458887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105586551424406778320611849 79189913568305083740458887)
          ·
            refine ⟨118784870352457625610688331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79189913568305083740458887 118784870352457625610688331)
            ·
              refine ⟨178177305528686438416032497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118784870352457625610688331 178177305528686438416032497)
              ·
                refine ⟨133632979146514828812024373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178177305528686438416032497 133632979146514828812024373)
                ·
                  refine ⟨12528091794985765201127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133632979146514828812024373 12528091794985765201127285)
                  ·
                    refine ⟨1174508605779915487605683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12528091794985765201127285 1174508605779915487605683)
                    ·
                      rfl

theorem cell23_6862042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_6862042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862042 prefixEnd_6862042 := by exact prefixLift 6862042
  have htrace : WordTrace (prefixWord ++ tailWord_6862042) baseStart_6862042 baseEnd_6862042 := by
    simpa [prefixWord, tailWord_6862042, baseEnd_6862042] using wordTrace_append hprefix tailTrace_6862042
  have hstable : (prefixWord ++ tailWord_6862042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862042).length < 2 ^ (prefixWord ++ tailWord_6862042).sum := by decide
  have hdescent : baseEnd_6862042 < baseStart_6862042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862063 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 6]
def baseStart_6862063 : Nat := 118140960795 + 6862063 * 2 ^ 59
def prefixEnd_6862063 : Nat := 4983230072969 + 3 ^ 40 * 6862063 * 2
def baseEnd_6862063 : Nat := 391504066714832320072717

theorem tailTrace_6862063 : CollatzResearch.WordTrace tailWord_6862063 prefixEnd_6862063 391504066714832320072717 := by
  unfold tailWord_6862063
  simp only [CollatzResearch.WordTrace]
  refine ⟨250279998938925172902038843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166853332625950115268025895 250279998938925172902038843)
  ·
    refine ⟨375419998408387759353058265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250279998938925172902038843 375419998408387759353058265)
    ·
      refine ⟨281564998806290819514793699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375419998408387759353058265 281564998806290819514793699)
      ·
        refine ⟨422347498209436229272190549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281564998806290819514793699 422347498209436229272190549)
        ·
          refine ⟨4949384744641830811783483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 422347498209436229272190549 4949384744641830811783483)
          ·
            refine ⟨7424077116962746217675225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949384744641830811783483 7424077116962746217675225)
            ·
              refine ⟨5568057837722059663256419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7424077116962746217675225 5568057837722059663256419)
              ·
                refine ⟨8352086756583089494884629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568057837722059663256419 8352086756583089494884629)
                ·
                  refine ⟨391504066714832320072717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8352086756583089494884629 391504066714832320072717)
                  ·
                    rfl

theorem cell23_6862063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 6].length) (baseStart_6862063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862063 prefixEnd_6862063 := by exact prefixLift 6862063
  have htrace : WordTrace (prefixWord ++ tailWord_6862063) baseStart_6862063 baseEnd_6862063 := by
    simpa [prefixWord, tailWord_6862063, baseEnd_6862063] using wordTrace_append hprefix tailTrace_6862063
  have hstable : (prefixWord ++ tailWord_6862063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862063).length < 2 ^ (prefixWord ++ tailWord_6862063).sum := by decide
  have hdescent : baseEnd_6862063 < baseStart_6862063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862079 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_6862079 : Nat := 118140960795 + 6862079 * 2 ^ 59
def prefixEnd_6862079 : Nat := 4983230072969 + 3 ^ 40 * 6862079 * 2
def baseEnd_6862079 : Nat := 3523544816123962818054379

theorem tailTrace_6862079 : CollatzResearch.WordTrace tailWord_6862079 prefixEnd_6862079 3523544816123962818054379 := by
  unfold tailWord_6862079
  simp only [CollatzResearch.WordTrace]
  refine ⟨250280582506867207634621291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166853721671244805089747527 250280582506867207634621291)
  ·
    refine ⟨375420873760300811451931937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250280582506867207634621291 375420873760300811451931937)
    ·
      refine ⟨281565655320225608588948953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375420873760300811451931937 281565655320225608588948953)
      ·
        refine ⟨211174241490169206441711715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281565655320225608588948953 211174241490169206441711715)
        ·
          refine ⟨316761362235253809662567573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211174241490169206441711715 316761362235253809662567573)
          ·
            refine ⟨14848188854777522327932855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316761362235253809662567573 14848188854777522327932855)
            ·
              refine ⟨22272283282166283491899283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14848188854777522327932855 22272283282166283491899283)
              ·
                refine ⟨33408424923249425237848925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22272283282166283491899283 33408424923249425237848925)
                ·
                  refine ⟨12528159346218534464193347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33408424923249425237848925 12528159346218534464193347)
                  ·
                    refine ⟨18792239019327801696290021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12528159346218534464193347 18792239019327801696290021)
                    ·
                      refine ⟨3523544816123962818054379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18792239019327801696290021 3523544816123962818054379)
                      ·
                        rfl

theorem cell23_6862079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_6862079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862079 prefixEnd_6862079 := by exact prefixLift 6862079
  have htrace : WordTrace (prefixWord ++ tailWord_6862079) baseStart_6862079 baseEnd_6862079 := by
    simpa [prefixWord, tailWord_6862079, baseEnd_6862079] using wordTrace_append hprefix tailTrace_6862079
  have hstable : (prefixWord ++ tailWord_6862079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862079).length < 2 ^ (prefixWord ++ tailWord_6862079).sum := by decide
  have hdescent : baseEnd_6862079 < baseStart_6862079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862106 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_6862106 : Nat := 118140960795 + 6862106 * 2 ^ 59
def prefixEnd_6862106 : Nat := 4983230072969 + 3 ^ 40 * 6862106 * 2
def baseEnd_6862106 : Nat := 1174519560033878070805585

theorem tailTrace_6862106 : CollatzResearch.WordTrace tailWord_6862106 prefixEnd_6862106 1174519560033878070805585 := by
  unfold tailWord_6862106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62570391819442347811463543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166854378185179594163902781 62570391819442347811463543)
  ·
    refine ⟨93855587729163521717195315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62570391819442347811463543 93855587729163521717195315)
    ·
      refine ⟨140783381593745282575792973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93855587729163521717195315 140783381593745282575792973)
      ·
        refine ⟨52793768097654480965922365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140783381593745282575792973 52793768097654480965922365)
        ·
          refine ⟨19797663036620430362220887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52793768097654480965922365 19797663036620430362220887)
          ·
            refine ⟨29696494554930645543331331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19797663036620430362220887 29696494554930645543331331)
            ·
              refine ⟨44544741832395968314996997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29696494554930645543331331 44544741832395968314996997)
              ·
                refine ⟨8352139093574244059061937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44544741832395968314996997 8352139093574244059061937)
                ·
                  refine ⟨6264104320180683044296453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8352139093574244059061937 6264104320180683044296453)
                  ·
                    refine ⟨1174519560033878070805585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264104320180683044296453 1174519560033878070805585)
                    ·
                      rfl

theorem cell23_6862106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_6862106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862106 prefixEnd_6862106 := by exact prefixLift 6862106
  have htrace : WordTrace (prefixWord ++ tailWord_6862106) baseStart_6862106 baseEnd_6862106 := by
    simpa [prefixWord, tailWord_6862106, baseEnd_6862106] using wordTrace_append hprefix tailTrace_6862106
  have hstable : (prefixWord ++ tailWord_6862106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862106).length < 2 ^ (prefixWord ++ tailWord_6862106).sum := by decide
  have hdescent : baseEnd_6862106 < baseStart_6862106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862134 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6862134 : Nat := 118140960795 + 6862134 * 2 ^ 59
def prefixEnd_6862134 : Nat := 4983230072969 + 3 ^ 40 * 6862134 * 2
def baseEnd_6862134 : Nat := 3523573057559960102866627

theorem tailTrace_6862134 : CollatzResearch.WordTrace tailWord_6862134 prefixEnd_6862134 3523573057559960102866627 := by
  unfold tailWord_6862134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642661782604247001742091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166855059014445301351915637 15642661782604247001742091)
  ·
    refine ⟨23463992673906370502613137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642661782604247001742091 23463992673906370502613137)
    ·
      refine ⟨17597994505429777876959853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23463992673906370502613137 17597994505429777876959853)
      ·
        refine ⟨6599247939536166703859945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17597994505429777876959853 6599247939536166703859945)
        ·
          refine ⟨4949435954652125027894959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599247939536166703859945 4949435954652125027894959)
          ·
            refine ⟨7424153931978187541842439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949435954652125027894959 7424153931978187541842439)
            ·
              refine ⟨11136230897967281312763659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424153931978187541842439 11136230897967281312763659)
              ·
                refine ⟨16704346346950921969145489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11136230897967281312763659 16704346346950921969145489)
                ·
                  refine ⟨12528259760213191476859117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16704346346950921969145489 12528259760213191476859117)
                  ·
                    refine ⟨4698097410079946803822169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12528259760213191476859117 4698097410079946803822169)
                    ·
                      refine ⟨3523573057559960102866627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698097410079946803822169 3523573057559960102866627)
                      ·
                        rfl

theorem cell23_6862134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6862134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862134 prefixEnd_6862134 := by exact prefixLift 6862134
  have htrace : WordTrace (prefixWord ++ tailWord_6862134) baseStart_6862134 baseEnd_6862134 := by
    simpa [prefixWord, tailWord_6862134, baseEnd_6862134] using wordTrace_append hprefix tailTrace_6862134
  have hstable : (prefixWord ++ tailWord_6862134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862134).length < 2 ^ (prefixWord ++ tailWord_6862134).sum := by decide
  have hdescent : baseEnd_6862134 < baseStart_6862134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862157 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_6862157 : Nat := 118140960795 + 6862157 * 2 ^ 59
def prefixEnd_6862157 : Nat := 4983230072969 + 3 ^ 40 * 6862157 * 2
def baseEnd_6862157 : Nat := 1174528289205004504293007

theorem tailTrace_6862157 : CollatzResearch.WordTrace tailWord_6862157 prefixEnd_6862157 1174528289205004504293007 := by
  unfold tailWord_6862157
  simp only [CollatzResearch.WordTrace]
  refine ⟨250283427400584626955960725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166855618267056417970640483 250283427400584626955960725)
  ·
    refine ⟨11732035659402404388560659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250283427400584626955960725 11732035659402404388560659)
    ·
      refine ⟨17598053489103606582840989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11732035659402404388560659 17598053489103606582840989)
      ·
        refine ⟨6599270058413852468565371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17598053489103606582840989 6599270058413852468565371)
        ·
          refine ⟨9898905087620778702848057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599270058413852468565371 9898905087620778702848057)
          ·
            refine ⟨7424178815715584027136043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9898905087620778702848057 7424178815715584027136043)
            ·
              refine ⟨11136268223573376040704065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424178815715584027136043 11136268223573376040704065)
              ·
                refine ⟨8352201167680032030528049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11136268223573376040704065 8352201167680032030528049)
                ·
                  refine ⟨6264150875760024022896037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8352201167680032030528049 6264150875760024022896037)
                  ·
                    refine ⟨1174528289205004504293007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264150875760024022896037 1174528289205004504293007)
                    ·
                      rfl

theorem cell23_6862157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_6862157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862157 prefixEnd_6862157 := by exact prefixLift 6862157
  have htrace : WordTrace (prefixWord ++ tailWord_6862157) baseStart_6862157 baseEnd_6862157 := by
    simpa [prefixWord, tailWord_6862157, baseEnd_6862157] using wordTrace_append hprefix tailTrace_6862157
  have hstable : (prefixWord ++ tailWord_6862157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862157).length < 2 ^ (prefixWord ++ tailWord_6862157).sum := by decide
  have hdescent : baseEnd_6862157 < baseStart_6862157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862179 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 6]
def baseStart_6862179 : Nat := 118140960795 + 6862179 * 2 ^ 59
def prefixEnd_6862179 : Nat := 4983230072969 + 3 ^ 40 * 6862179 * 2
def baseEnd_6862179 : Nat := 1174532054729804142267973

theorem tailTrace_6862179 : CollatzResearch.WordTrace tailWord_6862179 prefixEnd_6862179 1174532054729804142267973 := by
  unfold tailWord_6862179
  simp only [CollatzResearch.WordTrace]
  refine ⟨250284229806504924713261591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166856153204336616475507727 250284229806504924713261591)
  ·
    refine ⟨375426344709757387069892387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250284229806504924713261591 375426344709757387069892387)
    ·
      refine ⟨563139517064636080604838581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375426344709757387069892387 563139517064636080604838581)
      ·
        refine ⟨52794329724809632556703617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 563139517064636080604838581 52794329724809632556703617)
        ·
          refine ⟨39595747293607224417527713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52794329724809632556703617 39595747293607224417527713)
          ·
            refine ⟨29696810470205418313145785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39595747293607224417527713 29696810470205418313145785)
            ·
              refine ⟨22272607852654063734859339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29696810470205418313145785 22272607852654063734859339)
              ·
                refine ⟨33408911778981095602289009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22272607852654063734859339 33408911778981095602289009)
                ·
                  refine ⟨25056683834235821701716757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33408911778981095602289009 25056683834235821701716757)
                  ·
                    refine ⟨1174532054729804142267973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25056683834235821701716757 1174532054729804142267973)
                    ·
                      rfl

theorem cell23_6862179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_6862179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862179 prefixEnd_6862179 := by exact prefixLift 6862179
  have htrace : WordTrace (prefixWord ++ tailWord_6862179) baseStart_6862179 baseEnd_6862179 := by
    simpa [prefixWord, tailWord_6862179, baseEnd_6862179] using wordTrace_append hprefix tailTrace_6862179
  have hstable : (prefixWord ++ tailWord_6862179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862179).length < 2 ^ (prefixWord ++ tailWord_6862179).sum := by decide
  have hdescent : baseEnd_6862179 < baseStart_6862179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862180 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_6862180 : Nat := 118140960795 + 6862180 * 2 ^ 59
def prefixEnd_6862180 : Nat := 4983230072969 + 3 ^ 40 * 6862180 * 2
def baseEnd_6862180 : Nat := 3523596677670066922891415

theorem tailTrace_6862180 : CollatzResearch.WordTrace tailWord_6862180 prefixEnd_6862180 3523596677670066922891415 := by
  unfold tailWord_6862180
  simp only [CollatzResearch.WordTrace]
  refine ⟨125142133139750650942023997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166856177519667534589365329 125142133139750650942023997)
  ·
    refine ⟨46928299927406494103258999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125142133139750650942023997 46928299927406494103258999)
    ·
      refine ⟨70392449891109741154888499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46928299927406494103258999 70392449891109741154888499)
      ·
        refine ⟨105588674836664611732332749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70392449891109741154888499 105588674836664611732332749)
        ·
          refine ⟨39595753063749229399624781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105588674836664611732332749 39595753063749229399624781)
          ·
            refine ⟨14848407398905961024859293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39595753063749229399624781 14848407398905961024859293)
            ·
              refine ⟨5568152774589735384322235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14848407398905961024859293 5568152774589735384322235)
              ·
                refine ⟨8352229161884603076483353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568152774589735384322235 8352229161884603076483353)
                ·
                  refine ⟨6264171871413452307362515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8352229161884603076483353 6264171871413452307362515)
                  ·
                    refine ⟨9396257807120178461043773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264171871413452307362515 9396257807120178461043773)
                    ·
                      refine ⟨3523596677670066922891415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396257807120178461043773 3523596677670066922891415)
                      ·
                        rfl

theorem cell23_6862180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_6862180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862180 prefixEnd_6862180 := by exact prefixLift 6862180
  have htrace : WordTrace (prefixWord ++ tailWord_6862180) baseStart_6862180 baseEnd_6862180 := by
    simpa [prefixWord, tailWord_6862180, baseEnd_6862180] using wordTrace_append hprefix tailTrace_6862180
  have hstable : (prefixWord ++ tailWord_6862180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862180).length < 2 ^ (prefixWord ++ tailWord_6862180).sum := by decide
  have hdescent : baseEnd_6862180 < baseStart_6862180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862237 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_6862237 : Nat := 118140960795 + 6862237 * 2 ^ 59
def prefixEnd_6862237 : Nat := 4983230072969 + 3 ^ 40 * 6862237 * 2
def baseEnd_6862237 : Nat := 3523625946067373199878653

theorem tailTrace_6862237 : CollatzResearch.WordTrace tailWord_6862237 prefixEnd_6862237 3523625946067373199878653 := by
  unfold tailWord_6862237
  simp only [CollatzResearch.WordTrace]
  refine ⟨250286345240294800618872965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166857563493529867079248643 250286345240294800618872965)
  ·
    refine ⟨46928689732555275116038681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250286345240294800618872965 46928689732555275116038681)
    ·
      refine ⟨35196517299416456337029011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46928689732555275116038681 35196517299416456337029011)
      ·
        refine ⟨52794775949124684505543517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35196517299416456337029011 52794775949124684505543517)
        ·
          refine ⟨19798040980921756689578819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52794775949124684505543517 19798040980921756689578819)
          ·
            refine ⟨29697061471382635034368229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19798040980921756689578819 29697061471382635034368229)
            ·
              refine ⟨5568199025884244068944043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29697061471382635034368229 5568199025884244068944043)
              ·
                refine ⟨8352298538826366103416065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568199025884244068944043 8352298538826366103416065)
                ·
                  refine ⟨6264223904119774577562049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8352298538826366103416065 6264223904119774577562049)
                  ·
                    refine ⟨4698167928089830933171537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6264223904119774577562049 4698167928089830933171537)
                    ·
                      refine ⟨3523625946067373199878653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698167928089830933171537 3523625946067373199878653)
                      ·
                        rfl

theorem cell23_6862237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_6862237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862237 prefixEnd_6862237 := by exact prefixLift 6862237
  have htrace : WordTrace (prefixWord ++ tailWord_6862237) baseStart_6862237 baseEnd_6862237 := by
    simpa [prefixWord, tailWord_6862237, baseEnd_6862237] using wordTrace_append hprefix tailTrace_6862237
  have hstable : (prefixWord ++ tailWord_6862237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862237).length < 2 ^ (prefixWord ++ tailWord_6862237).sum := by decide
  have hdescent : baseEnd_6862237 < baseStart_6862237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862259 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_6862259 : Nat := 118140960795 + 6862259 * 2 ^ 59
def prefixEnd_6862259 : Nat := 4983230072969 + 3 ^ 40 * 6862259 * 2
def baseEnd_6862259 : Nat := 3523637242641772113803551

theorem tailTrace_6862259 : CollatzResearch.WordTrace tailWord_6862259 prefixEnd_6862259 3523637242641772113803551 := by
  unfold tailWord_6862259
  simp only [CollatzResearch.WordTrace]
  refine ⟨250287147646215098376173831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166858098430810065584115887 250287147646215098376173831)
  ·
    refine ⟨375430721469322647564260747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250287147646215098376173831 375430721469322647564260747)
    ·
      refine ⟨563146082203983971346391121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375430721469322647564260747 563146082203983971346391121)
      ·
        refine ⟨422359561652987978509793341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563146082203983971346391121 422359561652987978509793341)
        ·
          refine ⟨158384835619870491941172503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422359561652987978509793341 158384835619870491941172503)
          ·
            refine ⟨237577253429805737911758755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158384835619870491941172503 237577253429805737911758755)
            ·
              refine ⟨356365880144708606867638133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237577253429805737911758755 356365880144708606867638133)
              ·
                refine ⟨33409301263566431893841075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356365880144708606867638133 33409301263566431893841075)
                ·
                  refine ⟨50113951895349647840761613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33409301263566431893841075 50113951895349647840761613)
                  ·
                    refine ⟨18792731960756117940285605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50113951895349647840761613 18792731960756117940285605)
                    ·
                      refine ⟨3523637242641772113803551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18792731960756117940285605 3523637242641772113803551)
                      ·
                        rfl

theorem cell23_6862259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_6862259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862259 prefixEnd_6862259 := by exact prefixLift 6862259
  have htrace : WordTrace (prefixWord ++ tailWord_6862259) baseStart_6862259 baseEnd_6862259 := by
    simpa [prefixWord, tailWord_6862259, baseEnd_6862259] using wordTrace_append hprefix tailTrace_6862259
  have hstable : (prefixWord ++ tailWord_6862259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862259).length < 2 ^ (prefixWord ++ tailWord_6862259).sum := by decide
  have hdescent : baseEnd_6862259 < baseStart_6862259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862279 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_6862279 : Nat := 118140960795 + 6862279 * 2 ^ 59
def prefixEnd_6862279 : Nat := 4983230072969 + 3 ^ 40 * 6862279 * 2
def baseEnd_6862279 : Nat := 3523647512254862035553459

theorem tailTrace_6862279 : CollatzResearch.WordTrace tailWord_6862279 prefixEnd_6862279 3523647512254862035553459 := by
  unfold tailWord_6862279
  simp only [CollatzResearch.WordTrace]
  refine ⟨250287877106142641791901891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166858584737428427861267927 250287877106142641791901891)
  ·
    refine ⟨375431815659213962687852837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250287877106142641791901891 375431815659213962687852837)
    ·
      refine ⟨70393465436102618003972407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375431815659213962687852837 70393465436102618003972407)
      ·
        refine ⟨105590198154153927005958611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70393465436102618003972407 105590198154153927005958611)
        ·
          refine ⟨158385297231230890508937917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105590198154153927005958611 158385297231230890508937917)
          ·
            refine ⟨59394486461711583940851719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158385297231230890508937917 59394486461711583940851719)
            ·
              refine ⟨89091729692567375911277579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59394486461711583940851719 89091729692567375911277579)
              ·
                refine ⟨133637594538851063866916369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89091729692567375911277579 133637594538851063866916369)
                ·
                  refine ⟨100228195904138297900187277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133637594538851063866916369 100228195904138297900187277)
                  ·
                    refine ⟨37585573464051861712570229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100228195904138297900187277 37585573464051861712570229)
                    ·
                      refine ⟨3523647512254862035553459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37585573464051861712570229 3523647512254862035553459)
                      ·
                        rfl

theorem cell23_6862279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_6862279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862279 prefixEnd_6862279 := by exact prefixLift 6862279
  have htrace : WordTrace (prefixWord ++ tailWord_6862279) baseStart_6862279 baseEnd_6862279 := by
    simpa [prefixWord, tailWord_6862279, baseEnd_6862279] using wordTrace_append hprefix tailTrace_6862279
  have hstable : (prefixWord ++ tailWord_6862279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862279).length < 2 ^ (prefixWord ++ tailWord_6862279).sum := by decide
  have hdescent : baseEnd_6862279 < baseStart_6862279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862289 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_6862289 : Nat := 118140960795 + 6862289 * 2 ^ 59
def prefixEnd_6862289 : Nat := 4983230072969 + 3 ^ 40 * 6862289 * 2
def baseEnd_6862289 : Nat := 3523652647061406996428413

theorem tailTrace_6862289 : CollatzResearch.WordTrace tailWord_6862289 prefixEnd_6862289 3523652647061406996428413 := by
  unfold tailWord_6862289
  simp only [CollatzResearch.WordTrace]
  refine ⟨250288241836106413499765921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166858827890737608999843947 250288241836106413499765921)
  ·
    refine ⟨187716181377079810124824441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250288241836106413499765921 187716181377079810124824441)
    ·
      refine ⟨140787136032809857593618331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187716181377079810124824441 140787136032809857593618331)
      ·
        refine ⟨211180704049214786390427497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140787136032809857593618331 211180704049214786390427497)
        ·
          refine ⟨158385528036911089792820623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211180704049214786390427497 158385528036911089792820623)
          ·
            refine ⟨237578292055366634689230935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158385528036911089792820623 237578292055366634689230935)
            ·
              refine ⟨356367438083049952033846403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237578292055366634689230935 356367438083049952033846403)
              ·
                refine ⟨534551157124574928050769605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356367438083049952033846403 534551157124574928050769605)
                ·
                  refine ⟨100228341960857799009519301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534551157124574928050769605 100228341960857799009519301)
                  ·
                    refine ⟨18792814117660837314284869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100228341960857799009519301 18792814117660837314284869)
                    ·
                      refine ⟨3523652647061406996428413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18792814117660837314284869 3523652647061406996428413)
                      ·
                        rfl

theorem cell23_6862289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_6862289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862289 prefixEnd_6862289 := by exact prefixLift 6862289
  have htrace : WordTrace (prefixWord ++ tailWord_6862289) baseStart_6862289 baseEnd_6862289 := by
    simpa [prefixWord, tailWord_6862289, baseEnd_6862289] using wordTrace_append hprefix tailTrace_6862289
  have hstable : (prefixWord ++ tailWord_6862289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862289).length < 2 ^ (prefixWord ++ tailWord_6862289).sum := by decide
  have hdescent : baseEnd_6862289 < baseStart_6862289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862293 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6862293 : Nat := 118140960795 + 6862293 * 2 ^ 59
def prefixEnd_6862293 : Nat := 4983230072969 + 3 ^ 40 * 6862293 * 2
def baseEnd_6862293 : Nat := 3523654700984024980778395

theorem tailTrace_6862293 : CollatzResearch.WordTrace tailWord_6862293 prefixEnd_6862293 3523654700984024980778395 := by
  unfold tailWord_6862293
  simp only [CollatzResearch.WordTrace]
  refine ⟨250288387728091922182911533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166858925152061281455274355 250288387728091922182911533)
  ·
    refine ⟨93858145398034470818591825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250288387728091922182911533 93858145398034470818591825)
    ·
      refine ⟨70393609048525853113943869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93858145398034470818591825 70393609048525853113943869)
      ·
        refine ⟨26397603393197194917728951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70393609048525853113943869 26397603393197194917728951)
        ·
          refine ⟨39596405089795792376593427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26397603393197194917728951 39596405089795792376593427)
          ·
            refine ⟨59394607634693688564890141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39596405089795792376593427 59394607634693688564890141)
            ·
              refine ⟨22272977863010133211833803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59394607634693688564890141 22272977863010133211833803)
              ·
                refine ⟨33409466794515199817750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22272977863010133211833803 33409466794515199817750705)
                ·
                  refine ⟨25057100095886399863313029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33409466794515199817750705 25057100095886399863313029)
                  ·
                    refine ⟨4698206267978699974371193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25057100095886399863313029 4698206267978699974371193)
                    ·
                      refine ⟨3523654700984024980778395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698206267978699974371193 3523654700984024980778395)
                      ·
                        rfl

theorem cell23_6862293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6862293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862293 prefixEnd_6862293 := by exact prefixLift 6862293
  have htrace : WordTrace (prefixWord ++ tailWord_6862293) baseStart_6862293 baseEnd_6862293 := by
    simpa [prefixWord, tailWord_6862293, baseEnd_6862293] using wordTrace_append hprefix tailTrace_6862293
  have hstable : (prefixWord ++ tailWord_6862293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862293).length < 2 ^ (prefixWord ++ tailWord_6862293).sum := by decide
  have hdescent : baseEnd_6862293 < baseStart_6862293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862296 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_6862296 : Nat := 118140960795 + 6862296 * 2 ^ 59
def prefixEnd_6862296 : Nat := 4983230072969 + 3 ^ 40 * 6862296 * 2
def baseEnd_6862296 : Nat := 3523656241425988469040881

theorem tailTrace_6862296 : CollatzResearch.WordTrace tailWord_6862296 prefixEnd_6862296 3523656241425988469040881 := by
  unfold tailWord_6862296
  simp only [CollatzResearch.WordTrace]
  refine ⟨125144248573540526847635371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166858998098054035796847161 125144248573540526847635371)
  ·
    refine ⟨187716372860310790271453057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125144248573540526847635371 187716372860310790271453057)
    ·
      refine ⟨140787279645233092703589793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187716372860310790271453057 140787279645233092703589793)
      ·
        refine ⟨105590459733924819527692345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140787279645233092703589793 105590459733924819527692345)
        ·
          refine ⟨79192844800443614645769259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105590459733924819527692345 79192844800443614645769259)
          ·
            refine ⟨118789267200665421968653889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79192844800443614645769259 118789267200665421968653889)
            ·
              refine ⟨89091950400499066476490417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118789267200665421968653889 89091950400499066476490417)
              ·
                refine ⟨66818962800374299857367813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89091950400499066476490417 66818962800374299857367813)
                ·
                  refine ⟨12528555525070181223256465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66818962800374299857367813 12528555525070181223256465)
                  ·
                    refine ⟨9396416643802635917442349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12528555525070181223256465 9396416643802635917442349)
                    ·
                      refine ⟨3523656241425988469040881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396416643802635917442349 3523656241425988469040881)
                      ·
                        rfl

theorem cell23_6862296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_6862296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862296 prefixEnd_6862296 := by exact prefixLift 6862296
  have htrace : WordTrace (prefixWord ++ tailWord_6862296) baseStart_6862296 baseEnd_6862296 := by
    simpa [prefixWord, tailWord_6862296, baseEnd_6862296] using wordTrace_append hprefix tailTrace_6862296
  have hstable : (prefixWord ++ tailWord_6862296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862296).length < 2 ^ (prefixWord ++ tailWord_6862296).sum := by decide
  have hdescent : baseEnd_6862296 < baseStart_6862296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862320 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 1, 4]
def baseStart_6862320 : Nat := 118140960795 + 6862320 * 2 ^ 59
def prefixEnd_6862320 : Nat := 4983230072969 + 3 ^ 40 * 6862320 * 2
def baseEnd_6862320 : Nat := 1174556188320565458380257

theorem tailTrace_6862320 : CollatzResearch.WordTrace tailWord_6862320 prefixEnd_6862320 1174556188320565458380257 := by
  unfold tailWord_6862320
  simp only [CollatzResearch.WordTrace]
  refine ⟨125144686249497052897072207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166859581665996070529429609 125144686249497052897072207)
  ·
    refine ⟨187717029374245579345608311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125144686249497052897072207 187717029374245579345608311)
    ·
      refine ⟨281575544061368369018412467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187717029374245579345608311 281575544061368369018412467)
      ·
        refine ⟨422363316092052553527618701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281575544061368369018412467 422363316092052553527618701)
        ·
          refine ⟨158386243534519707572857013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422363316092052553527618701 158386243534519707572857013)
          ·
            refine ⟨14848710331361222584955345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158386243534519707572857013 14848710331361222584955345)
            ·
              refine ⟨11136532748520916938716509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14848710331361222584955345 11136532748520916938716509)
              ·
                refine ⟨4176199780695343852018691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11136532748520916938716509 4176199780695343852018691)
                ·
                  refine ⟨6264299671043015778028037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176199780695343852018691 6264299671043015778028037)
                  ·
                    refine ⟨1174556188320565458380257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264299671043015778028037 1174556188320565458380257)
                    ·
                      rfl

theorem cell23_6862320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_6862320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862320 prefixEnd_6862320 := by exact prefixLift 6862320
  have htrace : WordTrace (prefixWord ++ tailWord_6862320) baseStart_6862320 baseEnd_6862320 := by
    simpa [prefixWord, tailWord_6862320, baseEnd_6862320] using wordTrace_append hprefix tailTrace_6862320
  have hstable : (prefixWord ++ tailWord_6862320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862320).length < 2 ^ (prefixWord ++ tailWord_6862320).sum := by decide
  have hdescent : baseEnd_6862320 < baseStart_6862320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862333 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 6]
def baseStart_6862333 : Nat := 118140960795 + 6862333 * 2 ^ 59
def prefixEnd_6862333 : Nat := 4983230072969 + 3 ^ 40 * 6862333 * 2
def baseEnd_6862333 : Nat := 391519471134467202697579

theorem tailTrace_6862333 : CollatzResearch.WordTrace tailWord_6862333 prefixEnd_6862333 391519471134467202697579 := by
  unfold tailWord_6862333
  simp only [CollatzResearch.WordTrace]
  refine ⟨250289846647947009014367653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166859897765298006009578435 250289846647947009014367653)
  ·
    refine ⟨46929346246490064190193935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250289846647947009014367653 46929346246490064190193935)
    ·
      refine ⟨70394019369735096285290903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46929346246490064190193935 70394019369735096285290903)
      ·
        refine ⟨105591029054602644427936355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70394019369735096285290903 105591029054602644427936355)
        ·
          refine ⟨158386543581903966641904533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105591029054602644427936355 158386543581903966641904533)
          ·
            refine ⟨7424369230401748436339275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158386543581903966641904533 7424369230401748436339275)
            ·
              refine ⟨11136553845602622654508913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424369230401748436339275 11136553845602622654508913)
              ·
                refine ⟨8352415384201966990881685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11136553845602622654508913 8352415384201966990881685)
                ·
                  refine ⟨391519471134467202697579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8352415384201966990881685 391519471134467202697579)
                  ·
                    rfl

theorem cell23_6862333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_6862333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862333 prefixEnd_6862333 := by exact prefixLift 6862333
  have htrace : WordTrace (prefixWord ++ tailWord_6862333) baseStart_6862333 baseEnd_6862333 := by
    simpa [prefixWord, tailWord_6862333, baseEnd_6862333] using wordTrace_append hprefix tailTrace_6862333
  have hstable : (prefixWord ++ tailWord_6862333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862333).length < 2 ^ (prefixWord ++ tailWord_6862333).sum := by decide
  have hdescent : baseEnd_6862333 < baseStart_6862333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862339 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_6862339 : Nat := 118140960795 + 6862339 * 2 ^ 59
def prefixEnd_6862339 : Nat := 4983230072969 + 3 ^ 40 * 6862339 * 2
def baseEnd_6862339 : Nat := 3523678321094131800803183

theorem tailTrace_6862339 : CollatzResearch.WordTrace tailWord_6862339 prefixEnd_6862339 3523678321094131800803183 := by
  unfold tailWord_6862339
  simp only [CollatzResearch.WordTrace]
  refine ⟨250290065485925272039086071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166860043657283514692724047 250290065485925272039086071)
  ·
    refine ⟨375435098228887908058629107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250290065485925272039086071 375435098228887908058629107)
    ·
      refine ⟨563152647343331862087943661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375435098228887908058629107 563152647343331862087943661)
      ·
        refine ⟨211182242753749448282978873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563152647343331862087943661 211182242753749448282978873)
        ·
          refine ⟨158386682065312086212234155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211182242753749448282978873 158386682065312086212234155)
          ·
            refine ⟨237580023097968129318351233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158386682065312086212234155 237580023097968129318351233)
            ·
              refine ⟨178185017323476096988763425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237580023097968129318351233 178185017323476096988763425)
              ·
                refine ⟨133638762992607072741572569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178185017323476096988763425 133638762992607072741572569)
                ·
                  refine ⟨100229072244455304556179427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133638762992607072741572569 100229072244455304556179427)
                  ·
                    refine ⟨150343608366682956834269141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100229072244455304556179427 150343608366682956834269141)
                    ·
                      refine ⟨3523678321094131800803183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150343608366682956834269141 3523678321094131800803183)
                      ·
                        rfl

theorem cell23_6862339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_6862339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862339 prefixEnd_6862339 := by exact prefixLift 6862339
  have htrace : WordTrace (prefixWord ++ tailWord_6862339) baseStart_6862339 baseEnd_6862339 := by
    simpa [prefixWord, tailWord_6862339, baseEnd_6862339] using wordTrace_append hprefix tailTrace_6862339
  have hstable : (prefixWord ++ tailWord_6862339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862339).length < 2 ^ (prefixWord ++ tailWord_6862339).sum := by decide
  have hdescent : baseEnd_6862339 < baseStart_6862339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862350 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_6862350 : Nat := 118140960795 + 6862350 * 2 ^ 59
def prefixEnd_6862350 : Nat := 4983230072969 + 3 ^ 40 * 6862350 * 2
def baseEnd_6862350 : Nat := 391520441042370139751737

theorem tailTrace_6862350 : CollatzResearch.WordTrace tailWord_6862350 prefixEnd_6862350 391520441042370139751737 := by
  unfold tailWord_6862350
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286308336110677614717063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166860311125923613945157669 31286308336110677614717063)
  ·
    refine ⟨46929462504166016422075595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31286308336110677614717063 46929462504166016422075595)
    ·
      refine ⟨70394193756249024633113393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46929462504166016422075595 70394193756249024633113393)
      ·
        refine ⟨52795645317186768474835045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70394193756249024633113393 52795645317186768474835045)
        ·
          refine ⟨9899183496972519089031571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52795645317186768474835045 9899183496972519089031571)
          ·
            refine ⟨14848775245458778633547357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9899183496972519089031571 14848775245458778633547357)
            ·
              refine ⟨5568290717047041987580259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14848775245458778633547357 5568290717047041987580259)
              ·
                refine ⟨8352436075570562981370389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568290717047041987580259 8352436075570562981370389)
                ·
                  refine ⟨391520441042370139751737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8352436075570562981370389 391520441042370139751737)
                  ·
                    rfl

theorem cell23_6862350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_6862350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862350 prefixEnd_6862350 := by exact prefixLift 6862350
  have htrace : WordTrace (prefixWord ++ tailWord_6862350) baseStart_6862350 baseEnd_6862350 := by
    simpa [prefixWord, tailWord_6862350, baseEnd_6862350] using wordTrace_append hprefix tailTrace_6862350
  have hstable : (prefixWord ++ tailWord_6862350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862350).length < 2 ^ (prefixWord ++ tailWord_6862350).sum := by decide
  have hdescent : baseEnd_6862350 < baseStart_6862350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862393 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_6862393 : Nat := 118140960795 + 6862393 * 2 ^ 59
def prefixEnd_6862393 : Nat := 4983230072969 + 3 ^ 40 * 6862393 * 2
def baseEnd_6862393 : Nat := 1174568683016491529842645

theorem tailTrace_6862393 : CollatzResearch.WordTrace tailWord_6862393 prefixEnd_6862393 1174568683016491529842645 := by
  unfold tailWord_6862393
  simp only [CollatzResearch.WordTrace]
  refine ⟨250292035027729639261551833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166861356685153092841034555 250292035027729639261551833)
  ·
    refine ⟨187719026270797229446163875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250292035027729639261551833 187719026270797229446163875)
    ·
      refine ⟨281578539406195844169245813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187719026270797229446163875 281578539406195844169245813)
      ·
        refine ⟨26397988069330860390866795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281578539406195844169245813 26397988069330860390866795)
        ·
          refine ⟨39596982103996290586300193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26397988069330860390866795 39596982103996290586300193)
          ·
            refine ⟨29697736577997217939725145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39596982103996290586300193 29697736577997217939725145)
            ·
              refine ⟨22273302433497913454793859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29697736577997217939725145 22273302433497913454793859)
              ·
                refine ⟨33409953650246870182190789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22273302433497913454793859 33409953650246870182190789)
                ·
                  refine ⟨6264366309421288159160773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33409953650246870182190789 6264366309421288159160773)
                  ·
                    refine ⟨1174568683016491529842645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264366309421288159160773 1174568683016491529842645)
                    ·
                      rfl

theorem cell23_6862393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_6862393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862393 prefixEnd_6862393 := by exact prefixLift 6862393
  have htrace : WordTrace (prefixWord ++ tailWord_6862393) baseStart_6862393 baseEnd_6862393 := by
    simpa [prefixWord, tailWord_6862393, baseEnd_6862393] using wordTrace_append hprefix tailTrace_6862393
  have hstable : (prefixWord ++ tailWord_6862393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862393).length < 2 ^ (prefixWord ++ tailWord_6862393).sum := by decide
  have hdescent : baseEnd_6862393 < baseStart_6862393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862433 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_6862433 : Nat := 118140960795 + 6862433 * 2 ^ 59
def prefixEnd_6862433 : Nat := 4983230072969 + 3 ^ 40 * 6862433 * 2
def baseEnd_6862433 : Nat := 3523726588275654433027751

theorem tailTrace_6862433 : CollatzResearch.WordTrace tailWord_6862433 prefixEnd_6862433 3523726588275654433027751 := by
  unfold tailWord_6862433
  simp only [CollatzResearch.WordTrace]
  refine ⟨250293493947584726093007953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166862329298389817395338635 250293493947584726093007953)
  ·
    refine ⟨187720120460688544569755965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250293493947584726093007953 187720120460688544569755965)
    ·
      refine ⟨70395045172758204213658487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187720120460688544569755965 70395045172758204213658487)
      ·
        refine ⟨105592567759137306320487731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70395045172758204213658487 105592567759137306320487731)
        ·
          refine ⟨158388851638705959480731597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105592567759137306320487731 158388851638705959480731597)
          ·
            refine ⟨59395819364514734805274349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158388851638705959480731597 59395819364514734805274349)
            ·
              refine ⟨22273432261693025551977881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59395819364514734805274349 22273432261693025551977881)
              ·
                refine ⟨16705074196269769163983411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22273432261693025551977881 16705074196269769163983411)
                ·
                  refine ⟨25057611294404653745975117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16705074196269769163983411 25057611294404653745975117)
                  ·
                    refine ⟨9396604235401745154740669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25057611294404653745975117 9396604235401745154740669)
                    ·
                      refine ⟨3523726588275654433027751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396604235401745154740669 3523726588275654433027751)
                      ·
                        rfl

theorem cell23_6862433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_6862433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862433 prefixEnd_6862433 := by exact prefixLift 6862433
  have htrace : WordTrace (prefixWord ++ tailWord_6862433) baseStart_6862433 baseEnd_6862433 := by
    simpa [prefixWord, tailWord_6862433, baseEnd_6862433] using wordTrace_append hprefix tailTrace_6862433
  have hstable : (prefixWord ++ tailWord_6862433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862433).length < 2 ^ (prefixWord ++ tailWord_6862433).sum := by decide
  have hdescent : baseEnd_6862433 < baseStart_6862433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862437 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_6862437 : Nat := 118140960795 + 6862437 * 2 ^ 59
def prefixEnd_6862437 : Nat := 4983230072969 + 3 ^ 40 * 6862437 * 2
def baseEnd_6862437 : Nat := 3523728642198272417377733

theorem tailTrace_6862437 : CollatzResearch.WordTrace tailWord_6862437 prefixEnd_6862437 3523728642198272417377733 := by
  unfold tailWord_6862437
  simp only [CollatzResearch.WordTrace]
  refine ⟨250293639839570234776153565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166862426559713489850769043 250293639839570234776153565)
  ·
    refine ⟨93860114939838838041057587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250293639839570234776153565 93860114939838838041057587)
    ·
      refine ⟨140790172409758257061586381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93860114939838838041057587 140790172409758257061586381)
      ·
        refine ⟨52796314653659346398094893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140790172409758257061586381 52796314653659346398094893)
        ·
          refine ⟨19798617995122254899285585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52796314653659346398094893 19798617995122254899285585)
          ·
            refine ⟨14848963496341691174464189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19798617995122254899285585 14848963496341691174464189)
            ·
              refine ⟨5568361311128134190424071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14848963496341691174464189 5568361311128134190424071)
              ·
                refine ⟨8352541966692201285636107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568361311128134190424071 8352541966692201285636107)
                ·
                  refine ⟨12528812950038301928454161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8352541966692201285636107 12528812950038301928454161)
                  ·
                    refine ⟨9396609712528726446340621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12528812950038301928454161 9396609712528726446340621)
                    ·
                      refine ⟨3523728642198272417377733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396609712528726446340621 3523728642198272417377733)
                      ·
                        rfl

theorem cell23_6862437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_6862437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862437 prefixEnd_6862437 := by exact prefixLift 6862437
  have htrace : WordTrace (prefixWord ++ tailWord_6862437) baseStart_6862437 baseEnd_6862437 := by
    simpa [prefixWord, tailWord_6862437, baseEnd_6862437] using wordTrace_append hprefix tailTrace_6862437
  have hstable : (prefixWord ++ tailWord_6862437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862437).length < 2 ^ (prefixWord ++ tailWord_6862437).sum := by decide
  have hdescent : baseEnd_6862437 < baseStart_6862437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862453 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6862453 : Nat := 118140960795 + 6862453 * 2 ^ 59
def prefixEnd_6862453 : Nat := 4983230072969 + 3 ^ 40 * 6862453 * 2
def baseEnd_6862453 : Nat := 1174578952629581451592553

theorem tailTrace_6862453 : CollatzResearch.WordTrace tailWord_6862453 prefixEnd_6862453 1174578952629581451592553 := by
  unfold tailWord_6862453
  simp only [CollatzResearch.WordTrace]
  refine ⟨250294223407512269508736013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166862815605008179672490675 250294223407512269508736013)
  ·
    refine ⟨93860333777817101065776005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250294223407512269508736013 93860333777817101065776005)
    ·
      refine ⟨17598812583340706449833001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93860333777817101065776005 17598812583340706449833001)
      ·
        refine ⟨13199109437505529837374751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17598812583340706449833001 13199109437505529837374751)
        ·
          refine ⟨19798664156258294756062127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13199109437505529837374751 19798664156258294756062127)
          ·
            refine ⟨29697996234387442134093191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19798664156258294756062127 29697996234387442134093191)
            ·
              refine ⟨44546994351581163201139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29697996234387442134093191 44546994351581163201139787)
              ·
                refine ⟨66820491527371744801709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44546994351581163201139787 66820491527371744801709681)
                ·
                  refine ⟨50115368645528808601282261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66820491527371744801709681 50115368645528808601282261)
                  ·
                    refine ⟨1174578952629581451592553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50115368645528808601282261 1174578952629581451592553)
                    ·
                      rfl

theorem cell23_6862453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6862453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862453 prefixEnd_6862453 := by exact prefixLift 6862453
  have htrace : WordTrace (prefixWord ++ tailWord_6862453) baseStart_6862453 baseEnd_6862453 := by
    simpa [prefixWord, tailWord_6862453, baseEnd_6862453] using wordTrace_append hprefix tailTrace_6862453
  have hstable : (prefixWord ++ tailWord_6862453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862453).length < 2 ^ (prefixWord ++ tailWord_6862453).sum := by decide
  have hdescent : baseEnd_6862453 < baseStart_6862453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862494 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6862494 : Nat := 118140960795 + 6862494 * 2 ^ 59
def prefixEnd_6862494 : Nat := 4983230072969 + 3 ^ 40 * 6862494 * 2
def baseEnd_6862494 : Nat := 3523757910595578694364971

theorem tailTrace_6862494 : CollatzResearch.WordTrace tailWord_6862494 prefixEnd_6862494 3523757910595578694364971 := by
  unfold tailWord_6862494
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286964850045466688872317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166863812533575822340652357 31286964850045466688872317)
  ·
    refine ⟨11732611818767050008327119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31286964850045466688872317 11732611818767050008327119)
    ·
      refine ⟨17598917728150575012490679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11732611818767050008327119 17598917728150575012490679)
      ·
        refine ⟨26398376592225862518736019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17598917728150575012490679 26398376592225862518736019)
        ·
          refine ⟨39597564888338793778104029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26398376592225862518736019 39597564888338793778104029)
          ·
            refine ⟨14849086833127047666789011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39597564888338793778104029 14849086833127047666789011)
            ·
              refine ⟨22273630249690571500183517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14849086833127047666789011 22273630249690571500183517)
              ·
                refine ⟨8352611343633964312568819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22273630249690571500183517 8352611343633964312568819)
                ·
                  refine ⟨12528917015450946468853229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8352611343633964312568819 12528917015450946468853229)
                  ·
                    refine ⟨4698343880794104925819961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12528917015450946468853229 4698343880794104925819961)
                    ·
                      refine ⟨3523757910595578694364971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698343880794104925819961 3523757910595578694364971)
                      ·
                        rfl

theorem cell23_6862494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6862494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862494 prefixEnd_6862494 := by exact prefixLift 6862494
  have htrace : WordTrace (prefixWord ++ tailWord_6862494) baseStart_6862494 baseEnd_6862494 := by
    simpa [prefixWord, tailWord_6862494, baseEnd_6862494] using wordTrace_append hprefix tailTrace_6862494
  have hstable : (prefixWord ++ tailWord_6862494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862494).length < 2 ^ (prefixWord ++ tailWord_6862494).sum := by decide
  have hdescent : baseEnd_6862494 < baseStart_6862494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862583 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_6862583 : Nat := 118140960795 + 6862583 * 2 ^ 59
def prefixEnd_6862583 : Nat := 4983230072969 + 3 ^ 40 * 6862583 * 2
def baseEnd_6862583 : Nat := 3523803610373828846152061

theorem tailTrace_6862583 : CollatzResearch.WordTrace tailWord_6862583 prefixEnd_6862583 3523803610373828846152061 := by
  unfold tailWord_6862583
  simp only [CollatzResearch.WordTrace]
  refine ⟨250298964897041301710968403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166865976598027534473978935 250298964897041301710968403)
  ·
    refine ⟨375448447345561952566452605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250298964897041301710968403 375448447345561952566452605)
    ·
      refine ⟨140793167754585732212419727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375448447345561952566452605 140793167754585732212419727)
      ·
        refine ⟨211189751631878598318629591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140793167754585732212419727 211189751631878598318629591)
        ·
          refine ⟨316784627447817897477944387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211189751631878598318629591 316784627447817897477944387)
          ·
            refine ⟨475176941171726846216916581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316784627447817897477944387 475176941171726846216916581)
            ·
              refine ⟨89095676469698783665671859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475176941171726846216916581 89095676469698783665671859)
              ·
                refine ⟨133643514704548175498507789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89095676469698783665671859 133643514704548175498507789)
                ·
                  refine ⟨50116318014205565811940421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133643514704548175498507789 50116318014205565811940421)
                  ·
                    refine ⟨9396809627663543589738829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50116318014205565811940421 9396809627663543589738829)
                    ·
                      refine ⟨3523803610373828846152061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396809627663543589738829 3523803610373828846152061)
                      ·
                        rfl

theorem cell23_6862583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_6862583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862583 prefixEnd_6862583 := by exact prefixLift 6862583
  have htrace : WordTrace (prefixWord ++ tailWord_6862583) baseStart_6862583 baseEnd_6862583 := by
    simpa [prefixWord, tailWord_6862583, baseEnd_6862583] using wordTrace_append hprefix tailTrace_6862583
  have hstable : (prefixWord ++ tailWord_6862583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862583).length < 2 ^ (prefixWord ++ tailWord_6862583).sum := by decide
  have hdescent : baseEnd_6862583 < baseStart_6862583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862593 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6862593 : Nat := 118140960795 + 6862593 * 2 ^ 59
def prefixEnd_6862593 : Nat := 4983230072969 + 3 ^ 40 * 6862593 * 2
def baseEnd_6862593 : Nat := 3523808745180373807027015

theorem tailTrace_6862593 : CollatzResearch.WordTrace tailWord_6862593 prefixEnd_6862593 3523808745180373807027015 := by
  unfold tailWord_6862593
  simp only [CollatzResearch.WordTrace]
  refine ⟨250299329627005073418832433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166866219751336715612554955 250299329627005073418832433)
  ·
    refine ⟨187724497220253805064124325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250299329627005073418832433 187724497220253805064124325)
    ·
      refine ⟨35198343228797588449523311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187724497220253805064124325 35198343228797588449523311)
      ·
        refine ⟨52797514843196382674284967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35198343228797588449523311 52797514843196382674284967)
        ·
          refine ⟨79196272264794574011427451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52797514843196382674284967 79196272264794574011427451)
          ·
            refine ⟨118794408397191861017141177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79196272264794574011427451 118794408397191861017141177)
            ·
              refine ⟨89095806297893895762855883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118794408397191861017141177 89095806297893895762855883)
              ·
                refine ⟨133643709446840843644283825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89095806297893895762855883 133643709446840843644283825)
                ·
                  refine ⟨100232782085130632733212869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133643709446840843644283825 100232782085130632733212869)
                  ·
                    refine ⟨18793646640961993637477413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100232782085130632733212869 18793646640961993637477413)
                    ·
                      refine ⟨3523808745180373807027015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18793646640961993637477413 3523808745180373807027015)
                      ·
                        rfl

theorem cell23_6862593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6862593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862593 prefixEnd_6862593 := by exact prefixLift 6862593
  have htrace : WordTrace (prefixWord ++ tailWord_6862593) baseStart_6862593 baseEnd_6862593 := by
    simpa [prefixWord, tailWord_6862593, baseEnd_6862593] using wordTrace_append hprefix tailTrace_6862593
  have hstable : (prefixWord ++ tailWord_6862593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862593).length < 2 ^ (prefixWord ++ tailWord_6862593).sum := by decide
  have hdescent : baseEnd_6862593 < baseStart_6862593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862620 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 6]
def baseStart_6862620 : Nat := 118140960795 + 6862620 * 2 ^ 59
def prefixEnd_6862620 : Nat := 4983230072969 + 3 ^ 40 * 6862620 * 2
def baseEnd_6862620 : Nat := 391535845462005022376599

theorem tailTrace_6862620 : CollatzResearch.WordTrace tailWord_6862620 prefixEnd_6862620 391535845462005022376599 := by
  unfold tailWord_6862620
  simp only [CollatzResearch.WordTrace]
  refine ⟨125150157198953628515032657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166866876265271504686710209 125150157198953628515032657)
  ·
    refine ⟨93862617899215221386274493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125150157198953628515032657 93862617899215221386274493)
    ·
      refine ⟨35198481712205708019852935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93862617899215221386274493 35198481712205708019852935)
      ·
        refine ⟨52797722568308562029779403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35198481712205708019852935 52797722568308562029779403)
        ·
          refine ⟨79196583852462843044669105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52797722568308562029779403 79196583852462843044669105)
          ·
            refine ⟨59397437889347132283501829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79196583852462843044669105 59397437889347132283501829)
            ·
              refine ⟨11137019604252587303156593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59397437889347132283501829 11137019604252587303156593)
              ·
                refine ⟨8352764703189440477367445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11137019604252587303156593 8352764703189440477367445)
                ·
                  refine ⟨391535845462005022376599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8352764703189440477367445 391535845462005022376599)
                  ·
                    rfl

theorem cell23_6862620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_6862620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862620 prefixEnd_6862620 := by exact prefixLift 6862620
  have htrace : WordTrace (prefixWord ++ tailWord_6862620) baseStart_6862620 baseEnd_6862620 := by
    simpa [prefixWord, tailWord_6862620, baseEnd_6862620] using wordTrace_append hprefix tailTrace_6862620
  have hstable : (prefixWord ++ tailWord_6862620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862620).length < 2 ^ (prefixWord ++ tailWord_6862620).sum := by decide
  have hdescent : baseEnd_6862620 < baseStart_6862620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862623 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_6862623 : Nat := 118140960795 + 6862623 * 2 ^ 59
def prefixEnd_6862623 : Nat := 4983230072969 + 3 ^ 40 * 6862623 * 2
def baseEnd_6862623 : Nat := 3523824149600008689651877

theorem tailTrace_6862623 : CollatzResearch.WordTrace tailWord_6862623 prefixEnd_6862623 3523824149600008689651877 := by
  unfold tailWord_6862623
  simp only [CollatzResearch.WordTrace]
  refine ⟨250300423816896388542424523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166866949211264259028283015 250300423816896388542424523)
  ·
    refine ⟨375450635725344582813636785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250300423816896388542424523 375450635725344582813636785)
    ·
      refine ⟨281587976794008437110227589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375450635725344582813636785 281587976794008437110227589)
      ·
        refine ⟨52797745648876581958167673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281587976794008437110227589 52797745648876581958167673)
        ·
          refine ⟨39598309236657436468625755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52797745648876581958167673 39598309236657436468625755)
          ·
            refine ⟨59397463854986154702938633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39598309236657436468625755 59397463854986154702938633)
            ·
              refine ⟨44548097891239616027203975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59397463854986154702938633 44548097891239616027203975)
              ·
                refine ⟨66822146836859424040805963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44548097891239616027203975 66822146836859424040805963)
                ·
                  refine ⟨100233220255289136061208945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66822146836859424040805963 100233220255289136061208945)
                  ·
                    refine ⟨75174915191466852045906709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100233220255289136061208945 75174915191466852045906709)
                    ·
                      refine ⟨3523824149600008689651877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75174915191466852045906709 3523824149600008689651877)
                      ·
                        rfl

theorem cell23_6862623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_6862623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862623 prefixEnd_6862623 := by exact prefixLift 6862623
  have htrace : WordTrace (prefixWord ++ tailWord_6862623) baseStart_6862623 baseEnd_6862623 := by
    simpa [prefixWord, tailWord_6862623, baseEnd_6862623] using wordTrace_append hprefix tailTrace_6862623
  have hstable : (prefixWord ++ tailWord_6862623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862623).length < 2 ^ (prefixWord ++ tailWord_6862623).sum := by decide
  have hdescent : baseEnd_6862623 < baseStart_6862623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862650 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_6862650 : Nat := 118140960795 + 6862650 * 2 ^ 59
def prefixEnd_6862650 : Nat := 4983230072969 + 3 ^ 40 * 6862650 * 2
def baseEnd_6862650 : Nat := 1174612671192560028004751

theorem tailTrace_6862650 : CollatzResearch.WordTrace tailWord_6862650 prefixEnd_6862650 1174612671192560028004751 := by
  unfold tailWord_6862650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62575352146949643038414351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166867605725199048102438269 62575352146949643038414351)
  ·
    refine ⟨93863028220424464557621527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62575352146949643038414351 93863028220424464557621527)
    ·
      refine ⟨140794542330636696836432291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93863028220424464557621527 140794542330636696836432291)
      ·
        refine ⟨211191813495955045254648437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140794542330636696836432291 211191813495955045254648437)
        ·
          refine ⟨19799232515245785492623291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211191813495955045254648437 19799232515245785492623291)
          ·
            refine ⟨29698848772868678238934937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19799232515245785492623291 29698848772868678238934937)
            ·
              refine ⟨22274136579651508679201203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29698848772868678238934937 22274136579651508679201203)
              ·
                refine ⟨33411204869477263018801805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22274136579651508679201203 33411204869477263018801805)
                ·
                  refine ⟨12529201826053973632050677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33411204869477263018801805 12529201826053973632050677)
                  ·
                    refine ⟨1174612671192560028004751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12529201826053973632050677 1174612671192560028004751)
                    ·
                      rfl

theorem cell23_6862650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_6862650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862650 prefixEnd_6862650 := by exact prefixLift 6862650
  have htrace : WordTrace (prefixWord ++ tailWord_6862650) baseStart_6862650 baseEnd_6862650 := by
    simpa [prefixWord, tailWord_6862650, baseEnd_6862650] using wordTrace_append hprefix tailTrace_6862650
  have hstable : (prefixWord ++ tailWord_6862650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862650).length < 2 ^ (prefixWord ++ tailWord_6862650).sum := by decide
  have hdescent : baseEnd_6862650 < baseStart_6862650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862664 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_6862664 : Nat := 118140960795 + 6862664 * 2 ^ 59
def prefixEnd_6862664 : Nat := 4983230072969 + 3 ^ 40 * 6862664 * 2
def baseEnd_6862664 : Nat := 3523845202306843029239189

theorem tailTrace_6862664 : CollatzResearch.WordTrace tailWord_6862664 prefixEnd_6862664 3523845202306843029239189 := by
  unfold tailWord_6862664
  simp only [CollatzResearch.WordTrace]
  refine ⟨125150959604873926272333523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166867946139831901696444697 125150959604873926272333523)
  ·
    refine ⟨187726439407310889408500285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125150959604873926272333523 187726439407310889408500285)
    ·
      refine ⟨70397414777741583528187607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187726439407310889408500285 70397414777741583528187607)
      ·
        refine ⟨105596122166612375292281411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70397414777741583528187607 105596122166612375292281411)
        ·
          refine ⟨158394183249918562938422117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105596122166612375292281411 158394183249918562938422117)
          ·
            refine ⟨29698909359359730550954147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158394183249918562938422117 29698909359359730550954147)
            ·
              refine ⟨44548364039039595826431221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29698909359359730550954147 44548364039039595826431221)
              ·
                refine ⟨4176409128659962108727927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44548364039039595826431221 4176409128659962108727927)
                ·
                  refine ⟨6264613692989943163091891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176409128659962108727927 6264613692989943163091891)
                  ·
                    refine ⟨9396920539484914744637837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264613692989943163091891 9396920539484914744637837)
                    ·
                      refine ⟨3523845202306843029239189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396920539484914744637837 3523845202306843029239189)
                      ·
                        rfl

theorem cell23_6862664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_6862664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862664 prefixEnd_6862664 := by exact prefixLift 6862664
  have htrace : WordTrace (prefixWord ++ tailWord_6862664) baseStart_6862664 baseEnd_6862664 := by
    simpa [prefixWord, tailWord_6862664, baseEnd_6862664] using wordTrace_append hprefix tailTrace_6862664
  have hstable : (prefixWord ++ tailWord_6862664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862664).length < 2 ^ (prefixWord ++ tailWord_6862664).sum := by decide
  have hdescent : baseEnd_6862664 < baseStart_6862664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862693 : List Nat := [1, 3, 1, 3, 1, 1, 1, 12]
def baseStart_6862693 : Nat := 118140960795 + 6862693 * 2 ^ 59
def prefixEnd_6862693 : Nat := 4983230072969 + 3 ^ 40 * 6862693 * 2
def baseEnd_6862693 : Nat := 130513336786882348732465

theorem tailTrace_6862693 : CollatzResearch.WordTrace tailWord_6862693 prefixEnd_6862693 130513336786882348732465 := by
  unfold tailWord_6862693
  simp only [CollatzResearch.WordTrace]
  refine ⟨250302976926642790497472733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166868651284428526998315155 250302976926642790497472733)
  ·
    refine ⟨93863616347491046436552275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250302976926642790497472733 93863616347491046436552275)
    ·
      refine ⟨140795424521236569654828413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93863616347491046436552275 140795424521236569654828413)
      ·
        refine ⟨52798284195463713620560655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140795424521236569654828413 52798284195463713620560655)
        ·
          refine ⟨79197426293195570430840983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52798284195463713620560655 79197426293195570430840983)
          ·
            refine ⟨118796139439793355646261475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79197426293195570430840983 118796139439793355646261475)
            ·
              refine ⟨178194209159690033469392213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118796139439793355646261475 178194209159690033469392213)
              ·
                refine ⟨130513336786882348732465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 178194209159690033469392213 130513336786882348732465)
                ·
                  rfl

theorem cell23_6862693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 12].length) (baseStart_6862693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862693 prefixEnd_6862693 := by exact prefixLift 6862693
  have htrace : WordTrace (prefixWord ++ tailWord_6862693) baseStart_6862693 baseEnd_6862693 := by
    simpa [prefixWord, tailWord_6862693, baseEnd_6862693] using wordTrace_append hprefix tailTrace_6862693
  have hstable : (prefixWord ++ tailWord_6862693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862693).length < 2 ^ (prefixWord ++ tailWord_6862693).sum := by decide
  have hdescent : baseEnd_6862693 < baseStart_6862693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862700 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_6862700 : Nat := 118140960795 + 6862700 * 2 ^ 59
def prefixEnd_6862700 : Nat := 4983230072969 + 3 ^ 40 * 6862700 * 2
def baseEnd_6862700 : Nat := 3523863687610404888389023

theorem tailTrace_6862700 : CollatzResearch.WordTrace tailWord_6862700 prefixEnd_6862700 3523863687610404888389023 := by
  unfold tailWord_6862700
  simp only [CollatzResearch.WordTrace]
  refine ⟨125151616118808715346488777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166868821491744953795318369 125151616118808715346488777)
  ·
    refine ⟨93863712089106536509866583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125151616118808715346488777 93863712089106536509866583)
    ·
      refine ⟨140795568133659804764799875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93863712089106536509866583 140795568133659804764799875)
      ·
        refine ⟨211193352200489707147199813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140795568133659804764799875 211193352200489707147199813)
        ·
          refine ⟨39598753537591820090099965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211193352200489707147199813 39598753537591820090099965)
          ·
            refine ⟨14849532576596932533787487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39598753537591820090099965 14849532576596932533787487)
            ·
              refine ⟨22274298864895398800681231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14849532576596932533787487 22274298864895398800681231)
              ·
                refine ⟨33411448297343098201021847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22274298864895398800681231 33411448297343098201021847)
                ·
                  refine ⟨50117172446014647301532771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33411448297343098201021847 50117172446014647301532771)
                  ·
                    refine ⟨75175758669021970952299157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50117172446014647301532771 75175758669021970952299157)
                    ·
                      refine ⟨3523863687610404888389023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75175758669021970952299157 3523863687610404888389023)
                      ·
                        rfl

theorem cell23_6862700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_6862700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862700 prefixEnd_6862700 := by exact prefixLift 6862700
  have htrace : WordTrace (prefixWord ++ tailWord_6862700) baseStart_6862700 baseEnd_6862700 := by
    simpa [prefixWord, tailWord_6862700, baseEnd_6862700] using wordTrace_append hprefix tailTrace_6862700
  have hstable : (prefixWord ++ tailWord_6862700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862700).length < 2 ^ (prefixWord ++ tailWord_6862700).sum := by decide
  have hdescent : baseEnd_6862700 < baseStart_6862700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862720 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_6862720 : Nat := 118140960795 + 6862720 * 2 ^ 59
def prefixEnd_6862720 : Nat := 4983230072969 + 3 ^ 40 * 6862720 * 2
def baseEnd_6862720 : Nat := 3523873957223494810138931

theorem tailTrace_6862720 : CollatzResearch.WordTrace tailWord_6862720 prefixEnd_6862720 3523873957223494810138931 := by
  unfold tailWord_6862720
  simp only [CollatzResearch.WordTrace]
  refine ⟨125151980848772487054352807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166869307798363316072470409 125151980848772487054352807)
  ·
    refine ⟨187727971273158730581529211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125151980848772487054352807 187727971273158730581529211)
    ·
      refine ⟨281591956909738095872293817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187727971273158730581529211 281591956909738095872293817)
      ·
        refine ⟨211193967682303571904220363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281591956909738095872293817 211193967682303571904220363)
        ·
          refine ⟨316790951523455357856330545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211193967682303571904220363 316790951523455357856330545)
          ·
            refine ⟨237593213642591518392247909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316790951523455357856330545 237593213642591518392247909)
            ·
              refine ⟨44548727557985909698546483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237593213642591518392247909 44548727557985909698546483)
              ·
                refine ⟨66823091336978864547819725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44548727557985909698546483 66823091336978864547819725)
                ·
                  refine ⟨25058659251367074205432397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66823091336978864547819725 25058659251367074205432397)
                  ·
                    refine ⟨9396997219262652827037149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25058659251367074205432397 9396997219262652827037149)
                    ·
                      refine ⟨3523873957223494810138931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9396997219262652827037149 3523873957223494810138931)
                      ·
                        rfl

theorem cell23_6862720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_6862720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862720 prefixEnd_6862720 := by exact prefixLift 6862720
  have htrace : WordTrace (prefixWord ++ tailWord_6862720) baseStart_6862720 baseEnd_6862720 := by
    simpa [prefixWord, tailWord_6862720, baseEnd_6862720] using wordTrace_append hprefix tailTrace_6862720
  have hstable : (prefixWord ++ tailWord_6862720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862720).length < 2 ^ (prefixWord ++ tailWord_6862720).sum := by decide
  have hdescent : baseEnd_6862720 < baseStart_6862720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862727 : List Nat := [1, 1, 4, 2, 5, 1, 9]
def baseStart_6862727 : Nat := 118140960795 + 6862727 * 2 ^ 59
def prefixEnd_6862727 : Nat := 4983230072969 + 3 ^ 40 * 6862727 * 2
def baseEnd_6862727 : Nat := 43504661130716991145079

theorem tailTrace_6862727 : CollatzResearch.WordTrace tailWord_6862727 prefixEnd_6862727 43504661130716991145079 := by
  unfold tailWord_6862727
  simp only [CollatzResearch.WordTrace]
  refine ⟨250304217008519614304210435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166869478005679742869473623 250304217008519614304210435)
  ·
    refine ⟨375456325512779421456315653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250304217008519614304210435 375456325512779421456315653)
    ·
      refine ⟨70398061033646141523059185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375456325512779421456315653 70398061033646141523059185)
      ·
        refine ⟨52798545775234606142294389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70398061033646141523059185 52798545775234606142294389)
        ·
          refine ⟨4949863666428244325840099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52798545775234606142294389 4949863666428244325840099)
          ·
            refine ⟨7424795499642366488760149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949863666428244325840099 7424795499642366488760149)
            ·
              refine ⟨43504661130716991145079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7424795499642366488760149 43504661130716991145079)
              ·
                rfl

theorem cell23_6862727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 9].length) (baseStart_6862727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862727 prefixEnd_6862727 := by exact prefixLift 6862727
  have htrace : WordTrace (prefixWord ++ tailWord_6862727) baseStart_6862727 baseEnd_6862727 := by
    simpa [prefixWord, tailWord_6862727, baseEnd_6862727] using wordTrace_append hprefix tailTrace_6862727
  have hstable : (prefixWord ++ tailWord_6862727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862727).length < 2 ^ (prefixWord ++ tailWord_6862727).sum := by decide
  have hdescent : baseEnd_6862727 < baseStart_6862727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862737 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_6862737 : Nat := 118140960795 + 6862737 * 2 ^ 59
def prefixEnd_6862737 : Nat := 4983230072969 + 3 ^ 40 * 6862737 * 2
def baseEnd_6862737 : Nat := 3523882686394621243626353

theorem tailTrace_6862737 : CollatzResearch.WordTrace tailWord_6862737 prefixEnd_6862737 3523882686394621243626353 := by
  unfold tailWord_6862737
  simp only [CollatzResearch.WordTrace]
  refine ⟨250304581738483386012074465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166869721158988924008049643 250304581738483386012074465)
  ·
    refine ⟨187728436303862539509055849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250304581738483386012074465 187728436303862539509055849)
    ·
      refine ⟨140796327227896904631791887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187728436303862539509055849 140796327227896904631791887)
      ·
        refine ⟨211194490841845356947687831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140796327227896904631791887 211194490841845356947687831)
        ·
          refine ⟨316791736262768035421531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211194490841845356947687831 316791736262768035421531747)
          ·
            refine ⟨475187604394152053132297621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316791736262768035421531747 475187604394152053132297621)
            ·
              refine ⟨22274418955975877490576451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 475187604394152053132297621 22274418955975877490576451)
              ·
                refine ⟨33411628433963816235864677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22274418955975877490576451 33411628433963816235864677)
                ·
                  refine ⟨6264680331368215544224627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33411628433963816235864677 6264680331368215544224627)
                  ·
                    refine ⟨9397020497052323316336941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264680331368215544224627 9397020497052323316336941)
                    ·
                      refine ⟨3523882686394621243626353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397020497052323316336941 3523882686394621243626353)
                      ·
                        rfl

theorem cell23_6862737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_6862737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862737 prefixEnd_6862737 := by exact prefixLift 6862737
  have htrace : WordTrace (prefixWord ++ tailWord_6862737) baseStart_6862737 baseEnd_6862737 := by
    simpa [prefixWord, tailWord_6862737, baseEnd_6862737] using wordTrace_append hprefix tailTrace_6862737
  have hstable : (prefixWord ++ tailWord_6862737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862737).length < 2 ^ (prefixWord ++ tailWord_6862737).sum := by decide
  have hdescent : baseEnd_6862737 < baseStart_6862737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862738 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6862738 : Nat := 118140960795 + 6862738 * 2 ^ 59
def prefixEnd_6862738 : Nat := 4983230072969 + 3 ^ 40 * 6862738 * 2
def baseEnd_6862738 : Nat := 3523883199875275739713849

theorem tailTrace_6862738 : CollatzResearch.WordTrace tailWord_6862738 prefixEnd_6862738 3523883199875275739713849 := by
  unfold tailWord_6862738
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576154552869940795715217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166869745474319842121907245 62576154552869940795715217)
  ·
    refine ⟨46932115914652455596786413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62576154552869940795715217 46932115914652455596786413)
    ·
      refine ⟨17599543467994670848794905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46932115914652455596786413 17599543467994670848794905)
      ·
        refine ⟨13199657600996003136596179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17599543467994670848794905 13199657600996003136596179)
        ·
          refine ⟨19799486401494004704894269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13199657600996003136596179 19799486401494004704894269)
          ·
            refine ⟨7424807400560251764335351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19799486401494004704894269 7424807400560251764335351)
            ·
              refine ⟨11137211100840377646503027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424807400560251764335351 11137211100840377646503027)
              ·
                refine ⟨16705816651260566469754541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11137211100840377646503027 16705816651260566469754541)
                ·
                  refine ⟨6264681244222712426157953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16705816651260566469754541 6264681244222712426157953)
                  ·
                    refine ⟨4698510933167034319618465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6264681244222712426157953 4698510933167034319618465)
                    ·
                      refine ⟨3523883199875275739713849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698510933167034319618465 3523883199875275739713849)
                      ·
                        rfl

theorem cell23_6862738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6862738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862738 prefixEnd_6862738 := by exact prefixLift 6862738
  have htrace : WordTrace (prefixWord ++ tailWord_6862738) baseStart_6862738 baseEnd_6862738 := by
    simpa [prefixWord, tailWord_6862738, baseEnd_6862738] using wordTrace_append hprefix tailTrace_6862738
  have hstable : (prefixWord ++ tailWord_6862738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862738).length < 2 ^ (prefixWord ++ tailWord_6862738).sum := by decide
  have hdescent : baseEnd_6862738 < baseStart_6862738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862794 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_6862794 : Nat := 118140960795 + 6862794 * 2 ^ 59
def prefixEnd_6862794 : Nat := 4983230072969 + 3 ^ 40 * 6862794 * 2
def baseEnd_6862794 : Nat := 3523911954791927520613591

theorem tailTrace_6862794 : CollatzResearch.WordTrace tailWord_6862794 prefixEnd_6862794 3523911954791927520613591 := by
  unfold tailWord_6862794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576665174819221186724859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166871107132851256497932957 62576665174819221186724859)
  ·
    refine ⟨93864997762228831780087289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62576665174819221186724859 93864997762228831780087289)
    ·
      refine ⟨70398748321671623835065467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93864997762228831780087289 70398748321671623835065467)
      ·
        refine ⟨105598122482507435752598201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70398748321671623835065467 105598122482507435752598201)
        ·
          refine ⟨79198591861880576814448651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105598122482507435752598201 79198591861880576814448651)
          ·
            refine ⟨118797887792820865221672977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79198591861880576814448651 118797887792820865221672977)
            ·
              refine ⟨89098415844615648916254733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118797887792820865221672977 89098415844615648916254733)
              ·
                refine ⟨33411905941730868343595525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89098415844615648916254733 33411905941730868343595525)
                ·
                  refine ⟨6264732364074537814424161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33411905941730868343595525 6264732364074537814424161)
                  ·
                    refine ⟨4698549273055903360818121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6264732364074537814424161 4698549273055903360818121)
                    ·
                      refine ⟨3523911954791927520613591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698549273055903360818121 3523911954791927520613591)
                      ·
                        rfl

theorem cell23_6862794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_6862794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862794 prefixEnd_6862794 := by exact prefixLift 6862794
  have htrace : WordTrace (prefixWord ++ tailWord_6862794) baseStart_6862794 baseEnd_6862794 := by
    simpa [prefixWord, tailWord_6862794, baseEnd_6862794] using wordTrace_append hprefix tailTrace_6862794
  have hstable : (prefixWord ++ tailWord_6862794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862794).length < 2 ^ (prefixWord ++ tailWord_6862794).sum := by decide
  have hdescent : baseEnd_6862794 < baseStart_6862794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862840 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_6862840 : Nat := 118140960795 + 6862840 * 2 ^ 59
def prefixEnd_6862840 : Nat := 4983230072969 + 3 ^ 40 * 6862840 * 2
def baseEnd_6862840 : Nat := 3523935574902034340638379

theorem tailTrace_6862840 : CollatzResearch.WordTrace tailWord_6862840 prefixEnd_6862840 3523935574902034340638379 := by
  unfold tailWord_6862840
  simp only [CollatzResearch.WordTrace]
  refine ⟨125154169228555117301536987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166872225638073489735382649 125154169228555117301536987)
  ·
    refine ⟨187731253842832675952305481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125154169228555117301536987 187731253842832675952305481)
    ·
      refine ⟨140798440382124506964229111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187731253842832675952305481 140798440382124506964229111)
      ·
        refine ⟨211197660573186760446343667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140798440382124506964229111 211197660573186760446343667)
        ·
          refine ⟨316796490859780140669515501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211197660573186760446343667 316796490859780140669515501)
          ·
            refine ⟨118798684072417552751068313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316796490859780140669515501 118798684072417552751068313)
            ·
              refine ⟨89099013054313164563301235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118798684072417552751068313 89099013054313164563301235)
              ·
                refine ⟨133648519581469746844951853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89099013054313164563301235 133648519581469746844951853)
                ·
                  refine ⟨50118194843051155066856945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133648519581469746844951853 50118194843051155066856945)
                  ·
                    refine ⟨37588646132288366300142709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50118194843051155066856945 37588646132288366300142709)
                    ·
                      refine ⟨3523935574902034340638379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37588646132288366300142709 3523935574902034340638379)
                      ·
                        rfl

theorem cell23_6862840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_6862840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862840 prefixEnd_6862840 := by exact prefixLift 6862840
  have htrace : WordTrace (prefixWord ++ tailWord_6862840) baseStart_6862840 baseEnd_6862840 := by
    simpa [prefixWord, tailWord_6862840, baseEnd_6862840] using wordTrace_append hprefix tailTrace_6862840
  have hstable : (prefixWord ++ tailWord_6862840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862840).length < 2 ^ (prefixWord ++ tailWord_6862840).sum := by decide
  have hdescent : baseEnd_6862840 < baseStart_6862840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862924 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 6]
def baseStart_6862924 : Nat := 118140960795 + 6862924 * 2 ^ 59
def prefixEnd_6862924 : Nat := 4983230072969 + 3 ^ 40 * 6862924 * 2
def baseEnd_6862924 : Nat := 391553189697445779109777

theorem tailTrace_6862924 : CollatzResearch.WordTrace tailWord_6862924 prefixEnd_6862924 391553189697445779109777 := by
  unfold tailWord_6862924
  simp only [CollatzResearch.WordTrace]
  refine ⟨125155701094402958474565913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166874268125870611299421217 125155701094402958474565913)
  ·
    refine ⟨93866775820802218855924435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125155701094402958474565913 93866775820802218855924435)
    ·
      refine ⟨140800163731203328283886653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93866775820802218855924435 140800163731203328283886653)
      ·
        refine ⟨52800061399201248106457495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140800163731203328283886653 52800061399201248106457495)
        ·
          refine ⟨79200092098801872159686243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52800061399201248106457495 79200092098801872159686243)
          ·
            refine ⟨118800138148202808239529365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79200092098801872159686243 118800138148202808239529365)
            ·
              refine ⟨5568756475697006636227939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118800138148202808239529365 5568756475697006636227939)
              ·
                refine ⟨8353134713545509954341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568756475697006636227939 8353134713545509954341909)
                ·
                  refine ⟨391553189697445779109777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8353134713545509954341909 391553189697445779109777)
                  ·
                    rfl

theorem cell23_6862924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_6862924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862924 prefixEnd_6862924 := by exact prefixLift 6862924
  have htrace : WordTrace (prefixWord ++ tailWord_6862924) baseStart_6862924 baseEnd_6862924 := by
    simpa [prefixWord, tailWord_6862924, baseEnd_6862924] using wordTrace_append hprefix tailTrace_6862924
  have hstable : (prefixWord ++ tailWord_6862924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862924).length < 2 ^ (prefixWord ++ tailWord_6862924).sum := by decide
  have hdescent : baseEnd_6862924 < baseStart_6862924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862937 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_6862937 : Nat := 118140960795 + 6862937 * 2 ^ 59
def prefixEnd_6862937 : Nat := 4983230072969 + 3 ^ 40 * 6862937 * 2
def baseEnd_6862937 : Nat := 1174661794175173487041811

theorem tailTrace_6862937 : CollatzResearch.WordTrace tailWord_6862937 prefixEnd_6862937 1174661794175173487041811 := by
  unfold tailWord_6862937
  simp only [CollatzResearch.WordTrace]
  refine ⟨250311876337758820169355065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166874584225172546779570043 250311876337758820169355065)
  ·
    refine ⟨187733907253319115127016299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250311876337758820169355065 187733907253319115127016299)
    ·
      refine ⟨281600860879978672690524449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187733907253319115127016299 281600860879978672690524449)
      ·
        refine ⟨211200645659984004517893337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281600860879978672690524449 211200645659984004517893337)
        ·
          refine ⟨158400484244988003388420003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211200645659984004517893337 158400484244988003388420003)
          ·
            refine ⟨237600726367482005082630005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158400484244988003388420003 237600726367482005082630005)
            ·
              refine ⟨22275068096951437976496563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237600726367482005082630005 22275068096951437976496563)
              ·
                refine ⟨33412602145427156964744845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22275068096951437976496563 33412602145427156964744845)
                ·
                  refine ⟨12529725804535183861779317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33412602145427156964744845 12529725804535183861779317)
                  ·
                    refine ⟨1174661794175173487041811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12529725804535183861779317 1174661794175173487041811)
                    ·
                      rfl

theorem cell23_6862937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_6862937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862937 prefixEnd_6862937 := by exact prefixLift 6862937
  have htrace : WordTrace (prefixWord ++ tailWord_6862937) baseStart_6862937 baseEnd_6862937 := by
    simpa [prefixWord, tailWord_6862937, baseEnd_6862937] using wordTrace_append hprefix tailTrace_6862937
  have hstable : (prefixWord ++ tailWord_6862937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862937).length < 2 ^ (prefixWord ++ tailWord_6862937).sum := by decide
  have hdescent : baseEnd_6862937 < baseStart_6862937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6862984 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_6862984 : Nat := 118140960795 + 6862984 * 2 ^ 59
def prefixEnd_6862984 : Nat := 4983230072969 + 3 ^ 40 * 6862984 * 2
def baseEnd_6862984 : Nat := 1174669838705427259079239

theorem tailTrace_6862984 : CollatzResearch.WordTrace tailWord_6862984 prefixEnd_6862984 1174669838705427259079239 := by
  unfold tailWord_6862984
  simp only [CollatzResearch.WordTrace]
  refine ⟨125156795284294273598158003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166875727045725698130877337 125156795284294273598158003)
  ·
    refine ⟨187735192926441410397237005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125156795284294273598158003 187735192926441410397237005)
    ·
      refine ⟨70400697347415528898963877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187735192926441410397237005 70400697347415528898963877)
      ·
        refine ⟨13200130752640411668555727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70400697347415528898963877 13200130752640411668555727)
        ·
          refine ⟨19800196128960617502833591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200130752640411668555727 19800196128960617502833591)
          ·
            refine ⟨29700294193440926254250387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19800196128960617502833591 29700294193440926254250387)
            ·
              refine ⟨44550441290161389381375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29700294193440926254250387 44550441290161389381375581)
              ·
                refine ⟨16706415483810521018015843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44550441290161389381375581 16706415483810521018015843)
                ·
                  refine ⟨25059623225715781527023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16706415483810521018015843 25059623225715781527023765)
                  ·
                    refine ⟨1174669838705427259079239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25059623225715781527023765 1174669838705427259079239)
                    ·
                      rfl

theorem cell23_6862984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_6862984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6862984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6862984 prefixEnd_6862984 := by exact prefixLift 6862984
  have htrace : WordTrace (prefixWord ++ tailWord_6862984) baseStart_6862984 baseEnd_6862984 := by
    simpa [prefixWord, tailWord_6862984, baseEnd_6862984] using wordTrace_append hprefix tailTrace_6862984
  have hstable : (prefixWord ++ tailWord_6862984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6862984).length < 2 ^ (prefixWord ++ tailWord_6862984).sum := by decide
  have hdescent : baseEnd_6862984 < baseStart_6862984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6862984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863004 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6863004 : Nat := 118140960795 + 6863004 * 2 ^ 59
def prefixEnd_6863004 : Nat := 4983230072969 + 3 ^ 40 * 6863004 * 2
def baseEnd_6863004 : Nat := 3524019785729371698987625

theorem tailTrace_6863004 : CollatzResearch.WordTrace tailWord_6863004 prefixEnd_6863004 3524019785729371698987625 := by
  unfold tailWord_6863004
  simp only [CollatzResearch.WordTrace]
  refine ⟨125157160014258045306022033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166876213352344060408029377 125157160014258045306022033)
  ·
    refine ⟨93867870010693533979516525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125157160014258045306022033 93867870010693533979516525)
    ·
      refine ⟨35200451254010075242318697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93867870010693533979516525 35200451254010075242318697)
      ·
        refine ⟨26400338440507556431739023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35200451254010075242318697 26400338440507556431739023)
        ·
          refine ⟨39600507660761334647608535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26400338440507556431739023 39600507660761334647608535)
          ·
            refine ⟨59400761491142001971412803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39600507660761334647608535 59400761491142001971412803)
            ·
              refine ⟨89101142236713002957119205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59400761491142001971412803 89101142236713002957119205)
              ·
                refine ⟨16706464169383688054459851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89101142236713002957119205 16706464169383688054459851)
                ·
                  refine ⟨25059696254075532081689777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16706464169383688054459851 25059696254075532081689777)
                  ·
                    refine ⟨18794772190556649061267333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25059696254075532081689777 18794772190556649061267333)
                    ·
                      refine ⟨3524019785729371698987625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18794772190556649061267333 3524019785729371698987625)
                      ·
                        rfl

theorem cell23_6863004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6863004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863004 prefixEnd_6863004 := by exact prefixLift 6863004
  have htrace : WordTrace (prefixWord ++ tailWord_6863004) baseStart_6863004 baseEnd_6863004 := by
    simpa [prefixWord, tailWord_6863004, baseEnd_6863004] using wordTrace_append hprefix tailTrace_6863004
  have hstable : (prefixWord ++ tailWord_6863004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863004).length < 2 ^ (prefixWord ++ tailWord_6863004).sum := by decide
  have hdescent : baseEnd_6863004 < baseStart_6863004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863008 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4]
def baseStart_6863008 : Nat := 118140960795 + 6863008 * 2 ^ 59
def prefixEnd_6863008 : Nat := 4983230072969 + 3 ^ 40 * 6863008 * 2
def baseEnd_6863008 : Nat := 3524021839651989683337607

theorem tailTrace_6863008 : CollatzResearch.WordTrace tailWord_6863008 prefixEnd_6863008 3524021839651989683337607 := by
  unfold tailWord_6863008
  simp only [CollatzResearch.WordTrace]
  refine ⟨125157232960250799647594839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166876310613667732863459785 125157232960250799647594839)
  ·
    refine ⟨187735849440376199471392259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125157232960250799647594839 187735849440376199471392259)
    ·
      refine ⟨281603774160564299207088389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187735849440376199471392259 281603774160564299207088389)
      ·
        refine ⟨52800707655105806101329073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281603774160564299207088389 52800707655105806101329073)
        ·
          refine ⟨39600530741329354575996805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52800707655105806101329073 39600530741329354575996805)
          ·
            refine ⟨7425099513999253982999401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39600530741329354575996805 7425099513999253982999401)
            ·
              refine ⟨5568824635499440487249551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425099513999253982999401 5568824635499440487249551)
              ·
                refine ⟨8353236953249160730874327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568824635499440487249551 8353236953249160730874327)
                ·
                  refine ⟨12529855429873741096311491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8353236953249160730874327 12529855429873741096311491)
                  ·
                    refine ⟨18794783144810611644467237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12529855429873741096311491 18794783144810611644467237)
                    ·
                      refine ⟨3524021839651989683337607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18794783144810611644467237 3524021839651989683337607)
                      ·
                        rfl

theorem cell23_6863008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_6863008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863008 prefixEnd_6863008 := by exact prefixLift 6863008
  have htrace : WordTrace (prefixWord ++ tailWord_6863008) baseStart_6863008 baseEnd_6863008 := by
    simpa [prefixWord, tailWord_6863008, baseEnd_6863008] using wordTrace_append hprefix tailTrace_6863008
  have hstable : (prefixWord ++ tailWord_6863008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863008).length < 2 ^ (prefixWord ++ tailWord_6863008).sum := by decide
  have hdescent : baseEnd_6863008 < baseStart_6863008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863018 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6863018 : Nat := 118140960795 + 6863018 * 2 ^ 59
def prefixEnd_6863018 : Nat := 4983230072969 + 3 ^ 40 * 6863018 * 2
def baseEnd_6863018 : Nat := 1174675658152844881404187

theorem tailTrace_6863018 : CollatzResearch.WordTrace tailWord_6863018 prefixEnd_6863018 1174675658152844881404187 := by
  unfold tailWord_6863018
  simp only [CollatzResearch.WordTrace]
  refine ⟨62578707662616342750763427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166876553766976914002035805 62578707662616342750763427)
  ·
    refine ⟨93868061493924514126145141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62578707662616342750763427 93868061493924514126145141)
    ·
      refine ⟨8800130765055423199326107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93868061493924514126145141 8800130765055423199326107)
      ·
        refine ⟨13200196147583134798989161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800130765055423199326107 13200196147583134798989161)
        ·
          refine ⟨9900147110687351099241871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13200196147583134798989161 9900147110687351099241871)
          ·
            refine ⟨14850220666031026648862807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900147110687351099241871 14850220666031026648862807)
            ·
              refine ⟨22275330999046539973294211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14850220666031026648862807 22275330999046539973294211)
              ·
                refine ⟨33412996498569809959941317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22275330999046539973294211 33412996498569809959941317)
                ·
                  refine ⟨6264936843481839367488997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33412996498569809959941317 6264936843481839367488997)
                  ·
                    refine ⟨1174675658152844881404187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264936843481839367488997 1174675658152844881404187)
                    ·
                      rfl

theorem cell23_6863018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6863018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863018 prefixEnd_6863018 := by exact prefixLift 6863018
  have htrace : WordTrace (prefixWord ++ tailWord_6863018) baseStart_6863018 baseEnd_6863018 := by
    simpa [prefixWord, tailWord_6863018, baseEnd_6863018] using wordTrace_append hprefix tailTrace_6863018
  have hstable : (prefixWord ++ tailWord_6863018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863018).length < 2 ^ (prefixWord ++ tailWord_6863018).sum := by decide
  have hdescent : baseEnd_6863018 < baseStart_6863018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863025 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6863025 : Nat := 118140960795 + 6863025 * 2 ^ 59
def prefixEnd_6863025 : Nat := 4983230072969 + 3 ^ 40 * 6863025 * 2
def baseEnd_6863025 : Nat := 3524030568823116116825029

theorem tailTrace_6863025 : CollatzResearch.WordTrace tailWord_6863025 prefixEnd_6863025 3524030568823116116825029 := by
  unfold tailWord_6863025
  simp only [CollatzResearch.WordTrace]
  refine ⟨250315085961440011198558529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166876723974293340799039019 250315085961440011198558529)
  ·
    refine ⟨187736314471080008398918897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250315085961440011198558529 187736314471080008398918897)
    ·
      refine ⟨140802235853310006299189173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187736314471080008398918897 140802235853310006299189173)
      ·
        refine ⟨13200209611247813090548985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140802235853310006299189173 13200209611247813090548985)
        ·
          refine ⟨9900157208435859817911739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13200209611247813090548985 9900157208435859817911739)
          ·
            refine ⟨14850235812653789726867609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900157208435859817911739 14850235812653789726867609)
            ·
              refine ⟨11137676859490342295150707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14850235812653789726867609 11137676859490342295150707)
              ·
                refine ⟨16706515289235513442726061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11137676859490342295150707 16706515289235513442726061)
                ·
                  refine ⟨6264943233463317541022273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16706515289235513442726061 6264943233463317541022273)
                  ·
                    refine ⟨4698707425097488155766705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6264943233463317541022273 4698707425097488155766705)
                    ·
                      refine ⟨3524030568823116116825029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698707425097488155766705 3524030568823116116825029)
                      ·
                        rfl

theorem cell23_6863025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6863025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863025 prefixEnd_6863025 := by exact prefixLift 6863025
  have htrace : WordTrace (prefixWord ++ tailWord_6863025) baseStart_6863025 baseEnd_6863025 := by
    simpa [prefixWord, tailWord_6863025, baseEnd_6863025] using wordTrace_append hprefix tailTrace_6863025
  have hstable : (prefixWord ++ tailWord_6863025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863025).length < 2 ^ (prefixWord ++ tailWord_6863025).sum := by decide
  have hdescent : baseEnd_6863025 < baseStart_6863025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863038 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_6863038 : Nat := 118140960795 + 6863038 * 2 ^ 59
def prefixEnd_6863038 : Nat := 4983230072969 + 3 ^ 40 * 6863038 * 2
def baseEnd_6863038 : Nat := 3524037244071624565962469

theorem tailTrace_6863038 : CollatzResearch.WordTrace tailWord_6863038 prefixEnd_6863038 3524037244071624565962469 := by
  unfold tailWord_6863038
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289445013799114302347721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166877040073595276279187845 31289445013799114302347721)
  ·
    refine ⟨23467083760349335726760791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31289445013799114302347721 23467083760349335726760791)
    ·
      refine ⟨35200625640524003590141187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23467083760349335726760791 35200625640524003590141187)
      ·
        refine ⟨52800938460786005385211781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35200625640524003590141187 52800938460786005385211781)
        ·
          refine ⟨9900175961397376009727209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52800938460786005385211781 9900175961397376009727209)
          ·
            refine ⟨7425131971048032007295407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9900175961397376009727209 7425131971048032007295407)
            ·
              refine ⟨11137697956572048010943111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425131971048032007295407 11137697956572048010943111)
              ·
                refine ⟨16706546934858072016414667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11137697956572048010943111 16706546934858072016414667)
                ·
                  refine ⟨25059820402287108024622001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16706546934858072016414667 25059820402287108024622001)
                  ·
                    refine ⟨18794865301715331018466501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25059820402287108024622001 18794865301715331018466501)
                    ·
                      refine ⟨3524037244071624565962469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18794865301715331018466501 3524037244071624565962469)
                      ·
                        rfl

theorem cell23_6863038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_6863038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863038 prefixEnd_6863038 := by exact prefixLift 6863038
  have htrace : WordTrace (prefixWord ++ tailWord_6863038) baseStart_6863038 baseEnd_6863038 := by
    simpa [prefixWord, tailWord_6863038, baseEnd_6863038] using wordTrace_append hprefix tailTrace_6863038
  have hstable : (prefixWord ++ tailWord_6863038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863038).length < 2 ^ (prefixWord ++ tailWord_6863038).sum := by decide
  have hdescent : baseEnd_6863038 < baseStart_6863038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863042 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6863042 : Nat := 118140960795 + 6863042 * 2 ^ 59
def prefixEnd_6863042 : Nat := 4983230072969 + 3 ^ 40 * 6863042 * 2
def baseEnd_6863042 : Nat := 3524039297994242550312451

theorem tailTrace_6863042 : CollatzResearch.WordTrace tailWord_6863042 prefixEnd_6863042 3524039297994242550312451 := by
  unfold tailWord_6863042
  simp only [CollatzResearch.WordTrace]
  refine ⟨62578926500594605775481845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166877137334918948734618253 62578926500594605775481845)
  ·
    refine ⟨5866774359430744291451423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62578926500594605775481845 5866774359430744291451423)
    ·
      refine ⟨8800161539146116437177135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5866774359430744291451423 8800161539146116437177135)
      ·
        refine ⟨13200242308719174655765703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800161539146116437177135 13200242308719174655765703)
        ·
          refine ⟨19800363463078761983648555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200242308719174655765703 19800363463078761983648555)
          ·
            refine ⟨29700545194618142975472833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19800363463078761983648555 29700545194618142975472833)
            ·
              refine ⟨22275408895963607231604625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29700545194618142975472833 22275408895963607231604625)
              ·
                refine ⟨16706556671972705423703469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22275408895963607231604625 16706556671972705423703469)
                ·
                  refine ⟨6264958751989764533888801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16706556671972705423703469 6264958751989764533888801)
                  ·
                    refine ⟨4698719063992323400416601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6264958751989764533888801 4698719063992323400416601)
                    ·
                      refine ⟨3524039297994242550312451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698719063992323400416601 3524039297994242550312451)
                      ·
                        rfl

theorem cell23_6863042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6863042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863042 prefixEnd_6863042 := by exact prefixLift 6863042
  have htrace : WordTrace (prefixWord ++ tailWord_6863042) baseStart_6863042 baseEnd_6863042 := by
    simpa [prefixWord, tailWord_6863042, baseEnd_6863042] using wordTrace_append hprefix tailTrace_6863042
  have hstable : (prefixWord ++ tailWord_6863042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863042).length < 2 ^ (prefixWord ++ tailWord_6863042).sum := by decide
  have hdescent : baseEnd_6863042 < baseStart_6863042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863054 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6863054 : Nat := 118140960795 + 6863054 * 2 ^ 59
def prefixEnd_6863054 : Nat := 4983230072969 + 3 ^ 40 * 6863054 * 2
def baseEnd_6863054 : Nat := 3524045459762096503362395

theorem tailTrace_6863054 : CollatzResearch.WordTrace tailWord_6863054 prefixEnd_6863054 3524045459762096503362395 := by
  unfold tailWord_6863054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289517959791868643920527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166877429118889966100909477 31289517959791868643920527)
  ·
    refine ⟨46934276939687802965880791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31289517959791868643920527 46934276939687802965880791)
    ·
      refine ⟨70401415409531704448821187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46934276939687802965880791 70401415409531704448821187)
      ·
        refine ⟨105602123114297556673231781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70401415409531704448821187 105602123114297556673231781)
        ·
          refine ⟨19800398083930791876230959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105602123114297556673231781 19800398083930791876230959)
          ·
            refine ⟨29700597125896187814346439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19800398083930791876230959 29700597125896187814346439)
            ·
              refine ⟨44550895688844281721519659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29700597125896187814346439 44550895688844281721519659)
              ·
                refine ⟨66826343533266422582279489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44550895688844281721519659 66826343533266422582279489)
                ·
                  refine ⟨50119757649949816936709617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66826343533266422582279489 50119757649949816936709617)
                  ·
                    refine ⟨37589818237462362702532213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50119757649949816936709617 37589818237462362702532213)
                    ·
                      refine ⟨3524045459762096503362395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37589818237462362702532213 3524045459762096503362395)
                      ·
                        rfl

theorem cell23_6863054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6863054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863054 prefixEnd_6863054 := by exact prefixLift 6863054
  have htrace : WordTrace (prefixWord ++ tailWord_6863054) baseStart_6863054 baseEnd_6863054 := by
    simpa [prefixWord, tailWord_6863054, baseEnd_6863054] using wordTrace_append hprefix tailTrace_6863054
  have hstable : (prefixWord ++ tailWord_6863054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863054).length < 2 ^ (prefixWord ++ tailWord_6863054).sum := by decide
  have hdescent : baseEnd_6863054 < baseStart_6863054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863057 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_6863057 : Nat := 118140960795 + 6863057 * 2 ^ 59
def prefixEnd_6863057 : Nat := 4983230072969 + 3 ^ 40 * 6863057 * 2
def baseEnd_6863057 : Nat := 1174682333401353330541627

theorem tailTrace_6863057 : CollatzResearch.WordTrace tailWord_6863057 prefixEnd_6863057 1174682333401353330541627 := by
  unfold tailWord_6863057
  simp only [CollatzResearch.WordTrace]
  refine ⟨250316253097324080663723425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166877502064882720442482283 250316253097324080663723425)
  ·
    refine ⟨187737189822993060497792569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250316253097324080663723425 187737189822993060497792569)
    ·
      refine ⟨140802892367244795373344427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187737189822993060497792569 140802892367244795373344427)
      ·
        refine ⟨211204338550867193060016641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140802892367244795373344427 211204338550867193060016641)
        ·
          refine ⟨158403253913150394795012481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211204338550867193060016641 158403253913150394795012481)
          ·
            refine ⟨118802440434862796096259361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158403253913150394795012481 118802440434862796096259361)
            ·
              refine ⟨89101830326147097072194521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118802440434862796096259361 89101830326147097072194521)
              ·
                refine ⟨66826372744610322804145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89101830326147097072194521 66826372744610322804145891)
                ·
                  refine ⟨100239559116915484206218837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66826372744610322804145891 100239559116915484206218837)
                  ·
                    refine ⟨1174682333401353330541627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100239559116915484206218837 1174682333401353330541627)
                    ·
                      rfl

theorem cell23_6863057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_6863057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863057 prefixEnd_6863057 := by exact prefixLift 6863057
  have htrace : WordTrace (prefixWord ++ tailWord_6863057) baseStart_6863057 baseEnd_6863057 := by
    simpa [prefixWord, tailWord_6863057, baseEnd_6863057] using wordTrace_append hprefix tailTrace_6863057
  have hstable : (prefixWord ++ tailWord_6863057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863057).length < 2 ^ (prefixWord ++ tailWord_6863057).sum := by decide
  have hdescent : baseEnd_6863057 < baseStart_6863057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_6863067 : Nat := 118140960795 + 6863067 * 2 ^ 59
def prefixEnd_6863067 : Nat := 4983230072969 + 3 ^ 40 * 6863067 * 2
def baseEnd_6863067 : Nat := 3524052135010604952499835

theorem tailTrace_6863067 : CollatzResearch.WordTrace tailWord_6863067 prefixEnd_6863067 3524052135010604952499835 := by
  unfold tailWord_6863067
  simp only [CollatzResearch.WordTrace]
  refine ⟨250316617827287852371587455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166877745218191901581058303 250316617827287852371587455)
  ·
    refine ⟨375474926740931778557381183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250316617827287852371587455 375474926740931778557381183)
    ·
      refine ⟨563212390111397667836071775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375474926740931778557381183 563212390111397667836071775)
      ·
        refine ⟨844818585167096501754107663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563212390111397667836071775 844818585167096501754107663)
        ·
          refine ⟨1267227877750644752631161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844818585167096501754107663 1267227877750644752631161495)
          ·
            refine ⟨1900841816625967128946742243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267227877750644752631161495 1900841816625967128946742243)
            ·
              refine ⟨2851262724938950693420113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900841816625967128946742243 2851262724938950693420113365)
              ·
                refine ⟨66826470115756656877033907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2851262724938950693420113365 66826470115756656877033907)
                ·
                  refine ⟨100239705173634985315550861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66826470115756656877033907 100239705173634985315550861)
                  ·
                    refine ⟨37589889440113119493331573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100239705173634985315550861 37589889440113119493331573)
                    ·
                      refine ⟨3524052135010604952499835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37589889440113119493331573 3524052135010604952499835)
                      ·
                        rfl

theorem cell23_6863067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_6863067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863067 prefixEnd_6863067 := by exact prefixLift 6863067
  have htrace : WordTrace (prefixWord ++ tailWord_6863067) baseStart_6863067 baseEnd_6863067 := by
    simpa [prefixWord, tailWord_6863067, baseEnd_6863067] using wordTrace_append hprefix tailTrace_6863067
  have hstable : (prefixWord ++ tailWord_6863067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863067).length < 2 ^ (prefixWord ++ tailWord_6863067).sum := by decide
  have hdescent : baseEnd_6863067 < baseStart_6863067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863084 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_6863084 : Nat := 118140960795 + 6863084 * 2 ^ 59
def prefixEnd_6863084 : Nat := 4983230072969 + 3 ^ 40 * 6863084 * 2
def baseEnd_6863084 : Nat := 3524060864181731385987257

theorem tailTrace_6863084 : CollatzResearch.WordTrace tailWord_6863084 prefixEnd_6863084 3524060864181731385987257 := by
  unfold tailWord_6863084
  simp only [CollatzResearch.WordTrace]
  refine ⟨125158618934113132137478153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166878158578817509516637537 125158618934113132137478153)
  ·
    refine ⟨93868964200584849103108615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125158618934113132137478153 93868964200584849103108615)
    ·
      refine ⟨140803446300877273654662923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93868964200584849103108615 140803446300877273654662923)
      ·
        refine ⟨211205169451315910481994385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140803446300877273654662923 211205169451315910481994385)
        ·
          refine ⟨158403877088486932861495789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211205169451315910481994385 158403877088486932861495789)
          ·
            refine ⟨59401453908182599823060921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158403877088486932861495789 59401453908182599823060921)
            ·
              refine ⟨44551090431136949867295691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59401453908182599823060921 44551090431136949867295691)
              ·
                refine ⟨66826635646705424800943537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44551090431136949867295691 66826635646705424800943537)
                ·
                  refine ⟨50119976735029068600707653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66826635646705424800943537 50119976735029068600707653)
                  ·
                    refine ⟨9397495637817950362632685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50119976735029068600707653 9397495637817950362632685)
                    ·
                      refine ⟨3524060864181731385987257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397495637817950362632685 3524060864181731385987257)
                      ·
                        rfl

theorem cell23_6863084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_6863084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863084 prefixEnd_6863084 := by exact prefixLift 6863084
  have htrace : WordTrace (prefixWord ++ tailWord_6863084) baseStart_6863084 baseEnd_6863084 := by
    simpa [prefixWord, tailWord_6863084, baseEnd_6863084] using wordTrace_append hprefix tailTrace_6863084
  have hstable : (prefixWord ++ tailWord_6863084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863084).length < 2 ^ (prefixWord ++ tailWord_6863084).sum := by decide
  have hdescent : baseEnd_6863084 < baseStart_6863084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863138 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_6863138 : Nat := 118140960795 + 6863138 * 2 ^ 59
def prefixEnd_6863138 : Nat := 4983230072969 + 3 ^ 40 * 6863138 * 2
def baseEnd_6863138 : Nat := 391565399126341574968001

theorem tailTrace_6863138 : CollatzResearch.WordTrace tailWord_6863138 prefixEnd_6863138 391565399126341574968001 := by
  unfold tailWord_6863138
  simp only [CollatzResearch.WordTrace]
  refine ⟨62579801852507657874355517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166879471606687087664948045 62579801852507657874355517)
  ·
    refine ⟨23467425694690371702883319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62579801852507657874355517 23467425694690371702883319)
    ·
      refine ⟨35201138542035557554324979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23467425694690371702883319 35201138542035557554324979)
      ·
        refine ⟨52801707813053336331487469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35201138542035557554324979 52801707813053336331487469)
        ·
          refine ⟨19800640429895001124307801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52801707813053336331487469 19800640429895001124307801)
          ·
            refine ⟨14850480322421250843230851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19800640429895001124307801 14850480322421250843230851)
            ·
              refine ⟨22275720483631876264846277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14850480322421250843230851 22275720483631876264846277)
              ·
                refine ⟨4176697590680976799658677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22275720483631876264846277 4176697590680976799658677)
                ·
                  refine ⟨391565399126341574968001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176697590680976799658677 391565399126341574968001)
                  ·
                    rfl

theorem cell23_6863138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_6863138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863138 prefixEnd_6863138 := by exact prefixLift 6863138
  have htrace : WordTrace (prefixWord ++ tailWord_6863138) baseStart_6863138 baseEnd_6863138 := by
    simpa [prefixWord, tailWord_6863138, baseEnd_6863138] using wordTrace_append hprefix tailTrace_6863138
  have hstable : (prefixWord ++ tailWord_6863138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863138).length < 2 ^ (prefixWord ++ tailWord_6863138).sum := by decide
  have hdescent : baseEnd_6863138 < baseStart_6863138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863171 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4]
def baseStart_6863171 : Nat := 118140960795 + 6863171 * 2 ^ 59
def prefixEnd_6863171 : Nat := 4983230072969 + 3 ^ 40 * 6863171 * 2
def baseEnd_6863171 : Nat := 3524105536998672545599357

theorem tailTrace_6863171 : CollatzResearch.WordTrace tailWord_6863171 prefixEnd_6863171 3524105536998672545599357 := by
  unfold tailWord_6863171
  simp only [CollatzResearch.WordTrace]
  refine ⟨250320411018911078133373367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166880274012607385422248911 250320411018911078133373367)
  ·
    refine ⟨375480616528366617200060051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250320411018911078133373367 375480616528366617200060051)
    ·
      refine ⟨563220924792549925800090077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375480616528366617200060051 563220924792549925800090077)
      ·
        refine ⟨211207846797206222175033779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563220924792549925800090077 211207846797206222175033779)
        ·
          refine ⟨316811770195809333262550669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211207846797206222175033779 316811770195809333262550669)
          ·
            refine ⟨118804413823428499973456501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316811770195809333262550669 118804413823428499973456501)
            ·
              refine ⟨11137913795946421872511547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118804413823428499973456501 11137913795946421872511547)
              ·
                refine ⟨16706870693919632808767321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11137913795946421872511547 16706870693919632808767321)
                ·
                  refine ⟨12530153020439724606575491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16706870693919632808767321 12530153020439724606575491)
                  ·
                    refine ⟨18795229530659586909863237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12530153020439724606575491 18795229530659586909863237)
                    ·
                      refine ⟨3524105536998672545599357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18795229530659586909863237 3524105536998672545599357)
                      ·
                        rfl

theorem cell23_6863171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_6863171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863171 prefixEnd_6863171 := by exact prefixLift 6863171
  have htrace : WordTrace (prefixWord ++ tailWord_6863171) baseStart_6863171 baseEnd_6863171 := by
    simpa [prefixWord, tailWord_6863171, baseEnd_6863171] using wordTrace_append hprefix tailTrace_6863171
  have hstable : (prefixWord ++ tailWord_6863171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863171).length < 2 ^ (prefixWord ++ tailWord_6863171).sum := by decide
  have hdescent : baseEnd_6863171 < baseStart_6863171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863184 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_6863184 : Nat := 118140960795 + 6863184 * 2 ^ 59
def prefixEnd_6863184 : Nat := 4983230072969 + 3 ^ 40 * 6863184 * 2
def baseEnd_6863184 : Nat := 3524112212247180994736797

theorem tailTrace_6863184 : CollatzResearch.WordTrace tailWord_6863184 prefixEnd_6863184 3524112212247180994736797 := by
  unfold tailWord_6863184
  simp only [CollatzResearch.WordTrace]
  refine ⟨125160442583931990676798303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166880590111909320902397737 125160442583931990676798303)
  ·
    refine ⟨187740663875897986015197455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125160442583931990676798303 187740663875897986015197455)
    ·
      refine ⟨281610995813846979022796183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187740663875897986015197455 281610995813846979022796183)
      ·
        refine ⟨422416493720770468534194275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281610995813846979022796183 422416493720770468534194275)
        ·
          refine ⟨633624740581155702801291413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422416493720770468534194275 633624740581155702801291413)
          ·
            refine ⟨29701159714741673568810535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 633624740581155702801291413 29701159714741673568810535)
            ·
              refine ⟨44551739572112510353215803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29701159714741673568810535 44551739572112510353215803)
              ·
                refine ⟨66827609358168765529823705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44551739572112510353215803 66827609358168765529823705)
                ·
                  refine ⟨50120707018626574147367779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66827609358168765529823705 50120707018626574147367779)
                  ·
                    refine ⟨75181060527939861221051669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50120707018626574147367779 75181060527939861221051669)
                    ·
                      refine ⟨3524112212247180994736797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75181060527939861221051669 3524112212247180994736797)
                      ·
                        rfl

theorem cell23_6863184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_6863184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863184 prefixEnd_6863184 := by exact prefixLift 6863184
  have htrace : WordTrace (prefixWord ++ tailWord_6863184) baseStart_6863184 baseEnd_6863184 := by
    simpa [prefixWord, tailWord_6863184, baseEnd_6863184] using wordTrace_append hprefix tailTrace_6863184
  have hstable : (prefixWord ++ tailWord_6863184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863184).length < 2 ^ (prefixWord ++ tailWord_6863184).sum := by decide
  have hdescent : baseEnd_6863184 < baseStart_6863184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863188 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_6863188 : Nat := 118140960795 + 6863188 * 2 ^ 59
def prefixEnd_6863188 : Nat := 4983230072969 + 3 ^ 40 * 6863188 * 2
def baseEnd_6863188 : Nat := 3524114266169798979086779

theorem tailTrace_6863188 : CollatzResearch.WordTrace tailWord_6863188 prefixEnd_6863188 3524114266169798979086779 := by
  unfold tailWord_6863188
  simp only [CollatzResearch.WordTrace]
  refine ⟨125160515529924745018371109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166880687373232993357828145 125160515529924745018371109)
  ·
    refine ⟨23467596661860889690944583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125160515529924745018371109 23467596661860889690944583)
    ·
      refine ⟨35201394992791334536416875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23467596661860889690944583 35201394992791334536416875)
      ·
        refine ⟨52802092489187001804625313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35201394992791334536416875 52802092489187001804625313)
        ·
          refine ⟨39601569366890251353468985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52802092489187001804625313 39601569366890251353468985)
          ·
            refine ⟨29701177025167688515101739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39601569366890251353468985 29701177025167688515101739)
            ·
              refine ⟨44551765537751532772652609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29701177025167688515101739 44551765537751532772652609)
              ·
                refine ⟨33413824153313649579489457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44551765537751532772652609 33413824153313649579489457)
                ·
                  refine ⟨25060368114985237184617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33413824153313649579489457 25060368114985237184617093)
                  ·
                    refine ⟨4698819021559731972115705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25060368114985237184617093 4698819021559731972115705)
                    ·
                      refine ⟨3524114266169798979086779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698819021559731972115705 3524114266169798979086779)
                      ·
                        rfl

theorem cell23_6863188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_6863188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863188 prefixEnd_6863188 := by exact prefixLift 6863188
  have htrace : WordTrace (prefixWord ++ tailWord_6863188) baseStart_6863188 baseEnd_6863188 := by
    simpa [prefixWord, tailWord_6863188, baseEnd_6863188] using wordTrace_append hprefix tailTrace_6863188
  have hstable : (prefixWord ++ tailWord_6863188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863188).length < 2 ^ (prefixWord ++ tailWord_6863188).sum := by decide
  have hdescent : baseEnd_6863188 < baseStart_6863188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863191 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_6863191 : Nat := 118140960795 + 6863191 * 2 ^ 59
def prefixEnd_6863191 : Nat := 4983230072969 + 3 ^ 40 * 6863191 * 2
def baseEnd_6863191 : Nat := 3524115806611762467349265

theorem tailTrace_6863191 : CollatzResearch.WordTrace tailWord_6863191 prefixEnd_6863191 3524115806611762467349265 := by
  unfold tailWord_6863191
  simp only [CollatzResearch.WordTrace]
  refine ⟨250321140478838621549101427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166880760319225747699400951 250321140478838621549101427)
  ·
    refine ⟨375481710718257932323652141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250321140478838621549101427 375481710718257932323652141)
    ·
      refine ⟨140805641519346724621369553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375481710718257932323652141 140805641519346724621369553)
      ·
        refine ⟨105604231139510043466027165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140805641519346724621369553 105604231139510043466027165)
        ·
          refine ⟨39601586677316266299760187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105604231139510043466027165 39601586677316266299760187)
          ·
            refine ⟨59402380015974399449640281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39601586677316266299760187 59402380015974399449640281)
            ·
              refine ⟨44551785011980799587230211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59402380015974399449640281 44551785011980799587230211)
              ·
                refine ⟨66827677517971199380845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44551785011980799587230211 66827677517971199380845317)
                ·
                  refine ⟨12530189534619599883908497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66827677517971199380845317 12530189534619599883908497)
                  ·
                    refine ⟨9397642150964699912931373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12530189534619599883908497 9397642150964699912931373)
                    ·
                      refine ⟨3524115806611762467349265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397642150964699912931373 3524115806611762467349265)
                      ·
                        rfl

theorem cell23_6863191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_6863191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863191 prefixEnd_6863191 := by exact prefixLift 6863191
  have htrace : WordTrace (prefixWord ++ tailWord_6863191) baseStart_6863191 baseEnd_6863191 := by
    simpa [prefixWord, tailWord_6863191, baseEnd_6863191] using wordTrace_append hprefix tailTrace_6863191
  have hstable : (prefixWord ++ tailWord_6863191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863191).length < 2 ^ (prefixWord ++ tailWord_6863191).sum := by decide
  have hdescent : baseEnd_6863191 < baseStart_6863191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863255 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6863255 : Nat := 118140960795 + 6863255 * 2 ^ 59
def prefixEnd_6863255 : Nat := 4983230072969 + 3 ^ 40 * 6863255 * 2
def baseEnd_6863255 : Nat := 3524148669373650216948971

theorem tailTrace_6863255 : CollatzResearch.WordTrace tailWord_6863255 prefixEnd_6863255 3524148669373650216948971 := by
  unfold tailWord_6863255
  simp only [CollatzResearch.WordTrace]
  refine ⟨250323474750606760479431219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166882316500404506986287479 250323474750606760479431219)
  ·
    refine ⟨375485212125910140719146829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250323474750606760479431219 375485212125910140719146829)
    ·
      refine ⟨140806954547216302769680061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375485212125910140719146829 140806954547216302769680061)
      ·
        refine ⟨52802607955206113538630023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140806954547216302769680061 52802607955206113538630023)
        ·
          refine ⟨79203911932809170307945035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52802607955206113538630023 79203911932809170307945035)
          ·
            refine ⟨118805867899213755461917553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79203911932809170307945035 118805867899213755461917553)
            ·
              refine ⟨89104400924410316596438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118805867899213755461917553 89104400924410316596438165)
              ·
                refine ⟨4176768793331733590458039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89104400924410316596438165 4176768793331733590458039)
                ·
                  refine ⟨6265153189997600385687059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176768793331733590458039 6265153189997600385687059)
                  ·
                    refine ⟨9397729784996400578530589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265153189997600385687059 9397729784996400578530589)
                    ·
                      refine ⟨3524148669373650216948971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397729784996400578530589 3524148669373650216948971)
                      ·
                        rfl

theorem cell23_6863255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6863255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863255 prefixEnd_6863255 := by exact prefixLift 6863255
  have htrace : WordTrace (prefixWord ++ tailWord_6863255) baseStart_6863255 baseEnd_6863255 := by
    simpa [prefixWord, tailWord_6863255, baseEnd_6863255] using wordTrace_append hprefix tailTrace_6863255
  have hstable : (prefixWord ++ tailWord_6863255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863255).length < 2 ^ (prefixWord ++ tailWord_6863255).sum := by decide
  have hdescent : baseEnd_6863255 < baseStart_6863255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863262 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_6863262 : Nat := 118140960795 + 6863262 * 2 ^ 59
def prefixEnd_6863262 : Nat := 4983230072969 + 3 ^ 40 * 6863262 * 2
def baseEnd_6863262 : Nat := 391572473748692409951271

theorem tailTrace_6863262 : CollatzResearch.WordTrace tailWord_6863262 prefixEnd_6863262 391572473748692409951271 := by
  unfold tailWord_6863262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290466257697675084367005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166882486707720933783290693 31290466257697675084367005)
  ·
    refine ⟨11733924846636628156637627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31290466257697675084367005 11733924846636628156637627)
    ·
      refine ⟨17600887269954942234956441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733924846636628156637627 17600887269954942234956441)
      ·
        refine ⟨13200665452466206676217331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17600887269954942234956441 13200665452466206676217331)
        ·
          refine ⟨19800998178699310014325997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200665452466206676217331 19800998178699310014325997)
          ·
            refine ⟨7425374317012241255372249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19800998178699310014325997 7425374317012241255372249)
            ·
              refine ⟨5569030737759180941529187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425374317012241255372249 5569030737759180941529187)
              ·
                refine ⟨8353546106638771412293781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569030737759180941529187 8353546106638771412293781)
                ·
                  refine ⟨391572473748692409951271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8353546106638771412293781 391572473748692409951271)
                  ·
                    rfl

theorem cell23_6863262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_6863262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863262 prefixEnd_6863262 := by exact prefixLift 6863262
  have htrace : WordTrace (prefixWord ++ tailWord_6863262) baseStart_6863262 baseEnd_6863262 := by
    simpa [prefixWord, tailWord_6863262, baseEnd_6863262] using wordTrace_append hprefix tailTrace_6863262
  have hstable : (prefixWord ++ tailWord_6863262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863262).length < 2 ^ (prefixWord ++ tailWord_6863262).sum := by decide
  have hdescent : baseEnd_6863262 < baseStart_6863262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863311 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_6863311 : Nat := 118140960795 + 6863311 * 2 ^ 59
def prefixEnd_6863311 : Nat := 4983230072969 + 3 ^ 40 * 6863311 * 2
def baseEnd_6863311 : Nat := 3524177424290301997848713

theorem tailTrace_6863311 : CollatzResearch.WordTrace tailWord_6863311 prefixEnd_6863311 3524177424290301997848713 := by
  unfold tailWord_6863311
  simp only [CollatzResearch.WordTrace]
  refine ⟨250325517238403882043469787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166883678158935921362313191 250325517238403882043469787)
  ·
    refine ⟨375488275857605823065204681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250325517238403882043469787 375488275857605823065204681)
    ·
      refine ⟨281616206893204367298903511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375488275857605823065204681 281616206893204367298903511)
      ·
        refine ⟨422424310339806550948355267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281616206893204367298903511 422424310339806550948355267)
        ·
          refine ⟨633636465509709826422532901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422424310339806550948355267 633636465509709826422532901)
          ·
            refine ⟨118806837283070592454224919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 633636465509709826422532901 118806837283070592454224919)
            ·
              refine ⟨178210255924605888681337379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118806837283070592454224919 178210255924605888681337379)
              ·
                refine ⟨267315383886908833022006069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178210255924605888681337379 267315383886908833022006069)
                ·
                  refine ⟨25060817239397703095813069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267315383886908833022006069 25060817239397703095813069)
                  ·
                    refine ⟨9397806464774138660929901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25060817239397703095813069 9397806464774138660929901)
                    ·
                      refine ⟨3524177424290301997848713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397806464774138660929901 3524177424290301997848713)
                      ·
                        rfl

theorem cell23_6863311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_6863311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863311 prefixEnd_6863311 := by exact prefixLift 6863311
  have htrace : WordTrace (prefixWord ++ tailWord_6863311) baseStart_6863311 baseEnd_6863311 := by
    simpa [prefixWord, tailWord_6863311, baseEnd_6863311] using wordTrace_append hprefix tailTrace_6863311
  have hstable : (prefixWord ++ tailWord_6863311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863311).length < 2 ^ (prefixWord ++ tailWord_6863311).sum := by decide
  have hdescent : baseEnd_6863311 < baseStart_6863311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863328 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_6863328 : Nat := 118140960795 + 6863328 * 2 ^ 59
def prefixEnd_6863328 : Nat := 4983230072969 + 3 ^ 40 * 6863328 * 2
def baseEnd_6863328 : Nat := 3524186153461428431336135

theorem tailTrace_6863328 : CollatzResearch.WordTrace tailWord_6863328 prefixEnd_6863328 3524186153461428431336135 := by
  unfold tailWord_6863328
  simp only [CollatzResearch.WordTrace]
  refine ⟨125163068639671146973419319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166884091519561529297892425 125163068639671146973419319)
  ·
    refine ⟨187744602959506720460128979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125163068639671146973419319 187744602959506720460128979)
    ·
      refine ⟨281616904439260080690193469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187744602959506720460128979 281616904439260080690193469)
      ·
        refine ⟨105606339164722530258822551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281616904439260080690193469 105606339164722530258822551)
        ·
          refine ⟨158409508747083795388233827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105606339164722530258822551 158409508747083795388233827)
          ·
            refine ⟨237614263120625693082350741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158409508747083795388233827 237614263120625693082350741)
            ·
              refine ⟨11138168583779329363235191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237614263120625693082350741 11138168583779329363235191)
              ·
                refine ⟨16707252875668994044852787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11138168583779329363235191 16707252875668994044852787)
                ·
                  refine ⟨25060879313503491067279181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16707252875668994044852787 25060879313503491067279181)
                  ·
                    refine ⟨9397829742563809150229693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25060879313503491067279181 9397829742563809150229693)
                    ·
                      refine ⟨3524186153461428431336135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9397829742563809150229693 3524186153461428431336135)
                      ·
                        rfl

theorem cell23_6863328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_6863328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863328 prefixEnd_6863328 := by exact prefixLift 6863328
  have htrace : WordTrace (prefixWord ++ tailWord_6863328) baseStart_6863328 baseEnd_6863328 := by
    simpa [prefixWord, tailWord_6863328, baseEnd_6863328] using wordTrace_append hprefix tailTrace_6863328
  have hstable : (prefixWord ++ tailWord_6863328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863328).length < 2 ^ (prefixWord ++ tailWord_6863328).sum := by decide
  have hdescent : baseEnd_6863328 < baseStart_6863328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863346 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6863346 : Nat := 118140960795 + 6863346 * 2 ^ 59
def prefixEnd_6863346 : Nat := 4983230072969 + 3 ^ 40 * 6863346 * 2
def baseEnd_6863346 : Nat := 3524195396113209360911053

theorem tailTrace_6863346 : CollatzResearch.WordTrace tailWord_6863346 prefixEnd_6863346 3524195396113209360911053 := by
  unfold tailWord_6863346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62581698448319270755248473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166884529195518055347329261 62581698448319270755248473)
  ·
    refine ⟨46936273836239453066436355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62581698448319270755248473 46936273836239453066436355)
    ·
      refine ⟨70404410754359179599654533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46936273836239453066436355 70404410754359179599654533)
      ·
        refine ⟨13200827016442346174935225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70404410754359179599654533 13200827016442346174935225)
        ·
          refine ⟨9900620262331759631201419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13200827016442346174935225 9900620262331759631201419)
          ·
            refine ⟨14850930393497639446802129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900620262331759631201419 14850930393497639446802129)
            ·
              refine ⟨11138197795123229585101597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14850930393497639446802129 11138197795123229585101597)
              ·
                refine ⟨4176824173171211094413099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11138197795123229585101597 4176824173171211094413099)
                ·
                  refine ⟨6265236259756816641619649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176824173171211094413099 6265236259756816641619649)
                  ·
                    refine ⟨4698927194817612481214737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265236259756816641619649 4698927194817612481214737)
                    ·
                      refine ⟨3524195396113209360911053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698927194817612481214737 3524195396113209360911053)
                      ·
                        rfl

theorem cell23_6863346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6863346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863346 prefixEnd_6863346 := by exact prefixLift 6863346
  have htrace : WordTrace (prefixWord ++ tailWord_6863346) baseStart_6863346 baseEnd_6863346 := by
    simpa [prefixWord, tailWord_6863346, baseEnd_6863346] using wordTrace_append hprefix tailTrace_6863346
  have hstable : (prefixWord ++ tailWord_6863346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863346).length < 2 ^ (prefixWord ++ tailWord_6863346).sum := by decide
  have hdescent : baseEnd_6863346 < baseStart_6863346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863402 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6863402 : Nat := 118140960795 + 6863402 * 2 ^ 59
def prefixEnd_6863402 : Nat := 4983230072969 + 3 ^ 40 * 6863402 * 2
def baseEnd_6863402 : Nat := 3524224151029861141810795

theorem tailTrace_6863402 : CollatzResearch.WordTrace tailWord_6863402 prefixEnd_6863402 3524224151029861141810795 := by
  unfold tailWord_6863402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62582209070268551146258115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166885890854049469723354973 62582209070268551146258115)
  ·
    refine ⟨93873313605402826719387173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62582209070268551146258115 93873313605402826719387173)
    ·
      refine ⟨17601246301013030009885095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93873313605402826719387173 17601246301013030009885095)
      ·
        refine ⟨26401869451519545014827643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17601246301013030009885095 26401869451519545014827643)
        ·
          refine ⟨39602804177279317522241465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26401869451519545014827643 39602804177279317522241465)
          ·
            refine ⟨29702103132959488141681099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39602804177279317522241465 29702103132959488141681099)
            ·
              refine ⟨44553154699439232212521649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29702103132959488141681099 44553154699439232212521649)
              ·
                refine ⟨33414866024579424159391237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44553154699439232212521649 33414866024579424159391237)
                ·
                  refine ⟨6265287379608642029885857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33414866024579424159391237 6265287379608642029885857)
                  ·
                    refine ⟨4698965534706481522414393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265287379608642029885857 4698965534706481522414393)
                    ·
                      refine ⟨3524224151029861141810795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4698965534706481522414393 3524224151029861141810795)
                      ·
                        rfl

theorem cell23_6863402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6863402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863402 prefixEnd_6863402 := by exact prefixLift 6863402
  have htrace : WordTrace (prefixWord ++ tailWord_6863402) baseStart_6863402 baseEnd_6863402 := by
    simpa [prefixWord, tailWord_6863402, baseEnd_6863402] using wordTrace_append hprefix tailTrace_6863402
  have hstable : (prefixWord ++ tailWord_6863402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863402).length < 2 ^ (prefixWord ++ tailWord_6863402).sum := by decide
  have hdescent : baseEnd_6863402 < baseStart_6863402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863425 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 7]
def baseStart_6863425 : Nat := 118140960795 + 6863425 * 2 ^ 59
def prefixEnd_6863425 : Nat := 4983230072969 + 3 ^ 40 * 6863425 * 2
def baseEnd_6863425 : Nat := 391581773453879394647021

theorem tailTrace_6863425 : CollatzResearch.WordTrace tailWord_6863425 prefixEnd_6863425 391581773453879394647021 := by
  unfold tailWord_6863425
  simp only [CollatzResearch.WordTrace]
  refine ⟨250329675159990879513119729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166886450106660586342079819 250329675159990879513119729)
  ·
    refine ⟨187747256369993159634839797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250329675159990879513119729 187747256369993159634839797)
    ·
      refine ⟨17601305284686858715766231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187747256369993159634839797 17601305284686858715766231)
      ·
        refine ⟨26401957927030288073649347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17601305284686858715766231 26401957927030288073649347)
        ·
          refine ⟨39602936890545432110474021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26401957927030288073649347 39602936890545432110474021)
          ·
            refine ⟨7425550666977268520713879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39602936890545432110474021 7425550666977268520713879)
            ·
              refine ⟨11138326000465902781070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425550666977268520713879 11138326000465902781070819)
              ·
                refine ⟨16707489000698854171606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11138326000465902781070819 16707489000698854171606229)
                ·
                  refine ⟨391581773453879394647021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16707489000698854171606229 391581773453879394647021)
                  ·
                    rfl

theorem cell23_6863425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_6863425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863425 prefixEnd_6863425 := by exact prefixLift 6863425
  have htrace : WordTrace (prefixWord ++ tailWord_6863425) baseStart_6863425 baseEnd_6863425 := by
    simpa [prefixWord, tailWord_6863425, baseEnd_6863425] using wordTrace_append hprefix tailTrace_6863425
  have hstable : (prefixWord ++ tailWord_6863425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863425).length < 2 ^ (prefixWord ++ tailWord_6863425).sum := by decide
  have hdescent : baseEnd_6863425 < baseStart_6863425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863492 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6863492 : Nat := 118140960795 + 6863492 * 2 ^ 59
def prefixEnd_6863492 : Nat := 4983230072969 + 3 ^ 40 * 6863492 * 2
def baseEnd_6863492 : Nat := 3524270364288765789685381

theorem tailTrace_6863492 : CollatzResearch.WordTrace tailWord_6863492 prefixEnd_6863492 3524270364288765789685381 := by
  unfold tailWord_6863492
  simp only [CollatzResearch.WordTrace]
  refine ⟨125166059425374074977904365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166888079233832099970539153 125166059425374074977904365)
  ·
    refine ⟨46937272284515278116714137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125166059425374074977904365 46937272284515278116714137)
    ·
      refine ⟨35202954213386458587535603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46937272284515278116714137 35202954213386458587535603)
      ·
        refine ⟨52804431320079687881303405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35202954213386458587535603 52804431320079687881303405)
        ·
          refine ⟨19801661745029882955488777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52804431320079687881303405 19801661745029882955488777)
          ·
            refine ⟨14851246308772412216616583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19801661745029882955488777 14851246308772412216616583)
            ·
              refine ⟨22276869463158618324924875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851246308772412216616583 22276869463158618324924875)
              ·
                refine ⟨33415304194737927487387313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22276869463158618324924875 33415304194737927487387313)
                ·
                  refine ⟨25061478146053445615540485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33415304194737927487387313 25061478146053445615540485)
                  ·
                    refine ⟨4699027152385021052913841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25061478146053445615540485 4699027152385021052913841)
                    ·
                      refine ⟨3524270364288765789685381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699027152385021052913841 3524270364288765789685381)
                      ·
                        rfl

theorem cell23_6863492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6863492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863492 prefixEnd_6863492 := by exact prefixLift 6863492
  have htrace : WordTrace (prefixWord ++ tailWord_6863492) baseStart_6863492 baseEnd_6863492 := by
    simpa [prefixWord, tailWord_6863492, baseEnd_6863492] using wordTrace_append hprefix tailTrace_6863492
  have hstable : (prefixWord ++ tailWord_6863492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863492).length < 2 ^ (prefixWord ++ tailWord_6863492).sum := by decide
  have hdescent : baseEnd_6863492 < baseStart_6863492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863525 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_6863525 : Nat := 118140960795 + 6863525 * 2 ^ 59
def prefixEnd_6863525 : Nat := 4983230072969 + 3 ^ 40 * 6863525 * 2
def baseEnd_6863525 : Nat := 3524287309150364160572729

theorem tailTrace_6863525 : CollatzResearch.WordTrace tailWord_6863525 prefixEnd_6863525 3524287309150364160572729 := by
  unfold tailWord_6863525
  simp only [CollatzResearch.WordTrace]
  refine ⟨250333322459628596591760029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166888881639752397727840019 250333322459628596591760029)
  ·
    refine ⟨93874995922360723721910011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250333322459628596591760029 93874995922360723721910011)
    ·
      refine ⟨140812493883541085582865017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93874995922360723721910011 140812493883541085582865017)
      ·
        refine ⟨105609370412655814187148763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140812493883541085582865017 105609370412655814187148763)
        ·
          refine ⟨158414055618983721280723145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105609370412655814187148763 158414055618983721280723145)
          ·
            refine ⟨118810541714237790960542359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158414055618983721280723145 118810541714237790960542359)
            ·
              refine ⟨178215812571356686440813539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118810541714237790960542359 178215812571356686440813539)
              ·
                refine ⟨267323718857035029661220309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178215812571356686440813539 267323718857035029661220309)
                ·
                  refine ⟨6265399660711758507684851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267323718857035029661220309 6265399660711758507684851)
                  ·
                    refine ⟨9398099491067637761527277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265399660711758507684851 9398099491067637761527277)
                    ·
                      refine ⟨3524287309150364160572729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398099491067637761527277 3524287309150364160572729)
                      ·
                        rfl

theorem cell23_6863525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_6863525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863525 prefixEnd_6863525 := by exact prefixLift 6863525
  have htrace : WordTrace (prefixWord ++ tailWord_6863525) baseStart_6863525 baseEnd_6863525 := by
    simpa [prefixWord, tailWord_6863525, baseEnd_6863525] using wordTrace_append hprefix tailTrace_6863525
  have hstable : (prefixWord ++ tailWord_6863525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863525).length < 2 ^ (prefixWord ++ tailWord_6863525).sum := by decide
  have hdescent : baseEnd_6863525 < baseStart_6863525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863562 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_6863562 : Nat := 118140960795 + 6863562 * 2 ^ 59
def prefixEnd_6863562 : Nat := 4983230072969 + 3 ^ 40 * 6863562 * 2
def baseEnd_6863562 : Nat := 1174768769311526838603353

theorem tailTrace_6863562 : CollatzResearch.WordTrace tailWord_6863562 prefixEnd_6863562 1174768769311526838603353 := by
  unfold tailWord_6863562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62583667990123637977714235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166889781306996367940571293 62583667990123637977714235)
  ·
    refine ⟨93875501985185456966571353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62583667990123637977714235 93875501985185456966571353)
    ·
      refine ⟨70406626488889092724928515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93875501985185456966571353 70406626488889092724928515)
      ·
        refine ⟨105609939733333639087392773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70406626488889092724928515 105609939733333639087392773)
        ·
          refine ⟨19801863700000057328886145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105609939733333639087392773 19801863700000057328886145)
          ·
            refine ⟨14851397775000042996664609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19801863700000057328886145 14851397775000042996664609)
            ·
              refine ⟨11138548331250032247498457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14851397775000042996664609 11138548331250032247498457)
              ·
                refine ⟨8353911248437524185623843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11138548331250032247498457 8353911248437524185623843)
                ·
                  refine ⟨12530866872656286278435765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8353911248437524185623843 12530866872656286278435765)
                  ·
                    refine ⟨1174768769311526838603353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12530866872656286278435765 1174768769311526838603353)
                    ·
                      rfl

theorem cell23_6863562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_6863562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863562 prefixEnd_6863562 := by exact prefixLift 6863562
  have htrace : WordTrace (prefixWord ++ tailWord_6863562) baseStart_6863562 baseEnd_6863562 := by
    simpa [prefixWord, tailWord_6863562, baseEnd_6863562] using wordTrace_append hprefix tailTrace_6863562
  have hstable : (prefixWord ++ tailWord_6863562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863562).length < 2 ^ (prefixWord ++ tailWord_6863562).sum := by decide
  have hdescent : baseEnd_6863562 < baseStart_6863562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863575 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 4, 4]
def baseStart_6863575 : Nat := 118140960795 + 6863575 * 2 ^ 59
def prefixEnd_6863575 : Nat := 4983230072969 + 3 ^ 40 * 6863575 * 2
def baseEnd_6863575 : Nat := 1174770994394362988315833

theorem tailTrace_6863575 : CollatzResearch.WordTrace tailWord_6863575 prefixEnd_6863575 1174770994394362988315833 := by
  unfold tailWord_6863575
  simp only [CollatzResearch.WordTrace]
  refine ⟨250335146109447455131080179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166890097406298303420720119 250335146109447455131080179)
  ·
    refine ⟨375502719164171182696620269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250335146109447455131080179 375502719164171182696620269)
    ·
      refine ⟨140813519686564193511232601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375502719164171182696620269 140813519686564193511232601)
      ·
        refine ⟨105610139764923145133424451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140813519686564193511232601 105610139764923145133424451)
        ·
          refine ⟨158415209647384717700136677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105610139764923145133424451 158415209647384717700136677)
          ·
            refine ⟨29702851808884634568775627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158415209647384717700136677 29702851808884634568775627)
            ·
              refine ⟨44554277713326951853163441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29702851808884634568775627 44554277713326951853163441)
              ·
                refine ⟨33415708284995213889872581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44554277713326951853163441 33415708284995213889872581)
                ·
                  refine ⟨6265445303436602604351109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33415708284995213889872581 6265445303436602604351109)
                  ·
                    refine ⟨1174770994394362988315833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265445303436602604351109 1174770994394362988315833)
                    ·
                      rfl

theorem cell23_6863575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_6863575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863575 prefixEnd_6863575 := by exact prefixLift 6863575
  have htrace : WordTrace (prefixWord ++ tailWord_6863575) baseStart_6863575 baseEnd_6863575 := by
    simpa [prefixWord, tailWord_6863575, baseEnd_6863575] using wordTrace_append hprefix tailTrace_6863575
  have hstable : (prefixWord ++ tailWord_6863575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863575).length < 2 ^ (prefixWord ++ tailWord_6863575).sum := by decide
  have hdescent : baseEnd_6863575 < baseStart_6863575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863576 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_6863576 : Nat := 118140960795 + 6863576 * 2 ^ 59
def prefixEnd_6863576 : Nat := 4983230072969 + 3 ^ 40 * 6863576 * 2
def baseEnd_6863576 : Nat := 3524313496663743461034995

theorem tailTrace_6863576 : CollatzResearch.WordTrace tailWord_6863576 prefixEnd_6863576 3524313496663743461034995 := by
  unfold tailWord_6863576
  simp only [CollatzResearch.WordTrace]
  refine ⟨125167591291221916150933291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166890121721629221534577721 125167591291221916150933291)
  ·
    refine ⟨187751386936832874226399937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125167591291221916150933291 187751386936832874226399937)
    ·
      refine ⟨140813540202624655669799953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187751386936832874226399937 140813540202624655669799953)
      ·
        refine ⟨105610155151968491752349965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140813540202624655669799953 105610155151968491752349965)
        ·
          refine ⟨39603808181988184407131237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105610155151968491752349965 39603808181988184407131237)
          ·
            refine ⟨7425714034122784576337107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39603808181988184407131237 7425714034122784576337107)
            ·
              refine ⟨11138571051184176864505661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425714034122784576337107 11138571051184176864505661)
              ·
                refine ⟨4176964144194066324189623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11138571051184176864505661 4176964144194066324189623)
                ·
                  refine ⟨6265446216291099486284435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176964144194066324189623 6265446216291099486284435)
                  ·
                    refine ⟨9398169324436649229426653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265446216291099486284435 9398169324436649229426653)
                    ·
                      refine ⟨3524313496663743461034995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398169324436649229426653 3524313496663743461034995)
                      ·
                        rfl

theorem cell23_6863576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_6863576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863576 prefixEnd_6863576 := by exact prefixLift 6863576
  have htrace : WordTrace (prefixWord ++ tailWord_6863576) baseStart_6863576 baseEnd_6863576 := by
    simpa [prefixWord, tailWord_6863576, baseEnd_6863576] using wordTrace_append hprefix tailTrace_6863576
  have hstable : (prefixWord ++ tailWord_6863576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863576).length < 2 ^ (prefixWord ++ tailWord_6863576).sum := by decide
  have hdescent : baseEnd_6863576 < baseStart_6863576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863585 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6863585 : Nat := 118140960795 + 6863585 * 2 ^ 59
def prefixEnd_6863585 : Nat := 4983230072969 + 3 ^ 40 * 6863585 * 2
def baseEnd_6863585 : Nat := 3524318117989633925822453

theorem tailTrace_6863585 : CollatzResearch.WordTrace tailWord_6863585 prefixEnd_6863585 3524318117989633925822453 := by
  unfold tailWord_6863585
  simp only [CollatzResearch.WordTrace]
  refine ⟨250335510839411226838944209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166890340559607484559296139 250335510839411226838944209)
  ·
    refine ⟨187751633129558420129208157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250335510839411226838944209 187751633129558420129208157)
    ·
      refine ⟨70406862423584407548453059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187751633129558420129208157 70406862423584407548453059)
      ·
        refine ⟨105610293635376611322679589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70406862423584407548453059 105610293635376611322679589)
        ·
          refine ⟨19801930056633114623002423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105610293635376611322679589 19801930056633114623002423)
          ·
            refine ⟨29702895084949671934503635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19801930056633114623002423 29702895084949671934503635)
            ·
              refine ⟨44554342627424507901755453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29702895084949671934503635 44554342627424507901755453)
              ·
                refine ⟨16707878485284190463158295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44554342627424507901755453 16707878485284190463158295)
                ·
                  refine ⟨25061817727926285694737443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16707878485284190463158295 25061817727926285694737443)
                  ·
                    refine ⟨37592726591889428542106165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25061817727926285694737443 37592726591889428542106165)
                    ·
                      refine ⟨3524318117989633925822453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37592726591889428542106165 3524318117989633925822453)
                      ·
                        rfl

theorem cell23_6863585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6863585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863585 prefixEnd_6863585 := by exact prefixLift 6863585
  have htrace : WordTrace (prefixWord ++ tailWord_6863585) baseStart_6863585 baseEnd_6863585 := by
    simpa [prefixWord, tailWord_6863585, baseEnd_6863585] using wordTrace_append hprefix tailTrace_6863585
  have hstable : (prefixWord ++ tailWord_6863585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863585).length < 2 ^ (prefixWord ++ tailWord_6863585).sum := by decide
  have hdescent : baseEnd_6863585 < baseStart_6863585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863588 : List Nat := [2, 3, 1, 1, 1, 4, 11]
def baseStart_6863588 : Nat := 118140960795 + 6863588 * 2 ^ 59
def prefixEnd_6863588 : Nat := 4983230072969 + 3 ^ 40 * 6863588 * 2
def baseEnd_6863588 : Nat := 43510119239896264371419

theorem tailTrace_6863588 : CollatzResearch.WordTrace tailWord_6863588 prefixEnd_6863588 43510119239896264371419 := by
  unfold tailWord_6863588
  simp only [CollatzResearch.WordTrace]
  refine ⟨125167810129200179175651709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166890413505600238900868945 125167810129200179175651709)
  ·
    refine ⟨46937928798450067190869391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125167810129200179175651709 46937928798450067190869391)
    ·
      refine ⟨70406893197675100786304087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46937928798450067190869391 70406893197675100786304087)
      ·
        refine ⟨105610339796512651179456131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70406893197675100786304087 105610339796512651179456131)
        ·
          refine ⟨158415509694768976769184197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105610339796512651179456131 158415509694768976769184197)
          ·
            refine ⟨29702908067769183144222037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158415509694768976769184197 29702908067769183144222037)
            ·
              refine ⟨43510119239896264371419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29702908067769183144222037 43510119239896264371419)
              ·
                rfl

theorem cell23_6863588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 11].length) (baseStart_6863588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863588 prefixEnd_6863588 := by exact prefixLift 6863588
  have htrace : WordTrace (prefixWord ++ tailWord_6863588) baseStart_6863588 baseEnd_6863588 := by
    simpa [prefixWord, tailWord_6863588, baseEnd_6863588] using wordTrace_append hprefix tailTrace_6863588
  have hstable : (prefixWord ++ tailWord_6863588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863588).length < 2 ^ (prefixWord ++ tailWord_6863588).sum := by decide
  have hdescent : baseEnd_6863588 < baseStart_6863588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863599 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 3, 2, 2]
def baseStart_6863599 : Nat := 118140960795 + 6863599 * 2 ^ 59
def prefixEnd_6863599 : Nat := 4983230072969 + 3 ^ 40 * 6863599 * 2
def baseEnd_6863599 : Nat := 3524325306718796871047389

theorem tailTrace_6863599 : CollatzResearch.WordTrace tailWord_6863599 prefixEnd_6863599 3524325306718796871047389 := by
  unfold tailWord_6863599
  simp only [CollatzResearch.WordTrace]
  refine ⟨250336021461360507229953851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166890680974240338153302567 250336021461360507229953851)
  ·
    refine ⟨375504032192040760844930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250336021461360507229953851 375504032192040760844930777)
    ·
      refine ⟨281628024144030570633698083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375504032192040760844930777 281628024144030570633698083)
      ·
        refine ⟨422442036216045855950547125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281628024144030570633698083 422442036216045855950547125)
        ·
          refine ⟨39603940895254298995363793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 422442036216045855950547125 39603940895254298995363793)
          ·
            refine ⟨29702955671440724246522845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39603940895254298995363793 29702955671440724246522845)
            ·
              refine ⟨11138608376790271592446067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29702955671440724246522845 11138608376790271592446067)
              ·
                refine ⟨16707912565185407388669101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11138608376790271592446067 16707912565185407388669101)
                ·
                  refine ⟨6265467211944527770750913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16707912565185407388669101 6265467211944527770750913)
                  ·
                    refine ⟨4699100408958395828063185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265467211944527770750913 4699100408958395828063185)
                    ·
                      refine ⟨3524325306718796871047389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699100408958395828063185 3524325306718796871047389)
                      ·
                        rfl

theorem cell23_6863599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 2, 2].length) (baseStart_6863599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863599 prefixEnd_6863599 := by exact prefixLift 6863599
  have htrace : WordTrace (prefixWord ++ tailWord_6863599) baseStart_6863599 baseEnd_6863599 := by
    simpa [prefixWord, tailWord_6863599, baseEnd_6863599] using wordTrace_append hprefix tailTrace_6863599
  have hstable : (prefixWord ++ tailWord_6863599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863599).length < 2 ^ (prefixWord ++ tailWord_6863599).sum := by decide
  have hdescent : baseEnd_6863599 < baseStart_6863599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863608 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_6863608 : Nat := 118140960795 + 6863608 * 2 ^ 59
def prefixEnd_6863608 : Nat := 4983230072969 + 3 ^ 40 * 6863608 * 2
def baseEnd_6863608 : Nat := 3524329928044687335834847

theorem tailTrace_6863608 : CollatzResearch.WordTrace tailWord_6863608 prefixEnd_6863608 3524329928044687335834847 := by
  unfold tailWord_6863608
  simp only [CollatzResearch.WordTrace]
  refine ⟨125168174859163950883515739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166890899812218601178020985 125168174859163950883515739)
  ·
    refine ⟨187752262288745926325273609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125168174859163950883515739 187752262288745926325273609)
    ·
      refine ⟨140814196716559444743955207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187752262288745926325273609 140814196716559444743955207)
      ·
        refine ⟨211221295074839167115932811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140814196716559444743955207 211221295074839167115932811)
        ·
          refine ⟨316831942612258750673899217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211221295074839167115932811 316831942612258750673899217)
          ·
            refine ⟨237623956959194063005424413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316831942612258750673899217 237623956959194063005424413)
            ·
              refine ⟨89108983859697773627034155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237623956959194063005424413 89108983859697773627034155)
              ·
                refine ⟨133663475789546660440551233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89108983859697773627034155 133663475789546660440551233)
                ·
                  refine ⟨100247606842159995330413425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133663475789546660440551233 100247606842159995330413425)
                  ·
                    refine ⟨75185705131619996497810069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100247606842159995330413425 75185705131619996497810069)
                    ·
                      refine ⟨3524329928044687335834847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75185705131619996497810069 3524329928044687335834847)
                      ·
                        rfl

theorem cell23_6863608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_6863608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863608 prefixEnd_6863608 := by exact prefixLift 6863608
  have htrace : WordTrace (prefixWord ++ tailWord_6863608) baseStart_6863608 baseEnd_6863608 := by
    simpa [prefixWord, tailWord_6863608, baseEnd_6863608] using wordTrace_append hprefix tailTrace_6863608
  have hstable : (prefixWord ++ tailWord_6863608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863608).length < 2 ^ (prefixWord ++ tailWord_6863608).sum := by decide
  have hdescent : baseEnd_6863608 < baseStart_6863608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863615 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_6863615 : Nat := 118140960795 + 6863615 * 2 ^ 59
def prefixEnd_6863615 : Nat := 4983230072969 + 3 ^ 40 * 6863615 * 2
def baseEnd_6863615 : Nat := 3524333522409268808447315

theorem tailTrace_6863615 : CollatzResearch.WordTrace tailWord_6863615 prefixEnd_6863615 3524333522409268808447315 := by
  unfold tailWord_6863615
  simp only [CollatzResearch.WordTrace]
  refine ⟨250336605029302541962536299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166891070019535027975024199 250336605029302541962536299)
  ·
    refine ⟨375504907543953812943804449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250336605029302541962536299 375504907543953812943804449)
    ·
      refine ⟨281628680657965359707853337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375504907543953812943804449 281628680657965359707853337)
      ·
        refine ⟨211221510493474019780890003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281628680657965359707853337 211221510493474019780890003)
        ·
          refine ⟨316832265740211029671335005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211221510493474019780890003 316832265740211029671335005)
          ·
            refine ⟨118812099652579136126750627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316832265740211029671335005 118812099652579136126750627)
            ·
              refine ⟨178218149478868704190125941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118812099652579136126750627 178218149478868704190125941)
              ·
                refine ⟨16707951513643941017824307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178218149478868704190125941 16707951513643941017824307)
                ·
                  refine ⟨25061927270465911526736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16707951513643941017824307 25061927270465911526736461)
                  ·
                    refine ⟨9398222726424716822526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25061927270465911526736461 9398222726424716822526173)
                    ·
                      refine ⟨3524333522409268808447315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398222726424716822526173 3524333522409268808447315)
                      ·
                        rfl

theorem cell23_6863615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_6863615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863615 prefixEnd_6863615 := by exact prefixLift 6863615
  have htrace : WordTrace (prefixWord ++ tailWord_6863615) baseStart_6863615 baseEnd_6863615 := by
    simpa [prefixWord, tailWord_6863615, baseEnd_6863615] using wordTrace_append hprefix tailTrace_6863615
  have hstable : (prefixWord ++ tailWord_6863615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863615).length < 2 ^ (prefixWord ++ tailWord_6863615).sum := by decide
  have hdescent : baseEnd_6863615 < baseStart_6863615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863649 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6863649 : Nat := 118140960795 + 6863649 * 2 ^ 59
def prefixEnd_6863649 : Nat := 4983230072969 + 3 ^ 40 * 6863649 * 2
def baseEnd_6863649 : Nat := 3524350980751521675422159

theorem tailTrace_6863649 : CollatzResearch.WordTrace tailWord_6863649 prefixEnd_6863649 3524350980751521675422159 := by
  unfold tailWord_6863649
  simp only [CollatzResearch.WordTrace]
  refine ⟨250337845111179365769274001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166891896740786243846182667 250337845111179365769274001)
  ·
    refine ⟨187753383833384524326955501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250337845111179365769274001 187753383833384524326955501)
    ·
      refine ⟨70407518937519196622608313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187753383833384524326955501 70407518937519196622608313)
      ·
        refine ⟨52805639203139397466956235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70407518937519196622608313 52805639203139397466956235)
        ·
          refine ⟨79208458804709096200434353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52805639203139397466956235 79208458804709096200434353)
          ·
            refine ⟨59406344103531822150325765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79208458804709096200434353 59406344103531822150325765)
            ·
              refine ⟨11138689519412216653186081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59406344103531822150325765 11138689519412216653186081)
              ·
                refine ⟨8354017139559162489889561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11138689519412216653186081 8354017139559162489889561)
                ·
                  refine ⟨6265512854669371867417171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8354017139559162489889561 6265512854669371867417171)
                  ·
                    refine ⟨9398269282004057801125757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265512854669371867417171 9398269282004057801125757)
                    ·
                      refine ⟨3524350980751521675422159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398269282004057801125757 3524350980751521675422159)
                      ·
                        rfl

theorem cell23_6863649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6863649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863649 prefixEnd_6863649 := by exact prefixLift 6863649
  have htrace : WordTrace (prefixWord ++ tailWord_6863649) baseStart_6863649 baseEnd_6863649 := by
    simpa [prefixWord, tailWord_6863649, baseEnd_6863649] using wordTrace_append hprefix tailTrace_6863649
  have hstable : (prefixWord ++ tailWord_6863649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863649).length < 2 ^ (prefixWord ++ tailWord_6863649).sum := by decide
  have hdescent : baseEnd_6863649 < baseStart_6863649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863650 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_6863650 : Nat := 118140960795 + 6863650 * 2 ^ 59
def prefixEnd_6863650 : Nat := 4983230072969 + 3 ^ 40 * 6863650 * 2
def baseEnd_6863650 : Nat := 3524351494232176171509655

theorem tailTrace_6863650 : CollatzResearch.WordTrace tailWord_6863650 prefixEnd_6863650 3524351494232176171509655 := by
  unfold tailWord_6863650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62584470396043935735015101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166891921056117161960040269 62584470396043935735015101)
  ·
    refine ⟨23469176398516475900630663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62584470396043935735015101 23469176398516475900630663)
    ·
      refine ⟨35203764597774713850945995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469176398516475900630663 35203764597774713850945995)
      ·
        refine ⟨52805646896662070776418993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35203764597774713850945995 52805646896662070776418993)
        ·
          refine ⟨39604235172496553082314245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52805646896662070776418993 39604235172496553082314245)
          ·
            refine ⟨7425794094843103702933921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39604235172496553082314245 7425794094843103702933921)
            ·
              refine ⟨5569345571132327777200441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425794094843103702933921 5569345571132327777200441)
              ·
                refine ⟨4177009178349245832900331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569345571132327777200441 4177009178349245832900331)
                ·
                  refine ⟨6265513767523868749350497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177009178349245832900331 6265513767523868749350497)
                  ·
                    refine ⟨4699135325642901562012873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265513767523868749350497 4699135325642901562012873)
                    ·
                      refine ⟨3524351494232176171509655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699135325642901562012873 3524351494232176171509655)
                      ·
                        rfl

theorem cell23_6863650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_6863650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863650 prefixEnd_6863650 := by exact prefixLift 6863650
  have htrace : WordTrace (prefixWord ++ tailWord_6863650) baseStart_6863650 baseEnd_6863650 := by
    simpa [prefixWord, tailWord_6863650, baseEnd_6863650] using wordTrace_append hprefix tailTrace_6863650
  have hstable : (prefixWord ++ tailWord_6863650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863650).length < 2 ^ (prefixWord ++ tailWord_6863650).sum := by decide
  have hdescent : baseEnd_6863650 < baseStart_6863650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863665 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_6863665 : Nat := 118140960795 + 6863665 * 2 ^ 59
def prefixEnd_6863665 : Nat := 4983230072969 + 3 ^ 40 * 6863665 * 2
def baseEnd_6863665 : Nat := 1174786398813997870940695

theorem tailTrace_6863665 : CollatzResearch.WordTrace tailWord_6863665 prefixEnd_6863665 1174786398813997870940695 := by
  unfold tailWord_6863665
  simp only [CollatzResearch.WordTrace]
  refine ⟨250338428679121400501856449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166892285786080933667904299 250338428679121400501856449)
  ·
    refine ⟨187753821509341050376392337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250338428679121400501856449 187753821509341050376392337)
    ·
      refine ⟨140815366132005787782294253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187753821509341050376392337 140815366132005787782294253)
      ·
        refine ⟨52805762299502170418360345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140815366132005787782294253 52805762299502170418360345)
        ·
          refine ⟨39604321724626627813770259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52805762299502170418360345 39604321724626627813770259)
          ·
            refine ⟨59406482586939941720655389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39604321724626627813770259 59406482586939941720655389)
            ·
              refine ⟨22277430970102478145245771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59406482586939941720655389 22277430970102478145245771)
              ·
                refine ⟨33416146455153717217868657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22277430970102478145245771 33416146455153717217868657)
                ·
                  refine ⟨25062109841365287913401493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33416146455153717217868657 25062109841365287913401493)
                  ·
                    refine ⟨1174786398813997870940695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25062109841365287913401493 1174786398813997870940695)
                    ·
                      rfl

theorem cell23_6863665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_6863665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863665 prefixEnd_6863665 := by exact prefixLift 6863665
  have htrace : WordTrace (prefixWord ++ tailWord_6863665) baseStart_6863665 baseEnd_6863665 := by
    simpa [prefixWord, tailWord_6863665, baseEnd_6863665] using wordTrace_append hprefix tailTrace_6863665
  have hstable : (prefixWord ++ tailWord_6863665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863665).length < 2 ^ (prefixWord ++ tailWord_6863665).sum := by decide
  have hdescent : baseEnd_6863665 < baseStart_6863665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863693 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6863693 : Nat := 118140960795 + 6863693 * 2 ^ 59
def prefixEnd_6863693 : Nat := 4983230072969 + 3 ^ 40 * 6863693 * 2
def baseEnd_6863693 : Nat := 3524373573900319503271957

theorem tailTrace_6863693 : CollatzResearch.WordTrace tailWord_6863693 prefixEnd_6863693 3524373573900319503271957 := by
  unfold tailWord_6863693
  simp only [CollatzResearch.WordTrace]
  refine ⟨250339449923019961283875733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166892966615346640855917155 250339449923019961283875733)
  ·
    refine ⟨11734661715141560685181675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250339449923019961283875733 11734661715141560685181675)
    ·
      refine ⟨17601992572712341027772513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11734661715141560685181675 17601992572712341027772513)
      ·
        refine ⟨13201494429534255770829385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17601992572712341027772513 13201494429534255770829385)
        ·
          refine ⟨9901120822150691828122039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13201494429534255770829385 9901120822150691828122039)
          ·
            refine ⟨14851681233226037742183059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901120822150691828122039 14851681233226037742183059)
            ·
              refine ⟨22277521849839056613274589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851681233226037742183059 22277521849839056613274589)
              ·
                refine ⟨8354070693689646229977971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22277521849839056613274589 8354070693689646229977971)
                ·
                  refine ⟨12531106040534469344966957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354070693689646229977971 12531106040534469344966957)
                  ·
                    refine ⟨4699164765200426004362609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12531106040534469344966957 4699164765200426004362609)
                    ·
                      refine ⟨3524373573900319503271957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699164765200426004362609 3524373573900319503271957)
                      ·
                        rfl

theorem cell23_6863693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6863693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863693 prefixEnd_6863693 := by exact prefixLift 6863693
  have htrace : WordTrace (prefixWord ++ tailWord_6863693) baseStart_6863693 baseEnd_6863693 := by
    simpa [prefixWord, tailWord_6863693, baseEnd_6863693] using wordTrace_append hprefix tailTrace_6863693
  have hstable : (prefixWord ++ tailWord_6863693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863693).length < 2 ^ (prefixWord ++ tailWord_6863693).sum := by decide
  have hdescent : baseEnd_6863693 < baseStart_6863693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863706 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_6863706 : Nat := 118140960795 + 6863706 * 2 ^ 59
def prefixEnd_6863706 : Nat := 4983230072969 + 3 ^ 40 * 6863706 * 2
def baseEnd_6863706 : Nat := 3524380249148827952409397

theorem tailTrace_6863706 : CollatzResearch.WordTrace tailWord_6863706 prefixEnd_6863706 3524380249148827952409397 := by
  unfold tailWord_6863706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62584981017993216126024743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166893282714648576336065981 62584981017993216126024743)
  ·
    refine ⟨93877471526989824189037115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62584981017993216126024743 93877471526989824189037115)
    ·
      refine ⟨140816207290484736283555673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93877471526989824189037115 140816207290484736283555673)
      ·
        refine ⟨105612155467863552212666755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140816207290484736283555673 105612155467863552212666755)
        ·
          refine ⟨158418233201795328319000133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105612155467863552212666755 158418233201795328319000133)
          ·
            refine ⟨29703418725336624059812525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158418233201795328319000133 29703418725336624059812525)
            ·
              refine ⟨11138782022001234022429697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29703418725336624059812525 11138782022001234022429697)
              ·
                refine ⟨8354086516500925516822273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11138782022001234022429697 8354086516500925516822273)
                ·
                  refine ⟨6265564887375694137616705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8354086516500925516822273 6265564887375694137616705)
                  ·
                    refine ⟨4699173665531770603212529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265564887375694137616705 4699173665531770603212529)
                    ·
                      refine ⟨3524380249148827952409397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699173665531770603212529 3524380249148827952409397)
                      ·
                        rfl

theorem cell23_6863706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_6863706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863706 prefixEnd_6863706 := by exact prefixLift 6863706
  have htrace : WordTrace (prefixWord ++ tailWord_6863706) baseStart_6863706 baseEnd_6863706 := by
    simpa [prefixWord, tailWord_6863706, baseEnd_6863706] using wordTrace_append hprefix tailTrace_6863706
  have hstable : (prefixWord ++ tailWord_6863706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863706).length < 2 ^ (prefixWord ++ tailWord_6863706).sum := by decide
  have hdescent : baseEnd_6863706 < baseStart_6863706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863712 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 5]
def baseStart_6863712 : Nat := 118140960795 + 6863712 * 2 ^ 59
def prefixEnd_6863712 : Nat := 4983230072969 + 3 ^ 40 * 6863712 * 2
def baseEnd_6863712 : Nat := 391598147781417214326041

theorem tailTrace_6863712 : CollatzResearch.WordTrace tailWord_6863712 prefixEnd_6863712 391598147781417214326041 := by
  unfold tailWord_6863712
  simp only [CollatzResearch.WordTrace]
  refine ⟨125170071454975563764408695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166893428606634085019211593 125170071454975563764408695)
  ·
    refine ⟨187755107182463345646613043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125170071454975563764408695 187755107182463345646613043)
    ·
      refine ⟨281632660773695018469919565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187755107182463345646613043 281632660773695018469919565)
      ·
        refine ⟨105612247790135631926219837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281632660773695018469919565 105612247790135631926219837)
        ·
          refine ⟨39604592921300861972332439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105612247790135631926219837 39604592921300861972332439)
          ·
            refine ⟨59406889381951292958498659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39604592921300861972332439 59406889381951292958498659)
            ·
              refine ⟨89110334072926939437747989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59406889381951292958498659 89110334072926939437747989)
              ·
                refine ⟨4177046909668450286144437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89110334072926939437747989 4177046909668450286144437)
                ·
                  refine ⟨391598147781417214326041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177046909668450286144437 391598147781417214326041)
                  ·
                    rfl

theorem cell23_6863712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 5].length) (baseStart_6863712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863712 prefixEnd_6863712 := by exact prefixLift 6863712
  have htrace : WordTrace (prefixWord ++ tailWord_6863712) baseStart_6863712 baseEnd_6863712 := by
    simpa [prefixWord, tailWord_6863712, baseEnd_6863712] using wordTrace_append hprefix tailTrace_6863712
  have hstable : (prefixWord ++ tailWord_6863712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863712).length < 2 ^ (prefixWord ++ tailWord_6863712).sum := by decide
  have hdescent : baseEnd_6863712 < baseStart_6863712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863796 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6863796 : Nat := 118140960795 + 6863796 * 2 ^ 59
def prefixEnd_6863796 : Nat := 4983230072969 + 3 ^ 40 * 6863796 * 2
def baseEnd_6863796 : Nat := 3524426462407732600283983

theorem tailTrace_6863796 : CollatzResearch.WordTrace tailWord_6863796 prefixEnd_6863796 3524426462407732600283983 := by
  unfold tailWord_6863796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125171603320823404937437621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166895471094431206583250161 125171603320823404937437621)
  ·
    refine ⟨11734837811327194212884777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125171603320823404937437621 11734837811327194212884777)
    ·
      refine ⟨8801128358495395659663583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11734837811327194212884777 8801128358495395659663583)
      ·
        refine ⟨13201692537743093489495375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801128358495395659663583 13201692537743093489495375)
        ·
          refine ⟨19802538806614640234243063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201692537743093489495375 19802538806614640234243063)
          ·
            refine ⟨29703808209921960351364595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19802538806614640234243063 29703808209921960351364595)
            ·
              refine ⟨44555712314882940527046893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29703808209921960351364595 44555712314882940527046893)
              ·
                refine ⟨16708392118081102697642585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44555712314882940527046893 16708392118081102697642585)
                ·
                  refine ⟨12531294088560827023231939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16708392118081102697642585 12531294088560827023231939)
                  ·
                    refine ⟨18796941132841240534847909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12531294088560827023231939 18796941132841240534847909)
                    ·
                      refine ⟨3524426462407732600283983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18796941132841240534847909 3524426462407732600283983)
                      ·
                        rfl

theorem cell23_6863796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6863796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863796 prefixEnd_6863796 := by exact prefixLift 6863796
  have htrace : WordTrace (prefixWord ++ tailWord_6863796) baseStart_6863796 baseEnd_6863796 := by
    simpa [prefixWord, tailWord_6863796, baseEnd_6863796] using wordTrace_append hprefix tailTrace_6863796
  have hstable : (prefixWord ++ tailWord_6863796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863796).length < 2 ^ (prefixWord ++ tailWord_6863796).sum := by decide
  have hdescent : baseEnd_6863796 < baseStart_6863796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863806 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6863806 : Nat := 118140960795 + 6863806 * 2 ^ 59
def prefixEnd_6863806 : Nat := 4983230072969 + 3 ^ 40 * 6863806 * 2
def baseEnd_6863806 : Nat := 1174810532404759187052979

theorem tailTrace_6863806 : CollatzResearch.WordTrace tailWord_6863806 prefixEnd_6863806 1174810532404759187052979 := by
  unfold tailWord_6863806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292946421451322697842409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166895714247740387721826181 31292946421451322697842409)
  ·
    refine ⟨23469709816088492023381807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31292946421451322697842409 23469709816088492023381807)
    ·
      refine ⟨35204564724132738035072711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469709816088492023381807 35204564724132738035072711)
      ·
        refine ⟨52806847086199107052609067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35204564724132738035072711 52806847086199107052609067)
        ·
          refine ⟨79210270629298660578913601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52806847086199107052609067 79210270629298660578913601)
          ·
            refine ⟨59407702971973995434185201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79210270629298660578913601 59407702971973995434185201)
            ·
              refine ⟨44555777228980496575638901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59407702971973995434185201 44555777228980496575638901)
              ·
                refine ⟨4177104115216921553966147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44555777228980496575638901 4177104115216921553966147)
                ·
                  refine ⟨6265656172825382330949221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177104115216921553966147 6265656172825382330949221)
                  ·
                    refine ⟨1174810532404759187052979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265656172825382330949221 1174810532404759187052979)
                    ·
                      rfl

theorem cell23_6863806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6863806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863806 prefixEnd_6863806 := by exact prefixLift 6863806
  have htrace : WordTrace (prefixWord ++ tailWord_6863806) baseStart_6863806 baseEnd_6863806 := by
    simpa [prefixWord, tailWord_6863806, baseEnd_6863806] using wordTrace_append hprefix tailTrace_6863806
  have hstable : (prefixWord ++ tailWord_6863806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863806).length < 2 ^ (prefixWord ++ tailWord_6863806).sum := by decide
  have hdescent : baseEnd_6863806 < baseStart_6863806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863814 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_6863814 : Nat := 118140960795 + 6863814 * 2 ^ 59
def prefixEnd_6863814 : Nat := 4983230072969 + 3 ^ 40 * 6863814 * 2
def baseEnd_6863814 : Nat := 391603967228834836650989

theorem tailTrace_6863814 : CollatzResearch.WordTrace tailWord_6863814 prefixEnd_6863814 391603967228834836650989 := by
  unfold tailWord_6863814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823245723611924967157203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166895908770387732632686997 7823245723611924967157203)
  ·
    refine ⟨11734868585417887450735805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7823245723611924967157203 11734868585417887450735805)
    ·
      refine ⟨4400575719531707794025927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11734868585417887450735805 4400575719531707794025927)
      ·
        refine ⟨6600863579297561691038891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400575719531707794025927 6600863579297561691038891)
        ·
          refine ⟨9901295368946342536558337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600863579297561691038891 9901295368946342536558337)
          ·
            refine ⟨7425971526709756902418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9901295368946342536558337 7425971526709756902418753)
            ·
              refine ⟨5569478645032317676814065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425971526709756902418753 5569478645032317676814065)
              ·
                refine ⟨4177108983774238257610549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569478645032317676814065 4177108983774238257610549)
                ·
                  refine ⟨391603967228834836650989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177108983774238257610549 391603967228834836650989)
                  ·
                    rfl

theorem cell23_6863814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_6863814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863814 prefixEnd_6863814 := by exact prefixLift 6863814
  have htrace : WordTrace (prefixWord ++ tailWord_6863814) baseStart_6863814 baseEnd_6863814 := by
    simpa [prefixWord, tailWord_6863814, baseEnd_6863814] using wordTrace_append hprefix tailTrace_6863814
  have hstable : (prefixWord ++ tailWord_6863814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863814).length < 2 ^ (prefixWord ++ tailWord_6863814).sum := by decide
  have hdescent : baseEnd_6863814 < baseStart_6863814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863823 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 1, 4]
def baseStart_6863823 : Nat := 118140960795 + 6863823 * 2 ^ 59
def prefixEnd_6863823 : Nat := 4983230072969 + 3 ^ 40 * 6863823 * 2
def baseEnd_6863823 : Nat := 1174813442128467998215453

theorem tailTrace_6863823 : CollatzResearch.WordTrace tailWord_6863823 prefixEnd_6863823 1174813442128467998215453 := by
  unfold tailWord_6863823
  simp only [CollatzResearch.WordTrace]
  refine ⟨250344191412548993486108123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166896127608365995657405415 250344191412548993486108123)
  ·
    refine ⟨375516287118823490229162185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250344191412548993486108123 375516287118823490229162185)
    ·
      refine ⟨281637215339117617671871639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375516287118823490229162185 281637215339117617671871639)
      ·
        refine ⟨422455823008676426507807459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281637215339117617671871639 422455823008676426507807459)
        ·
          refine ⟨633683734513014639761711189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422455823008676426507807459 633683734513014639761711189)
          ·
            refine ⟨7425981263824390309707553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 633683734513014639761711189 7425981263824390309707553)
            ·
              refine ⟨5569485947868292732280665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425981263824390309707553 5569485947868292732280665)
              ·
                refine ⟨4177114460901219549210499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569485947868292732280665 4177114460901219549210499)
                ·
                  refine ⟨6265671691351829323815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177114460901219549210499 6265671691351829323815749)
                  ·
                    refine ⟨1174813442128467998215453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265671691351829323815749 1174813442128467998215453)
                    ·
                      rfl

theorem cell23_6863823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_6863823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863823 prefixEnd_6863823 := by exact prefixLift 6863823
  have htrace : WordTrace (prefixWord ++ tailWord_6863823) baseStart_6863823 baseEnd_6863823 := by
    simpa [prefixWord, tailWord_6863823, baseEnd_6863823] using wordTrace_append hprefix tailTrace_6863823
  have hstable : (prefixWord ++ tailWord_6863823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863823).length < 2 ^ (prefixWord ++ tailWord_6863823).sum := by decide
  have hdescent : baseEnd_6863823 < baseStart_6863823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863832 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_6863832 : Nat := 118140960795 + 6863832 * 2 ^ 59
def prefixEnd_6863832 : Nat := 4983230072969 + 3 ^ 40 * 6863832 * 2
def baseEnd_6863832 : Nat := 1174814982570431486477939

theorem tailTrace_6863832 : CollatzResearch.WordTrace tailWord_6863832 prefixEnd_6863832 1174814982570431486477939 := by
  unfold tailWord_6863832
  simp only [CollatzResearch.WordTrace]
  refine ⟨125172259834758194011592875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166896346446344258682123833 125172259834758194011592875)
  ·
    refine ⟨187758389752137291017389313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125172259834758194011592875 187758389752137291017389313)
    ·
      refine ⟨140818792314102968263041985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187758389752137291017389313 140818792314102968263041985)
      ·
        refine ⟨105614094235577226197281489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140818792314102968263041985 105614094235577226197281489)
        ·
          refine ⟨79210570676682919647961117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105614094235577226197281489 79210570676682919647961117)
          ·
            refine ⟨29703964003756094867985419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79210570676682919647961117 29703964003756094867985419)
            ·
              refine ⟨44555946005634142301978129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29703964003756094867985419 44555946005634142301978129)
              ·
                refine ⟨33416959504225606726483597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44555946005634142301978129 33416959504225606726483597)
                ·
                  refine ⟨12531359814084602522431349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33416959504225606726483597 12531359814084602522431349)
                  ·
                    refine ⟨1174814982570431486477939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12531359814084602522431349 1174814982570431486477939)
                    ·
                      rfl

theorem cell23_6863832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_6863832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863832 prefixEnd_6863832 := by exact prefixLift 6863832
  have htrace : WordTrace (prefixWord ++ tailWord_6863832) baseStart_6863832 baseEnd_6863832 := by
    simpa [prefixWord, tailWord_6863832, baseEnd_6863832] using wordTrace_append hprefix tailTrace_6863832
  have hstable : (prefixWord ++ tailWord_6863832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863832).length < 2 ^ (prefixWord ++ tailWord_6863832).sum := by decide
  have hdescent : baseEnd_6863832 < baseStart_6863832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863879 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 4, 4]
def baseStart_6863879 : Nat := 118140960795 + 6863879 * 2 ^ 59
def prefixEnd_6863879 : Nat := 4983230072969 + 3 ^ 40 * 6863879 * 2
def baseEnd_6863879 : Nat := 1174823027100685258515367

theorem tailTrace_6863879 : CollatzResearch.WordTrace tailWord_6863879 prefixEnd_6863879 1174823027100685258515367 := by
  unfold tailWord_6863879
  simp only [CollatzResearch.WordTrace]
  refine ⟨250346233900346115050146691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166897489266897410033431127 250346233900346115050146691)
  ·
    refine ⟨375519350850519172575220037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250346233900346115050146691 375519350850519172575220037)
    ·
      refine ⟨70409878284472344857853757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375519350850519172575220037 70409878284472344857853757)
      ·
        refine ⟨26403704356677129321695159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70409878284472344857853757 26403704356677129321695159)
        ·
          refine ⟨39605556535015693982542739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26403704356677129321695159 39605556535015693982542739)
          ·
            refine ⟨59408334802523540973814109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39605556535015693982542739 59408334802523540973814109)
            ·
              refine ⟨22278125550946327865180291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59408334802523540973814109 22278125550946327865180291)
              ·
                refine ⟨33417188326419491797770437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22278125550946327865180291 33417188326419491797770437)
                ·
                  refine ⟨6265722811203654712081957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33417188326419491797770437 6265722811203654712081957)
                  ·
                    refine ⟨1174823027100685258515367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265722811203654712081957 1174823027100685258515367)
                    ·
                      rfl

theorem cell23_6863879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_6863879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863879 prefixEnd_6863879 := by exact prefixLift 6863879
  have htrace : WordTrace (prefixWord ++ tailWord_6863879) baseStart_6863879 baseEnd_6863879 := by
    simpa [prefixWord, tailWord_6863879, baseEnd_6863879] using wordTrace_append hprefix tailTrace_6863879
  have hstable : (prefixWord ++ tailWord_6863879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863879).length < 2 ^ (prefixWord ++ tailWord_6863879).sum := by decide
  have hdescent : baseEnd_6863879 < baseStart_6863879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863906 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_6863906 : Nat := 118140960795 + 6863906 * 2 ^ 59
def prefixEnd_6863906 : Nat := 4983230072969 + 3 ^ 40 * 6863906 * 2
def baseEnd_6863906 : Nat := 3524482945279727169908477

theorem tailTrace_6863906 : CollatzResearch.WordTrace tailWord_6863906 prefixEnd_6863906 3524482945279727169908477 := by
  unfold tailWord_6863906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62586804667812074665344893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166898145780832199107586381 62586804667812074665344893)
  ·
    refine ⟨23470051750429527999504335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62586804667812074665344893 23470051750429527999504335)
    ·
      refine ⟨35205077625644291999256503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23470051750429527999504335 35205077625644291999256503)
      ·
        refine ⟨52807616438466437998884755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35205077625644291999256503 52807616438466437998884755)
        ·
          refine ⟨79211424657699656998327133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52807616438466437998884755 79211424657699656998327133)
          ·
            refine ⟨29704284246637371374372675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79211424657699656998327133 29704284246637371374372675)
            ·
              refine ⟨44556426369956057061559013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29704284246637371374372675 44556426369956057061559013)
              ·
                refine ⟨8354329944366760699042315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44556426369956057061559013 8354329944366760699042315)
                ·
                  refine ⟨12531494916550141048563473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354329944366760699042315 12531494916550141048563473)
                  ·
                    refine ⟨9398621187412605786422605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12531494916550141048563473 9398621187412605786422605)
                    ·
                      refine ⟨3524482945279727169908477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398621187412605786422605 3524482945279727169908477)
                      ·
                        rfl

theorem cell23_6863906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_6863906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863906 prefixEnd_6863906 := by exact prefixLift 6863906
  have htrace : WordTrace (prefixWord ++ tailWord_6863906) baseStart_6863906 baseEnd_6863906 := by
    simpa [prefixWord, tailWord_6863906, baseEnd_6863906] using wordTrace_append hprefix tailTrace_6863906
  have hstable : (prefixWord ++ tailWord_6863906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863906).length < 2 ^ (prefixWord ++ tailWord_6863906).sum := by decide
  have hdescent : baseEnd_6863906 < baseStart_6863906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863936 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_6863936 : Nat := 118140960795 + 6863936 * 2 ^ 59
def prefixEnd_6863936 : Nat := 4983230072969 + 3 ^ 40 * 6863936 * 2
def baseEnd_6863936 : Nat := 3524498349699362052533339

theorem tailTrace_6863936 : CollatzResearch.WordTrace tailWord_6863936 prefixEnd_6863936 3524498349699362052533339 := by
  unfold tailWord_6863936
  simp only [CollatzResearch.WordTrace]
  refine ⟨125174156430569806892485831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166898875240759742523314441 125174156430569806892485831)
  ·
    refine ⟨187761234645854710338728747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125174156430569806892485831 187761234645854710338728747)
    ·
      refine ⟨281641851968782065508093121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187761234645854710338728747 281641851968782065508093121)
      ·
        refine ⟨211231388976586549131069841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281641851968782065508093121 211231388976586549131069841)
        ·
          refine ⟨158423541732439911848302381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211231388976586549131069841 158423541732439911848302381)
          ·
            refine ⟨59408828149664966943113393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158423541732439911848302381 59408828149664966943113393)
            ·
              refine ⟨44556621112248725207335045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59408828149664966943113393 44556621112248725207335045)
              ·
                refine ⟨8354366458546635976375321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44556621112248725207335045 8354366458546635976375321)
                ·
                  refine ⟨6265774843909976982281491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8354366458546635976375321 6265774843909976982281491)
                  ·
                    refine ⟨9398662265864965473422237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265774843909976982281491 9398662265864965473422237)
                    ·
                      refine ⟨3524498349699362052533339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398662265864965473422237 3524498349699362052533339)
                      ·
                        rfl

theorem cell23_6863936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_6863936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863936 prefixEnd_6863936 := by exact prefixLift 6863936
  have htrace : WordTrace (prefixWord ++ tailWord_6863936) baseStart_6863936 baseEnd_6863936 := by
    simpa [prefixWord, tailWord_6863936, baseEnd_6863936] using wordTrace_append hprefix tailTrace_6863936
  have hstable : (prefixWord ++ tailWord_6863936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863936).length < 2 ^ (prefixWord ++ tailWord_6863936).sum := by decide
  have hdescent : baseEnd_6863936 < baseStart_6863936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863937 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6863937 : Nat := 118140960795 + 6863937 * 2 ^ 59
def prefixEnd_6863937 : Nat := 4983230072969 + 3 ^ 40 * 6863937 * 2
def baseEnd_6863937 : Nat := 3524498863180016548620835

theorem tailTrace_6863937 : CollatzResearch.WordTrace tailWord_6863937 prefixEnd_6863937 3524498863180016548620835 := by
  unfold tailWord_6863937
  simp only [CollatzResearch.WordTrace]
  refine ⟨250348349334135990955758065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166898899556090660637172043 250348349334135990955758065)
  ·
    refine ⟨187761262000601993216818549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250348349334135990955758065 187761262000601993216818549)
    ·
      refine ⟨17602618312556436864076739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187761262000601993216818549 17602618312556436864076739)
      ·
        refine ⟨26403927468834655296115109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17602618312556436864076739 26403927468834655296115109)
        ·
          refine ⟨4950736400406497868021583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26403927468834655296115109 4950736400406497868021583)
          ·
            refine ⟨7426104600609746802032375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950736400406497868021583 7426104600609746802032375)
            ·
              refine ⟨11139156900914620203048563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426104600609746802032375 11139156900914620203048563)
              ·
                refine ⟨16708735351371930304572845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11139156900914620203048563 16708735351371930304572845)
                ·
                  refine ⟨6265775756764473864214817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16708735351371930304572845 6265775756764473864214817)
                  ·
                    refine ⟨4699331817573355398161113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265775756764473864214817 4699331817573355398161113)
                    ·
                      refine ⟨3524498863180016548620835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699331817573355398161113 3524498863180016548620835)
                      ·
                        rfl

theorem cell23_6863937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6863937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863937 prefixEnd_6863937 := by exact prefixLift 6863937
  have htrace : WordTrace (prefixWord ++ tailWord_6863937) baseStart_6863937 baseEnd_6863937 := by
    simpa [prefixWord, tailWord_6863937, baseEnd_6863937] using wordTrace_append hprefix tailTrace_6863937
  have hstable : (prefixWord ++ tailWord_6863937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863937).length < 2 ^ (prefixWord ++ tailWord_6863937).sum := by decide
  have hdescent : baseEnd_6863937 < baseStart_6863937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863952 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_6863952 : Nat := 118140960795 + 6863952 * 2 ^ 59
def prefixEnd_6863952 : Nat := 4983230072969 + 3 ^ 40 * 6863952 * 2
def baseEnd_6863952 : Nat := 1174835521796611329977755

theorem tailTrace_6863952 : CollatzResearch.WordTrace tailWord_6863952 prefixEnd_6863952 1174835521796611329977755 := by
  unfold tailWord_6863952
  simp only [CollatzResearch.WordTrace]
  refine ⟨125174448214540824258777055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166899264286054432345036073 125174448214540824258777055)
  ·
    refine ⟨187761672321811236388165583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125174448214540824258777055 187761672321811236388165583)
    ·
      refine ⟨281642508482716854582248375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187761672321811236388165583 281642508482716854582248375)
      ·
        refine ⟨422463762724075281873372563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281642508482716854582248375 422463762724075281873372563)
        ·
          refine ⟨633695644086112922810058845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422463762724075281873372563 633695644086112922810058845)
          ·
            refine ⟨237635866532292346053772067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633695644086112922810058845 237635866532292346053772067)
            ·
              refine ⟨356453799798438519080658101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237635866532292346053772067 356453799798438519080658101)
              ·
                refine ⟨33417543731103611163811697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356453799798438519080658101 33417543731103611163811697)
                ·
                  refine ⟨25063157798327708372858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33417543731103611163811697 25063157798327708372858773)
                  ·
                    refine ⟨1174835521796611329977755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25063157798327708372858773 1174835521796611329977755)
                    ·
                      rfl

theorem cell23_6863952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_6863952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863952 prefixEnd_6863952 := by exact prefixLift 6863952
  have htrace : WordTrace (prefixWord ++ tailWord_6863952) baseStart_6863952 baseEnd_6863952 := by
    simpa [prefixWord, tailWord_6863952, baseEnd_6863952] using wordTrace_append hprefix tailTrace_6863952
  have hstable : (prefixWord ++ tailWord_6863952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863952).length < 2 ^ (prefixWord ++ tailWord_6863952).sum := by decide
  have hdescent : baseEnd_6863952 < baseStart_6863952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863953 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_6863953 : Nat := 118140960795 + 6863953 * 2 ^ 59
def prefixEnd_6863953 : Nat := 4983230072969 + 3 ^ 40 * 6863953 * 2
def baseEnd_6863953 : Nat := 3524507078870488486020761

theorem tailTrace_6863953 : CollatzResearch.WordTrace tailWord_6863953 prefixEnd_6863953 3524507078870488486020761 := by
  unfold tailWord_6863953
  simp only [CollatzResearch.WordTrace]
  refine ⟨250348932902078025688340513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166899288601385350458893675 250348932902078025688340513)
  ·
    refine ⟨187761699676558519266255385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250348932902078025688340513 187761699676558519266255385)
    ·
      refine ⟨140821274757418889449691539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187761699676558519266255385 140821274757418889449691539)
      ·
        refine ⟨211231912136128334174537309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140821274757418889449691539 211231912136128334174537309)
        ·
          refine ⟨79211967051048125315451491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211231912136128334174537309 79211967051048125315451491)
          ·
            refine ⟨118817950576572187973177237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79211967051048125315451491 118817950576572187973177237)
            ·
              refine ⟨5569591433276821311242683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118817950576572187973177237 5569591433276821311242683)
              ·
                refine ⟨8354387149915231966864025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569591433276821311242683 8354387149915231966864025)
                ·
                  refine ⟨6265790362436423975148019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8354387149915231966864025 6265790362436423975148019)
                  ·
                    refine ⟨9398685543654635962722029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265790362436423975148019 9398685543654635962722029)
                    ·
                      refine ⟨3524507078870488486020761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398685543654635962722029 3524507078870488486020761)
                      ·
                        rfl

theorem cell23_6863953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_6863953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863953 prefixEnd_6863953 := by exact prefixLift 6863953
  have htrace : WordTrace (prefixWord ++ tailWord_6863953) baseStart_6863953 baseEnd_6863953 := by
    simpa [prefixWord, tailWord_6863953, baseEnd_6863953] using wordTrace_append hprefix tailTrace_6863953
  have hstable : (prefixWord ++ tailWord_6863953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863953).length < 2 ^ (prefixWord ++ tailWord_6863953).sum := by decide
  have hdescent : baseEnd_6863953 < baseStart_6863953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6863992 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_6863992 : Nat := 118140960795 + 6863992 * 2 ^ 59
def prefixEnd_6863992 : Nat := 4983230072969 + 3 ^ 40 * 6863992 * 2
def baseEnd_6863992 : Nat := 3524527104616013833433081

theorem tailTrace_6863992 : CollatzResearch.WordTrace tailWord_6863992 prefixEnd_6863992 3524527104616013833433081 := by
  unfold tailWord_6863992
  simp only [CollatzResearch.WordTrace]
  refine ⟨125175177674468367674505115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166900236899291156899340153 125175177674468367674505115)
  ·
    refine ⟨187762766511702551511757673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125175177674468367674505115 187762766511702551511757673)
    ·
      refine ⟨140822074883776913633818255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187762766511702551511757673 140822074883776913633818255)
      ·
        refine ⟨211233112325665370450727383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140822074883776913633818255 211233112325665370450727383)
        ·
          refine ⟨316849668488498055676091075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211233112325665370450727383 316849668488498055676091075)
          ·
            refine ⟨475274502732747083514136613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316849668488498055676091075 475274502732747083514136613)
            ·
              refine ⟨89113969262390078158900615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475274502732747083514136613 89113969262390078158900615)
              ·
                refine ⟨133670953893585117238350923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89113969262390078158900615 133670953893585117238350923)
                ·
                  refine ⟨200506430840377675857526385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133670953893585117238350923 200506430840377675857526385)
                  ·
                    refine ⟨150379823130283256893144789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200506430840377675857526385 150379823130283256893144789)
                    ·
                      refine ⟨3524527104616013833433081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150379823130283256893144789 3524527104616013833433081)
                      ·
                        rfl

theorem cell23_6863992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_6863992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6863992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6863992 prefixEnd_6863992 := by exact prefixLift 6863992
  have htrace : WordTrace (prefixWord ++ tailWord_6863992) baseStart_6863992 baseEnd_6863992 := by
    simpa [prefixWord, tailWord_6863992, baseEnd_6863992] using wordTrace_append hprefix tailTrace_6863992
  have hstable : (prefixWord ++ tailWord_6863992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6863992).length < 2 ^ (prefixWord ++ tailWord_6863992).sum := by decide
  have hdescent : baseEnd_6863992 < baseStart_6863992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6863992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864009 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_6864009 : Nat := 118140960795 + 6864009 * 2 ^ 59
def prefixEnd_6864009 : Nat := 4983230072969 + 3 ^ 40 * 6864009 * 2
def baseEnd_6864009 : Nat := 3524535833787140266920503

theorem tailTrace_6864009 : CollatzResearch.WordTrace tailWord_6864009 prefixEnd_6864009 3524535833787140266920503 := by
  unfold tailWord_6864009
  simp only [CollatzResearch.WordTrace]
  refine ⟨250350975389875147252379081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166900650259916764834919387 250350975389875147252379081)
  ·
    refine ⟨187763231542406360439284311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250350975389875147252379081 187763231542406360439284311)
    ·
      refine ⟨281644847313609540658926467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187763231542406360439284311 281644847313609540658926467)
      ·
        refine ⟨422467270970414310988389701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281644847313609540658926467 422467270970414310988389701)
        ·
          refine ⟨79212613306952683310323069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422467270970414310988389701 79212613306952683310323069)
          ·
            refine ⟨29704729990107256241371151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79212613306952683310323069 29704729990107256241371151)
            ·
              refine ⟨44557094985160884362056727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29704729990107256241371151 44557094985160884362056727)
              ·
                refine ⟨66835642477741326543085091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44557094985160884362056727 66835642477741326543085091)
                ·
                  refine ⟨100253463716611989814627637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66835642477741326543085091 100253463716611989814627637)
                  ·
                    refine ⟨9398762223432374045121341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100253463716611989814627637 9398762223432374045121341)
                    ·
                      refine ⟨3524535833787140266920503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398762223432374045121341 3524535833787140266920503)
                      ·
                        rfl

theorem cell23_6864009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_6864009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864009 prefixEnd_6864009 := by exact prefixLift 6864009
  have htrace : WordTrace (prefixWord ++ tailWord_6864009) baseStart_6864009 baseEnd_6864009 := by
    simpa [prefixWord, tailWord_6864009, baseEnd_6864009] using wordTrace_append hprefix tailTrace_6864009
  have hstable : (prefixWord ++ tailWord_6864009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864009).length < 2 ^ (prefixWord ++ tailWord_6864009).sum := by decide
  have hdescent : baseEnd_6864009 < baseStart_6864009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864029 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6864029 : Nat := 118140960795 + 6864029 * 2 ^ 59
def prefixEnd_6864029 : Nat := 4983230072969 + 3 ^ 40 * 6864029 * 2
def baseEnd_6864029 : Nat := 1174848701133410062890137

theorem tailTrace_6864029 : CollatzResearch.WordTrace tailWord_6864029 prefixEnd_6864029 1174848701133410062890137 := by
  unfold tailWord_6864029
  simp only [CollatzResearch.WordTrace]
  refine ⟨250351704849802690668107141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166901136566535127112071427 250351704849802690668107141)
  ·
    refine ⟨46940944659338004500270089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250351704849802690668107141 46940944659338004500270089)
    ·
      refine ⟨35205708494503503375202567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46940944659338004500270089 35205708494503503375202567)
      ·
        refine ⟨52808562741755255062803851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35205708494503503375202567 52808562741755255062803851)
        ·
          refine ⟨79212844112632882594205777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52808562741755255062803851 79212844112632882594205777)
          ·
            refine ⟨59409633084474661945654333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79212844112632882594205777 59409633084474661945654333)
            ·
              refine ⟨22278612406677998229620375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59409633084474661945654333 22278612406677998229620375)
              ·
                refine ⟨33417918610016997344430563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22278612406677998229620375 33417918610016997344430563)
                ·
                  refine ⟨50126877915025496016645845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33417918610016997344430563 50126877915025496016645845)
                  ·
                    refine ⟨1174848701133410062890137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50126877915025496016645845 1174848701133410062890137)
                    ·
                      rfl

theorem cell23_6864029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6864029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864029 prefixEnd_6864029 := by exact prefixLift 6864029
  have htrace : WordTrace (prefixWord ++ tailWord_6864029) baseStart_6864029 baseEnd_6864029 := by
    simpa [prefixWord, tailWord_6864029, baseEnd_6864029] using wordTrace_append hprefix tailTrace_6864029
  have hstable : (prefixWord ++ tailWord_6864029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864029).length < 2 ^ (prefixWord ++ tailWord_6864029).sum := by decide
  have hdescent : baseEnd_6864029 < baseStart_6864029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864119 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 5, 5]
def baseStart_6864119 : Nat := 118140960795 + 6864119 * 2 ^ 59
def prefixEnd_6864119 : Nat := 4983230072969 + 3 ^ 40 * 6864119 * 2
def baseEnd_6864119 : Nat := 1174864105553044945514999

theorem tailTrace_6864119 : CollatzResearch.WordTrace tailWord_6864119 prefixEnd_6864119 1174864105553044945514999 := by
  unfold tailWord_6864119
  simp only [CollatzResearch.WordTrace]
  refine ⟨250354987419476636038883411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166903324946317757359255607 250354987419476636038883411)
  ·
    refine ⟨375532481129214954058325117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250354987419476636038883411 375532481129214954058325117)
    ·
      refine ⟨140824680423455607771871919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375532481129214954058325117 140824680423455607771871919)
      ·
        refine ⟨211237020635183411657807879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140824680423455607771871919 211237020635183411657807879)
        ·
          refine ⟨316855530952775117486711819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211237020635183411657807879 316855530952775117486711819)
          ·
            refine ⟨475283296429162676230067729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316855530952775117486711819 475283296429162676230067729)
            ·
              refine ⟨356462472321872007172550797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475283296429162676230067729 356462472321872007172550797)
              ·
                refine ⟨133673427120702002689706549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356462472321872007172550797 133673427120702002689706549)
                ·
                  refine ⟨12531883792565812752159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133673427120702002689706549 12531883792565812752159989)
                  ·
                    refine ⟨1174864105553044945514999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12531883792565812752159989 1174864105553044945514999)
                    ·
                      rfl

theorem cell23_6864119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_6864119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864119 prefixEnd_6864119 := by exact prefixLift 6864119
  have htrace : WordTrace (prefixWord ++ tailWord_6864119) baseStart_6864119 baseEnd_6864119 := by
    simpa [prefixWord, tailWord_6864119, baseEnd_6864119] using wordTrace_append hprefix tailTrace_6864119
  have hstable : (prefixWord ++ tailWord_6864119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864119).length < 2 ^ (prefixWord ++ tailWord_6864119).sum := by decide
  have hdescent : baseEnd_6864119 < baseStart_6864119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864176 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_6864176 : Nat := 118140960795 + 6864176 * 2 ^ 59
def prefixEnd_6864176 : Nat := 4983230072969 + 3 ^ 40 * 6864176 * 2
def baseEnd_6864176 : Nat := 3524621585056441113532235

theorem tailTrace_6864176 : CollatzResearch.WordTrace tailWord_6864176 prefixEnd_6864176 3524621585056441113532235 := by
  unfold tailWord_6864176
  simp only [CollatzResearch.WordTrace]
  refine ⟨125178533190135067386854191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166904710920180089849138921 125178533190135067386854191)
  ·
    refine ⟨187767799785202601080281287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125178533190135067386854191 187767799785202601080281287)
    ·
      refine ⟨281651699677803901620421931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187767799785202601080281287 281651699677803901620421931)
      ·
        refine ⟨422477549516705852430632897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281651699677803901620421931 422477549516705852430632897)
        ·
          refine ⟨316858162137529389322974673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422477549516705852430632897 316858162137529389322974673)
          ·
            refine ⟨237643621603147041992231005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316858162137529389322974673 237643621603147041992231005)
            ·
              refine ⟨89116358101180140747086627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237643621603147041992231005 89116358101180140747086627)
              ·
                refine ⟨133674537151770211120629941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89116358101180140747086627 133674537151770211120629941)
                ·
                  refine ⟨12531987857978457292559057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133674537151770211120629941 12531987857978457292559057)
                  ·
                    refine ⟨9398990893483842969419293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12531987857978457292559057 9398990893483842969419293)
                    ·
                      refine ⟨3524621585056441113532235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9398990893483842969419293 3524621585056441113532235)
                      ·
                        rfl

theorem cell23_6864176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_6864176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864176 prefixEnd_6864176 := by exact prefixLift 6864176
  have htrace : WordTrace (prefixWord ++ tailWord_6864176) baseStart_6864176 baseEnd_6864176 := by
    simpa [prefixWord, tailWord_6864176, baseEnd_6864176] using wordTrace_append hprefix tailTrace_6864176
  have hstable : (prefixWord ++ tailWord_6864176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864176).length < 2 ^ (prefixWord ++ tailWord_6864176).sum := by decide
  have hdescent : baseEnd_6864176 < baseStart_6864176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864233 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 3, 3, 2]
def baseStart_6864233 : Nat := 118140960795 + 6864233 * 2 ^ 59
def prefixEnd_6864233 : Nat := 4983230072969 + 3 ^ 40 * 6864233 * 2
def baseEnd_6864233 : Nat := 3524650853453747390519473

theorem tailTrace_6864233 : CollatzResearch.WordTrace tailWord_6864233 prefixEnd_6864233 3524650853453747390519473 := by
  unfold tailWord_6864233
  simp only [CollatzResearch.WordTrace]
  refine ⟨250359145341063633508533353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166906096894042422339022235 250359145341063633508533353)
  ·
    refine ⟨187769359005797725131400015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250359145341063633508533353 187769359005797725131400015)
    ·
      refine ⟨281654038508696587697100023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187769359005797725131400015 281654038508696587697100023)
      ·
        refine ⟨422481057763044881545650035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281654038508696587697100023 422481057763044881545650035)
        ·
          refine ⟨633721586644567322318475053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422481057763044881545650035 633721586644567322318475053)
          ·
            refine ⟨237645594991712745869428145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633721586644567322318475053 237645594991712745869428145)
            ·
              refine ⟨178234196243784559402071109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237645594991712745869428145 178234196243784559402071109)
              ·
                refine ⟨33418911795709604887888333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178234196243784559402071109 33418911795709604887888333)
                ·
                  refine ⟨12532091923391101832958125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33418911795709604887888333 12532091923391101832958125)
                  ·
                    refine ⟨4699534471271663187359297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12532091923391101832958125 4699534471271663187359297)
                    ·
                      refine ⟨3524650853453747390519473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699534471271663187359297 3524650853453747390519473)
                      ·
                        rfl

theorem cell23_6864233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3, 2].length) (baseStart_6864233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864233 prefixEnd_6864233 := by exact prefixLift 6864233
  have htrace : WordTrace (prefixWord ++ tailWord_6864233) baseStart_6864233 baseEnd_6864233 := by
    simpa [prefixWord, tailWord_6864233, baseEnd_6864233] using wordTrace_append hprefix tailTrace_6864233
  have hstable : (prefixWord ++ tailWord_6864233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864233).length < 2 ^ (prefixWord ++ tailWord_6864233).sum := by decide
  have hdescent : baseEnd_6864233 < baseStart_6864233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864258 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6864258 : Nat := 118140960795 + 6864258 * 2 ^ 59
def prefixEnd_6864258 : Nat := 4983230072969 + 3 ^ 40 * 6864258 * 2
def baseEnd_6864258 : Nat := 3524663690470109792706859

theorem tailTrace_6864258 : CollatzResearch.WordTrace tailWord_6864258 prefixEnd_6864258 3524663690470109792706859 := by
  unfold tailWord_6864258
  simp only [CollatzResearch.WordTrace]
  refine ⟨62590014291493265694548357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166906704777315375185462285 62590014291493265694548357)
  ·
    refine ⟨11735627679654987317727817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62590014291493265694548357 11735627679654987317727817)
    ·
      refine ⟨8801720759741240488295863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11735627679654987317727817 8801720759741240488295863)
      ·
        refine ⟨13202581139611860732443795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801720759741240488295863 13202581139611860732443795)
        ·
          refine ⟨19803871709417791098665693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202581139611860732443795 19803871709417791098665693)
          ·
            refine ⟨7426451891031671661999635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19803871709417791098665693 7426451891031671661999635)
            ·
              refine ⟨11139677836547507492999453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426451891031671661999635 11139677836547507492999453)
              ·
                refine ⟨4177379188705315309874795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11139677836547507492999453 4177379188705315309874795)
                ·
                  refine ⟨6266068783057972964812193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177379188705315309874795 6266068783057972964812193)
                  ·
                    refine ⟨4699551587293479723609145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6266068783057972964812193 4699551587293479723609145)
                    ·
                      refine ⟨3524663690470109792706859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699551587293479723609145 3524663690470109792706859)
                      ·
                        rfl

theorem cell23_6864258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6864258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864258 prefixEnd_6864258 := by exact prefixLift 6864258
  have htrace : WordTrace (prefixWord ++ tailWord_6864258) baseStart_6864258 baseEnd_6864258 := by
    simpa [prefixWord, tailWord_6864258, baseEnd_6864258] using wordTrace_append hprefix tailTrace_6864258
  have hstable : (prefixWord ++ tailWord_6864258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864258).length < 2 ^ (prefixWord ++ tailWord_6864258).sum := by decide
  have hdescent : baseEnd_6864258 < baseStart_6864258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864370 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6864370 : Nat := 118140960795 + 6864370 * 2 ^ 59
def prefixEnd_6864370 : Nat := 4983230072969 + 3 ^ 40 * 6864370 * 2
def baseEnd_6864370 : Nat := 3524721200303413354506343

theorem tailTrace_6864370 : CollatzResearch.WordTrace tailWord_6864370 prefixEnd_6864370 3524721200303413354506343 := by
  unfold tailWord_6864370
  simp only [CollatzResearch.WordTrace]
  refine ⟨62591035535391826476567641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166909428094378203937513709 62591035535391826476567641)
  ·
    refine ⟨46943276651543869857425731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62591035535391826476567641 46943276651543869857425731)
    ·
      refine ⟨70414914977315804786138597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46943276651543869857425731 70414914977315804786138597)
      ·
        refine ⟨13202796558246713397400987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70414914977315804786138597 13202796558246713397400987)
        ·
          refine ⟨19804194837370070096101481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202796558246713397400987 19804194837370070096101481)
          ·
            refine ⟨14853146128027552572076111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19804194837370070096101481 14853146128027552572076111)
            ·
              refine ⟨22279719192041328858114167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14853146128027552572076111 22279719192041328858114167)
              ·
                refine ⟨33419578788061993287171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22279719192041328858114167 33419578788061993287171251)
                ·
                  refine ⟨50129368182092989930756877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33419578788061993287171251 50129368182092989930756877)
                  ·
                    refine ⟨18798513068284871224033829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50129368182092989930756877 18798513068284871224033829)
                    ·
                      refine ⟨3524721200303413354506343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18798513068284871224033829 3524721200303413354506343)
                      ·
                        rfl

theorem cell23_6864370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6864370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864370 prefixEnd_6864370 := by exact prefixLift 6864370
  have htrace : WordTrace (prefixWord ++ tailWord_6864370) baseStart_6864370 baseEnd_6864370 := by
    simpa [prefixWord, tailWord_6864370, baseEnd_6864370] using wordTrace_append hprefix tailTrace_6864370
  have hstable : (prefixWord ++ tailWord_6864370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864370).length < 2 ^ (prefixWord ++ tailWord_6864370).sum := by decide
  have hdescent : baseEnd_6864370 < baseStart_6864370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864413 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6864413 : Nat := 118140960795 + 6864413 * 2 ^ 59
def prefixEnd_6864413 : Nat := 4983230072969 + 3 ^ 40 * 6864413 * 2
def baseEnd_6864413 : Nat := 3524743279971556686268645

theorem tailTrace_6864413 : CollatzResearch.WordTrace tailWord_6864413 prefixEnd_6864413 3524743279971556686268645 := by
  unfold tailWord_6864413
  simp only [CollatzResearch.WordTrace]
  refine ⟨250365710480411524250085893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166910473653607682833390595 250365710480411524250085893)
  ·
    refine ⟨46943570715077160796891105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250365710480411524250085893 46943570715077160796891105)
    ·
      refine ⟨35207678036307870597668329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46943570715077160796891105 35207678036307870597668329)
      ·
        refine ⟨26405758527230902948251247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35207678036307870597668329 26405758527230902948251247)
        ·
          refine ⟨39608637790846354422376871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26405758527230902948251247 39608637790846354422376871)
          ·
            refine ⟨59412956686269531633565307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39608637790846354422376871 59412956686269531633565307)
            ·
              refine ⟨89119435029404297450347961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59412956686269531633565307 89119435029404297450347961)
              ·
                refine ⟨66839576272053223087760971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89119435029404297450347961 66839576272053223087760971)
                ·
                  refine ⟨100259364408079834631641457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66839576272053223087760971 100259364408079834631641457)
                  ·
                    refine ⟨75194523306059875973731093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100259364408079834631641457 75194523306059875973731093)
                    ·
                      refine ⟨3524743279971556686268645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75194523306059875973731093 3524743279971556686268645)
                      ·
                        rfl

theorem cell23_6864413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6864413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864413 prefixEnd_6864413 := by exact prefixLift 6864413
  have htrace : WordTrace (prefixWord ++ tailWord_6864413) baseStart_6864413 baseEnd_6864413 := by
    simpa [prefixWord, tailWord_6864413, baseEnd_6864413] using wordTrace_append hprefix tailTrace_6864413
  have hstable : (prefixWord ++ tailWord_6864413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864413).length < 2 ^ (prefixWord ++ tailWord_6864413).sum := by decide
  have hdescent : baseEnd_6864413 < baseStart_6864413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864440 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_6864440 : Nat := 118140960795 + 6864440 * 2 ^ 59
def prefixEnd_6864440 : Nat := 4983230072969 + 3 ^ 40 * 6864440 * 2
def baseEnd_6864440 : Nat := 1174919047983076026877007

theorem tailTrace_6864440 : CollatzResearch.WordTrace tailWord_6864440 prefixEnd_6864440 1174919047983076026877007 := by
  unfold tailWord_6864440
  simp only [CollatzResearch.WordTrace]
  refine ⟨125183347625656853930659387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166911130167542471907545849 125183347625656853930659387)
  ·
    refine ⟨187775021438485280895989081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125183347625656853930659387 187775021438485280895989081)
    ·
      refine ⟨140831266078863960671991811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187775021438485280895989081 140831266078863960671991811)
      ·
        refine ⟨211246899118295941007987717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140831266078863960671991811 211246899118295941007987717)
        ·
          refine ⟨39608793584680488938997697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211246899118295941007987717 39608793584680488938997697)
          ·
            refine ⟨29706595188510366704248273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39608793584680488938997697 29706595188510366704248273)
            ·
              refine ⟨22279946391382775028186205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29706595188510366704248273 22279946391382775028186205)
              ·
                refine ⟨8354979896768540635569827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22279946391382775028186205 8354979896768540635569827)
                ·
                  refine ⟨12532469845152810953354741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354979896768540635569827 12532469845152810953354741)
                  ·
                    refine ⟨1174919047983076026877007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12532469845152810953354741 1174919047983076026877007)
                    ·
                      rfl

theorem cell23_6864440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_6864440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864440 prefixEnd_6864440 := by exact prefixLift 6864440
  have htrace : WordTrace (prefixWord ++ tailWord_6864440) baseStart_6864440 baseEnd_6864440 := by
    simpa [prefixWord, tailWord_6864440, baseEnd_6864440] using wordTrace_append hprefix tailTrace_6864440
  have hstable : (prefixWord ++ tailWord_6864440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864440).length < 2 ^ (prefixWord ++ tailWord_6864440).sum := by decide
  have hdescent : baseEnd_6864440 < baseStart_6864440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864447 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 2, 3, 2]
def baseStart_6864447 : Nat := 118140960795 + 6864447 * 2 ^ 59
def prefixEnd_6864447 : Nat := 4983230072969 + 3 ^ 40 * 6864447 * 2
def baseEnd_6864447 : Nat := 3524760738313809553243489

theorem tailTrace_6864447 : CollatzResearch.WordTrace tailWord_6864447 prefixEnd_6864447 3524760738313809553243489 := by
  unfold tailWord_6864447
  simp only [CollatzResearch.WordTrace]
  refine ⟨250366950562288348056823595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166911300374858898704549063 250366950562288348056823595)
  ·
    refine ⟨375550425843432522085235393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250366950562288348056823595 375550425843432522085235393)
    ·
      refine ⟨281662819382574391563926545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375550425843432522085235393 281662819382574391563926545)
      ·
        refine ⟨211247114536930793672944909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281662819382574391563926545 211247114536930793672944909)
        ·
          refine ⟨79217667951349047627354341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211247114536930793672944909 79217667951349047627354341)
          ·
            refine ⟨14853312740877946430128939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79217667951349047627354341 14853312740877946430128939)
            ·
              refine ⟨22279969111316919645193409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14853312740877946430128939 22279969111316919645193409)
              ·
                refine ⟨16709976833487689733895057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22279969111316919645193409 16709976833487689733895057)
                ·
                  refine ⟨12532482625115767300421293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16709976833487689733895057 12532482625115767300421293)
                  ·
                    refine ⟨4699680984418412737657985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12532482625115767300421293 4699680984418412737657985)
                    ·
                      refine ⟨3524760738313809553243489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699680984418412737657985 3524760738313809553243489)
                      ·
                        rfl

theorem cell23_6864447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_6864447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864447 prefixEnd_6864447 := by exact prefixLift 6864447
  have htrace : WordTrace (prefixWord ++ tailWord_6864447) baseStart_6864447 baseEnd_6864447 := by
    simpa [prefixWord, tailWord_6864447, baseEnd_6864447] using wordTrace_append hprefix tailTrace_6864447
  have hstable : (prefixWord ++ tailWord_6864447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864447).length < 2 ^ (prefixWord ++ tailWord_6864447).sum := by decide
  have hdescent : baseEnd_6864447 < baseStart_6864447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864461 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 6]
def baseStart_6864461 : Nat := 118140960795 + 6864461 * 2 ^ 59
def prefixEnd_6864461 : Nat := 4983230072969 + 3 ^ 40 * 6864461 * 2
def baseEnd_6864461 : Nat := 391640880782552499829825

theorem tailTrace_6864461 : CollatzResearch.WordTrace tailWord_6864461 prefixEnd_6864461 391640880782552499829825 := by
  unfold tailWord_6864461
  simp only [CollatzResearch.WordTrace]
  refine ⟨250367461184237628447833237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166911640789491752298555491 250367461184237628447833237)
  ·
    refine ⟨11735974743011138833492183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250367461184237628447833237 11735974743011138833492183)
    ·
      refine ⟨17603962114516708250238275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11735974743011138833492183 17603962114516708250238275)
      ·
        refine ⟨26405943171775062375357413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17603962114516708250238275 26405943171775062375357413)
        ·
          refine ⟨4951114344707824195379515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26405943171775062375357413 4951114344707824195379515)
          ·
            refine ⟨7426671517061736293069273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951114344707824195379515 7426671517061736293069273)
            ·
              refine ⟨5570003637796302219801955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7426671517061736293069273 5570003637796302219801955)
              ·
                refine ⟨8355005456694453329702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570003637796302219801955 8355005456694453329702933)
                ·
                  refine ⟨391640880782552499829825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8355005456694453329702933 391640880782552499829825)
                  ·
                    rfl

theorem cell23_6864461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_6864461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864461 prefixEnd_6864461 := by exact prefixLift 6864461
  have htrace : WordTrace (prefixWord ++ tailWord_6864461) baseStart_6864461 baseEnd_6864461 := by
    simpa [prefixWord, tailWord_6864461, baseEnd_6864461] using wordTrace_append hprefix tailTrace_6864461
  have hstable : (prefixWord ++ tailWord_6864461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864461).length < 2 ^ (prefixWord ++ tailWord_6864461).sum := by decide
  have hdescent : baseEnd_6864461 < baseStart_6864461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864463 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_6864463 : Nat := 118140960795 + 6864463 * 2 ^ 59
def prefixEnd_6864463 : Nat := 4983230072969 + 3 ^ 40 * 6864463 * 2
def baseEnd_6864463 : Nat := 3524768954004281490643415

theorem tailTrace_6864463 : CollatzResearch.WordTrace tailWord_6864463 prefixEnd_6864463 3524768954004281490643415 := by
  unfold tailWord_6864463
  simp only [CollatzResearch.WordTrace]
  refine ⟨250367534130230382789406043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166911689420153588526270695 250367534130230382789406043)
  ·
    refine ⟨375551301195345574184109065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250367534130230382789406043 375551301195345574184109065)
    ·
      refine ⟨281663475896509180638081799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375551301195345574184109065 281663475896509180638081799)
      ·
        refine ⟨422495213844763770957122699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281663475896509180638081799 422495213844763770957122699)
        ·
          refine ⟨633742820767145656435684049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422495213844763770957122699 633742820767145656435684049)
          ·
            refine ⟨475307115575359242326763037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633742820767145656435684049 475307115575359242326763037)
            ·
              refine ⟨178240168340759715872536139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475307115575359242326763037 178240168340759715872536139)
              ·
                refine ⟨267360252511139573808804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178240168340759715872536139 267360252511139573808804209)
                ·
                  refine ⟨200520189383354680356603157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267360252511139573808804209 200520189383354680356603157)
                  ·
                    refine ⟨9399383877344750641715773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200520189383354680356603157 9399383877344750641715773)
                    ·
                      refine ⟨3524768954004281490643415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9399383877344750641715773 3524768954004281490643415)
                      ·
                        rfl

theorem cell23_6864463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_6864463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864463 prefixEnd_6864463 := by exact prefixLift 6864463
  have htrace : WordTrace (prefixWord ++ tailWord_6864463) baseStart_6864463 baseEnd_6864463 := by
    simpa [prefixWord, tailWord_6864463, baseEnd_6864463] using wordTrace_append hprefix tailTrace_6864463
  have hstable : (prefixWord ++ tailWord_6864463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864463).length < 2 ^ (prefixWord ++ tailWord_6864463).sum := by decide
  have hdescent : baseEnd_6864463 < baseStart_6864463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864473 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6864473 : Nat := 118140960795 + 6864473 * 2 ^ 59
def prefixEnd_6864473 : Nat := 4983230072969 + 3 ^ 40 * 6864473 * 2
def baseEnd_6864473 : Nat := 3524774088810826451518369

theorem tailTrace_6864473 : CollatzResearch.WordTrace tailWord_6864473 prefixEnd_6864473 3524774088810826451518369 := by
  unfold tailWord_6864473
  simp only [CollatzResearch.WordTrace]
  refine ⟨250367898860194154497270073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166911932573462769664846715 250367898860194154497270073)
  ·
    refine ⟨187775924145145615872952555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250367898860194154497270073 187775924145145615872952555)
    ·
      refine ⟨281663886217718423809428833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187775924145145615872952555 281663886217718423809428833)
      ·
        refine ⟨211247914663288817857071625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281663886217718423809428833 211247914663288817857071625)
        ·
          refine ⟨158435935997466613392803719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211247914663288817857071625 158435935997466613392803719)
          ·
            refine ⟨237653903996199920089205579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158435935997466613392803719 237653903996199920089205579)
            ·
              refine ⟨356480855994299880133808369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237653903996199920089205579 356480855994299880133808369)
              ·
                refine ⟨267360641995724910100356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356480855994299880133808369 267360641995724910100356277)
                ·
                  refine ⟨25065060187099210321908401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267360641995724910100356277 25065060187099210321908401)
                  ·
                    refine ⟨18798795140324407741431301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25065060187099210321908401 18798795140324407741431301)
                    ·
                      refine ⟨3524774088810826451518369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18798795140324407741431301 3524774088810826451518369)
                      ·
                        rfl

theorem cell23_6864473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6864473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864473 prefixEnd_6864473 := by exact prefixLift 6864473
  have htrace : WordTrace (prefixWord ++ tailWord_6864473) baseStart_6864473 baseEnd_6864473 := by
    simpa [prefixWord, tailWord_6864473, baseEnd_6864473] using wordTrace_append hprefix tailTrace_6864473
  have hstable : (prefixWord ++ tailWord_6864473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864473).length < 2 ^ (prefixWord ++ tailWord_6864473).sum := by decide
  have hdescent : baseEnd_6864473 < baseStart_6864473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864483 : List Nat := [1, 1, 1, 5, 1, 3, 2, 9]
def baseStart_6864483 : Nat := 118140960795 + 6864483 * 2 ^ 59
def prefixEnd_6864483 : Nat := 4983230072969 + 3 ^ 40 * 6864483 * 2
def baseEnd_6864483 : Nat := 130547378652495237496049

theorem tailTrace_6864483 : CollatzResearch.WordTrace tailWord_6864483 prefixEnd_6864483 130547378652495237496049 := by
  unfold tailWord_6864483
  simp only [CollatzResearch.WordTrace]
  refine ⟨250368263590157926205134103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166912175726771950803422735 250368263590157926205134103)
  ·
    refine ⟨375552395385236889307701155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250368263590157926205134103 375552395385236889307701155)
    ·
      refine ⟨563328593077855333961551733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375552395385236889307701155 563328593077855333961551733)
      ·
        refine ⟨52812055601048937558895475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 563328593077855333961551733 52812055601048937558895475)
        ·
          refine ⟨79218083401573406338343213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52812055601048937558895475 79218083401573406338343213)
          ·
            refine ⟨29706781275590027376878705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79218083401573406338343213 29706781275590027376878705)
            ·
              refine ⟨22280085956692520532659029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29706781275590027376878705 22280085956692520532659029)
              ·
                refine ⟨130547378652495237496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22280085956692520532659029 130547378652495237496049)
                ·
                  rfl

theorem cell23_6864483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 9].length) (baseStart_6864483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864483 prefixEnd_6864483 := by exact prefixLift 6864483
  have htrace : WordTrace (prefixWord ++ tailWord_6864483) baseStart_6864483 baseEnd_6864483 := by
    simpa [prefixWord, tailWord_6864483, baseEnd_6864483] using wordTrace_append hprefix tailTrace_6864483
  have hstable : (prefixWord ++ tailWord_6864483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864483).length < 2 ^ (prefixWord ++ tailWord_6864483).sum := by decide
  have hdescent : baseEnd_6864483 < baseStart_6864483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864490 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6864490 : Nat := 118140960795 + 6864490 * 2 ^ 59
def prefixEnd_6864490 : Nat := 4983230072969 + 3 ^ 40 * 6864490 * 2
def baseEnd_6864490 : Nat := 3524782817981952885005791

theorem tailTrace_6864490 : CollatzResearch.WordTrace tailWord_6864490 prefixEnd_6864490 3524782817981952885005791 := by
  unfold tailWord_6864490
  simp only [CollatzResearch.WordTrace]
  refine ⟨62592129725283141600159731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166912345934088377600425949 62592129725283141600159731)
  ·
    refine ⟨93888194587924712400239597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62592129725283141600159731 93888194587924712400239597)
    ·
      refine ⟨35208072970471767150089849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93888194587924712400239597 35208072970471767150089849)
      ·
        refine ⟨26406054727853825362567387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35208072970471767150089849 26406054727853825362567387)
        ·
          refine ⟨39609082091780738043851081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26406054727853825362567387 39609082091780738043851081)
          ·
            refine ⟨29706811568835553532888311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39609082091780738043851081 29706811568835553532888311)
            ·
              refine ⟨44560217353253330299332467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29706811568835553532888311 44560217353253330299332467)
              ·
                refine ⟨66840326029879995448998701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44560217353253330299332467 66840326029879995448998701)
                ·
                  refine ⟨25065122261204998293374513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66840326029879995448998701 25065122261204998293374513)
                  ·
                    refine ⟨18798841695903748720030885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25065122261204998293374513 18798841695903748720030885)
                    ·
                      refine ⟨3524782817981952885005791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18798841695903748720030885 3524782817981952885005791)
                      ·
                        rfl

theorem cell23_6864490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6864490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864490 prefixEnd_6864490 := by exact prefixLift 6864490
  have htrace : WordTrace (prefixWord ++ tailWord_6864490) baseStart_6864490 baseEnd_6864490 := by
    simpa [prefixWord, tailWord_6864490, baseEnd_6864490] using wordTrace_append hprefix tailTrace_6864490
  have hstable : (prefixWord ++ tailWord_6864490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864490).length < 2 ^ (prefixWord ++ tailWord_6864490).sum := by decide
  have hdescent : baseEnd_6864490 < baseStart_6864490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864590 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_6864590 : Nat := 118140960795 + 6864590 * 2 ^ 59
def prefixEnd_6864590 : Nat := 4983230072969 + 3 ^ 40 * 6864590 * 2
def baseEnd_6864590 : Nat := 391648240671933610417259

theorem tailTrace_6864590 : CollatzResearch.WordTrace tailWord_6864590 prefixEnd_6864590 391648240671933610417259 := by
  unfold tailWord_6864590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31296520775096285434909903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166914777467180188986186149 31296520775096285434909903)
  ·
    refine ⟨46944781162644428152364855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31296520775096285434909903 46944781162644428152364855)
    ·
      refine ⟨70417171743966642228547283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46944781162644428152364855 70417171743966642228547283)
      ·
        refine ⟨105625757615949963342820925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70417171743966642228547283 105625757615949963342820925)
        ·
          refine ⟨39609659105981236253557847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105625757615949963342820925 39609659105981236253557847)
          ·
            refine ⟨59414488658971854380336771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39609659105981236253557847 59414488658971854380336771)
            ·
              refine ⟨89121732988457781570505157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59414488658971854380336771 89121732988457781570505157)
              ·
                refine ⟨16710324935335834044469717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89121732988457781570505157 16710324935335834044469717)
                ·
                  refine ⟨391648240671933610417259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16710324935335834044469717 391648240671933610417259)
                  ·
                    rfl

theorem cell23_6864590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_6864590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864590 prefixEnd_6864590 := by exact prefixLift 6864590
  have htrace : WordTrace (prefixWord ++ tailWord_6864590) baseStart_6864590 baseEnd_6864590 := by
    simpa [prefixWord, tailWord_6864590, baseEnd_6864590] using wordTrace_append hprefix tailTrace_6864590
  have hstable : (prefixWord ++ tailWord_6864590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864590).length < 2 ^ (prefixWord ++ tailWord_6864590).sum := by decide
  have hdescent : baseEnd_6864590 < baseStart_6864590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864604 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6864604 : Nat := 118140960795 + 6864604 * 2 ^ 59
def prefixEnd_6864604 : Nat := 4983230072969 + 3 ^ 40 * 6864604 * 2
def baseEnd_6864604 : Nat := 3524841354776565438980267

theorem tailTrace_6864604 : CollatzResearch.WordTrace tailWord_6864604 prefixEnd_6864604 3524841354776565438980267 := by
  unfold tailWord_6864604
  simp only [CollatzResearch.WordTrace]
  refine ⟨125186338411359781935144433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166915117881813042580192577 125186338411359781935144433)
  ·
    refine ⟨93889753808519836451358325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125186338411359781935144433 93889753808519836451358325)
    ·
      refine ⟨8802164419548734667314843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93889753808519836451358325 8802164419548734667314843)
      ·
        refine ⟨13203246629323102000972265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8802164419548734667314843 13203246629323102000972265)
        ·
          refine ⟨9902434971992326500729199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203246629323102000972265 9902434971992326500729199)
          ·
            refine ⟨14853652457988489751093799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9902434971992326500729199 14853652457988489751093799)
            ·
              refine ⟨22280478686982734626640699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14853652457988489751093799 22280478686982734626640699)
              ·
                refine ⟨33420718030474101939961049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22280478686982734626640699 33420718030474101939961049)
                ·
                  refine ⟨25065538522855576454970787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33420718030474101939961049 25065538522855576454970787)
                  ·
                    refine ⟨37598307784283364682456181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25065538522855576454970787 37598307784283364682456181)
                    ·
                      refine ⟨3524841354776565438980267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37598307784283364682456181 3524841354776565438980267)
                      ·
                        rfl

theorem cell23_6864604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6864604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864604 prefixEnd_6864604 := by exact prefixLift 6864604
  have htrace : WordTrace (prefixWord ++ tailWord_6864604) baseStart_6864604 baseEnd_6864604 := by
    simpa [prefixWord, tailWord_6864604, baseEnd_6864604] using wordTrace_append hprefix tailTrace_6864604
  have hstable : (prefixWord ++ tailWord_6864604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864604).length < 2 ^ (prefixWord ++ tailWord_6864604).sum := by decide
  have hdescent : baseEnd_6864604 < baseStart_6864604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864620 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_6864620 : Nat := 118140960795 + 6864620 * 2 ^ 59
def prefixEnd_6864620 : Nat := 4983230072969 + 3 ^ 40 * 6864620 * 2
def baseEnd_6864620 : Nat := 1174949856822345792126731

theorem tailTrace_6864620 : CollatzResearch.WordTrace tailWord_6864620 prefixEnd_6864620 1174949856822345792126731 := by
  unfold tailWord_6864620
  simp only [CollatzResearch.WordTrace]
  refine ⟨125186630195330799301435657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166915506927107732401914209 125186630195330799301435657)
  ·
    refine ⟨93889972646498099476076743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125186630195330799301435657 93889972646498099476076743)
    ·
      refine ⟨140834958969747149214115115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93889972646498099476076743 140834958969747149214115115)
      ·
        refine ⟨211252438454620723821172673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140834958969747149214115115 211252438454620723821172673)
        ·
          refine ⟨158439328840965542865879505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211252438454620723821172673 158439328840965542865879505)
          ·
            refine ⟨118829496630724157149409629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158439328840965542865879505 118829496630724157149409629)
            ·
              refine ⟨44561061236521558931028611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118829496630724157149409629 44561061236521558931028611)
              ·
                refine ⟨66841591854782338396542917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44561061236521558931028611 66841591854782338396542917)
                ·
                  refine ⟨12532798472771688449351797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66841591854782338396542917 12532798472771688449351797)
                  ·
                    refine ⟨1174949856822345792126731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12532798472771688449351797 1174949856822345792126731)
                    ·
                      rfl

theorem cell23_6864620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_6864620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864620 prefixEnd_6864620 := by exact prefixLift 6864620
  have htrace : WordTrace (prefixWord ++ tailWord_6864620) baseStart_6864620 baseEnd_6864620 := by
    simpa [prefixWord, tailWord_6864620, baseEnd_6864620] using wordTrace_append hprefix tailTrace_6864620
  have hstable : (prefixWord ++ tailWord_6864620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864620).length < 2 ^ (prefixWord ++ tailWord_6864620).sum := by decide
  have hdescent : baseEnd_6864620 < baseStart_6864620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864657 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_6864657 : Nat := 118140960795 + 6864657 * 2 ^ 59
def prefixEnd_6864657 : Nat := 4983230072969 + 3 ^ 40 * 6864657 * 2
def baseEnd_6864657 : Nat := 3524868569251253731617523

theorem tailTrace_6864657 : CollatzResearch.WordTrace tailWord_6864657 prefixEnd_6864657 3524868569251253731617523 := by
  unfold tailWord_6864657
  simp only [CollatzResearch.WordTrace]
  refine ⟨250374609891527553921968225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166916406594351702614645483 250374609891527553921968225)
  ·
    refine ⟨187780957418645665441476169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250374609891527553921968225 187780957418645665441476169)
    ·
      refine ⟨140835718063984249081107127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187780957418645665441476169 140835718063984249081107127)
      ·
        refine ⟨211253577095976373621660691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140835718063984249081107127 211253577095976373621660691)
        ·
          refine ⟨316880365643964560432491037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211253577095976373621660691 316880365643964560432491037)
          ·
            refine ⟨118830137116486710162184139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316880365643964560432491037 118830137116486710162184139)
            ·
              refine ⟨178245205674730065243276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118830137116486710162184139 178245205674730065243276209)
              ·
                refine ⟨133683904256047548932457157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178245205674730065243276209 133683904256047548932457157)
                ·
                  refine ⟨25065732048008915424835717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133683904256047548932457157 25065732048008915424835717)
                  ·
                    refine ⟨4699824759001671642156697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25065732048008915424835717 4699824759001671642156697)
                    ·
                      refine ⟨3524868569251253731617523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699824759001671642156697 3524868569251253731617523)
                      ·
                        rfl

theorem cell23_6864657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_6864657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864657 prefixEnd_6864657 := by exact prefixLift 6864657
  have htrace : WordTrace (prefixWord ++ tailWord_6864657) baseStart_6864657 baseEnd_6864657 := by
    simpa [prefixWord, tailWord_6864657, baseEnd_6864657] using wordTrace_append hprefix tailTrace_6864657
  have hstable : (prefixWord ++ tailWord_6864657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864657).length < 2 ^ (prefixWord ++ tailWord_6864657).sum := by decide
  have hdescent : baseEnd_6864657 < baseStart_6864657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864674 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_6864674 : Nat := 118140960795 + 6864674 * 2 ^ 59
def prefixEnd_6864674 : Nat := 4983230072969 + 3 ^ 40 * 6864674 * 2
def baseEnd_6864674 : Nat := 3524877298422380165104945

theorem tailTrace_6864674 : CollatzResearch.WordTrace tailWord_6864674 prefixEnd_6864674 3524877298422380165104945 := by
  unfold tailWord_6864674
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593807483116491456334269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166916819954977310550224717 62593807483116491456334269)
  ·
    refine ⟨23472677806168684296125351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62593807483116491456334269 23472677806168684296125351)
    ·
      refine ⟨35209016709253026444188027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23472677806168684296125351 35209016709253026444188027)
      ·
        refine ⟨52813525063879539666282041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35209016709253026444188027 52813525063879539666282041)
        ·
          refine ⟨39610143797909654749711531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52813525063879539666282041 39610143797909654749711531)
          ·
            refine ⟨59415215696864482124567297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39610143797909654749711531 59415215696864482124567297)
            ·
              refine ⟨44561411772648361593425473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59415215696864482124567297 44561411772648361593425473)
              ·
                refine ⟨33421058829486271195069105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44561411772648361593425473 33421058829486271195069105)
                ·
                  refine ⟨25065794122114703396301829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33421058829486271195069105 25065794122114703396301829)
                  ·
                    refine ⟨4699836397896506886806593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25065794122114703396301829 4699836397896506886806593)
                    ·
                      refine ⟨3524877298422380165104945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4699836397896506886806593 3524877298422380165104945)
                      ·
                        rfl

theorem cell23_6864674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_6864674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864674 prefixEnd_6864674 := by exact prefixLift 6864674
  have htrace : WordTrace (prefixWord ++ tailWord_6864674) baseStart_6864674 baseEnd_6864674 := by
    simpa [prefixWord, tailWord_6864674, baseEnd_6864674] using wordTrace_append hprefix tailTrace_6864674
  have hstable : (prefixWord ++ tailWord_6864674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864674).length < 2 ^ (prefixWord ++ tailWord_6864674).sum := by decide
  have hdescent : baseEnd_6864674 < baseStart_6864674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864720 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_6864720 : Nat := 118140960795 + 6864720 * 2 ^ 59
def prefixEnd_6864720 : Nat := 4983230072969 + 3 ^ 40 * 6864720 * 2
def baseEnd_6864720 : Nat := 3524900918532486985129733

theorem tailTrace_6864720 : CollatzResearch.WordTrace tailWord_6864720 prefixEnd_6864720 3524900918532486985129733 := by
  unfold tailWord_6864720
  simp only [CollatzResearch.WordTrace]
  refine ⟨125188453845149657840755807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166917938460199543787674409 125188453845149657840755807)
  ·
    refine ⟨187782680767724486761133711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125188453845149657840755807 187782680767724486761133711)
    ·
      refine ⟨281674021151586730141700567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187782680767724486761133711 281674021151586730141700567)
      ·
        refine ⟨422511031727380095212550851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281674021151586730141700567 422511031727380095212550851)
        ·
          refine ⟨633766547591070142818826277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422511031727380095212550851 633766547591070142818826277)
          ·
            refine ⟨118831227673325651778529927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 633766547591070142818826277 118831227673325651778529927)
            ·
              refine ⟨178246841509988477667794891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118831227673325651778529927 178246841509988477667794891)
              ·
                refine ⟨267370262264982716501692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178246841509988477667794891 267370262264982716501692337)
                ·
                  refine ⟨200527696698737037376269253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267370262264982716501692337 200527696698737037376269253)
                  ·
                    refine ⟨37598943131013194508050485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200527696698737037376269253 37598943131013194508050485)
                    ·
                      refine ⟨3524900918532486985129733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37598943131013194508050485 3524900918532486985129733)
                      ·
                        rfl

theorem cell23_6864720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_6864720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864720 prefixEnd_6864720 := by exact prefixLift 6864720
  have htrace : WordTrace (prefixWord ++ tailWord_6864720) baseStart_6864720 baseEnd_6864720 := by
    simpa [prefixWord, tailWord_6864720, baseEnd_6864720] using wordTrace_append hprefix tailTrace_6864720
  have hstable : (prefixWord ++ tailWord_6864720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864720).length < 2 ^ (prefixWord ++ tailWord_6864720).sum := by decide
  have hdescent : baseEnd_6864720 < baseStart_6864720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864775 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_6864775 : Nat := 118140960795 + 6864775 * 2 ^ 59
def prefixEnd_6864775 : Nat := 4983230072969 + 3 ^ 40 * 6864775 * 2
def baseEnd_6864775 : Nat := 3524929159968484269941981

theorem tailTrace_6864775 : CollatzResearch.WordTrace tailWord_6864775 prefixEnd_6864775 3524929159968484269941981 := by
  unfold tailWord_6864775
  simp only [CollatzResearch.WordTrace]
  refine ⟨250378913705100060074763779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166919275803400040049842519 250378913705100060074763779)
  ·
    refine ⟨375568370557650090112145669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250378913705100060074763779 375568370557650090112145669)
    ·
      refine ⟨70419069479559391896027313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375568370557650090112145669 70419069479559391896027313)
      ·
        refine ⟨52814302109669543922020485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70419069479559391896027313 52814302109669543922020485)
        ·
          refine ⟨9902681645563039485378841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52814302109669543922020485 9902681645563039485378841)
          ·
            refine ⟨7427011234172279614034131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902681645563039485378841 7427011234172279614034131)
            ·
              refine ⟨11140516851258419421051197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427011234172279614034131 11140516851258419421051197)
              ·
                refine ⟨4177693819221907282894199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11140516851258419421051197 4177693819221907282894199)
                ·
                  refine ⟨6266540728832860924341299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177693819221907282894199 6266540728832860924341299)
                  ·
                    refine ⟨9399811093249291386511949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6266540728832860924341299 9399811093249291386511949)
                    ·
                      refine ⟨3524929159968484269941981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9399811093249291386511949 3524929159968484269941981)
                      ·
                        rfl

theorem cell23_6864775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_6864775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864775 prefixEnd_6864775 := by exact prefixLift 6864775
  have htrace : WordTrace (prefixWord ++ tailWord_6864775) baseStart_6864775 baseEnd_6864775 := by
    simpa [prefixWord, tailWord_6864775, baseEnd_6864775] using wordTrace_append hprefix tailTrace_6864775
  have hstable : (prefixWord ++ tailWord_6864775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864775).length < 2 ^ (prefixWord ++ tailWord_6864775).sum := by decide
  have hdescent : baseEnd_6864775 < baseStart_6864775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864777 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_6864777 : Nat := 118140960795 + 6864777 * 2 ^ 59
def prefixEnd_6864777 : Nat := 4983230072969 + 3 ^ 40 * 6864777 * 2
def baseEnd_6864777 : Nat := 3524930186929793262116971

theorem tailTrace_6864777 : CollatzResearch.WordTrace tailWord_6864777 prefixEnd_6864777 3524930186929793262116971 := by
  unfold tailWord_6864777
  simp only [CollatzResearch.WordTrace]
  refine ⟨250378986651092814416336585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166919324434061876277557723 250378986651092814416336585)
  ·
    refine ⟨187784239988319610812252439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250378986651092814416336585 187784239988319610812252439)
    ·
      refine ⟨281676359982479416218378659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187784239988319610812252439 281676359982479416218378659)
      ·
        refine ⟨422514539973719124327567989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281676359982479416218378659 422514539973719124327567989)
        ·
          refine ⟨39610738122536167905709499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 422514539973719124327567989 39610738122536167905709499)
          ·
            refine ⟨59416107183804251858564249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39610738122536167905709499 59416107183804251858564249)
            ·
              refine ⟨44562080387853188893923187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59416107183804251858564249 44562080387853188893923187)
              ·
                refine ⟨66843120581779783340884781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44562080387853188893923187 66843120581779783340884781)
                ·
                  refine ⟨25066170218167418752831793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66843120581779783340884781 25066170218167418752831793)
                  ·
                    refine ⟨18799627663625564064623845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25066170218167418752831793 18799627663625564064623845)
                    ·
                      refine ⟨3524930186929793262116971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18799627663625564064623845 3524930186929793262116971)
                      ·
                        rfl

theorem cell23_6864777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_6864777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864777 prefixEnd_6864777 := by exact prefixLift 6864777
  have htrace : WordTrace (prefixWord ++ tailWord_6864777) baseStart_6864777 baseEnd_6864777 := by
    simpa [prefixWord, tailWord_6864777, baseEnd_6864777] using wordTrace_append hprefix tailTrace_6864777
  have hstable : (prefixWord ++ tailWord_6864777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864777).length < 2 ^ (prefixWord ++ tailWord_6864777).sum := by decide
  have hdescent : baseEnd_6864777 < baseStart_6864777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864792 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6864792 : Nat := 118140960795 + 6864792 * 2 ^ 59
def prefixEnd_6864792 : Nat := 4983230072969 + 3 ^ 40 * 6864792 * 2
def baseEnd_6864792 : Nat := 3524937889139610703429403

theorem tailTrace_6864792 : CollatzResearch.WordTrace tailWord_6864792 prefixEnd_6864792 3524937889139610703429403 := by
  unfold tailWord_6864792
  simp only [CollatzResearch.WordTrace]
  refine ⟨125189766873019235989066315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166919689164025647985421753 125189766873019235989066315)
  ·
    refine ⟨187784650309528853983599473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125189766873019235989066315 187784650309528853983599473)
    ·
      refine ⟨140838487732146640487699605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187784650309528853983599473 140838487732146640487699605)
      ·
        refine ⟨6601804112444373772860919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140838487732146640487699605 6601804112444373772860919)
        ·
          refine ⟨9902706168666560659291379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601804112444373772860919 9902706168666560659291379)
          ·
            refine ⟨14854059252999840988937069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9902706168666560659291379 14854059252999840988937069)
            ·
              refine ⟨5570272219874940370851401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14854059252999840988937069 5570272219874940370851401)
              ·
                refine ⟨4177704164906205278138551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570272219874940370851401 4177704164906205278138551)
                ·
                  refine ⟨6266556247359307917207827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177704164906205278138551 6266556247359307917207827)
                  ·
                    refine ⟨9399834371038961875811741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6266556247359307917207827 9399834371038961875811741)
                    ·
                      refine ⟨3524937889139610703429403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9399834371038961875811741 3524937889139610703429403)
                      ·
                        rfl

theorem cell23_6864792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6864792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864792 prefixEnd_6864792 := by exact prefixLift 6864792
  have htrace : WordTrace (prefixWord ++ tailWord_6864792) baseStart_6864792 baseEnd_6864792 := by
    simpa [prefixWord, tailWord_6864792, baseEnd_6864792] using wordTrace_append hprefix tailTrace_6864792
  have hstable : (prefixWord ++ tailWord_6864792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864792).length < 2 ^ (prefixWord ++ tailWord_6864792).sum := by decide
  have hdescent : baseEnd_6864792 < baseStart_6864792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864847 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 6]
def baseStart_6864847 : Nat := 118140960795 + 6864847 * 2 ^ 59
def prefixEnd_6864847 : Nat := 4983230072969 + 3 ^ 40 * 6864847 * 2
def baseEnd_6864847 : Nat := 1174988710191869329413883

theorem tailTrace_6864847 : CollatzResearch.WordTrace tailWord_6864847 prefixEnd_6864847 1174988710191869329413883 := by
  unfold tailWord_6864847
  simp only [CollatzResearch.WordTrace]
  refine ⟨250381539760839216371384795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166921026507226144247589863 250381539760839216371384795)
  ·
    refine ⟨375572309641258824557077193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250381539760839216371384795 375572309641258824557077193)
    ·
      refine ⟨281679232230944118417807895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375572309641258824557077193 281679232230944118417807895)
      ·
        refine ⟨422518848346416177626711843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281679232230944118417807895 422518848346416177626711843)
        ·
          refine ⟨633778272519624266440067765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422518848346416177626711843 633778272519624266440067765)
          ·
            refine ⟨59416713048714774978756353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 633778272519624266440067765 59416713048714774978756353)
            ·
              refine ⟨44562534786536081234067265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59416713048714774978756353 44562534786536081234067265)
              ·
                refine ⟨33421901089902060925550449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44562534786536081234067265 33421901089902060925550449)
                ·
                  refine ⟨25066425817426545694162837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33421901089902060925550449 25066425817426545694162837)
                  ·
                    refine ⟨1174988710191869329413883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25066425817426545694162837 1174988710191869329413883)
                    ·
                      rfl

theorem cell23_6864847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_6864847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864847 prefixEnd_6864847 := by exact prefixLift 6864847
  have htrace : WordTrace (prefixWord ++ tailWord_6864847) baseStart_6864847 baseEnd_6864847 := by
    simpa [prefixWord, tailWord_6864847, baseEnd_6864847] using wordTrace_append hprefix tailTrace_6864847
  have hstable : (prefixWord ++ tailWord_6864847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864847).length < 2 ^ (prefixWord ++ tailWord_6864847).sum := by decide
  have hdescent : baseEnd_6864847 < baseStart_6864847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864874 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_6864874 : Nat := 118140960795 + 6864874 * 2 ^ 59
def prefixEnd_6864874 : Nat := 4983230072969 + 3 ^ 40 * 6864874 * 2
def baseEnd_6864874 : Nat := 3524979994553279382604025

theorem tailTrace_6864874 : CollatzResearch.WordTrace tailWord_6864874 prefixEnd_6864874 3524979994553279382604025 := by
  unfold tailWord_6864874
  simp only [CollatzResearch.WordTrace]
  refine ⟨62595631132935349995654419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166921683021160933321745117 62595631132935349995654419)
  ·
    refine ⟨93893446699403024993481629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62595631132935349995654419 93893446699403024993481629)
    ·
      refine ⟨35210042512276134372555611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93893446699403024993481629 35210042512276134372555611)
      ·
        refine ⟨52815063768414201558833417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35210042512276134372555611 52815063768414201558833417)
        ·
          refine ⟨39611297826310651169125063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52815063768414201558833417 39611297826310651169125063)
          ·
            refine ⟨59416946739465976753687595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39611297826310651169125063 59416946739465976753687595)
            ·
              refine ⟨89125420109198965130531393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59416946739465976753687595 89125420109198965130531393)
              ·
                refine ⟨66844065081899223847898545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89125420109198965130531393 66844065081899223847898545)
                ·
                  refine ⟨50133048811424417885923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66844065081899223847898545 50133048811424417885923909)
                  ·
                    refine ⟨9399946652142078353610733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50133048811424417885923909 9399946652142078353610733)
                    ·
                      refine ⟨3524979994553279382604025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9399946652142078353610733 3524979994553279382604025)
                      ·
                        rfl

theorem cell23_6864874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_6864874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864874 prefixEnd_6864874 := by exact prefixLift 6864874
  have htrace : WordTrace (prefixWord ++ tailWord_6864874) baseStart_6864874 baseEnd_6864874 := by
    simpa [prefixWord, tailWord_6864874, baseEnd_6864874] using wordTrace_append hprefix tailTrace_6864874
  have hstable : (prefixWord ++ tailWord_6864874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864874).length < 2 ^ (prefixWord ++ tailWord_6864874).sum := by decide
  have hdescent : baseEnd_6864874 < baseStart_6864874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864904 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_6864904 : Nat := 118140960795 + 6864904 * 2 ^ 59
def prefixEnd_6864904 : Nat := 4983230072969 + 3 ^ 40 * 6864904 * 2
def baseEnd_6864904 : Nat := 3524995398972914265228887

theorem tailTrace_6864904 : CollatzResearch.WordTrace tailWord_6864904 prefixEnd_6864904 3524995398972914265228887 := by
  unfold tailWord_6864904
  simp only [CollatzResearch.WordTrace]
  refine ⟨125191809360816357553104883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166922412481088476737473177 125191809360816357553104883)
  ·
    refine ⟨187787714041224536329657325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125191809360816357553104883 187787714041224536329657325)
    ·
      refine ⟨70420392765459201123621497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187787714041224536329657325 70420392765459201123621497)
      ·
        refine ⟨52815294574094400842716123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70420392765459201123621497 52815294574094400842716123)
        ·
          refine ⟨79222941861141601264074185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52815294574094400842716123 79222941861141601264074185)
          ·
            refine ⟨59417206395856200948055639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79222941861141601264074185 59417206395856200948055639)
            ·
              refine ⟨89125809593784301422083459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59417206395856200948055639 89125809593784301422083459)
              ·
                refine ⟨133688714390676452133125189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89125809593784301422083459 133688714390676452133125189)
                ·
                  refine ⟨25066633948251834774960973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133688714390676452133125189 25066633948251834774960973)
                  ·
                    refine ⟨9399987730594438040610365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25066633948251834774960973 9399987730594438040610365)
                    ·
                      refine ⟨3524995398972914265228887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9399987730594438040610365 3524995398972914265228887)
                      ·
                        rfl

theorem cell23_6864904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_6864904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864904 prefixEnd_6864904 := by exact prefixLift 6864904
  have htrace : WordTrace (prefixWord ++ tailWord_6864904) baseStart_6864904 baseEnd_6864904 := by
    simpa [prefixWord, tailWord_6864904, baseEnd_6864904] using wordTrace_append hprefix tailTrace_6864904
  have hstable : (prefixWord ++ tailWord_6864904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864904).length < 2 ^ (prefixWord ++ tailWord_6864904).sum := by decide
  have hdescent : baseEnd_6864904 < baseStart_6864904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864924 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6864924 : Nat := 118140960795 + 6864924 * 2 ^ 59
def prefixEnd_6864924 : Nat := 4983230072969 + 3 ^ 40 * 6864924 * 2
def baseEnd_6864924 : Nat := 1175001889528668062326265

theorem tailTrace_6864924 : CollatzResearch.WordTrace tailWord_6864924 prefixEnd_6864924 1175001889528668062326265 := by
  unfold tailWord_6864924
  simp only [CollatzResearch.WordTrace]
  refine ⟨125192174090780129260968913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166922898787706839014625217 125192174090780129260968913)
  ·
    refine ⟨93894130568085096945726685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125192174090780129260968913 93894130568085096945726685)
    ·
      refine ⟨35210298963031911354647507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93894130568085096945726685 35210298963031911354647507)
      ·
        refine ⟨52815448444547867031971261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35210298963031911354647507 52815448444547867031971261)
        ·
          refine ⟨19805793166705450136989223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52815448444547867031971261 19805793166705450136989223)
          ·
            refine ⟨29708689750058175205483835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19805793166705450136989223 29708689750058175205483835)
            ·
              refine ⟨44563034625087262808225753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29708689750058175205483835 44563034625087262808225753)
              ·
                refine ⟨33422275968815447106169315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44563034625087262808225753 33422275968815447106169315)
                ·
                  refine ⟨50133413953223170659253973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33422275968815447106169315 50133413953223170659253973)
                  ·
                    refine ⟨1175001889528668062326265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50133413953223170659253973 1175001889528668062326265)
                    ·
                      rfl

theorem cell23_6864924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6864924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864924 prefixEnd_6864924 := by exact prefixLift 6864924
  have htrace : WordTrace (prefixWord ++ tailWord_6864924) baseStart_6864924 baseEnd_6864924 := by
    simpa [prefixWord, tailWord_6864924, baseEnd_6864924] using wordTrace_append hprefix tailTrace_6864924
  have hstable : (prefixWord ++ tailWord_6864924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864924).length < 2 ^ (prefixWord ++ tailWord_6864924).sum := by decide
  have hdescent : baseEnd_6864924 < baseStart_6864924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864944 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_6864944 : Nat := 118140960795 + 6864944 * 2 ^ 59
def prefixEnd_6864944 : Nat := 4983230072969 + 3 ^ 40 * 6864944 * 2
def baseEnd_6864944 : Nat := 3525015938199094108728703

theorem tailTrace_6864944 : CollatzResearch.WordTrace tailWord_6864944 prefixEnd_6864944 3525015938199094108728703 := by
  unfold tailWord_6864944
  simp only [CollatzResearch.WordTrace]
  refine ⟨125192538820743900968832943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166923385094325201291777257 125192538820743900968832943)
  ·
    refine ⟨187788808231115851453249415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125192538820743900968832943 187788808231115851453249415)
    ·
      refine ⟨281683212346673777179874123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187788808231115851453249415 281683212346673777179874123)
      ·
        refine ⟨422524818520010665769811185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281683212346673777179874123 422524818520010665769811185)
        ·
          refine ⟨316893613890007999327358389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422524818520010665769811185 316893613890007999327358389)
          ·
            refine ⟨29708776302188249936939849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316893613890007999327358389 29708776302188249936939849)
            ·
              refine ⟨22281582226641187452704887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29708776302188249936939849 22281582226641187452704887)
              ·
                refine ⟨33422373339961781179057331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22281582226641187452704887 33422373339961781179057331)
                ·
                  refine ⟨50133560009942671768585997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33422373339961781179057331 50133560009942671768585997)
                  ·
                    refine ⟨18800085003728501913219749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50133560009942671768585997 18800085003728501913219749)
                    ·
                      refine ⟨3525015938199094108728703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18800085003728501913219749 3525015938199094108728703)
                      ·
                        rfl

theorem cell23_6864944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_6864944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864944 prefixEnd_6864944 := by exact prefixLift 6864944
  have htrace : WordTrace (prefixWord ++ tailWord_6864944) baseStart_6864944 baseEnd_6864944 := by
    simpa [prefixWord, tailWord_6864944, baseEnd_6864944] using wordTrace_append hprefix tailTrace_6864944
  have hstable : (prefixWord ++ tailWord_6864944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864944).length < 2 ^ (prefixWord ++ tailWord_6864944).sum := by decide
  have hdescent : baseEnd_6864944 < baseStart_6864944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864958 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6864958 : Nat := 118140960795 + 6864958 * 2 ^ 59
def prefixEnd_6864958 : Nat := 4983230072969 + 3 ^ 40 * 6864958 * 2
def baseEnd_6864958 : Nat := 1175007708976085684651213

theorem tailTrace_6864958 : CollatzResearch.WordTrace tailWord_6864958 prefixEnd_6864958 1175007708976085684651213 := by
  unfold tailWord_6864958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31298198532929635291084441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166923725508958054885783685 31298198532929635291084441)
  ·
    refine ⟨23473648899697226468313331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31298198532929635291084441 23473648899697226468313331)
    ·
      refine ⟨35210473349545839702469997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23473648899697226468313331 35210473349545839702469997)
      ·
        refine ⟨13203927506079689888426249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35210473349545839702469997 13203927506079689888426249)
        ·
          refine ⟨9902945629559767416319687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203927506079689888426249 9902945629559767416319687)
          ·
            refine ⟨14854418444339651124479531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9902945629559767416319687 14854418444339651124479531)
            ·
              refine ⟨22281627666509476686719297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14854418444339651124479531 22281627666509476686719297)
              ·
                refine ⟨16711220749882107515039473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22281627666509476686719297 16711220749882107515039473)
                ·
                  refine ⟨12533415562411580636279605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16711220749882107515039473 12533415562411580636279605)
                  ·
                    refine ⟨1175007708976085684651213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12533415562411580636279605 1175007708976085684651213)
                    ·
                      rfl

theorem cell23_6864958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6864958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864958 prefixEnd_6864958 := by exact prefixLift 6864958
  have htrace : WordTrace (prefixWord ++ tailWord_6864958) baseStart_6864958 baseEnd_6864958 := by
    simpa [prefixWord, tailWord_6864958, baseEnd_6864958] using wordTrace_append hprefix tailTrace_6864958
  have hstable : (prefixWord ++ tailWord_6864958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864958).length < 2 ^ (prefixWord ++ tailWord_6864958).sum := by decide
  have hdescent : baseEnd_6864958 < baseStart_6864958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6864961 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6864961 : Nat := 118140960795 + 6864961 * 2 ^ 59
def prefixEnd_6864961 : Nat := 4983230072969 + 3 ^ 40 * 6864961 * 2
def baseEnd_6864961 : Nat := 3525024667370220542216125

theorem tailTrace_6864961 : CollatzResearch.WordTrace tailWord_6864961 prefixEnd_6864961 3525024667370220542216125 := by
  unfold tailWord_6864961
  simp only [CollatzResearch.WordTrace]
  refine ⟨250385697682426213841034737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166923798454950809227356491 250385697682426213841034737)
  ·
    refine ⟨187789273261819660380776053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250385697682426213841034737 187789273261819660380776053)
    ·
      refine ⟨17605244368295593160697755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187789273261819660380776053 17605244368295593160697755)
      ·
        refine ⟨26407866552443389741046633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17605244368295593160697755 26407866552443389741046633)
        ·
          refine ⟨19805899914332542305784975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26407866552443389741046633 19805899914332542305784975)
          ·
            refine ⟨29708849871498813458677463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19805899914332542305784975 29708849871498813458677463)
            ·
              refine ⟨44563274807248220188016195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29708849871498813458677463 44563274807248220188016195)
              ·
                refine ⟨66844912210872330282024293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44563274807248220188016195 66844912210872330282024293)
                ·
                  refine ⟨12533421039538561927879555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66844912210872330282024293 12533421039538561927879555)
                  ·
                    refine ⟨18800131559307842891819333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12533421039538561927879555 18800131559307842891819333)
                    ·
                      refine ⟨3525024667370220542216125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18800131559307842891819333 3525024667370220542216125)
                      ·
                        rfl

theorem cell23_6864961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6864961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6864961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6864961 prefixEnd_6864961 := by exact prefixLift 6864961
  have htrace : WordTrace (prefixWord ++ tailWord_6864961) baseStart_6864961 baseEnd_6864961 := by
    simpa [prefixWord, tailWord_6864961, baseEnd_6864961] using wordTrace_append hprefix tailTrace_6864961
  have hstable : (prefixWord ++ tailWord_6864961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6864961).length < 2 ^ (prefixWord ++ tailWord_6864961).sum := by decide
  have hdescent : baseEnd_6864961 < baseStart_6864961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6864961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865028 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6865028 : Nat := 118140960795 + 6865028 * 2 ^ 59
def prefixEnd_6865028 : Nat := 4983230072969 + 3 ^ 40 * 6865028 * 2
def baseEnd_6865028 : Nat := 3525059070574071780078317

theorem tailTrace_6865028 : CollatzResearch.WordTrace tailWord_6865028 prefixEnd_6865028 3525059070574071780078317 := by
  unfold tailWord_6865028
  simp only [CollatzResearch.WordTrace]
  refine ⟨125194070686591742141861869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166925427582122322855815825 125194070686591742141861869)
  ·
    refine ⟨46947776507471903303198201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125194070686591742141861869 46947776507471903303198201)
    ·
      refine ⟨35210832380603927477398651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46947776507471903303198201 35210832380603927477398651)
      ·
        refine ⟨52816248570905891216097977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35210832380603927477398651 52816248570905891216097977)
        ·
          refine ⟨39612186428179418412073483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52816248570905891216097977 39612186428179418412073483)
          ·
            refine ⟨59418279642269127618110225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39612186428179418412073483 59418279642269127618110225)
            ·
              refine ⟨44563709731701845713582669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59418279642269127618110225 44563709731701845713582669)
              ·
                refine ⟨16711391149388192142593501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44563709731701845713582669 16711391149388192142593501)
                ·
                  refine ⟨6266771681020572053472563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16711391149388192142593501 6266771681020572053472563)
                  ·
                    refine ⟨9400157521530858080208845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6266771681020572053472563 9400157521530858080208845)
                    ·
                      refine ⟨3525059070574071780078317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400157521530858080208845 3525059070574071780078317)
                      ·
                        rfl

theorem cell23_6865028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6865028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865028 prefixEnd_6865028 := by exact prefixLift 6865028
  have htrace : WordTrace (prefixWord ++ tailWord_6865028) baseStart_6865028 baseEnd_6865028 := by
    simpa [prefixWord, tailWord_6865028, baseEnd_6865028] using wordTrace_append hprefix tailTrace_6865028
  have hstable : (prefixWord ++ tailWord_6865028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865028).length < 2 ^ (prefixWord ++ tailWord_6865028).sum := by decide
  have hdescent : baseEnd_6865028 < baseStart_6865028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865046 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6865046 : Nat := 118140960795 + 6865046 * 2 ^ 59
def prefixEnd_6865046 : Nat := 4983230072969 + 3 ^ 40 * 6865046 * 2
def baseEnd_6865046 : Nat := 3525068313225852709653235

theorem tailTrace_6865046 : CollatzResearch.WordTrace tailWord_6865046 prefixEnd_6865046 3525068313225852709653235 := by
  unfold tailWord_6865046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649299867944892084867437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166925865258078848905252661 15649299867944892084867437)
  ·
    refine ⟨5868487450479334531825289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15649299867944892084867437 5868487450479334531825289)
    ·
      refine ⟨4401365587859500898868967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5868487450479334531825289 4401365587859500898868967)
      ·
        refine ⟨6602048381789251348303451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401365587859500898868967 6602048381789251348303451)
        ·
          refine ⟨9903072572683877022455177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602048381789251348303451 9903072572683877022455177)
          ·
            refine ⟨7427304429512907766841383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9903072572683877022455177 7427304429512907766841383)
            ·
              refine ⟨11140956644269361650262075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427304429512907766841383 11140956644269361650262075)
              ·
                refine ⟨16711434966404042475393113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11140956644269361650262075 16711434966404042475393113)
                ·
                  refine ⟨12533576224803031856544835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16711434966404042475393113 12533576224803031856544835)
                  ·
                    refine ⟨18800364337204547784817253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12533576224803031856544835 18800364337204547784817253)
                    ·
                      refine ⟨3525068313225852709653235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18800364337204547784817253 3525068313225852709653235)
                      ·
                        rfl

theorem cell23_6865046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6865046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865046 prefixEnd_6865046 := by exact prefixLift 6865046
  have htrace : WordTrace (prefixWord ++ tailWord_6865046) baseStart_6865046 baseEnd_6865046 := by
    simpa [prefixWord, tailWord_6865046, baseEnd_6865046] using wordTrace_append hprefix tailTrace_6865046
  have hstable : (prefixWord ++ tailWord_6865046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865046).length < 2 ^ (prefixWord ++ tailWord_6865046).sum := by decide
  have hdescent : baseEnd_6865046 < baseStart_6865046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865055 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6865055 : Nat := 118140960795 + 6865055 * 2 ^ 59
def prefixEnd_6865055 : Nat := 4983230072969 + 3 ^ 40 * 6865055 * 2
def baseEnd_6865055 : Nat := 3525072934551743174440693

theorem tailTrace_6865055 : CollatzResearch.WordTrace tailWord_6865055 prefixEnd_6865055 3525072934551743174440693 := by
  unfold tailWord_6865055
  simp only [CollatzResearch.WordTrace]
  refine ⟨250389126144085667894956619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166926084096057111929971079 250389126144085667894956619)
  ·
    refine ⟨375583689216128501842434929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250389126144085667894956619 375583689216128501842434929)
    ·
      refine ⟨281687766912096376381826197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375583689216128501842434929 281687766912096376381826197)
      ·
        refine ⟨13204114074004517642898103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281687766912096376381826197 13204114074004517642898103)
        ·
          refine ⟨19806171111006776464347155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204114074004517642898103 19806171111006776464347155)
          ·
            refine ⟨29709256666510164696520733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19806171111006776464347155 29709256666510164696520733)
            ·
              refine ⟨11140971249941311761195275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29709256666510164696520733 11140971249941311761195275)
              ·
                refine ⟨16711456874911967641792913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11140971249941311761195275 16711456874911967641792913)
                ·
                  refine ⟨12533592656183975731344685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16711456874911967641792913 12533592656183975731344685)
                  ·
                    refine ⟨4700097246068990899254257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12533592656183975731344685 4700097246068990899254257)
                    ·
                      refine ⟨3525072934551743174440693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700097246068990899254257 3525072934551743174440693)
                      ·
                        rfl

theorem cell23_6865055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6865055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865055 prefixEnd_6865055 := by exact prefixLift 6865055
  have htrace : WordTrace (prefixWord ++ tailWord_6865055) baseStart_6865055 baseEnd_6865055 := by
    simpa [prefixWord, tailWord_6865055, baseEnd_6865055] using wordTrace_append hprefix tailTrace_6865055
  have hstable : (prefixWord ++ tailWord_6865055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865055).length < 2 ^ (prefixWord ++ tailWord_6865055).sum := by decide
  have hdescent : baseEnd_6865055 < baseStart_6865055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865061 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_6865061 : Nat := 118140960795 + 6865061 * 2 ^ 59
def prefixEnd_6865061 : Nat := 4983230072969 + 3 ^ 40 * 6865061 * 2
def baseEnd_6865061 : Nat := 1175025338478556716988555

theorem tailTrace_6865061 : CollatzResearch.WordTrace tailWord_6865061 prefixEnd_6865061 1175025338478556716988555 := by
  unfold tailWord_6865061
  simp only [CollatzResearch.WordTrace]
  refine ⟨250389344982063930919675037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166926229988042620613116691 250389344982063930919675037)
  ·
    refine ⟨93896004368273974094878139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250389344982063930919675037 93896004368273974094878139)
    ·
      refine ⟨140844006552410961142317209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93896004368273974094878139 140844006552410961142317209)
      ·
        refine ⟨105633004914308220856737907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140844006552410961142317209 105633004914308220856737907)
        ·
          refine ⟨158449507371462331285106861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105633004914308220856737907 158449507371462331285106861)
          ·
            refine ⟨59418565264298374231915073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158449507371462331285106861 59418565264298374231915073)
            ·
              refine ⟨44563923948223780673936305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59418565264298374231915073 44563923948223780673936305)
              ·
                refine ⟨33422942961167835505452229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44563923948223780673936305 33422942961167835505452229)
                ·
                  refine ⟨6266801805218969157272293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33422942961167835505452229 6266801805218969157272293)
                  ·
                    refine ⟨1175025338478556716988555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6266801805218969157272293 1175025338478556716988555)
                    ·
                      rfl

theorem cell23_6865061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_6865061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865061 prefixEnd_6865061 := by exact prefixLift 6865061
  have htrace : WordTrace (prefixWord ++ tailWord_6865061) baseStart_6865061 baseEnd_6865061 := by
    simpa [prefixWord, tailWord_6865061, baseEnd_6865061] using wordTrace_append hprefix tailTrace_6865061
  have hstable : (prefixWord ++ tailWord_6865061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865061).length < 2 ^ (prefixWord ++ tailWord_6865061).sum := by decide
  have hdescent : baseEnd_6865061 < baseStart_6865061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865074 : List Nat := [3, 2, 1, 1, 1, 3, 12]
def baseStart_6865074 : Nat := 118140960795 + 6865074 * 2 ^ 59
def prefixEnd_6865074 : Nat := 4983230072969 + 3 ^ 40 * 6865074 * 2
def baseEnd_6865074 : Nat := 43519539391162698766705

theorem tailTrace_6865074 : CollatzResearch.WordTrace tailWord_6865074 prefixEnd_6865074 43519539391162698766705 := by
  unfold tailWord_6865074
  simp only [CollatzResearch.WordTrace]
  refine ⟨62597454782754208534974569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166926546087344556093265517 62597454782754208534974569)
  ·
    refine ⟨46948091087065656401230927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62597454782754208534974569 46948091087065656401230927)
    ·
      refine ⟨70422136630598484601846391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46948091087065656401230927 70422136630598484601846391)
      ·
        refine ⟨105633204945897726902769587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70422136630598484601846391 105633204945897726902769587)
        ·
          refine ⟨158449807418846590354154381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105633204945897726902769587 158449807418846590354154381)
          ·
            refine ⟨59418677782067471382807893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158449807418846590354154381 59418677782067471382807893)
            ·
              refine ⟨43519539391162698766705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 59418677782067471382807893 43519539391162698766705)
              ·
                rfl

theorem cell23_6865074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 12].length) (baseStart_6865074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865074 prefixEnd_6865074 := by exact prefixLift 6865074
  have htrace : WordTrace (prefixWord ++ tailWord_6865074) baseStart_6865074 baseEnd_6865074 := by
    simpa [prefixWord, tailWord_6865074, baseEnd_6865074] using wordTrace_append hprefix tailTrace_6865074
  have hstable : (prefixWord ++ tailWord_6865074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865074).length < 2 ^ (prefixWord ++ tailWord_6865074).sum := by decide
  have hdescent : baseEnd_6865074 < baseStart_6865074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865161 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_6865161 : Nat := 118140960795 + 6865161 * 2 ^ 59
def prefixEnd_6865161 : Nat := 4983230072969 + 3 ^ 40 * 6865161 * 2
def baseEnd_6865161 : Nat := 3525127363501119759715205

theorem tailTrace_6865161 : CollatzResearch.WordTrace tailWord_6865161 prefixEnd_6865161 3525127363501119759715205 := by
  unfold tailWord_6865161
  simp only [CollatzResearch.WordTrace]
  refine ⟨250392992281701647998315337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166928661521134431998876891 250392992281701647998315337)
  ·
    refine ⟨187794744211276235998736503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250392992281701647998315337 187794744211276235998736503)
    ·
      refine ⟨281692116316914353998104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187794744211276235998736503 281692116316914353998104755)
      ·
        refine ⟨422538174475371530997157133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281692116316914353998104755 422538174475371530997157133)
        ·
          refine ⟨158451815428264324123933925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422538174475371530997157133 158451815428264324123933925)
          ·
            refine ⟨29709715392799560773237611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158451815428264324123933925 29709715392799560773237611)
            ·
              refine ⟨44564573089199341159856417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29709715392799560773237611 44564573089199341159856417)
              ·
                refine ⟨33423429816899505869892313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44564573089199341159856417 33423429816899505869892313)
                ·
                  refine ⟨25067572362674629402419235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33423429816899505869892313 25067572362674629402419235)
                  ·
                    refine ⟨37601358544011944103628853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25067572362674629402419235 37601358544011944103628853)
                    ·
                      refine ⟨3525127363501119759715205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37601358544011944103628853 3525127363501119759715205)
                      ·
                        rfl

theorem cell23_6865161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_6865161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865161 prefixEnd_6865161 := by exact prefixLift 6865161
  have htrace : WordTrace (prefixWord ++ tailWord_6865161) baseStart_6865161 baseEnd_6865161 := by
    simpa [prefixWord, tailWord_6865161, baseEnd_6865161] using wordTrace_append hprefix tailTrace_6865161
  have hstable : (prefixWord ++ tailWord_6865161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865161).length < 2 ^ (prefixWord ++ tailWord_6865161).sum := by decide
  have hdescent : baseEnd_6865161 < baseStart_6865161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865175 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6865175 : Nat := 118140960795 + 6865175 * 2 ^ 59
def prefixEnd_6865175 : Nat := 4983230072969 + 3 ^ 40 * 6865175 * 2
def baseEnd_6865175 : Nat := 3525134552230282704940141

theorem tailTrace_6865175 : CollatzResearch.WordTrace tailWord_6865175 prefixEnd_6865175 3525134552230282704940141 := by
  unfold tailWord_6865175
  simp only [CollatzResearch.WordTrace]
  refine ⟨250393502903650928389324979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166929001935767285592883319 250393502903650928389324979)
  ·
    refine ⟨375590254355476392583987469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250393502903650928389324979 375590254355476392583987469)
    ·
      refine ⟨140846345383303647218995301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375590254355476392583987469 140846345383303647218995301)
      ·
        refine ⟨26408689759369433853561619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140846345383303647218995301 26408689759369433853561619)
        ·
          refine ⟨39613034639054150780342429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26408689759369433853561619 39613034639054150780342429)
          ·
            refine ⟨14854887989645306542628411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39613034639054150780342429 14854887989645306542628411)
            ·
              refine ⟨22282331984467959813942617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14854887989645306542628411 22282331984467959813942617)
              ·
                refine ⟨16711748988350969860456963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22282331984467959813942617 16711748988350969860456963)
                ·
                  refine ⟨25067623482526454790685445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16711748988350969860456963 25067623482526454790685445)
                  ·
                    refine ⟨4700179402973710273253521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25067623482526454790685445 4700179402973710273253521)
                    ·
                      refine ⟨3525134552230282704940141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700179402973710273253521 3525134552230282704940141)
                      ·
                        rfl

theorem cell23_6865175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6865175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865175 prefixEnd_6865175 := by exact prefixLift 6865175
  have htrace : WordTrace (prefixWord ++ tailWord_6865175) baseStart_6865175 baseEnd_6865175 := by
    simpa [prefixWord, tailWord_6865175, baseEnd_6865175] using wordTrace_append hprefix tailTrace_6865175
  have hstable : (prefixWord ++ tailWord_6865175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865175).length < 2 ^ (prefixWord ++ tailWord_6865175).sum := by decide
  have hdescent : baseEnd_6865175 < baseStart_6865175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865292 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_6865292 : Nat := 118140960795 + 6865292 * 2 ^ 59
def prefixEnd_6865292 : Nat := 4983230072969 + 3 ^ 40 * 6865292 * 2
def baseEnd_6865292 : Nat := 1175064876488952915725701

theorem tailTrace_6865292 : CollatzResearch.WordTrace tailWord_6865292 prefixEnd_6865292 1175064876488952915725701 := by
  unfold tailWord_6865292
  simp only [CollatzResearch.WordTrace]
  refine ⟨125198885122113528685667065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166931846829484704914222753 125198885122113528685667065)
  ·
    refine ⟨93899163841585146514250299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125198885122113528685667065 93899163841585146514250299)
    ·
      refine ⟨140848745762377719771375449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93899163841585146514250299 140848745762377719771375449)
      ·
        refine ⟨105636559321783289828531587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140848745762377719771375449 105636559321783289828531587)
        ·
          refine ⟨158454838982674934742797381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105636559321783289828531587 158454838982674934742797381)
          ·
            refine ⟨29710282309251550264274509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158454838982674934742797381 29710282309251550264274509)
            ·
              refine ⟨11141355865969331349102941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29710282309251550264274509 11141355865969331349102941)
              ·
                refine ⟨4178008449738499255913603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11141355865969331349102941 4178008449738499255913603)
                ·
                  refine ⟨6267012674607748883870405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178008449738499255913603 6267012674607748883870405)
                  ·
                    refine ⟨1175064876488952915725701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267012674607748883870405 1175064876488952915725701)
                    ·
                      rfl

theorem cell23_6865292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_6865292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865292 prefixEnd_6865292 := by exact prefixLift 6865292
  have htrace : WordTrace (prefixWord ++ tailWord_6865292) baseStart_6865292 baseEnd_6865292 := by
    simpa [prefixWord, tailWord_6865292, baseEnd_6865292] using wordTrace_append hprefix tailTrace_6865292
  have hstable : (prefixWord ++ tailWord_6865292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865292).length < 2 ^ (prefixWord ++ tailWord_6865292).sum := by decide
  have hdescent : baseEnd_6865292 < baseStart_6865292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865309 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6865309 : Nat := 118140960795 + 6865309 * 2 ^ 59
def prefixEnd_6865309 : Nat := 4983230072969 + 3 ^ 40 * 6865309 * 2
def baseEnd_6865309 : Nat := 1175067786212661726888175

theorem tailTrace_6865309 : CollatzResearch.WordTrace tailWord_6865309 prefixEnd_6865309 1175067786212661726888175 := by
  unfold tailWord_6865309
  simp only [CollatzResearch.WordTrace]
  refine ⟨250398390285165469274702981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166932260190110312849801987 250398390285165469274702981)
  ·
    refine ⟨46949698178468525489006809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250398390285165469274702981 46949698178468525489006809)
    ·
      refine ⟨35212273633851394116755107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46949698178468525489006809 35212273633851394116755107)
      ·
        refine ⟨52818410450777091175132661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35212273633851394116755107 52818410450777091175132661)
        ·
          refine ⟨4951725979760352297668687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52818410450777091175132661 4951725979760352297668687)
          ·
            refine ⟨7427588969640528446503031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951725979760352297668687 7427588969640528446503031)
            ·
              refine ⟨11141383454460792669754547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427588969640528446503031 11141383454460792669754547)
              ·
                refine ⟨16712075181691189004631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11141383454460792669754547 16712075181691189004631821)
                ·
                  refine ⟨6267028193134195876736933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16712075181691189004631821 6267028193134195876736933)
                  ·
                    refine ⟨1175067786212661726888175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267028193134195876736933 1175067786212661726888175)
                    ·
                      rfl

theorem cell23_6865309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6865309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865309 prefixEnd_6865309 := by exact prefixLift 6865309
  have htrace : WordTrace (prefixWord ++ tailWord_6865309) baseStart_6865309 baseEnd_6865309 := by
    simpa [prefixWord, tailWord_6865309, baseEnd_6865309] using wordTrace_append hprefix tailTrace_6865309
  have hstable : (prefixWord ++ tailWord_6865309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865309).length < 2 ^ (prefixWord ++ tailWord_6865309).sum := by decide
  have hdescent : baseEnd_6865309 < baseStart_6865309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865335 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 1, 5]
def baseStart_6865335 : Nat := 118140960795 + 6865335 * 2 ^ 59
def prefixEnd_6865335 : Nat := 4983230072969 + 3 ^ 40 * 6865335 * 2
def baseEnd_6865335 : Nat := 1175072236378334026313135

theorem tailTrace_6865335 : CollatzResearch.WordTrace tailWord_6865335 prefixEnd_6865335 1175072236378334026313135 := by
  unfold tailWord_6865335
  simp only [CollatzResearch.WordTrace]
  refine ⟨250399338583071275715149459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166932892388714183810099639 250399338583071275715149459)
  ·
    refine ⟨375599007874606913572724189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250399338583071275715149459 375599007874606913572724189)
    ·
      refine ⟨140849627952977592589771571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375599007874606913572724189 140849627952977592589771571)
      ·
        refine ⟨211274441929466388884657357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140849627952977592589771571 211274441929466388884657357)
        ·
          refine ⟨79227915723549895831746509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211274441929466388884657357 79227915723549895831746509)
          ·
            refine ⟨29710468396331210936904941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79227915723549895831746509 29710468396331210936904941)
            ·
              refine ⟨11141425648624204101339353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29710468396331210936904941 11141425648624204101339353)
              ·
                refine ⟨8356069236468153076004515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11141425648624204101339353 8356069236468153076004515)
                ·
                  refine ⟨12534103854702229614006773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356069236468153076004515 12534103854702229614006773)
                  ·
                    refine ⟨1175072236378334026313135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12534103854702229614006773 1175072236378334026313135)
                    ·
                      rfl

theorem cell23_6865335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_6865335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865335 prefixEnd_6865335 := by exact prefixLift 6865335
  have htrace : WordTrace (prefixWord ++ tailWord_6865335) baseStart_6865335 baseEnd_6865335 := by
    simpa [prefixWord, tailWord_6865335, baseEnd_6865335] using wordTrace_append hprefix tailTrace_6865335
  have hstable : (prefixWord ++ tailWord_6865335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865335).length < 2 ^ (prefixWord ++ tailWord_6865335).sum := by decide
  have hdescent : baseEnd_6865335 < baseStart_6865335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865342 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_6865342 : Nat := 118140960795 + 6865342 * 2 ^ 59
def prefixEnd_6865342 : Nat := 4983230072969 + 3 ^ 40 * 6865342 * 2
def baseEnd_6865342 : Nat := 3525220303499583551551873

theorem tailTrace_6865342 : CollatzResearch.WordTrace tailWord_6865342 prefixEnd_6865342 3525220303499583551551873 := by
  unfold tailWord_6865342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31299949236755739488831785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166933062596030610607102853 31299949236755739488831785)
  ·
    refine ⟨23474961927566804616623839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31299949236755739488831785 23474961927566804616623839)
    ·
      refine ⟨35212442891350206924935759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23474961927566804616623839 35212442891350206924935759)
      ·
        refine ⟨52818664337025310387403639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35212442891350206924935759 52818664337025310387403639)
        ·
          refine ⟨79227996505537965581105459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52818664337025310387403639 79227996505537965581105459)
          ·
            refine ⟨118841994758306948371658189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79227996505537965581105459 118841994758306948371658189)
            ·
              refine ⟨44565748034365105639371821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118841994758306948371658189 44565748034365105639371821)
              ·
                refine ⟨16712155512886914614764433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44565748034365105639371821 16712155512886914614764433)
                ·
                  refine ⟨12534116634665185961073325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16712155512886914614764433 12534116634665185961073325)
                  ·
                    refine ⟨4700293737999444735402497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12534116634665185961073325 4700293737999444735402497)
                    ·
                      refine ⟨3525220303499583551551873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700293737999444735402497 3525220303499583551551873)
                      ·
                        rfl

theorem cell23_6865342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_6865342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865342 prefixEnd_6865342 := by exact prefixLift 6865342
  have htrace : WordTrace (prefixWord ++ tailWord_6865342) baseStart_6865342 baseEnd_6865342 := by
    simpa [prefixWord, tailWord_6865342, baseEnd_6865342] using wordTrace_append hprefix tailTrace_6865342
  have hstable : (prefixWord ++ tailWord_6865342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865342).length < 2 ^ (prefixWord ++ tailWord_6865342).sum := by decide
  have hdescent : baseEnd_6865342 < baseStart_6865342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865352 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_6865352 : Nat := 118140960795 + 6865352 * 2 ^ 59
def prefixEnd_6865352 : Nat := 4983230072969 + 3 ^ 40 * 6865352 * 2
def baseEnd_6865352 : Nat := 1175075146102042837475609

theorem tailTrace_6865352 : CollatzResearch.WordTrace tailWord_6865352 prefixEnd_6865352 1175075146102042837475609 := by
  unfold tailWord_6865352
  simp only [CollatzResearch.WordTrace]
  refine ⟨125199979312004843809259155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166933305749339791745678873 125199979312004843809259155)
  ·
    refine ⟨187799968968007265713888733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125199979312004843809259155 187799968968007265713888733)
    ·
      refine ⟨70424988363002724642708275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187799968968007265713888733 70424988363002724642708275)
      ·
        refine ⟨105637482544504086964062413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70424988363002724642708275 105637482544504086964062413)
        ·
          refine ⟨39614055954189032611523405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105637482544504086964062413 39614055954189032611523405)
          ·
            refine ⟨14855270982820887229321277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39614055954189032611523405 14855270982820887229321277)
            ·
              refine ⟨5570726618557832710995479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14855270982820887229321277 5570726618557832710995479)
              ·
                refine ⟨8356089927836749066493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570726618557832710995479 8356089927836749066493219)
                ·
                  refine ⟨12534134891755123599739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356089927836749066493219 12534134891755123599739829)
                  ·
                    refine ⟨1175075146102042837475609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12534134891755123599739829 1175075146102042837475609)
                    ·
                      rfl

theorem cell23_6865352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_6865352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865352 prefixEnd_6865352 := by exact prefixLift 6865352
  have htrace : WordTrace (prefixWord ++ tailWord_6865352) baseStart_6865352 baseEnd_6865352 := by
    simpa [prefixWord, tailWord_6865352, baseEnd_6865352] using wordTrace_append hprefix tailTrace_6865352
  have hstable : (prefixWord ++ tailWord_6865352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865352).length < 2 ^ (prefixWord ++ tailWord_6865352).sum := by decide
  have hdescent : baseEnd_6865352 < baseStart_6865352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865366 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6865366 : Nat := 118140960795 + 6865366 * 2 ^ 59
def prefixEnd_6865366 : Nat := 4983230072969 + 3 ^ 40 * 6865366 * 2
def baseEnd_6865366 : Nat := 3525232627035291457651763

theorem tailTrace_6865366 : CollatzResearch.WordTrace tailWord_6865366 prefixEnd_6865366 3525232627035291457651763 := by
  unfold tailWord_6865366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650029327872435500595497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166933646163972645339685301 15650029327872435500595497)
  ·
    refine ⟨11737521995904326625446623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15650029327872435500595497 11737521995904326625446623)
    ·
      refine ⟨17606282993856489938169935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11737521995904326625446623 17606282993856489938169935)
      ·
        refine ⟨26409424490784734907254903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17606282993856489938169935 26409424490784734907254903)
        ·
          refine ⟨39614136736177102360882355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26409424490784734907254903 39614136736177102360882355)
          ·
            refine ⟨59421205104265653541323533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39614136736177102360882355 59421205104265653541323533)
            ·
              refine ⟨22282951914099620077996325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59421205104265653541323533 22282951914099620077996325)
              ·
                refine ⟨4178053483893678764624311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22282951914099620077996325 4178053483893678764624311)
                ·
                  refine ⟨6267080225840518146936467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178053483893678764624311 6267080225840518146936467)
                  ·
                    refine ⟨9400620338760777220404701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6267080225840518146936467 9400620338760777220404701)
                    ·
                      refine ⟨3525232627035291457651763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400620338760777220404701 3525232627035291457651763)
                      ·
                        rfl

theorem cell23_6865366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6865366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865366 prefixEnd_6865366 := by exact prefixLift 6865366
  have htrace : WordTrace (prefixWord ++ tailWord_6865366) baseStart_6865366 baseEnd_6865366 := by
    simpa [prefixWord, tailWord_6865366, baseEnd_6865366] using wordTrace_append hprefix tailTrace_6865366
  have hstable : (prefixWord ++ tailWord_6865366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865366).length < 2 ^ (prefixWord ++ tailWord_6865366).sum := by decide
  have hdescent : baseEnd_6865366 < baseStart_6865366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865368 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_6865368 : Nat := 118140960795 + 6865368 * 2 ^ 59
def prefixEnd_6865368 : Nat := 4983230072969 + 3 ^ 40 * 6865368 * 2
def baseEnd_6865368 : Nat := 3525233653996600449826753

theorem tailTrace_6865368 : CollatzResearch.WordTrace tailWord_6865368 prefixEnd_6865368 3525233653996600449826753 := by
  unfold tailWord_6865368
  simp only [CollatzResearch.WordTrace]
  refine ⟨125200271095975861175550379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166933694794634481567400505 125200271095975861175550379)
  ·
    refine ⟨187800406643963791763325569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125200271095975861175550379 187800406643963791763325569)
    ·
      refine ⟨140850304982972843822494177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187800406643963791763325569 140850304982972843822494177)
      ·
        refine ⟨105637728737229632866870633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140850304982972843822494177 105637728737229632866870633)
        ·
          refine ⟨79228296552922224650152975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105637728737229632866870633 79228296552922224650152975)
          ·
            refine ⟨118842444829383336975229463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79228296552922224650152975 118842444829383336975229463)
            ·
              refine ⟨178263667244075005462844195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118842444829383336975229463 178263667244075005462844195)
              ·
                refine ⟨267395500866112508194266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178263667244075005462844195 267395500866112508194266293)
                ·
                  refine ⟨25068328206198047643212465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267395500866112508194266293 25068328206198047643212465)
                  ·
                    refine ⟨18801246154648535732409349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25068328206198047643212465 18801246154648535732409349)
                    ·
                      refine ⟨3525233653996600449826753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18801246154648535732409349 3525233653996600449826753)
                      ·
                        rfl

theorem cell23_6865368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_6865368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865368 prefixEnd_6865368 := by exact prefixLift 6865368
  have htrace : WordTrace (prefixWord ++ tailWord_6865368) baseStart_6865368 baseEnd_6865368 := by
    simpa [prefixWord, tailWord_6865368, baseEnd_6865368] using wordTrace_append hprefix tailTrace_6865368
  have hstable : (prefixWord ++ tailWord_6865368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865368).length < 2 ^ (prefixWord ++ tailWord_6865368).sum := by decide
  have hdescent : baseEnd_6865368 < baseStart_6865368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865375 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_6865375 : Nat := 118140960795 + 6865375 * 2 ^ 59
def prefixEnd_6865375 : Nat := 4983230072969 + 3 ^ 40 * 6865375 * 2
def baseEnd_6865375 : Nat := 3525237248361181922439221

theorem tailTrace_6865375 : CollatzResearch.WordTrace tailWord_6865375 prefixEnd_6865375 3525237248361181922439221 := by
  unfold tailWord_6865375
  simp only [CollatzResearch.WordTrace]
  refine ⟨250400797502926362546605579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166933865001950908364403719 250400797502926362546605579)
  ·
    refine ⟨375601196254389543819908369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250400797502926362546605579 375601196254389543819908369)
    ·
      refine ⟨281700897190792157864931277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375601196254389543819908369 281700897190792157864931277)
      ·
        refine ⟨105637836446547059199349229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281700897190792157864931277 105637836446547059199349229)
        ·
          refine ⟨39614188667455147199755961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105637836446547059199349229 39614188667455147199755961)
          ·
            refine ⟨29710641500591360399816971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39614188667455147199755961 29710641500591360399816971)
            ·
              refine ⟨44565962250887040599725457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29710641500591360399816971 44565962250887040599725457)
              ·
                refine ⟨33424471688165280449794093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44565962250887040599725457 33424471688165280449794093)
                ·
                  refine ⟨12534176883061980168672785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33424471688165280449794093 12534176883061980168672785)
                  ·
                    refine ⟨9400632662296485126504589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12534176883061980168672785 9400632662296485126504589)
                    ·
                      refine ⟨3525237248361181922439221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400632662296485126504589 3525237248361181922439221)
                      ·
                        rfl

theorem cell23_6865375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_6865375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865375 prefixEnd_6865375 := by exact prefixLift 6865375
  have htrace : WordTrace (prefixWord ++ tailWord_6865375) baseStart_6865375 baseEnd_6865375 := by
    simpa [prefixWord, tailWord_6865375, baseEnd_6865375] using wordTrace_append hprefix tailTrace_6865375
  have hstable : (prefixWord ++ tailWord_6865375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865375).length < 2 ^ (prefixWord ++ tailWord_6865375).sum := by decide
  have hdescent : baseEnd_6865375 < baseStart_6865375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865389 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6865389 : Nat := 118140960795 + 6865389 * 2 ^ 59
def prefixEnd_6865389 : Nat := 4983230072969 + 3 ^ 40 * 6865389 * 2
def baseEnd_6865389 : Nat := 3525244437090344867664157

theorem tailTrace_6865389 : CollatzResearch.WordTrace tailWord_6865389 prefixEnd_6865389 3525244437090344867664157 := by
  unfold tailWord_6865389
  simp only [CollatzResearch.WordTrace]
  refine ⟨250401308124875642937615221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166934205416583761958410147 250401308124875642937615221)
  ·
    refine ⟨23475122636707091525401427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250401308124875642937615221 23475122636707091525401427)
    ·
      refine ⟨35212683955060637288102141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475122636707091525401427 35212683955060637288102141)
      ·
        refine ⟨13204756483147738983038303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35212683955060637288102141 13204756483147738983038303)
        ·
          refine ⟨19807134724721608474557455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204756483147738983038303 19807134724721608474557455)
          ·
            refine ⟨29710702087082412711836183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807134724721608474557455 29710702087082412711836183)
            ·
              refine ⟨44566053130623619067754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29710702087082412711836183 44566053130623619067754275)
              ·
                refine ⟨66849079695935428601631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44566053130623619067754275 66849079695935428601631413)
                ·
                  refine ⟨6267101221493946431402945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66849079695935428601631413 6267101221493946431402945)
                  ·
                    refine ⟨4700325916120459823552209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267101221493946431402945 4700325916120459823552209)
                    ·
                      refine ⟨3525244437090344867664157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700325916120459823552209 3525244437090344867664157)
                      ·
                        rfl

theorem cell23_6865389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6865389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865389 prefixEnd_6865389 := by exact prefixLift 6865389
  have htrace : WordTrace (prefixWord ++ tailWord_6865389) baseStart_6865389 baseEnd_6865389 := by
    simpa [prefixWord, tailWord_6865389, baseEnd_6865389] using wordTrace_append hprefix tailTrace_6865389
  have hstable : (prefixWord ++ tailWord_6865389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865389).length < 2 ^ (prefixWord ++ tailWord_6865389).sum := by decide
  have hdescent : baseEnd_6865389 < baseStart_6865389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865405 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_6865405 : Nat := 118140960795 + 6865405 * 2 ^ 59
def prefixEnd_6865405 : Nat := 4983230072969 + 3 ^ 40 * 6865405 * 2
def baseEnd_6865405 : Nat := 3525252652780816805064083

theorem tailTrace_6865405 : CollatzResearch.WordTrace tailWord_6865405 prefixEnd_6865405 3525252652780816805064083 := by
  unfold tailWord_6865405
  simp only [CollatzResearch.WordTrace]
  refine ⟨250401891692817677670197669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166934594461878451780131779 250401891692817677670197669)
  ·
    refine ⟨46950354692403314563162063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250401891692817677670197669 46950354692403314563162063)
    ·
      refine ⟨70425532038604971844743095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46950354692403314563162063 70425532038604971844743095)
      ·
        refine ⟨105638298057907457767114643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70425532038604971844743095 105638298057907457767114643)
        ·
          refine ⟨158457447086861186650671965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105638298057907457767114643 158457447086861186650671965)
          ·
            refine ⟨59421542657572944994001987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158457447086861186650671965 59421542657572944994001987)
            ·
              refine ⟨89132313986359417491002981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59421542657572944994001987 89132313986359417491002981)
              ·
                refine ⟨16712308872442390779563059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89132313986359417491002981 16712308872442390779563059)
                ·
                  refine ⟨25068463308663586169344589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16712308872442390779563059 25068463308663586169344589)
                  ·
                    refine ⟨9400673740748844813504221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25068463308663586169344589 9400673740748844813504221)
                    ·
                      refine ⟨3525252652780816805064083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400673740748844813504221 3525252652780816805064083)
                      ·
                        rfl

theorem cell23_6865405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_6865405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865405 prefixEnd_6865405 := by exact prefixLift 6865405
  have htrace : WordTrace (prefixWord ++ tailWord_6865405) baseStart_6865405 baseEnd_6865405 := by
    simpa [prefixWord, tailWord_6865405, baseEnd_6865405] using wordTrace_append hprefix tailTrace_6865405
  have hstable : (prefixWord ++ tailWord_6865405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865405).length < 2 ^ (prefixWord ++ tailWord_6865405).sum := by decide
  have hdescent : baseEnd_6865405 < baseStart_6865405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865409 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_6865409 : Nat := 118140960795 + 6865409 * 2 ^ 59
def prefixEnd_6865409 : Nat := 4983230072969 + 3 ^ 40 * 6865409 * 2
def baseEnd_6865409 : Nat := 3525254706703434789414065

theorem tailTrace_6865409 : CollatzResearch.WordTrace tailWord_6865409 prefixEnd_6865409 3525254706703434789414065 := by
  unfold tailWord_6865409
  simp only [CollatzResearch.WordTrace]
  refine ⟨250402037584803186353343281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166934691723202124235562187 250402037584803186353343281)
  ·
    refine ⟨187801528188602389765007461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250402037584803186353343281 187801528188602389765007461)
    ·
      refine ⟨35212786535362948080938899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187801528188602389765007461 35212786535362948080938899)
      ·
        refine ⟨52819179803044422121408349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35212786535362948080938899 52819179803044422121408349)
        ·
          refine ⟨19807192426141658295528131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52819179803044422121408349 19807192426141658295528131)
          ·
            refine ⟨29710788639212487443292197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807192426141658295528131 29710788639212487443292197)
            ·
              refine ⟨5570772869852341395617287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29710788639212487443292197 5570772869852341395617287)
              ·
                refine ⟨8356159304778512093425931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570772869852341395617287 8356159304778512093425931)
                ·
                  refine ⟨12534238957167768140138897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356159304778512093425931 12534238957167768140138897)
                  ·
                    refine ⟨9400679217875826105104173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12534238957167768140138897 9400679217875826105104173)
                    ·
                      refine ⟨3525254706703434789414065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400679217875826105104173 3525254706703434789414065)
                      ·
                        rfl

theorem cell23_6865409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_6865409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865409 prefixEnd_6865409 := by exact prefixLift 6865409
  have htrace : WordTrace (prefixWord ++ tailWord_6865409) baseStart_6865409 baseEnd_6865409 := by
    simpa [prefixWord, tailWord_6865409, baseEnd_6865409] using wordTrace_append hprefix tailTrace_6865409
  have hstable : (prefixWord ++ tailWord_6865409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865409).length < 2 ^ (prefixWord ++ tailWord_6865409).sum := by decide
  have hdescent : baseEnd_6865409 < baseStart_6865409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865465 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6865465 : Nat := 118140960795 + 6865465 * 2 ^ 59
def prefixEnd_6865465 : Nat := 4983230072969 + 3 ^ 40 * 6865465 * 2
def baseEnd_6865465 : Nat := 3525283461620086570313807

theorem tailTrace_6865465 : CollatzResearch.WordTrace tailWord_6865465 prefixEnd_6865465 3525283461620086570313807 := by
  unfold tailWord_6865465
  simp only [CollatzResearch.WordTrace]
  refine ⟨250404080072600307917381849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166936053381733538611587899 250404080072600307917381849)
  ·
    refine ⟨187803060054450230938036387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250404080072600307917381849 187803060054450230938036387)
    ·
      refine ⟨281704590081675346407054581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187803060054450230938036387 281704590081675346407054581)
      ·
        refine ⟨26409805320157063725661367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281704590081675346407054581 26409805320157063725661367)
        ·
          refine ⟨39614707980235595588492051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26409805320157063725661367 39614707980235595588492051)
          ·
            refine ⟨59422061970353393382738077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39614707980235595588492051 59422061970353393382738077)
            ·
              refine ⟨22283273238882522518526779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59422061970353393382738077 22283273238882522518526779)
              ·
                refine ⟨33424909858323783777790169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22283273238882522518526779 33424909858323783777790169)
                ·
                  refine ⟨25068682393742837833342627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33424909858323783777790169 25068682393742837833342627)
                  ·
                    refine ⟨37603023590614256750013941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25068682393742837833342627 37603023590614256750013941)
                    ·
                      refine ⟨3525283461620086570313807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37603023590614256750013941 3525283461620086570313807)
                      ·
                        rfl

theorem cell23_6865465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6865465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865465 prefixEnd_6865465 := by exact prefixLift 6865465
  have htrace : WordTrace (prefixWord ++ tailWord_6865465) baseStart_6865465 baseEnd_6865465 := by
    simpa [prefixWord, tailWord_6865465, baseEnd_6865465] using wordTrace_append hprefix tailTrace_6865465
  have hstable : (prefixWord ++ tailWord_6865465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865465).length < 2 ^ (prefixWord ++ tailWord_6865465).sum := by decide
  have hdescent : baseEnd_6865465 < baseStart_6865465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865479 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_6865479 : Nat := 118140960795 + 6865479 * 2 ^ 59
def prefixEnd_6865479 : Nat := 4983230072969 + 3 ^ 40 * 6865479 * 2
def baseEnd_6865479 : Nat := 3525290650349249515538743

theorem tailTrace_6865479 : CollatzResearch.WordTrace tailWord_6865479 prefixEnd_6865479 3525290650349249515538743 := by
  unfold tailWord_6865479
  simp only [CollatzResearch.WordTrace]
  refine ⟨250404590694549588308391491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166936393796366392205594327 250404590694549588308391491)
  ·
    refine ⟨375606886041824382462587237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250404590694549588308391491 375606886041824382462587237)
    ·
      refine ⟨70426291132842071711735107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375606886041824382462587237 70426291132842071711735107)
      ·
        refine ⟨105639436699263107567602661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70426291132842071711735107 105639436699263107567602661)
        ·
          refine ⟨19807394381111832668925499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105639436699263107567602661 19807394381111832668925499)
          ·
            refine ⟨29711091571667749003388249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807394381111832668925499 29711091571667749003388249)
            ·
              refine ⟨22283318678750811752541187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29711091571667749003388249 22283318678750811752541187)
              ·
                refine ⟨33424978018126217628811781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22283318678750811752541187 33424978018126217628811781)
                ·
                  refine ⟨6267183378398665805402209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33424978018126217628811781 6267183378398665805402209)
                  ·
                    refine ⟨4700387533798999354051657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267183378398665805402209 4700387533798999354051657)
                    ·
                      refine ⟨3525290650349249515538743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700387533798999354051657 3525290650349249515538743)
                      ·
                        rfl

theorem cell23_6865479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_6865479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865479 prefixEnd_6865479 := by exact prefixLift 6865479
  have htrace : WordTrace (prefixWord ++ tailWord_6865479) baseStart_6865479 baseEnd_6865479 := by
    simpa [prefixWord, tailWord_6865479, baseEnd_6865479] using wordTrace_append hprefix tailTrace_6865479
  have hstable : (prefixWord ++ tailWord_6865479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865479).length < 2 ^ (prefixWord ++ tailWord_6865479).sum := by decide
  have hdescent : baseEnd_6865479 < baseStart_6865479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865488 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_6865488 : Nat := 118140960795 + 6865488 * 2 ^ 59
def prefixEnd_6865488 : Nat := 4983230072969 + 3 ^ 40 * 6865488 * 2
def baseEnd_6865488 : Nat := 3525295271675139980326201

theorem tailTrace_6865488 : CollatzResearch.WordTrace tailWord_6865488 prefixEnd_6865488 3525295271675139980326201 := by
  unfold tailWord_6865488
  simp only [CollatzResearch.WordTrace]
  refine ⟨125202459475758491422734559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166936612634344655230312745 125202459475758491422734559)
  ·
    refine ⟨187803689213637737134101839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125202459475758491422734559 187803689213637737134101839)
    ·
      refine ⟨281705533820456605701152759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187803689213637737134101839 281705533820456605701152759)
      ·
        refine ⟨422558300730684908551729139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281705533820456605701152759 422558300730684908551729139)
        ·
          refine ⟨633837451096027362827593709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422558300730684908551729139 633837451096027362827593709)
          ·
            refine ⟨237689044161010261060347641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633837451096027362827593709 237689044161010261060347641)
            ·
              refine ⟨178266783120757695795260731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237689044161010261060347641 178266783120757695795260731)
              ·
                refine ⟨267400174681136543692891097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178266783120757695795260731 267400174681136543692891097)
                ·
                  refine ⟨200550131010852407769668323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267400174681136543692891097 200550131010852407769668323)
                  ·
                    refine ⟨300825196516278611654502485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200550131010852407769668323 300825196516278611654502485)
                    ·
                      refine ⟨3525295271675139980326201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 300825196516278611654502485 3525295271675139980326201)
                      ·
                        rfl

theorem cell23_6865488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_6865488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865488 prefixEnd_6865488 := by exact prefixLift 6865488
  have htrace : WordTrace (prefixWord ++ tailWord_6865488) baseStart_6865488 baseEnd_6865488 := by
    simpa [prefixWord, tailWord_6865488, baseEnd_6865488] using wordTrace_append hprefix tailTrace_6865488
  have hstable : (prefixWord ++ tailWord_6865488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865488).length < 2 ^ (prefixWord ++ tailWord_6865488).sum := by decide
  have hdescent : baseEnd_6865488 < baseStart_6865488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865495 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_6865495 : Nat := 118140960795 + 6865495 * 2 ^ 59
def prefixEnd_6865495 : Nat := 4983230072969 + 3 ^ 40 * 6865495 * 2
def baseEnd_6865495 : Nat := 3525298866039721452938669

theorem tailTrace_6865495 : CollatzResearch.WordTrace tailWord_6865495 prefixEnd_6865495 3525298866039721452938669 := by
  unfold tailWord_6865495
  simp only [CollatzResearch.WordTrace]
  refine ⟨250405174262491623040973939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166936782841661082027315959 250405174262491623040973939)
  ·
    refine ⟨375607761393737434561460909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250405174262491623040973939 375607761393737434561460909)
    ·
      refine ⟨140852910522651537960547841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375607761393737434561460909 140852910522651537960547841)
      ·
        refine ⟨105639682891988653470410881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140852910522651537960547841 105639682891988653470410881)
        ·
          refine ⟨79229762168991490102808161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105639682891988653470410881 79229762168991490102808161)
          ·
            refine ⟨59422321626743617577106121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79229762168991490102808161 59422321626743617577106121)
            ·
              refine ⟨44566741220057713182829591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59422321626743617577106121 44566741220057713182829591)
              ·
                refine ⟨66850111830086569774244387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44566741220057713182829591 66850111830086569774244387)
                ·
                  refine ⟨100275167745129854661366581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66850111830086569774244387 100275167745129854661366581)
                  ·
                    refine ⟨9400796976105923874503117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100275167745129854661366581 9400796976105923874503117)
                    ·
                      refine ⟨3525298866039721452938669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400796976105923874503117 3525298866039721452938669)
                      ·
                        rfl

theorem cell23_6865495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_6865495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865495 prefixEnd_6865495 := by exact prefixLift 6865495
  have htrace : WordTrace (prefixWord ++ tailWord_6865495) baseStart_6865495 baseEnd_6865495 := by
    simpa [prefixWord, tailWord_6865495, baseEnd_6865495] using wordTrace_append hprefix tailTrace_6865495
  have hstable : (prefixWord ++ tailWord_6865495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865495).length < 2 ^ (prefixWord ++ tailWord_6865495).sum := by decide
  have hdescent : baseEnd_6865495 < baseStart_6865495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865496 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_6865496 : Nat := 118140960795 + 6865496 * 2 ^ 59
def prefixEnd_6865496 : Nat := 4983230072969 + 3 ^ 40 * 6865496 * 2
def baseEnd_6865496 : Nat := 3525299379520375949026165

theorem tailTrace_6865496 : CollatzResearch.WordTrace tailWord_6865496 prefixEnd_6865496 3525299379520375949026165 := by
  unfold tailWord_6865496
  simp only [CollatzResearch.WordTrace]
  refine ⟨125202605367744000105880171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166936807156992000141173561 125202605367744000105880171)
  ·
    refine ⟨187803908051616000158820257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125202605367744000105880171 187803908051616000158820257)
    ·
      refine ⟨140852931038712000119115193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187803908051616000158820257 140852931038712000119115193)
      ·
        refine ⟨105639698279034000089336395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140852931038712000119115193 105639698279034000089336395)
        ·
          refine ⟨158459547418551000134004593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105639698279034000089336395 158459547418551000134004593)
          ·
            refine ⟨118844660563913250100503445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158459547418551000134004593 118844660563913250100503445)
            ·
              refine ⟨5570843463933433598461099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118844660563913250100503445 5570843463933433598461099)
              ·
                refine ⟨8356265195900150397691649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570843463933433598461099 8356265195900150397691649)
                ·
                  refine ⟨6267198896925112798268737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8356265195900150397691649 6267198896925112798268737)
                  ·
                    refine ⟨4700399172693834598701553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267198896925112798268737 4700399172693834598701553)
                    ·
                      refine ⟨3525299379520375949026165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700399172693834598701553 3525299379520375949026165)
                      ·
                        rfl

theorem cell23_6865496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_6865496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865496 prefixEnd_6865496 := by exact prefixLift 6865496
  have htrace : WordTrace (prefixWord ++ tailWord_6865496) baseStart_6865496 baseEnd_6865496 := by
    simpa [prefixWord, tailWord_6865496, baseEnd_6865496] using wordTrace_append hprefix tailTrace_6865496
  have hstable : (prefixWord ++ tailWord_6865496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865496).length < 2 ^ (prefixWord ++ tailWord_6865496).sum := by decide
  have hdescent : baseEnd_6865496 < baseStart_6865496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865535 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_6865535 : Nat := 118140960795 + 6865535 * 2 ^ 59
def prefixEnd_6865535 : Nat := 4983230072969 + 3 ^ 40 * 6865535 * 2
def baseEnd_6865535 : Nat := 3525319405265901296438485

theorem tailTrace_6865535 : CollatzResearch.WordTrace tailWord_6865535 prefixEnd_6865535 3525319405265901296438485 := by
  unfold tailWord_6865535
  simp only [CollatzResearch.WordTrace]
  refine ⟨250406633182346709872430059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166937755454897806581620039 250406633182346709872430059)
  ·
    refine ⟨375609949773520064808645089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250406633182346709872430059 375609949773520064808645089)
    ·
      refine ⟨281707462330140048606483817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375609949773520064808645089 281707462330140048606483817)
      ·
        refine ⟨211280596747605036454862863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281707462330140048606483817 211280596747605036454862863)
        ·
          refine ⟨316920895121407554682294295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211280596747605036454862863 316920895121407554682294295)
          ·
            refine ⟨475381342682111332023441443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316920895121407554682294295 475381342682111332023441443)
            ·
              refine ⟨713072014023166998035162165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475381342682111332023441443 713072014023166998035162165)
              ·
                refine ⟨66850501314671906065796453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 713072014023166998035162165 66850501314671906065796453)
                ·
                  refine ⟨12534468996500982387336835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66850501314671906065796453 12534468996500982387336835)
                  ·
                    refine ⟨18801703494751473581005253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12534468996500982387336835 18801703494751473581005253)
                    ·
                      refine ⟨3525319405265901296438485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18801703494751473581005253 3525319405265901296438485)
                      ·
                        rfl

theorem cell23_6865535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_6865535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865535 prefixEnd_6865535 := by exact prefixLift 6865535
  have htrace : WordTrace (prefixWord ++ tailWord_6865535) baseStart_6865535 baseEnd_6865535 := by
    simpa [prefixWord, tailWord_6865535, baseEnd_6865535] using wordTrace_append hprefix tailTrace_6865535
  have hstable : (prefixWord ++ tailWord_6865535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865535).length < 2 ^ (prefixWord ++ tailWord_6865535).sum := by decide
  have hdescent : baseEnd_6865535 < baseStart_6865535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865555 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3]
def baseStart_6865555 : Nat := 118140960795 + 6865555 * 2 ^ 59
def prefixEnd_6865555 : Nat := 4983230072969 + 3 ^ 40 * 6865555 * 2
def baseEnd_6865555 : Nat := 3525329674878991218188393

theorem tailTrace_6865555 : CollatzResearch.WordTrace tailWord_6865555 prefixEnd_6865555 3525329674878991218188393 := by
  unfold tailWord_6865555
  simp only [CollatzResearch.WordTrace]
  refine ⟨250407362642274253288158119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166938241761516168858772079 250407362642274253288158119)
  ·
    refine ⟨375611043963411379932237179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250407362642274253288158119 375611043963411379932237179)
    ·
      refine ⟨563416565945117069898355769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375611043963411379932237179 563416565945117069898355769)
      ·
        refine ⟨422562424458837802423766827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563416565945117069898355769 422562424458837802423766827)
        ·
          refine ⟨633843636688256703635650241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422562424458837802423766827 633843636688256703635650241)
          ·
            refine ⟨475382727516192527726737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633843636688256703635650241 475382727516192527726737681)
            ·
              refine ⟨356537045637144395795053261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475382727516192527726737681 356537045637144395795053261)
              ·
                refine ⟨133701392113929148423144973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356537045637144395795053261 133701392113929148423144973)
                ·
                  refine ⟨50138022042723430658679365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133701392113929148423144973 50138022042723430658679365)
                  ·
                    refine ⟨9400879133010643248502381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50138022042723430658679365 9400879133010643248502381)
                    ·
                      refine ⟨3525329674878991218188393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400879133010643248502381 3525329674878991218188393)
                      ·
                        rfl

theorem cell23_6865555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_6865555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865555 prefixEnd_6865555 := by exact prefixLift 6865555
  have htrace : WordTrace (prefixWord ++ tailWord_6865555) baseStart_6865555 baseEnd_6865555 := by
    simpa [prefixWord, tailWord_6865555, baseEnd_6865555] using wordTrace_append hprefix tailTrace_6865555
  have hstable : (prefixWord ++ tailWord_6865555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865555).length < 2 ^ (prefixWord ++ tailWord_6865555).sum := by decide
  have hdescent : baseEnd_6865555 < baseStart_6865555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865572 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_6865572 : Nat := 118140960795 + 6865572 * 2 ^ 59
def prefixEnd_6865572 : Nat := 4983230072969 + 3 ^ 40 * 6865572 * 2
def baseEnd_6865572 : Nat := 3525338404050117651675815

theorem tailTrace_6865572 : CollatzResearch.WordTrace tailWord_6865572 prefixEnd_6865572 3525338404050117651675815 := by
  unfold tailWord_6865572
  simp only [CollatzResearch.WordTrace]
  refine ⟨125203991341606332595763485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166938655122141776794351313 125203991341606332595763485)
  ·
    refine ⟨46951496753102374723411307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125203991341606332595763485 46951496753102374723411307)
    ·
      refine ⟨70427245129653562085116961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46951496753102374723411307 70427245129653562085116961)
      ·
        refine ⟨52820433847240171563837721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70427245129653562085116961 52820433847240171563837721)
        ·
          refine ⟨39615325385430128672878291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52820433847240171563837721 39615325385430128672878291)
          ·
            refine ⟨59422988078145193009317437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39615325385430128672878291 59422988078145193009317437)
            ·
              refine ⟨22283620529304447378494039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59422988078145193009317437 22283620529304447378494039)
              ·
                refine ⟨33425430793956671067741059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22283620529304447378494039 33425430793956671067741059)
                ·
                  refine ⟨50138146190935006601611589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33425430793956671067741059 50138146190935006601611589)
                  ·
                    refine ⟨9400902410800313737802173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50138146190935006601611589 9400902410800313737802173)
                    ·
                      refine ⟨3525338404050117651675815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9400902410800313737802173 3525338404050117651675815)
                      ·
                        rfl

theorem cell23_6865572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_6865572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865572 prefixEnd_6865572 := by exact prefixLift 6865572
  have htrace : WordTrace (prefixWord ++ tailWord_6865572) baseStart_6865572 baseEnd_6865572 := by
    simpa [prefixWord, tailWord_6865572, baseEnd_6865572] using wordTrace_append hprefix tailTrace_6865572
  have hstable : (prefixWord ++ tailWord_6865572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865572).length < 2 ^ (prefixWord ++ tailWord_6865572).sum := by decide
  have hdescent : baseEnd_6865572 < baseStart_6865572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865642 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_6865642 : Nat := 118140960795 + 6865642 * 2 ^ 59
def prefixEnd_6865642 : Nat := 4983230072969 + 3 ^ 40 * 6865642 * 2
def baseEnd_6865642 : Nat := 3525374347695932377800493

theorem tailTrace_6865642 : CollatzResearch.WordTrace tailWord_6865642 prefixEnd_6865642 3525374347695932377800493 := by
  unfold tailWord_6865642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62602633948239766786643795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166940357195306044764383453 62602633948239766786643795)
  ·
    refine ⟨93903950922359650179965693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62602633948239766786643795 93903950922359650179965693)
    ·
      refine ⟨35213981595884868817487135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93903950922359650179965693 35213981595884868817487135)
      ·
        refine ⟨52820972393827303226230703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35213981595884868817487135 52820972393827303226230703)
        ·
          refine ⟨79231458590740954839346055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52820972393827303226230703 79231458590740954839346055)
          ·
            refine ⟨118847187886111432259019083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79231458590740954839346055 118847187886111432259019083)
            ·
              refine ⟨178270781829167148388528625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118847187886111432259019083 178270781829167148388528625)
              ·
                refine ⟨133703086371875361291396469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178270781829167148388528625 133703086371875361291396469)
                ·
                  refine ⟨12534664347363315121068419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133703086371875361291396469 12534664347363315121068419)
                  ·
                    refine ⟨18801996521044972681602629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12534664347363315121068419 18801996521044972681602629)
                    ·
                      refine ⟨3525374347695932377800493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18801996521044972681602629 3525374347695932377800493)
                      ·
                        rfl

theorem cell23_6865642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_6865642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865642 prefixEnd_6865642 := by exact prefixLift 6865642
  have htrace : WordTrace (prefixWord ++ tailWord_6865642) baseStart_6865642 baseEnd_6865642 := by
    simpa [prefixWord, tailWord_6865642, baseEnd_6865642] using wordTrace_append hprefix tailTrace_6865642
  have hstable : (prefixWord ++ tailWord_6865642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865642).length < 2 ^ (prefixWord ++ tailWord_6865642).sum := by decide
  have hdescent : baseEnd_6865642 < baseStart_6865642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865646 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_6865646 : Nat := 118140960795 + 6865646 * 2 ^ 59
def prefixEnd_6865646 : Nat := 4983230072969 + 3 ^ 40 * 6865646 * 2
def baseEnd_6865646 : Nat := 3525376401618550362150475

theorem tailTrace_6865646 : CollatzResearch.WordTrace tailWord_6865646 prefixEnd_6865646 3525376401618550362150475 := by
  unfold tailWord_6865646
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301335210618071978715099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166940454456629717219813861 31301335210618071978715099)
  ·
    refine ⟨46952002815927107968072649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31301335210618071978715099 46952002815927107968072649)
    ·
      refine ⟨35214002111945330976054487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46952002815927107968072649 35214002111945330976054487)
      ·
        refine ⟨52821003167917996464081731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35214002111945330976054487 52821003167917996464081731)
        ·
          refine ⟨79231504751876994696122597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52821003167917996464081731 79231504751876994696122597)
          ·
            refine ⟨14855907140976936505522987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79231504751876994696122597 14855907140976936505522987)
            ·
              refine ⟨22283860711465404758284481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14855907140976936505522987 22283860711465404758284481)
              ·
                refine ⟨16712895533599053568713361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22283860711465404758284481 16712895533599053568713361)
                ·
                  refine ⟨12534671650199290176535021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16712895533599053568713361 12534671650199290176535021)
                  ·
                    refine ⟨4700501868824733816200633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12534671650199290176535021 4700501868824733816200633)
                    ·
                      refine ⟨3525376401618550362150475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700501868824733816200633 3525376401618550362150475)
                      ·
                        rfl

theorem cell23_6865646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_6865646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865646 prefixEnd_6865646 := by exact prefixLift 6865646
  have htrace : WordTrace (prefixWord ++ tailWord_6865646) baseStart_6865646 baseEnd_6865646 := by
    simpa [prefixWord, tailWord_6865646, baseEnd_6865646] using wordTrace_append hprefix tailTrace_6865646
  have hstable : (prefixWord ++ tailWord_6865646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865646).length < 2 ^ (prefixWord ++ tailWord_6865646).sum := by decide
  have hdescent : baseEnd_6865646 < baseStart_6865646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865672 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6865672 : Nat := 118140960795 + 6865672 * 2 ^ 59
def prefixEnd_6865672 : Nat := 4983230072969 + 3 ^ 40 * 6865672 * 2
def baseEnd_6865672 : Nat := 3525389752115567260425355

theorem tailTrace_6865672 : CollatzResearch.WordTrace tailWord_6865672 prefixEnd_6865672 3525389752115567260425355 := by
  unfold tailWord_6865672
  simp only [CollatzResearch.WordTrace]
  refine ⟨125205814991425191135083635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166941086655233588180111513 125205814991425191135083635)
  ·
    refine ⟨187808722487137786702625453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125205814991425191135083635 187808722487137786702625453)
    ·
      refine ⟨70428270932676670013484545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187808722487137786702625453 70428270932676670013484545)
      ·
        refine ⟨52821203199507502510113409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70428270932676670013484545 52821203199507502510113409)
        ·
          refine ⟨39615902399630626882585057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52821203199507502510113409 39615902399630626882585057)
          ·
            refine ⟨29711926799722970161938793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39615902399630626882585057 29711926799722970161938793)
            ·
              refine ⟨22283945099792227621454095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29711926799722970161938793 22283945099792227621454095)
              ·
                refine ⟨33425917649688341432181143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22283945099792227621454095 33425917649688341432181143)
                ·
                  refine ⟨50138876474532512148271715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33425917649688341432181143 50138876474532512148271715)
                  ·
                    refine ⟨75208314711798768222407573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50138876474532512148271715 75208314711798768222407573)
                    ·
                      refine ⟨3525389752115567260425355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75208314711798768222407573 3525389752115567260425355)
                      ·
                        rfl

theorem cell23_6865672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6865672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865672 prefixEnd_6865672 := by exact prefixLift 6865672
  have htrace : WordTrace (prefixWord ++ tailWord_6865672) baseStart_6865672 baseEnd_6865672 := by
    simpa [prefixWord, tailWord_6865672, baseEnd_6865672] using wordTrace_append hprefix tailTrace_6865672
  have hstable : (prefixWord ++ tailWord_6865672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865672).length < 2 ^ (prefixWord ++ tailWord_6865672).sum := by decide
  have hdescent : baseEnd_6865672 < baseStart_6865672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865716 : List Nat := [2, 5, 1, 1, 3, 2, 1, 8]
def baseStart_6865716 : Nat := 118140960795 + 6865716 * 2 ^ 59
def prefixEnd_6865716 : Nat := 4983230072969 + 3 ^ 40 * 6865716 * 2
def baseEnd_6865716 : Nat := 130570827602383892158339

theorem tailTrace_6865716 : CollatzResearch.WordTrace tailWord_6865716 prefixEnd_6865716 130570827602383892158339 := by
  unfold tailWord_6865716
  simp only [CollatzResearch.WordTrace]
  refine ⟨125206617397345488892384501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166942156529793985189846001 125206617397345488892384501)
  ·
    refine ⟨11738120381001139583661047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125206617397345488892384501 11738120381001139583661047)
    ·
      refine ⟨17607180571501709375491571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738120381001139583661047 17607180571501709375491571)
      ·
        refine ⟨26410770857252564063237357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607180571501709375491571 26410770857252564063237357)
        ·
          refine ⟨9904039071469711523714009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26410770857252564063237357 9904039071469711523714009)
          ·
            refine ⟨7428029303602283642785507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9904039071469711523714009 7428029303602283642785507)
            ·
              refine ⟨11142043955403425464178261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428029303602283642785507 11142043955403425464178261)
              ·
                refine ⟨130570827602383892158339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11142043955403425464178261 130570827602383892158339)
                ·
                  rfl

theorem cell23_6865716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 8].length) (baseStart_6865716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865716 prefixEnd_6865716 := by exact prefixLift 6865716
  have htrace : WordTrace (prefixWord ++ tailWord_6865716) baseStart_6865716 baseEnd_6865716 := by
    simpa [prefixWord, tailWord_6865716, baseEnd_6865716] using wordTrace_append hprefix tailTrace_6865716
  have hstable : (prefixWord ++ tailWord_6865716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865716).length < 2 ^ (prefixWord ++ tailWord_6865716).sum := by decide
  have hdescent : baseEnd_6865716 < baseStart_6865716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865719 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_6865719 : Nat := 118140960795 + 6865719 * 2 ^ 59
def prefixEnd_6865719 : Nat := 4983230072969 + 3 ^ 40 * 6865719 * 2
def baseEnd_6865719 : Nat := 3525413885706328576537639

theorem tailTrace_6865719 : CollatzResearch.WordTrace tailWord_6865719 prefixEnd_6865719 3525413885706328576537639 := by
  unfold tailWord_6865719
  simp only [CollatzResearch.WordTrace]
  refine ⟨250413344213680109297128211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166942229475786739531418807 250413344213680109297128211)
  ·
    refine ⟨375620016320520163945692317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250413344213680109297128211 375620016320520163945692317)
    ·
      refine ⟨140857506120195061479634619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375620016320520163945692317 140857506120195061479634619)
      ·
        refine ⟨211286259180292592219451929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140857506120195061479634619 211286259180292592219451929)
        ·
          refine ⟨158464694385219444164588947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211286259180292592219451929 158464694385219444164588947)
          ·
            refine ⟨237697041577829166246883421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158464694385219444164588947 237697041577829166246883421)
            ·
              refine ⟨89136390591685937342581283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237697041577829166246883421 89136390591685937342581283)
              ·
                refine ⟨133704585887528906013871925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89136390591685937342581283 133704585887528906013871925)
                ·
                  refine ⟨12534804926955834938800493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133704585887528906013871925 12534804926955834938800493)
                  ·
                    refine ⟨4700551847608438102050185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12534804926955834938800493 4700551847608438102050185)
                    ·
                      refine ⟨3525413885706328576537639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700551847608438102050185 3525413885706328576537639)
                      ·
                        rfl

theorem cell23_6865719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_6865719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865719 prefixEnd_6865719 := by exact prefixLift 6865719
  have htrace : WordTrace (prefixWord ++ tailWord_6865719) baseStart_6865719 baseEnd_6865719 := by
    simpa [prefixWord, tailWord_6865719, baseEnd_6865719] using wordTrace_append hprefix tailTrace_6865719
  have hstable : (prefixWord ++ tailWord_6865719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865719).length < 2 ^ (prefixWord ++ tailWord_6865719).sum := by decide
  have hdescent : baseEnd_6865719 < baseStart_6865719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865736 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_6865736 : Nat := 118140960795 + 6865736 * 2 ^ 59
def prefixEnd_6865736 : Nat := 4983230072969 + 3 ^ 40 * 6865736 * 2
def baseEnd_6865736 : Nat := 3525422614877455010025061

theorem tailTrace_6865736 : CollatzResearch.WordTrace tailWord_6865736 prefixEnd_6865736 3525422614877455010025061 := by
  unfold tailWord_6865736
  simp only [CollatzResearch.WordTrace]
  refine ⟨125206982127309260600248531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166942642836412347466998041 125206982127309260600248531)
  ·
    refine ⟨187810473190963890900372797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125206982127309260600248531 187810473190963890900372797)
    ·
      refine ⟨70428927446611459087639799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187810473190963890900372797 70428927446611459087639799)
      ·
        refine ⟨105643391169917188631459699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70428927446611459087639799 105643391169917188631459699)
        ·
          refine ⟨158465086754875782947189549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105643391169917188631459699 158465086754875782947189549)
          ·
            refine ⟨59424407533078418605196081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158465086754875782947189549 59424407533078418605196081)
            ·
              refine ⟨44568305649808813953897061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59424407533078418605196081 44568305649808813953897061)
              ·
                refine ⟨8356557309339152616355699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44568305649808813953897061 8356557309339152616355699)
                ·
                  refine ⟨12534835964008728924533549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356557309339152616355699 12534835964008728924533549)
                  ·
                    refine ⟨4700563486503273346700081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12534835964008728924533549 4700563486503273346700081)
                    ·
                      refine ⟨3525422614877455010025061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700563486503273346700081 3525422614877455010025061)
                      ·
                        rfl

theorem cell23_6865736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_6865736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865736 prefixEnd_6865736 := by exact prefixLift 6865736
  have htrace : WordTrace (prefixWord ++ tailWord_6865736) baseStart_6865736 baseEnd_6865736 := by
    simpa [prefixWord, tailWord_6865736, baseEnd_6865736] using wordTrace_append hprefix tailTrace_6865736
  have hstable : (prefixWord ++ tailWord_6865736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865736).length < 2 ^ (prefixWord ++ tailWord_6865736).sum := by decide
  have hdescent : baseEnd_6865736 < baseStart_6865736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865752 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_6865752 : Nat := 118140960795 + 6865752 * 2 ^ 59
def prefixEnd_6865752 : Nat := 4983230072969 + 3 ^ 40 * 6865752 * 2
def baseEnd_6865752 : Nat := 3525430830567926947424987

theorem tailTrace_6865752 : CollatzResearch.WordTrace tailWord_6865752 prefixEnd_6865752 3525430830567926947424987 := by
  unfold tailWord_6865752
  simp only [CollatzResearch.WordTrace]
  refine ⟨125207273911280277966539755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166943031881707037288719673 125207273911280277966539755)
  ·
    refine ⟨187810910866920416949809633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125207273911280277966539755 187810910866920416949809633)
    ·
      refine ⟨140858183150190312712357225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187810910866920416949809633 140858183150190312712357225)
      ·
        refine ⟨105643637362642734534267919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140858183150190312712357225 105643637362642734534267919)
        ·
          refine ⟨158465456043964101801401879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105643637362642734534267919 158465456043964101801401879)
          ·
            refine ⟨237698184065946152702102819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158465456043964101801401879 237698184065946152702102819)
            ·
              refine ⟨356547276098919229053154229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237698184065946152702102819 356547276098919229053154229)
              ·
                refine ⟨33426307134273677723733209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356547276098919229053154229 33426307134273677723733209)
                ·
                  refine ⟨25069730350705258292799907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33426307134273677723733209 25069730350705258292799907)
                  ·
                    refine ⟨37604595526057887439199861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25069730350705258292799907 37604595526057887439199861)
                    ·
                      refine ⟨3525430830567926947424987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37604595526057887439199861 3525430830567926947424987)
                      ·
                        rfl

theorem cell23_6865752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_6865752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865752 prefixEnd_6865752 := by exact prefixLift 6865752
  have htrace : WordTrace (prefixWord ++ tailWord_6865752) baseStart_6865752 baseEnd_6865752 := by
    simpa [prefixWord, tailWord_6865752, baseEnd_6865752] using wordTrace_append hprefix tailTrace_6865752
  have hstable : (prefixWord ++ tailWord_6865752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865752).length < 2 ^ (prefixWord ++ tailWord_6865752).sum := by decide
  have hdescent : baseEnd_6865752 < baseStart_6865752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865753 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 1, 3, 2]
def baseStart_6865753 : Nat := 118140960795 + 6865753 * 2 ^ 59
def prefixEnd_6865753 : Nat := 4983230072969 + 3 ^ 40 * 6865753 * 2
def baseEnd_6865753 : Nat := 3525431344048581443512483

theorem tailTrace_6865753 : CollatzResearch.WordTrace tailWord_6865753 prefixEnd_6865753 3525431344048581443512483 := by
  unfold tailWord_6865753
  simp only [CollatzResearch.WordTrace]
  refine ⟨250414584295556933103865913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166943056197037955402577275 250414584295556933103865913)
  ·
    refine ⟨187810938221667699827899435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250414584295556933103865913 187810938221667699827899435)
    ·
      refine ⟨281716407332501549741849153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187810938221667699827899435 281716407332501549741849153)
      ·
        refine ⟨211287305499376162306386865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281716407332501549741849153 211287305499376162306386865)
        ·
          refine ⟨158465479124532121729790149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211287305499376162306386865 158465479124532121729790149)
          ·
            refine ⟨29712277335849772824335653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158465479124532121729790149 29712277335849772824335653)
            ·
              refine ⟨5571052000471832404562935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29712277335849772824335653 5571052000471832404562935)
              ·
                refine ⟨8356578000707748606844403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571052000471832404562935 8356578000707748606844403)
                ·
                  refine ⟨12534867001061622910266605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356578000707748606844403 12534867001061622910266605)
                  ·
                    refine ⟨4700575125398108591349977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12534867001061622910266605 4700575125398108591349977)
                    ·
                      refine ⟨3525431344048581443512483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700575125398108591349977 3525431344048581443512483)
                      ·
                        rfl

theorem cell23_6865753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_6865753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865753 prefixEnd_6865753 := by exact prefixLift 6865753
  have htrace : WordTrace (prefixWord ++ tailWord_6865753) baseStart_6865753 baseEnd_6865753 := by
    simpa [prefixWord, tailWord_6865753, baseEnd_6865753] using wordTrace_append hprefix tailTrace_6865753
  have hstable : (prefixWord ++ tailWord_6865753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865753).length < 2 ^ (prefixWord ++ tailWord_6865753).sum := by decide
  have hdescent : baseEnd_6865753 < baseStart_6865753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865809 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_6865809 : Nat := 118140960795 + 6865809 * 2 ^ 59
def prefixEnd_6865809 : Nat := 4983230072969 + 3 ^ 40 * 6865809 * 2
def baseEnd_6865809 : Nat := 3525460098965233224412225

theorem tailTrace_6865809 : CollatzResearch.WordTrace tailWord_6865809 prefixEnd_6865809 3525460098965233224412225 := by
  unfold tailWord_6865809
  simp only [CollatzResearch.WordTrace]
  refine ⟨250416626783354054667904481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166944417855569369778602987 250416626783354054667904481)
  ·
    refine ⟨187812470087515541000928361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250416626783354054667904481 187812470087515541000928361)
    ·
      refine ⟨140859352565636655750696271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187812470087515541000928361 140859352565636655750696271)
      ·
        refine ⟨211289028848454983626044407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140859352565636655750696271 211289028848454983626044407)
        ·
          refine ⟨316933543272682475439066611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211289028848454983626044407 316933543272682475439066611)
          ·
            refine ⟨475400314909023713158599917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316933543272682475439066611 475400314909023713158599917)
            ·
              refine ⟨178275118090883892434474969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475400314909023713158599917 178275118090883892434474969)
              ·
                refine ⟨133706338568162919325856227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178275118090883892434474969 133706338568162919325856227)
                ·
                  refine ⟨200559507852244378988784341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133706338568162919325856227 200559507852244378988784341)
                  ·
                    refine ⟨4700613465286977632549633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200559507852244378988784341 4700613465286977632549633)
                    ·
                      refine ⟨3525460098965233224412225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700613465286977632549633 3525460098965233224412225)
                      ·
                        rfl

theorem cell23_6865809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_6865809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865809 prefixEnd_6865809 := by exact prefixLift 6865809
  have htrace : WordTrace (prefixWord ++ tailWord_6865809) baseStart_6865809 baseEnd_6865809 := by
    simpa [prefixWord, tailWord_6865809, baseEnd_6865809] using wordTrace_append hprefix tailTrace_6865809
  have hstable : (prefixWord ++ tailWord_6865809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865809).length < 2 ^ (prefixWord ++ tailWord_6865809).sum := by decide
  have hdescent : baseEnd_6865809 < baseStart_6865809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865823 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 5]
def baseStart_6865823 : Nat := 118140960795 + 6865823 * 2 ^ 59
def prefixEnd_6865823 : Nat := 4983230072969 + 3 ^ 40 * 6865823 * 2
def baseEnd_6865823 : Nat := 391718587521599574404129

theorem tailTrace_6865823 : CollatzResearch.WordTrace tailWord_6865823 prefixEnd_6865823 391718587521599574404129 := by
  unfold tailWord_6865823
  simp only [CollatzResearch.WordTrace]
  refine ⟨250417137405303335058914123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166944758270202223372609415 250417137405303335058914123)
  ·
    refine ⟨375625706107955002588371185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250417137405303335058914123 375625706107955002588371185)
    ·
      refine ⟨281719279580966251941278389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375625706107955002588371185 281719279580966251941278389)
      ·
        refine ⟨26411182460715586119494849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281719279580966251941278389 26411182460715586119494849)
        ·
          refine ⟨19808386845536689589621137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26411182460715586119494849 19808386845536689589621137)
          ·
            refine ⟨14856290134152517192215853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19808386845536689589621137 14856290134152517192215853)
            ·
              refine ⟨5571108800307193947080945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14856290134152517192215853 5571108800307193947080945)
              ·
                refine ⟨4178331600230395460310709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571108800307193947080945 4178331600230395460310709)
                ·
                  refine ⟨391718587521599574404129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178331600230395460310709 391718587521599574404129)
                  ·
                    rfl

theorem cell23_6865823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 5].length) (baseStart_6865823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865823 prefixEnd_6865823 := by exact prefixLift 6865823
  have htrace : WordTrace (prefixWord ++ tailWord_6865823) baseStart_6865823 baseEnd_6865823 := by
    simpa [prefixWord, tailWord_6865823, baseEnd_6865823] using wordTrace_append hprefix tailTrace_6865823
  have hstable : (prefixWord ++ tailWord_6865823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865823).length < 2 ^ (prefixWord ++ tailWord_6865823).sum := by decide
  have hdescent : baseEnd_6865823 < baseStart_6865823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865856 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_6865856 : Nat := 118140960795 + 6865856 * 2 ^ 59
def prefixEnd_6865856 : Nat := 4983230072969 + 3 ^ 40 * 6865856 * 2
def baseEnd_6865856 : Nat := 3525484232555994540524509

theorem tailTrace_6865856 : CollatzResearch.WordTrace tailWord_6865856 prefixEnd_6865856 3525484232555994540524509 := by
  unfold tailWord_6865856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125209170507091890847432711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166945560676122521129910281 125209170507091890847432711)
  ·
    refine ⟨187813755760637836271149067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125209170507091890847432711 187813755760637836271149067)
    ·
      refine ⟨281720633640956754406723601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187813755760637836271149067 281720633640956754406723601)
      ·
        refine ⟨211290475230717565805042701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281720633640956754406723601 211290475230717565805042701)
        ·
          refine ⟨79233928211519087176891013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211290475230717565805042701 79233928211519087176891013)
          ·
            refine ⟨14856361539659828845667065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79233928211519087176891013 14856361539659828845667065)
            ·
              refine ⟨11142271154744871634250299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14856361539659828845667065 11142271154744871634250299)
              ·
                refine ⟨16713406732117307451375449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142271154744871634250299 16713406732117307451375449)
                ·
                  refine ⟨12535055049087980588531587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713406732117307451375449 12535055049087980588531587)
                  ·
                    refine ⟨18802582573631970882797381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535055049087980588531587 18802582573631970882797381)
                    ·
                      refine ⟨3525484232555994540524509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18802582573631970882797381 3525484232555994540524509)
                      ·
                        rfl

theorem cell23_6865856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_6865856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865856 prefixEnd_6865856 := by exact prefixLift 6865856
  have htrace : WordTrace (prefixWord ++ tailWord_6865856) baseStart_6865856 baseEnd_6865856 := by
    simpa [prefixWord, tailWord_6865856, baseEnd_6865856] using wordTrace_append hprefix tailTrace_6865856
  have hstable : (prefixWord ++ tailWord_6865856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865856).length < 2 ^ (prefixWord ++ tailWord_6865856).sum := by decide
  have hdescent : baseEnd_6865856 < baseStart_6865856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865859 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3]
def baseStart_6865859 : Nat := 118140960795 + 6865859 * 2 ^ 59
def prefixEnd_6865859 : Nat := 4983230072969 + 3 ^ 40 * 6865859 * 2
def baseEnd_6865859 : Nat := 3525485772997958028786995

theorem tailTrace_6865859 : CollatzResearch.WordTrace tailWord_6865859 prefixEnd_6865859 3525485772997958028786995 := by
  unfold tailWord_6865859
  simp only [CollatzResearch.WordTrace]
  refine ⟨250418450433172913207224631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166945633622115275471483087 250418450433172913207224631)
  ·
    refine ⟨375627675649759369810836947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250418450433172913207224631 375627675649759369810836947)
    ·
      refine ⟨563441513474639054716255421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375627675649759369810836947 563441513474639054716255421)
      ·
        refine ⟨211290567552989645518595783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563441513474639054716255421 211290567552989645518595783)
        ·
          refine ⟨316935851329484468277893675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211290567552989645518595783 316935851329484468277893675)
          ·
            refine ⟨475403776994226702416840513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316935851329484468277893675 475403776994226702416840513)
            ·
              refine ⟨356552832745670026812630385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475403776994226702416840513 356552832745670026812630385)
              ·
                refine ⟨267414624559252520109472789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356552832745670026812630385 267414624559252520109472789)
                ·
                  refine ⟨12535060526214961880131537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267414624559252520109472789 12535060526214961880131537)
                  ·
                    refine ⟨9401295394661221410098653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12535060526214961880131537 9401295394661221410098653)
                    ·
                      refine ⟨3525485772997958028786995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401295394661221410098653 3525485772997958028786995)
                      ·
                        rfl

theorem cell23_6865859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_6865859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865859 prefixEnd_6865859 := by exact prefixLift 6865859
  have htrace : WordTrace (prefixWord ++ tailWord_6865859) baseStart_6865859 baseEnd_6865859 := by
    simpa [prefixWord, tailWord_6865859, baseEnd_6865859] using wordTrace_append hprefix tailTrace_6865859
  have hstable : (prefixWord ++ tailWord_6865859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865859).length < 2 ^ (prefixWord ++ tailWord_6865859).sum := by decide
  have hdescent : baseEnd_6865859 < baseStart_6865859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865889 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_6865889 : Nat := 118140960795 + 6865889 * 2 ^ 59
def prefixEnd_6865889 : Nat := 4983230072969 + 3 ^ 40 * 6865889 * 2
def baseEnd_6865889 : Nat := 3525501177417592911411857

theorem tailTrace_6865889 : CollatzResearch.WordTrace tailWord_6865889 prefixEnd_6865889 3525501177417592911411857 := by
  unfold tailWord_6865889
  simp only [CollatzResearch.WordTrace]
  refine ⟨250419544623064228330816721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166946363082042818887211147 250419544623064228330816721)
  ·
    refine ⟨187814658467298171248112541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250419544623064228330816721 187814658467298171248112541)
    ·
      refine ⟨70430496925236814218042203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187814658467298171248112541 70430496925236814218042203)
      ·
        refine ⟨105645745387855221327063305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70430496925236814218042203 105645745387855221327063305)
        ·
          refine ⟨79234309040891415995297479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105645745387855221327063305 79234309040891415995297479)
          ·
            refine ⟨118851463561337123992946219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79234309040891415995297479 118851463561337123992946219)
            ·
              refine ⟨178277195342005685989419329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118851463561337123992946219 178277195342005685989419329)
              ·
                refine ⟨133707896506504264492064497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178277195342005685989419329 133707896506504264492064497)
                ·
                  refine ⟨100280922379878198369048373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133707896506504264492064497 100280922379878198369048373)
                  ·
                    refine ⟨9401336473113581097098285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100280922379878198369048373 9401336473113581097098285)
                    ·
                      refine ⟨3525501177417592911411857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401336473113581097098285 3525501177417592911411857)
                      ·
                        rfl

theorem cell23_6865889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_6865889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865889 prefixEnd_6865889 := by exact prefixLift 6865889
  have htrace : WordTrace (prefixWord ++ tailWord_6865889) baseStart_6865889 baseEnd_6865889 := by
    simpa [prefixWord, tailWord_6865889, baseEnd_6865889] using wordTrace_append hprefix tailTrace_6865889
  have hstable : (prefixWord ++ tailWord_6865889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865889).length < 2 ^ (prefixWord ++ tailWord_6865889).sum := by decide
  have hdescent : baseEnd_6865889 < baseStart_6865889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865890 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6865890 : Nat := 118140960795 + 6865890 * 2 ^ 59
def prefixEnd_6865890 : Nat := 4983230072969 + 3 ^ 40 * 6865890 * 2
def baseEnd_6865890 : Nat := 3525501690898247407499353

theorem tailTrace_6865890 : CollatzResearch.WordTrace tailWord_6865890 prefixEnd_6865890 3525501690898247407499353 := by
  unfold tailWord_6865890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62604895274015151375400781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166946387397373737001068749 62604895274015151375400781)
  ·
    refine ⟨23476835727755681765775293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62604895274015151375400781 23476835727755681765775293)
    ·
      refine ⟨8803813397908380662165735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23476835727755681765775293 8803813397908380662165735)
      ·
        refine ⟨13205720096862570993248603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803813397908380662165735 13205720096862570993248603)
        ·
          refine ⟨19808580145293856489872905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205720096862570993248603 19808580145293856489872905)
          ·
            refine ⟨14856435108970392367404679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19808580145293856489872905 14856435108970392367404679)
            ·
              refine ⟨22284652663455588551107019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856435108970392367404679 22284652663455588551107019)
              ·
                refine ⟨33426978995183382826660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22284652663455588551107019 33426978995183382826660529)
                ·
                  refine ⟨25070234246387537119995397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33426978995183382826660529 25070234246387537119995397)
                  ·
                    refine ⟨4700668921197663209999137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25070234246387537119995397 4700668921197663209999137)
                    ·
                      refine ⟨3525501690898247407499353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700668921197663209999137 3525501690898247407499353)
                      ·
                        rfl

theorem cell23_6865890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6865890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865890 prefixEnd_6865890 := by exact prefixLift 6865890
  have htrace : WordTrace (prefixWord ++ tailWord_6865890) baseStart_6865890 baseEnd_6865890 := by
    simpa [prefixWord, tailWord_6865890, baseEnd_6865890] using wordTrace_append hprefix tailTrace_6865890
  have hstable : (prefixWord ++ tailWord_6865890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865890).length < 2 ^ (prefixWord ++ tailWord_6865890).sum := by decide
  have hdescent : baseEnd_6865890 < baseStart_6865890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865910 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6865910 : Nat := 118140960795 + 6865910 * 2 ^ 59
def prefixEnd_6865910 : Nat := 4983230072969 + 3 ^ 40 * 6865910 * 2
def baseEnd_6865910 : Nat := 3525511960511337329249261

theorem tailTrace_6865910 : CollatzResearch.WordTrace tailWord_6865910 prefixEnd_6865910 3525511960511337329249261 := by
  unfold tailWord_6865910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651269409749259307333199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166946873703992099278220789 15651269409749259307333199)
  ·
    refine ⟨23476904114623888960999799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651269409749259307333199 23476904114623888960999799)
    ·
      refine ⟨35215356171935833441499699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23476904114623888960999799 35215356171935833441499699)
      ·
        refine ⟨52823034257903750162249549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35215356171935833441499699 52823034257903750162249549)
        ·
          refine ⟨19808637846713906310843581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52823034257903750162249549 19808637846713906310843581)
          ·
            refine ⟨7428239192517714866566343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19808637846713906310843581 7428239192517714866566343)
            ·
              refine ⟨11142358788776572299849515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428239192517714866566343 11142358788776572299849515)
              ·
                refine ⟨16713538183164858449774273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142358788776572299849515 16713538183164858449774273)
                ·
                  refine ⟨12535153637373643837330705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713538183164858449774273 12535153637373643837330705)
                  ·
                    refine ⟨9401365228030232877998029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12535153637373643837330705 9401365228030232877998029)
                    ·
                      refine ⟨3525511960511337329249261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401365228030232877998029 3525511960511337329249261)
                      ·
                        rfl

theorem cell23_6865910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6865910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865910 prefixEnd_6865910 := by exact prefixLift 6865910
  have htrace : WordTrace (prefixWord ++ tailWord_6865910) baseStart_6865910 baseEnd_6865910 := by
    simpa [prefixWord, tailWord_6865910, baseEnd_6865910] using wordTrace_append hprefix tailTrace_6865910
  have hstable : (prefixWord ++ tailWord_6865910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865910).length < 2 ^ (prefixWord ++ tailWord_6865910).sum := by decide
  have hdescent : baseEnd_6865910 < baseStart_6865910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865963 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 3, 2, 2]
def baseStart_6865963 : Nat := 118140960795 + 6865963 * 2 ^ 59
def prefixEnd_6865963 : Nat := 4983230072969 + 3 ^ 40 * 6865963 * 2
def baseEnd_6865963 : Nat := 3525539174986025621886517

theorem tailTrace_6865963 : CollatzResearch.WordTrace tailWord_6865963 prefixEnd_6865963 3525539174986025621886517 := by
  unfold tailWord_6865963
  simp only [CollatzResearch.WordTrace]
  refine ⟨250422243624796138969010543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166948162416530759312673695 250422243624796138969010543)
  ·
    refine ⟨375633365437194208453515815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250422243624796138969010543 375633365437194208453515815)
    ·
      refine ⟨563450048155791312680273723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375633365437194208453515815 563450048155791312680273723)
      ·
        refine ⟨845175072233686969020410585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563450048155791312680273723 845175072233686969020410585)
        ·
          refine ⟨633881304175265226765307939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845175072233686969020410585 633881304175265226765307939)
          ·
            refine ⟨950821956262897840147961909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633881304175265226765307939 950821956262897840147961909)
            ·
              refine ⟨89139558399646672513871429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 950821956262897840147961909 89139558399646672513871429)
              ·
                refine ⟨16713667199933751096350893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89139558399646672513871429 16713667199933751096350893)
                ·
                  refine ⟨6267625199975156661131585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16713667199933751096350893 6267625199975156661131585)
                  ·
                    refine ⟨4700718899981367495848689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267625199975156661131585 4700718899981367495848689)
                    ·
                      refine ⟨3525539174986025621886517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700718899981367495848689 3525539174986025621886517)
                      ·
                        rfl

theorem cell23_6865963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2, 2].length) (baseStart_6865963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865963 prefixEnd_6865963 := by exact prefixLift 6865963
  have htrace : WordTrace (prefixWord ++ tailWord_6865963) baseStart_6865963 baseEnd_6865963 := by
    simpa [prefixWord, tailWord_6865963, baseEnd_6865963] using wordTrace_append hprefix tailTrace_6865963
  have hstable : (prefixWord ++ tailWord_6865963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865963).length < 2 ^ (prefixWord ++ tailWord_6865963).sum := by decide
  have hdescent : baseEnd_6865963 < baseStart_6865963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865966 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6865966 : Nat := 118140960795 + 6865966 * 2 ^ 59
def prefixEnd_6865966 : Nat := 4983230072969 + 3 ^ 40 * 6865966 * 2
def baseEnd_6865966 : Nat := 3525540715427989110149003

theorem tailTrace_6865966 : CollatzResearch.WordTrace tailWord_6865966 prefixEnd_6865966 3525540715427989110149003 := by
  unfold tailWord_6865966
  simp only [CollatzResearch.WordTrace]
  refine ⟨31302794130473158810171219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166948235362523513654246501 31302794130473158810171219)
  ·
    refine ⟨46954191195709738215256829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31302794130473158810171219 46954191195709738215256829)
    ·
      refine ⟨17607821698391151830721311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46954191195709738215256829 17607821698391151830721311)
      ·
        refine ⟨26411732547586727746081967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607821698391151830721311 26411732547586727746081967)
        ·
          refine ⟨39617598821380091619122951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26411732547586727746081967 39617598821380091619122951)
          ·
            refine ⟨59426398232070137428684427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39617598821380091619122951 59426398232070137428684427)
            ·
              refine ⟨89139597348105206143026641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59426398232070137428684427 89139597348105206143026641)
              ·
                refine ⟨66854698011078904607269981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89139597348105206143026641 66854698011078904607269981)
                ·
                  refine ⟨25070511754154589227726243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66854698011078904607269981 25070511754154589227726243)
                  ·
                    refine ⟨37605767631231883841589365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25070511754154589227726243 37605767631231883841589365)
                    ·
                      refine ⟨3525540715427989110149003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37605767631231883841589365 3525540715427989110149003)
                      ·
                        rfl

theorem cell23_6865966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6865966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865966 prefixEnd_6865966 := by exact prefixLift 6865966
  have htrace : WordTrace (prefixWord ++ tailWord_6865966) baseStart_6865966 baseEnd_6865966 := by
    simpa [prefixWord, tailWord_6865966, baseEnd_6865966] using wordTrace_append hprefix tailTrace_6865966
  have hstable : (prefixWord ++ tailWord_6865966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865966).length < 2 ^ (prefixWord ++ tailWord_6865966).sum := by decide
  have hdescent : baseEnd_6865966 < baseStart_6865966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865969 : List Nat := [1, 2, 2, 3, 1, 2, 3, 9]
def baseStart_6865969 : Nat := 118140960795 + 6865969 * 2 ^ 59
def prefixEnd_6865969 : Nat := 4983230072969 + 3 ^ 40 * 6865969 * 2
def baseEnd_6865969 : Nat := 130575639106294540681907

theorem tailTrace_6865969 : CollatzResearch.WordTrace tailWord_6865969 prefixEnd_6865969 130575639106294540681907 := by
  unfold tailWord_6865969
  simp only [CollatzResearch.WordTrace]
  refine ⟨250422462462774401993728961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166948308308516267995819307 250422462462774401993728961)
  ·
    refine ⟨187816846847080801495296721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250422462462774401993728961 187816846847080801495296721)
    ·
      refine ⟨140862635135310601121472541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187816846847080801495296721 140862635135310601121472541)
      ·
        refine ⟨52823488175741475420552203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140862635135310601121472541 52823488175741475420552203)
        ·
          refine ⟨79235232263612213130828305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52823488175741475420552203 79235232263612213130828305)
          ·
            refine ⟨59426424197709159848121229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79235232263612213130828305 59426424197709159848121229)
            ·
              refine ⟨22284909074140934943045461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59426424197709159848121229 22284909074140934943045461)
              ·
                refine ⟨130575639106294540681907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22284909074140934943045461 130575639106294540681907)
                ·
                  rfl

theorem cell23_6865969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 9].length) (baseStart_6865969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865969 prefixEnd_6865969 := by exact prefixLift 6865969
  have htrace : WordTrace (prefixWord ++ tailWord_6865969) baseStart_6865969 baseEnd_6865969 := by
    simpa [prefixWord, tailWord_6865969, baseEnd_6865969] using wordTrace_append hprefix tailTrace_6865969
  have hstable : (prefixWord ++ tailWord_6865969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865969).length < 2 ^ (prefixWord ++ tailWord_6865969).sum := by decide
  have hdescent : baseEnd_6865969 < baseStart_6865969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865974 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_6865974 : Nat := 118140960795 + 6865974 * 2 ^ 59
def prefixEnd_6865974 : Nat := 4983230072969 + 3 ^ 40 * 6865974 * 2
def baseEnd_6865974 : Nat := 3525544823273225078848967

theorem tailTrace_6865974 : CollatzResearch.WordTrace tailWord_6865974 prefixEnd_6865974 3525544823273225078848967 := by
  unfold tailWord_6865974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651415301734767990478811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166948429885170858565107317 15651415301734767990478811)
  ·
    refine ⟨23477122952602151985718217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651415301734767990478811 23477122952602151985718217)
    ·
      refine ⟨17607842214451613989288663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23477122952602151985718217 17607842214451613989288663)
      ·
        refine ⟨26411763321677420983932995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607842214451613989288663 26411763321677420983932995)
        ·
          refine ⟨39617644982516131475899493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26411763321677420983932995 39617644982516131475899493)
          ·
            refine ⟨7428308434221774651731155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39617644982516131475899493 7428308434221774651731155)
            ·
              refine ⟨11142462651332661977596733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428308434221774651731155 11142462651332661977596733)
              ·
                refine ⟨4178423494249748241598775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11142462651332661977596733 4178423494249748241598775)
                ·
                  refine ⟨6267635241374622362398163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178423494249748241598775 6267635241374622362398163)
                  ·
                    refine ⟨9401452862061933543597245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6267635241374622362398163 9401452862061933543597245)
                    ·
                      refine ⟨3525544823273225078848967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401452862061933543597245 3525544823273225078848967)
                      ·
                        rfl

theorem cell23_6865974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_6865974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865974 prefixEnd_6865974 := by exact prefixLift 6865974
  have htrace : WordTrace (prefixWord ++ tailWord_6865974) baseStart_6865974 baseEnd_6865974 := by
    simpa [prefixWord, tailWord_6865974, baseEnd_6865974] using wordTrace_append hprefix tailTrace_6865974
  have hstable : (prefixWord ++ tailWord_6865974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865974).length < 2 ^ (prefixWord ++ tailWord_6865974).sum := by decide
  have hdescent : baseEnd_6865974 < baseStart_6865974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
