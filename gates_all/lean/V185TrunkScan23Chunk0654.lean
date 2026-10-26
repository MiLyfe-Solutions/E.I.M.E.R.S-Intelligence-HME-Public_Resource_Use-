import V185TrunkScan23Chunk0653

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3866872 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_3866872 : Nat := 118140960795 + 3866872 * 2 ^ 59
def prefixEnd_3866872 : Nat := 4983230072969 + 3 ^ 40 * 3866872 * 2
def baseEnd_3866872 : Nat := 661854655137566693072195

theorem tailTrace_3866872 : CollatzResearch.WordTrace tailWord_3866872 prefixEnd_3866872 661854655137566693072195 := by
  unfold tailWord_3866872
  simp only [CollatzResearch.WordTrace]
  refine ⟨70518204223495314002425435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94024272297993752003233913 70518204223495314002425435)
  ·
    refine ⟨105777306335242971003638153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70518204223495314002425435 105777306335242971003638153)
    ·
      refine ⟨79332979751432228252728615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105777306335242971003638153 79332979751432228252728615)
      ·
        refine ⟨118999469627148342379092923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79332979751432228252728615 118999469627148342379092923)
        ·
          refine ⟨178499204440722513568639385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118999469627148342379092923 178499204440722513568639385)
          ·
            refine ⟨133874403330541885176479539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178499204440722513568639385 133874403330541885176479539)
            ·
              refine ⟨200811604995812827764719309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133874403330541885176479539 200811604995812827764719309)
              ·
                refine ⟨75304351873429810411769741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200811604995812827764719309 75304351873429810411769741)
                ·
                  refine ⟨28239131952536178904413653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75304351873429810411769741 28239131952536178904413653)
                  ·
                    refine ⟨661854655137566693072195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28239131952536178904413653 661854655137566693072195)
                    ·
                      rfl

theorem cell23_3866872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_3866872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866872 prefixEnd_3866872 := by exact prefixLift 3866872
  have htrace : WordTrace (prefixWord ++ tailWord_3866872) baseStart_3866872 baseEnd_3866872 := by
    simpa [prefixWord, tailWord_3866872, baseEnd_3866872] using wordTrace_append hprefix tailTrace_3866872
  have hstable : (prefixWord ++ tailWord_3866872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866872).length < 2 ^ (prefixWord ++ tailWord_3866872).sum := by decide
  have hdescent : baseEnd_3866872 < baseStart_3866872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866889 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_3866889 : Nat := 118140960795 + 3866889 * 2 ^ 59
def prefixEnd_3866889 : Nat := 4983230072969 + 3 ^ 40 * 3866889 * 2
def baseEnd_3866889 : Nat := 661857564861275504234669

theorem tailTrace_3866889 : CollatzResearch.WordTrace tailWord_3866889 prefixEnd_3866889 661857564861275504234669 := by
  unfold tailWord_3866889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141037028487929039908219721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94024685658619359938813147 141037028487929039908219721)
  ·
    refine ⟨105777771365946779931164791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141037028487929039908219721 105777771365946779931164791)
    ·
      refine ⟨158666657048920169896747187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105777771365946779931164791 158666657048920169896747187)
      ·
        refine ⟨237999985573380254845120781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158666657048920169896747187 237999985573380254845120781)
        ·
          refine ⟨89249994590017595566920293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237999985573380254845120781 89249994590017595566920293)
          ·
            refine ⟨16734373985628299168797555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89249994590017595566920293 16734373985628299168797555)
            ·
              refine ⟨25101560978442448753196333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16734373985628299168797555 25101560978442448753196333)
              ·
                refine ⟨9413085366915918282448625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25101560978442448753196333 9413085366915918282448625)
                ·
                  refine ⟨7059814025186938711836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413085366915918282448625 7059814025186938711836469)
                  ·
                    refine ⟨661857564861275504234669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7059814025186938711836469 661857564861275504234669)
                    ·
                      rfl

theorem cell23_3866889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_3866889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866889 prefixEnd_3866889 := by exact prefixLift 3866889
  have htrace : WordTrace (prefixWord ++ tailWord_3866889) baseStart_3866889 baseEnd_3866889 := by
    simpa [prefixWord, tailWord_3866889, baseEnd_3866889] using wordTrace_append hprefix tailTrace_3866889
  have hstable : (prefixWord ++ tailWord_3866889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866889).length < 2 ^ (prefixWord ++ tailWord_3866889).sum := by decide
  have hdescent : baseEnd_3866889 < baseStart_3866889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866910 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3866910 : Nat := 118140960795 + 3866910 * 2 ^ 59
def prefixEnd_3866910 : Nat := 4983230072969 + 3 ^ 40 * 3866910 * 2
def baseEnd_3866910 : Nat := 220620386408618992282379

theorem tailTrace_3866910 : CollatzResearch.WordTrace tailWord_3866910 prefixEnd_3866910 220620386408618992282379 := by
  unfold tailWord_3866910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629724302606620061841773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94025196280568640329822789 17629724302606620061841773)
  ·
    refine ⟨6611146613477482523190665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17629724302606620061841773 6611146613477482523190665)
    ·
      refine ⟨4958359960108111892392999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6611146613477482523190665 4958359960108111892392999)
      ·
        refine ⟨7437539940162167838589499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958359960108111892392999 7437539940162167838589499)
        ·
          refine ⟨11156309910243251757884249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437539940162167838589499 11156309910243251757884249)
          ·
            refine ⟨8367232432682438818413187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11156309910243251757884249 8367232432682438818413187)
            ·
              refine ⟨12550848649023658227619781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367232432682438818413187 12550848649023658227619781)
              ·
                refine ⟨2353284121691935917678709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12550848649023658227619781 2353284121691935917678709)
                ·
                  refine ⟨220620386408618992282379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353284121691935917678709 220620386408618992282379)
                  ·
                    rfl

theorem cell23_3866910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3866910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866910 prefixEnd_3866910 := by exact prefixLift 3866910
  have htrace : WordTrace (prefixWord ++ tailWord_3866910) baseStart_3866910 baseEnd_3866910 := by
    simpa [prefixWord, tailWord_3866910, baseEnd_3866910] using wordTrace_append hprefix tailTrace_3866910
  have hstable : (prefixWord ++ tailWord_3866910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866910).length < 2 ^ (prefixWord ++ tailWord_3866910).sum := by decide
  have hdescent : baseEnd_3866910 < baseStart_3866910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3866983 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 6]
def baseStart_3866983 : Nat := 118140960795 + 3866983 * 2 ^ 59
def prefixEnd_3866983 : Nat := 4983230072969 + 3 ^ 40 * 3866983 * 2
def baseEnd_3866983 : Nat := 220624551307261016103175

theorem tailTrace_3866983 : CollatzResearch.WordTrace tailWord_3866983 prefixEnd_3866983 220624551307261016103175 := by
  unfold tailWord_3866983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141040456949588493962141603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94026971299725662641427735 141040456949588493962141603)
  ·
    refine ⟨211560685424382740943212405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141040456949588493962141603 211560685424382740943212405)
    ·
      refine ⟨19833814258535881963426163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211560685424382740943212405 19833814258535881963426163)
      ·
        refine ⟨29750721387803822945139245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833814258535881963426163 29750721387803822945139245)
        ·
          refine ⟨11156520520426433604427217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29750721387803822945139245 11156520520426433604427217)
          ·
            refine ⟨8367390390319825203320413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11156520520426433604427217 8367390390319825203320413)
            ·
              refine ⟨3137771396369934451245155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8367390390319825203320413 3137771396369934451245155)
              ·
                refine ⟨4706657094554901676867733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137771396369934451245155 4706657094554901676867733)
                ·
                  refine ⟨220624551307261016103175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4706657094554901676867733 220624551307261016103175)
                  ·
                    rfl

theorem cell23_3866983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 6].length) (baseStart_3866983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3866983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3866983 prefixEnd_3866983 := by exact prefixLift 3866983
  have htrace : WordTrace (prefixWord ++ tailWord_3866983) baseStart_3866983 baseEnd_3866983 := by
    simpa [prefixWord, tailWord_3866983, baseEnd_3866983] using wordTrace_append hprefix tailTrace_3866983
  have hstable : (prefixWord ++ tailWord_3866983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3866983).length < 2 ^ (prefixWord ++ tailWord_3866983).sum := by decide
  have hdescent : baseEnd_3866983 < baseStart_3866983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3866983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867043 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 2, 4]
def baseStart_3867043 : Nat := 118140960795 + 3867043 * 2 ^ 59
def prefixEnd_3867043 : Nat := 4983230072969 + 3 ^ 40 * 3867043 * 2
def baseEnd_3867043 : Nat := 661883923534872970059433

theorem tailTrace_3867043 : CollatzResearch.WordTrace tailWord_3867043 prefixEnd_3867043 661883923534872970059433 := by
  unfold tailWord_3867043
  simp only [CollatzResearch.WordTrace]
  refine ⟨141042645329371124209325783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94028430219580749472883855 141042645329371124209325783)
  ·
    refine ⟨211563967994056686313988675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141042645329371124209325783 211563967994056686313988675)
    ·
      refine ⟨317345951991085029470983013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211563967994056686313988675 317345951991085029470983013)
      ·
        refine ⟨59502365998328443025809315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317345951991085029470983013 59502365998328443025809315)
        ·
          refine ⟨89253548997492664538713973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59502365998328443025809315 89253548997492664538713973)
          ·
            refine ⟨8367520218514937300504435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89253548997492664538713973 8367520218514937300504435)
            ·
              refine ⟨12551280327772405950756653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367520218514937300504435 12551280327772405950756653)
              ·
                refine ⟨4706730122914652231533745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12551280327772405950756653 4706730122914652231533745)
                ·
                  refine ⟨3530047592185989173650309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706730122914652231533745 3530047592185989173650309)
                  ·
                    refine ⟨661883923534872970059433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530047592185989173650309 661883923534872970059433)
                    ·
                      rfl

theorem cell23_3867043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 4].length) (baseStart_3867043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867043 prefixEnd_3867043 := by exact prefixLift 3867043
  have htrace : WordTrace (prefixWord ++ tailWord_3867043) baseStart_3867043 baseEnd_3867043 := by
    simpa [prefixWord, tailWord_3867043, baseEnd_3867043] using wordTrace_append hprefix tailTrace_3867043
  have hstable : (prefixWord ++ tailWord_3867043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867043).length < 2 ^ (prefixWord ++ tailWord_3867043).sum := by decide
  have hdescent : baseEnd_3867043 < baseStart_3867043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867073 : List Nat := [1, 2, 7, 1, 12]
def baseStart_3867073 : Nat := 118140960795 + 3867073 * 2 ^ 59
def prefixEnd_3867073 : Nat := 4983230072969 + 3 ^ 40 * 3867073 * 2
def baseEnd_3867073 : Nat := 2723823285355629345409

theorem tailTrace_3867073 : CollatzResearch.WordTrace tailWord_3867073 prefixEnd_3867073 2723823285355629345409 := by
  unfold tailWord_3867073
  simp only [CollatzResearch.WordTrace]
  refine ⟨141043739519262439332917873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94029159679508292888611915 141043739519262439332917873)
  ·
    refine ⟨105782804639446829499688405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141043739519262439332917873 105782804639446829499688405)
    ·
      refine ⟨2479284483737035066398947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105782804639446829499688405 2479284483737035066398947)
      ·
        refine ⟨3718926725605552599598421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479284483737035066398947 3718926725605552599598421)
        ·
          refine ⟨2723823285355629345409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3718926725605552599598421 2723823285355629345409)
          ·
            rfl

theorem cell23_3867073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 12].length) (baseStart_3867073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867073 prefixEnd_3867073 := by exact prefixLift 3867073
  have htrace : WordTrace (prefixWord ++ tailWord_3867073) baseStart_3867073 baseEnd_3867073 := by
    simpa [prefixWord, tailWord_3867073, baseEnd_3867073] using wordTrace_append hprefix tailTrace_3867073
  have hstable : (prefixWord ++ tailWord_3867073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867073).length < 2 ^ (prefixWord ++ tailWord_3867073).sum := by decide
  have hdescent : baseEnd_3867073 < baseStart_3867073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867084 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3867084 : Nat := 118140960795 + 3867084 * 2 ^ 59
def prefixEnd_3867084 : Nat := 4983230072969 + 3 ^ 40 * 3867084 * 2
def baseEnd_3867084 : Nat := 1985672823311453249765611

theorem tailTrace_3867084 : CollatzResearch.WordTrace tailWord_3867084 prefixEnd_3867084 1985672823311453249765611 := by
  unfold tailWord_3867084
  simp only [CollatzResearch.WordTrace]
  refine ⟨70522070361111294105784153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94029427148148392141045537 70522070361111294105784153)
  ·
    refine ⟨52891552770833470579338115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70522070361111294105784153 52891552770833470579338115)
    ·
      refine ⟨79337329156250205869007173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52891552770833470579338115 79337329156250205869007173)
      ·
        refine ⟨14875749216796913600438845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79337329156250205869007173 14875749216796913600438845)
        ·
          refine ⟨5578405956298842600164567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14875749216796913600438845 5578405956298842600164567)
          ·
            refine ⟨8367608934448263900246851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578405956298842600164567 8367608934448263900246851)
            ·
              refine ⟨12551413401672395850370277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367608934448263900246851 12551413401672395850370277)
              ·
                refine ⟨2353390012813574221944427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12551413401672395850370277 2353390012813574221944427)
                ·
                  refine ⟨3530085019220361332916641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353390012813574221944427 3530085019220361332916641)
                  ·
                    refine ⟨2647563764415270999687481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530085019220361332916641 2647563764415270999687481)
                    ·
                      refine ⟨1985672823311453249765611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647563764415270999687481 1985672823311453249765611)
                      ·
                        rfl

theorem cell23_3867084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3867084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867084 prefixEnd_3867084 := by exact prefixLift 3867084
  have htrace : WordTrace (prefixWord ++ tailWord_3867084) baseStart_3867084 baseEnd_3867084 := by
    simpa [prefixWord, tailWord_3867084, baseEnd_3867084] using wordTrace_append hprefix tailTrace_3867084
  have hstable : (prefixWord ++ tailWord_3867084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867084).length < 2 ^ (prefixWord ++ tailWord_3867084).sum := by decide
  have hdescent : baseEnd_3867084 < baseStart_3867084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867090 : List Nat := [3, 2, 2, 4, 1, 2, 1, 8]
def baseStart_3867090 : Nat := 118140960795 + 3867090 * 2 ^ 59
def prefixEnd_3867090 : Nat := 4983230072969 + 3 ^ 40 * 3867090 * 2
def baseEnd_3867090 : Nat := 73543552007236304677429

theorem tailTrace_3867090 : CollatzResearch.WordTrace tailWord_3867090 prefixEnd_3867090 73543552007236304677429 := by
  unfold tailWord_3867090
  simp only [CollatzResearch.WordTrace]
  refine ⟨35261089890050212809071681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94029573040133900824191149 35261089890050212809071681)
  ·
    refine ⟨26445817417537659606803761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35261089890050212809071681 26445817417537659606803761)
    ·
      refine ⟨19834363063153244705102821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26445817417537659606803761 19834363063153244705102821)
      ·
        refine ⟨3718943074341233382206779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19834363063153244705102821 3718943074341233382206779)
        ·
          refine ⟨5578414611511850073310169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718943074341233382206779 5578414611511850073310169)
          ·
            refine ⟨4183810958633887554982627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578414611511850073310169 4183810958633887554982627)
            ·
              refine ⟨6275716437950831332473941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183810958633887554982627 6275716437950831332473941)
              ·
                refine ⟨73543552007236304677429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6275716437950831332473941 73543552007236304677429)
                ·
                  rfl

theorem cell23_3867090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_3867090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867090 prefixEnd_3867090 := by exact prefixLift 3867090
  have htrace : WordTrace (prefixWord ++ tailWord_3867090) baseStart_3867090 baseEnd_3867090 := by
    simpa [prefixWord, tailWord_3867090, baseEnd_3867090] using wordTrace_append hprefix tailTrace_3867090
  have hstable : (prefixWord ++ tailWord_3867090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867090).length < 2 ^ (prefixWord ++ tailWord_3867090).sum := by decide
  have hdescent : baseEnd_3867090 < baseStart_3867090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867123 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 4, 2]
def baseStart_3867123 : Nat := 118140960795 + 3867123 * 2 ^ 59
def prefixEnd_3867123 : Nat := 4983230072969 + 3 ^ 40 * 3867123 * 2
def baseEnd_3867123 : Nat := 1985692849056978597177931

theorem tailTrace_3867123 : CollatzResearch.WordTrace tailWord_3867123 prefixEnd_3867123 1985692849056978597177931 := by
  unfold tailWord_3867123
  simp only [CollatzResearch.WordTrace]
  refine ⟨141045563169081297872238023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94030375446054198581492015 141045563169081297872238023)
  ·
    refine ⟨211568344753621946808357035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141045563169081297872238023 211568344753621946808357035)
    ·
      refine ⟨317352517130432920212535553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211568344753621946808357035 317352517130432920212535553)
      ·
        refine ⟨238014387847824690159401665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317352517130432920212535553 238014387847824690159401665)
        ·
          refine ⟨178510790885868517619551249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238014387847824690159401665 178510790885868517619551249)
          ·
            refine ⟨133883093164401388214663437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178510790885868517619551249 133883093164401388214663437)
            ·
              refine ⟨50206159936650520580498789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133883093164401388214663437 50206159936650520580498789)
              ·
                refine ⟨9413654988121972608843523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50206159936650520580498789 9413654988121972608843523)
                ·
                  refine ⟨14120482482182958913265285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9413654988121972608843523 14120482482182958913265285)
                  ·
                    refine ⟨2647590465409304796237241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14120482482182958913265285 2647590465409304796237241)
                    ·
                      refine ⟨1985692849056978597177931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647590465409304796237241 1985692849056978597177931)
                      ·
                        rfl

theorem cell23_3867123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4, 2].length) (baseStart_3867123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867123 prefixEnd_3867123 := by exact prefixLift 3867123
  have htrace : WordTrace (prefixWord ++ tailWord_3867123) baseStart_3867123 baseEnd_3867123 := by
    simpa [prefixWord, tailWord_3867123, baseEnd_3867123] using wordTrace_append hprefix tailTrace_3867123
  have hstable : (prefixWord ++ tailWord_3867123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867123).length < 2 ^ (prefixWord ++ tailWord_3867123).sum := by decide
  have hdescent : baseEnd_3867123 < baseStart_3867123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867193 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_3867193 : Nat := 118140960795 + 3867193 * 2 ^ 59
def prefixEnd_3867193 : Nat := 4983230072969 + 3 ^ 40 * 3867193 * 2
def baseEnd_3867193 : Nat := 661909597567597774434203

theorem tailTrace_3867193 : CollatzResearch.WordTrace tailWord_3867193 prefixEnd_3867193 661909597567597774434203 := by
  unfold tailWord_3867193
  simp only [CollatzResearch.WordTrace]
  refine ⟨141048116278827699827286233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94032077519218466551524155 141048116278827699827286233)
  ·
    refine ⟨105786087209120774870464675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141048116278827699827286233 105786087209120774870464675)
    ·
      refine ⟨158679130813681162305697013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105786087209120774870464675 158679130813681162305697013)
      ·
        refine ⟨14876168513782608966159095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158679130813681162305697013 14876168513782608966159095)
        ·
          refine ⟨22314252770673913449238643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14876168513782608966159095 22314252770673913449238643)
          ·
            refine ⟨33471379156010870173857965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22314252770673913449238643 33471379156010870173857965)
            ·
              refine ⟨12551767183504076315196737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33471379156010870173857965 12551767183504076315196737)
              ·
                refine ⟨9413825387628057236397553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12551767183504076315196737 9413825387628057236397553)
                ·
                  refine ⟨7060369040721042927298165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413825387628057236397553 7060369040721042927298165)
                  ·
                    refine ⟨661909597567597774434203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7060369040721042927298165 661909597567597774434203)
                    ·
                      rfl

theorem cell23_3867193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_3867193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867193 prefixEnd_3867193 := by exact prefixLift 3867193
  have htrace : WordTrace (prefixWord ++ tailWord_3867193) baseStart_3867193 baseEnd_3867193 := by
    simpa [prefixWord, tailWord_3867193, baseEnd_3867193] using wordTrace_append hprefix tailTrace_3867193
  have hstable : (prefixWord ++ tailWord_3867193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867193).length < 2 ^ (prefixWord ++ tailWord_3867193).sum := by decide
  have hdescent : baseEnd_3867193 < baseStart_3867193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867197 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 5]
def baseStart_3867197 : Nat := 118140960795 + 3867197 * 2 ^ 59
def prefixEnd_3867197 : Nat := 4983230072969 + 3 ^ 40 * 3867197 * 2
def baseEnd_3867197 : Nat := 220636760736156811961399

theorem tailTrace_3867197 : CollatzResearch.WordTrace tailWord_3867197 prefixEnd_3867197 220636760736156811961399 := by
  unfold tailWord_3867197
  simp only [CollatzResearch.WordTrace]
  refine ⟨141048262170813208510431845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94032174780542139006954563 141048262170813208510431845)
  ·
    refine ⟨26446549157027476595705971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141048262170813208510431845 26446549157027476595705971)
    ·
      refine ⟨39669823735541214893558957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26446549157027476595705971 39669823735541214893558957)
      ·
        refine ⟨14876183900827955585084609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39669823735541214893558957 14876183900827955585084609)
        ·
          refine ⟨11157137925620966688813457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14876183900827955585084609 11157137925620966688813457)
          ·
            refine ⟨8367853444215725016610093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11157137925620966688813457 8367853444215725016610093)
            ·
              refine ⟨3137945041580896881228785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8367853444215725016610093 3137945041580896881228785)
              ·
                refine ⟨2353458781185672660921589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137945041580896881228785 2353458781185672660921589)
                ·
                  refine ⟨220636760736156811961399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353458781185672660921589 220636760736156811961399)
                  ·
                    rfl

theorem cell23_3867197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_3867197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867197 prefixEnd_3867197 := by exact prefixLift 3867197
  have htrace : WordTrace (prefixWord ++ tailWord_3867197) baseStart_3867197 baseEnd_3867197 := by
    simpa [prefixWord, tailWord_3867197, baseEnd_3867197] using wordTrace_append hprefix tailTrace_3867197
  have hstable : (prefixWord ++ tailWord_3867197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867197).length < 2 ^ (prefixWord ++ tailWord_3867197).sum := by decide
  have hdescent : baseEnd_3867197 < baseStart_3867197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867223 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 5, 4]
def baseStart_3867223 : Nat := 118140960795 + 3867223 * 2 ^ 59
def prefixEnd_3867223 : Nat := 4983230072969 + 3 ^ 40 * 3867223 * 2
def baseEnd_3867223 : Nat := 661914732374142735309157

theorem tailTrace_3867223 : CollatzResearch.WordTrace tailWord_3867223 prefixEnd_3867223 661914732374142735309157 := by
  unfold tailWord_3867223
  simp only [CollatzResearch.WordTrace]
  refine ⟨141049210468719014950878323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94032806979146009967252215 141049210468719014950878323)
  ·
    refine ⟨211573815703078522426317485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141049210468719014950878323 211573815703078522426317485)
    ·
      refine ⟨79340180888654445909869057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211573815703078522426317485 79340180888654445909869057)
      ·
        refine ⟨59505135666490834432401793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79340180888654445909869057 59505135666490834432401793)
        ·
          refine ⟨44628851749868125824301345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59505135666490834432401793 44628851749868125824301345)
          ·
            refine ⟨33471638812401094368226009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44628851749868125824301345 33471638812401094368226009)
            ·
              refine ⟨25103729109300820776169507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33471638812401094368226009 25103729109300820776169507)
              ·
                refine ⟨37655593663951231164254261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25103729109300820776169507 37655593663951231164254261)
                ·
                  refine ⟨3530211905995427921648837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37655593663951231164254261 3530211905995427921648837)
                  ·
                    refine ⟨661914732374142735309157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530211905995427921648837 661914732374142735309157)
                    ·
                      rfl

theorem cell23_3867223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_3867223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867223 prefixEnd_3867223 := by exact prefixLift 3867223
  have htrace : WordTrace (prefixWord ++ tailWord_3867223) baseStart_3867223 baseEnd_3867223 := by
    simpa [prefixWord, tailWord_3867223, baseEnd_3867223] using wordTrace_append hprefix tailTrace_3867223
  have hstable : (prefixWord ++ tailWord_3867223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867223).length < 2 ^ (prefixWord ++ tailWord_3867223).sum := by decide
  have hdescent : baseEnd_3867223 < baseStart_3867223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867226 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3867226 : Nat := 118140960795 + 3867226 * 2 ^ 59
def prefixEnd_3867226 : Nat := 4983230072969 + 3 ^ 40 * 3867226 * 2
def baseEnd_3867226 : Nat := 1985745737564391694189957

theorem tailTrace_3867226 : CollatzResearch.WordTrace tailWord_3867226 prefixEnd_3867226 1985745737564391694189957 := by
  unfold tailWord_3867226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262329971927036615809383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94032879925138764308825021 35262329971927036615809383)
  ·
    refine ⟨52893494957890554923714075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262329971927036615809383 52893494957890554923714075)
    ·
      refine ⟨79340242436835832385571113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52893494957890554923714075 79340242436835832385571113)
      ·
        refine ⟨59505181827626874289178335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79340242436835832385571113 59505181827626874289178335)
        ·
          refine ⟨89257772741440311433767503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59505181827626874289178335 89257772741440311433767503)
          ·
            refine ⟨133886659112160467150651255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89257772741440311433767503 133886659112160467150651255)
            ·
              refine ⟨200829988668240700725976883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133886659112160467150651255 200829988668240700725976883)
              ·
                refine ⟨301244983002361051088965325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200829988668240700725976883 301244983002361051088965325)
                ·
                  refine ⟨112966868625885394158361997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301244983002361051088965325 112966868625885394158361997)
                  ·
                    refine ⟨42362575734707022809385749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112966868625885394158361997 42362575734707022809385749)
                    ·
                      refine ⟨1985745737564391694189957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42362575734707022809385749 1985745737564391694189957)
                      ·
                        rfl

theorem cell23_3867226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3867226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867226 prefixEnd_3867226 := by exact prefixLift 3867226
  have htrace : WordTrace (prefixWord ++ tailWord_3867226) baseStart_3867226 baseEnd_3867226 := by
    simpa [prefixWord, tailWord_3867226, baseEnd_3867226] using wordTrace_append hprefix tailTrace_3867226
  have hstable : (prefixWord ++ tailWord_3867226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867226).length < 2 ^ (prefixWord ++ tailWord_3867226).sum := by decide
  have hdescent : baseEnd_3867226 < baseStart_3867226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_3867256 : Nat := 118140960795 + 3867256 * 2 ^ 59
def prefixEnd_3867256 : Nat := 4983230072969 + 3 ^ 40 * 3867256 * 2
def baseEnd_3867256 : Nat := 1985761141984026576814819

theorem tailTrace_3867256 : CollatzResearch.WordTrace tailWord_3867256 prefixEnd_3867256 1985761141984026576814819 := by
  unfold tailWord_3867256
  simp only [CollatzResearch.WordTrace]
  refine ⟨70525207038799730793414811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94033609385066307724553081 70525207038799730793414811)
  ·
    refine ⟨105787810558199596190122217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70525207038799730793414811 105787810558199596190122217)
    ·
      refine ⟨79340857918649697142591663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105787810558199596190122217 79340857918649697142591663)
      ·
        refine ⟨119011286877974545713887495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79340857918649697142591663 119011286877974545713887495)
        ·
          refine ⟨178516930316961818570831243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119011286877974545713887495 178516930316961818570831243)
          ·
            refine ⟨267775395475442727856246865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178516930316961818570831243 267775395475442727856246865)
            ·
              refine ⟨200831546606582045892185149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267775395475442727856246865 200831546606582045892185149)
              ·
                refine ⟨75311829977468267209569431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200831546606582045892185149 75311829977468267209569431)
                ·
                  refine ⟨112967744966202400814354147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75311829977468267209569431 112967744966202400814354147)
                  ·
                    refine ⟨169451617449303601221531221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112967744966202400814354147 169451617449303601221531221)
                    ·
                      refine ⟨1985761141984026576814819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 169451617449303601221531221 1985761141984026576814819)
                      ·
                        rfl

theorem cell23_3867256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_3867256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867256 prefixEnd_3867256 := by exact prefixLift 3867256
  have htrace : WordTrace (prefixWord ++ tailWord_3867256) baseStart_3867256 baseEnd_3867256 := by
    simpa [prefixWord, tailWord_3867256, baseEnd_3867256] using wordTrace_append hprefix tailTrace_3867256
  have hstable : (prefixWord ++ tailWord_3867256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867256).length < 2 ^ (prefixWord ++ tailWord_3867256).sum := by decide
  have hdescent : baseEnd_3867256 < baseStart_3867256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867257 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 1, 4]
def baseStart_3867257 : Nat := 118140960795 + 3867257 * 2 ^ 59
def prefixEnd_3867257 : Nat := 4983230072969 + 3 ^ 40 * 3867257 * 2
def baseEnd_3867257 : Nat := 661920551821560357634105

theorem tailTrace_3867257 : CollatzResearch.WordTrace tailWord_3867257 prefixEnd_3867257 661920551821560357634105 := by
  unfold tailWord_3867257
  simp only [CollatzResearch.WordTrace]
  refine ⟨141050450550595838757616025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94033633700397225838410683 141050450550595838757616025)
  ·
    refine ⟨105787837912946879068212019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141050450550595838757616025 105787837912946879068212019)
    ·
      refine ⟨158681756869420318602318029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105787837912946879068212019 158681756869420318602318029)
      ·
        refine ⟨59505658826032619475869261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158681756869420318602318029 59505658826032619475869261)
        ·
          refine ⟨22314622059762232303450973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59505658826032619475869261 22314622059762232303450973)
          ·
            refine ⟨8367983272410837113794115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22314622059762232303450973 8367983272410837113794115)
            ·
              refine ⟨12551974908616255670691173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367983272410837113794115 12551974908616255670691173)
              ·
                refine ⟨2353495295365547938254595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12551974908616255670691173 2353495295365547938254595)
                ·
                  refine ⟨3530242943048321907381893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353495295365547938254595 3530242943048321907381893)
                  ·
                    refine ⟨661920551821560357634105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530242943048321907381893 661920551821560357634105)
                    ·
                      rfl

theorem cell23_3867257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_3867257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867257 prefixEnd_3867257 := by exact prefixLift 3867257
  have htrace : WordTrace (prefixWord ++ tailWord_3867257) baseStart_3867257 baseEnd_3867257 := by
    simpa [prefixWord, tailWord_3867257, baseEnd_3867257] using wordTrace_append hprefix tailTrace_3867257
  have hstable : (prefixWord ++ tailWord_3867257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867257).length < 2 ^ (prefixWord ++ tailWord_3867257).sum := by decide
  have hdescent : baseEnd_3867257 < baseStart_3867257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867284 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3867284 : Nat := 118140960795 + 3867284 * 2 ^ 59
def prefixEnd_3867284 : Nat := 4983230072969 + 3 ^ 40 * 3867284 * 2
def baseEnd_3867284 : Nat := 1985775519442352467264691

theorem tailTrace_3867284 : CollatzResearch.WordTrace tailWord_3867284 prefixEnd_3867284 1985775519442352467264691 := by
  unfold tailWord_3867284
  simp only [CollatzResearch.WordTrace]
  refine ⟨70525717660749011184424453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94034290214332014912565937 70525717660749011184424453)
  ·
    refine ⟨13223572061390439597079585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70525717660749011184424453 13223572061390439597079585)
    ·
      refine ⟨9917679046042829697809689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13223572061390439597079585 9917679046042829697809689)
      ·
        refine ⟨7438259284532122273357267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917679046042829697809689 7438259284532122273357267)
        ·
          refine ⟨11157388926798183410035901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438259284532122273357267 11157388926798183410035901)
          ·
            refine ⟨4184020847549318778763463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11157388926798183410035901 4184020847549318778763463)
            ·
              refine ⟨6276031271323978168145195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184020847549318778763463 6276031271323978168145195)
              ·
                refine ⟨9414046906985967252217793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276031271323978168145195 9414046906985967252217793)
                ·
                  refine ⟨7060535180239475439163345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414046906985967252217793 7060535180239475439163345)
                  ·
                    refine ⟨5295401385179606579372509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060535180239475439163345 5295401385179606579372509)
                    ·
                      refine ⟨1985775519442352467264691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5295401385179606579372509 1985775519442352467264691)
                      ·
                        rfl

theorem cell23_3867284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3867284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867284 prefixEnd_3867284 := by exact prefixLift 3867284
  have htrace : WordTrace (prefixWord ++ tailWord_3867284) baseStart_3867284 baseEnd_3867284 := by
    simpa [prefixWord, tailWord_3867284, baseEnd_3867284] using wordTrace_append hprefix tailTrace_3867284
  have hstable : (prefixWord ++ tailWord_3867284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867284).length < 2 ^ (prefixWord ++ tailWord_3867284).sum := by decide
  have hdescent : baseEnd_3867284 < baseStart_3867284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867300 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3867300 : Nat := 118140960795 + 3867300 * 2 ^ 59
def prefixEnd_3867300 : Nat := 4983230072969 + 3 ^ 40 * 3867300 * 2
def baseEnd_3867300 : Nat := 661927911710941468221539

theorem tailTrace_3867300 : CollatzResearch.WordTrace tailWord_3867300 prefixEnd_3867300 661927911710941468221539 := by
  unfold tailWord_3867300
  simp only [CollatzResearch.WordTrace]
  refine ⟨70526009444720028550715677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94034679259626704734287569 70526009444720028550715677)
  ·
    refine ⟨26447253541770010706518379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70526009444720028550715677 26447253541770010706518379)
    ·
      refine ⟨39670880312655016059777569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26447253541770010706518379 39670880312655016059777569)
      ·
        refine ⟨29753160234491262044833177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39670880312655016059777569 29753160234491262044833177)
        ·
          refine ⟨22314870175868446533624883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29753160234491262044833177 22314870175868446533624883)
          ·
            refine ⟨33472305263802669800437325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22314870175868446533624883 33472305263802669800437325)
            ·
              refine ⟨12552114473926001175163997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33472305263802669800437325 12552114473926001175163997)
              ·
                refine ⟨4707042927722250440686499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12552114473926001175163997 4707042927722250440686499)
                ·
                  refine ⟨7060564391583375661029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707042927722250440686499 7060564391583375661029749)
                  ·
                    refine ⟨661927911710941468221539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7060564391583375661029749 661927911710941468221539)
                    ·
                      rfl

theorem cell23_3867300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3867300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867300 prefixEnd_3867300 := by exact prefixLift 3867300
  have htrace : WordTrace (prefixWord ++ tailWord_3867300) baseStart_3867300 baseEnd_3867300 := by
    simpa [prefixWord, tailWord_3867300, baseEnd_3867300] using wordTrace_append hprefix tailTrace_3867300
  have hstable : (prefixWord ++ tailWord_3867300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867300).length < 2 ^ (prefixWord ++ tailWord_3867300).sum := by decide
  have hdescent : baseEnd_3867300 < baseStart_3867300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867348 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3867348 : Nat := 118140960795 + 3867348 * 2 ^ 59
def prefixEnd_3867348 : Nat := 4983230072969 + 3 ^ 40 * 3867348 * 2
def baseEnd_3867348 : Nat := 1985808382204240216864397

theorem tailTrace_3867348 : CollatzResearch.WordTrace tailWord_3867348 prefixEnd_3867348 1985808382204240216864397 := by
  unfold tailWord_3867348
  simp only [CollatzResearch.WordTrace]
  refine ⟨70526884796633080649589349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94035846395510774199452465 70526884796633080649589349)
  ·
    refine ⟨13223790899368702621798003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70526884796633080649589349 13223790899368702621798003)
    ·
      refine ⟨19835686349053053932697005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13223790899368702621798003 19835686349053053932697005)
      ·
        refine ⟨7438382380894895224761377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19835686349053053932697005 7438382380894895224761377)
        ·
          refine ⟨5578786785671171418571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438382380894895224761377 5578786785671171418571033)
          ·
            refine ⟨4184090089253378563928275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578786785671171418571033 4184090089253378563928275)
            ·
              refine ⟨6276135133880067845892413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184090089253378563928275 6276135133880067845892413)
              ·
                refine ⟨2353550675205025442209655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6276135133880067845892413 2353550675205025442209655)
                ·
                  refine ⟨3530326012807538163314483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353550675205025442209655 3530326012807538163314483)
                  ·
                    refine ⟨5295489019211307244971725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530326012807538163314483 5295489019211307244971725)
                    ·
                      refine ⟨1985808382204240216864397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5295489019211307244971725 1985808382204240216864397)
                      ·
                        rfl

theorem cell23_3867348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3867348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867348 prefixEnd_3867348 := by exact prefixLift 3867348
  have htrace : WordTrace (prefixWord ++ tailWord_3867348) baseStart_3867348 baseEnd_3867348 := by
    simpa [prefixWord, tailWord_3867348, baseEnd_3867348] using wordTrace_append hprefix tailTrace_3867348
  have hstable : (prefixWord ++ tailWord_3867348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867348).length < 2 ^ (prefixWord ++ tailWord_3867348).sum := by decide
  have hdescent : baseEnd_3867348 < baseStart_3867348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867393 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3867393 : Nat := 118140960795 + 3867393 * 2 ^ 59
def prefixEnd_3867393 : Nat := 4983230072969 + 3 ^ 40 * 3867393 * 2
def baseEnd_3867393 : Nat := 1985831488833692540801689

theorem tailTrace_3867393 : CollatzResearch.WordTrace tailWord_3867393 prefixEnd_3867393 1985831488833692540801689 := by
  unfold tailWord_3867393
  simp only [CollatzResearch.WordTrace]
  refine ⟨141055410878103133984566833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94036940585402089323044555 141055410878103133984566833)
  ·
    refine ⟨105791558158577350488425125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141055410878103133984566833 105791558158577350488425125)
    ·
      refine ⟨19835917154733253216579711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105791558158577350488425125 19835917154733253216579711)
      ·
        refine ⟨29753875732099879824869567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19835917154733253216579711 29753875732099879824869567)
        ·
          refine ⟨44630813598149819737304351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29753875732099879824869567 44630813598149819737304351)
          ·
            refine ⟨66946220397224729605956527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44630813598149819737304351 66946220397224729605956527)
            ·
              refine ⟨100419330595837094408934791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66946220397224729605956527 100419330595837094408934791)
              ·
                refine ⟨150628995893755641613402187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100419330595837094408934791 150628995893755641613402187)
                ·
                  refine ⟨225943493840633462420103281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150628995893755641613402187 225943493840633462420103281)
                  ·
                    refine ⟨169457620380475096815077461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225943493840633462420103281 169457620380475096815077461)
                    ·
                      refine ⟨1985831488833692540801689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 169457620380475096815077461 1985831488833692540801689)
                      ·
                        rfl

theorem cell23_3867393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3867393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867393 prefixEnd_3867393 := by exact prefixLift 3867393
  have htrace : WordTrace (prefixWord ++ tailWord_3867393) baseStart_3867393 baseEnd_3867393 := by
    simpa [prefixWord, tailWord_3867393, baseEnd_3867393] using wordTrace_append hprefix tailTrace_3867393
  have hstable : (prefixWord ++ tailWord_3867393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867393).length < 2 ^ (prefixWord ++ tailWord_3867393).sum := by decide
  have hdescent : baseEnd_3867393 < baseStart_3867393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867403 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 6]
def baseStart_3867403 : Nat := 118140960795 + 3867403 * 2 ^ 59
def prefixEnd_3867403 : Nat := 4983230072969 + 3 ^ 40 * 3867403 * 2
def baseEnd_3867403 : Nat := 661945541213412500558881

theorem tailTrace_3867403 : CollatzResearch.WordTrace tailWord_3867403 prefixEnd_3867403 661945541213412500558881 := by
  unfold tailWord_3867403
  simp only [CollatzResearch.WordTrace]
  refine ⟨141055775608066905692430863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94037183738711270461620575 141055775608066905692430863)
  ·
    refine ⟨211583663412100358538646295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141055775608066905692430863 211583663412100358538646295)
    ·
      refine ⟨317375495118150537807969443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211583663412100358538646295 317375495118150537807969443)
      ·
        refine ⟨476063242677225806711954165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317375495118150537807969443 476063242677225806711954165)
        ·
          refine ⟨44630929000989919379245703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476063242677225806711954165 44630929000989919379245703)
          ·
            refine ⟨66946393501484879068868555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44630929000989919379245703 66946393501484879068868555)
            ·
              refine ⟨100419590252227318603302833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66946393501484879068868555 100419590252227318603302833)
              ·
                refine ⟨75314692689170488952477125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100419590252227318603302833 75314692689170488952477125)
                ·
                  refine ⟨14121504879219466678589461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75314692689170488952477125 14121504879219466678589461)
                  ·
                    refine ⟨661945541213412500558881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14121504879219466678589461 661945541213412500558881)
                    ·
                      rfl

theorem cell23_3867403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_3867403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867403 prefixEnd_3867403 := by exact prefixLift 3867403
  have htrace : WordTrace (prefixWord ++ tailWord_3867403) baseStart_3867403 baseEnd_3867403 := by
    simpa [prefixWord, tailWord_3867403, baseEnd_3867403] using wordTrace_append hprefix tailTrace_3867403
  have hstable : (prefixWord ++ tailWord_3867403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867403).length < 2 ^ (prefixWord ++ tailWord_3867403).sum := by decide
  have hdescent : baseEnd_3867403 < baseStart_3867403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867480 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_3867480 : Nat := 118140960795 + 3867480 * 2 ^ 59
def prefixEnd_3867480 : Nat := 4983230072969 + 3 ^ 40 * 3867480 * 2
def baseEnd_3867480 : Nat := 661958720550211233471263

theorem tailTrace_3867480 : CollatzResearch.WordTrace tailWord_3867480 prefixEnd_3867480 661958720550211233471263 := by
  unfold tailWord_3867480
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529292014393973921491947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94039056019191965228655929 70529292014393973921491947)
  ·
    refine ⟨105793938021590960882237921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70529292014393973921491947 105793938021590960882237921)
    ·
      refine ⟨79345453516193220661678441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105793938021590960882237921 79345453516193220661678441)
      ·
        refine ⟨59509090137144915496258831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79345453516193220661678441 59509090137144915496258831)
        ·
          refine ⟨89263635205717373244388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59509090137144915496258831 89263635205717373244388247)
          ·
            refine ⟨133895452808576059866582371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89263635205717373244388247 133895452808576059866582371)
            ·
              refine ⟨200843179212864089799873557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133895452808576059866582371 200843179212864089799873557)
              ·
                refine ⟨9414524025603004209369073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200843179212864089799873557 9414524025603004209369073)
                ·
                  refine ⟨7060893019202253157026805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414524025603004209369073 7060893019202253157026805)
                  ·
                    refine ⟨661958720550211233471263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7060893019202253157026805 661958720550211233471263)
                    ·
                      rfl

theorem cell23_3867480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_3867480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867480 prefixEnd_3867480 := by exact prefixLift 3867480
  have htrace : WordTrace (prefixWord ++ tailWord_3867480) baseStart_3867480 baseEnd_3867480 := by
    simpa [prefixWord, tailWord_3867480, baseEnd_3867480] using wordTrace_append hprefix tailTrace_3867480
  have hstable : (prefixWord ++ tailWord_3867480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867480).length < 2 ^ (prefixWord ++ tailWord_3867480).sum := by decide
  have hdescent : baseEnd_3867480 < baseStart_3867480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867484 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 5]
def baseStart_3867484 : Nat := 118140960795 + 3867484 * 2 ^ 59
def prefixEnd_3867484 : Nat := 4983230072969 + 3 ^ 40 * 3867484 * 2
def baseEnd_3867484 : Nat := 220653135063694631640419

theorem tailTrace_3867484 : CollatzResearch.WordTrace tailWord_3867484 prefixEnd_3867484 220653135063694631640419 := by
  unfold tailWord_3867484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529364960386728263064753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94039153280515637684086337 70529364960386728263064753)
  ·
    refine ⟨52897023720290046197298565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70529364960386728263064753 52897023720290046197298565)
    ·
      refine ⟨9918191947554383661993481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52897023720290046197298565 9918191947554383661993481)
      ·
        refine ⟨7438643960665787746495111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9918191947554383661993481 7438643960665787746495111)
        ·
          refine ⟨11157965940998681619742667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438643960665787746495111 11157965940998681619742667)
          ·
            refine ⟨16736948911498022429614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157965940998681619742667 16736948911498022429614001)
            ·
              refine ⟨12552711683623516822210501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16736948911498022429614001 12552711683623516822210501)
              ·
                refine ⟨2353633440679409404164469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12552711683623516822210501 2353633440679409404164469)
                ·
                  refine ⟨220653135063694631640419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353633440679409404164469 220653135063694631640419)
                  ·
                    rfl

theorem cell23_3867484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_3867484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867484 prefixEnd_3867484 := by exact prefixLift 3867484
  have htrace : WordTrace (prefixWord ++ tailWord_3867484) baseStart_3867484 baseEnd_3867484 := by
    simpa [prefixWord, tailWord_3867484, baseEnd_3867484] using wordTrace_append hprefix tailTrace_3867484
  have hstable : (prefixWord ++ tailWord_3867484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867484).length < 2 ^ (prefixWord ++ tailWord_3867484).sum := by decide
  have hdescent : baseEnd_3867484 < baseStart_3867484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867500 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_3867500 : Nat := 118140960795 + 3867500 * 2 ^ 59
def prefixEnd_3867500 : Nat := 4983230072969 + 3 ^ 40 * 3867500 * 2
def baseEnd_3867500 : Nat := 1985886431263723622163697

theorem tailTrace_3867500 : CollatzResearch.WordTrace tailWord_3867500 prefixEnd_3867500 1985886431263723622163697 := by
  unfold tailWord_3867500
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529656744357745629355977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94039542325810327505807969 70529656744357745629355977)
  ·
    refine ⟨52897242558268309222016983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70529656744357745629355977 52897242558268309222016983)
    ·
      refine ⟨79345863837402463833025475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52897242558268309222016983 79345863837402463833025475)
      ·
        refine ⟨119018795756103695749538213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79345863837402463833025475 119018795756103695749538213)
        ·
          refine ⟨22316024204269442953038415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119018795756103695749538213 22316024204269442953038415)
          ·
            refine ⟨33474036306404164429557623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22316024204269442953038415 33474036306404164429557623)
            ·
              refine ⟨50211054459606246644336435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33474036306404164429557623 50211054459606246644336435)
              ·
                refine ⟨75316581689409369966504653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50211054459606246644336435 75316581689409369966504653)
                ·
                  refine ⟨28243718133528513737439245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75316581689409369966504653 28243718133528513737439245)
                  ·
                    refine ⟨10591394300073192651539717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28243718133528513737439245 10591394300073192651539717)
                    ·
                      refine ⟨1985886431263723622163697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10591394300073192651539717 1985886431263723622163697)
                      ·
                        rfl

theorem cell23_3867500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_3867500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867500 prefixEnd_3867500 := by exact prefixLift 3867500
  have htrace : WordTrace (prefixWord ++ tailWord_3867500) baseStart_3867500 baseEnd_3867500 := by
    simpa [prefixWord, tailWord_3867500, baseEnd_3867500] using wordTrace_append hprefix tailTrace_3867500
  have hstable : (prefixWord ++ tailWord_3867500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867500).length < 2 ^ (prefixWord ++ tailWord_3867500).sum := by decide
  have hdescent : baseEnd_3867500 < baseStart_3867500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867517 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_3867517 : Nat := 118140960795 + 3867517 * 2 ^ 59
def prefixEnd_3867517 : Nat := 4983230072969 + 3 ^ 40 * 3867517 * 2
def baseEnd_3867517 : Nat := 1985895160434850055651119

theorem tailTrace_3867517 : CollatzResearch.WordTrace tailWord_3867517 prefixEnd_3867517 1985895160434850055651119 := by
  unfold tailWord_3867517
  simp only [CollatzResearch.WordTrace]
  refine ⟨141059933529653903162080805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94039955686435935441387203 141059933529653903162080805)
  ·
    refine ⟨26448737536810106842890151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141059933529653903162080805 26448737536810106842890151)
    ·
      refine ⟨39673106305215160264335227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448737536810106842890151 39673106305215160264335227)
      ·
        refine ⟨59509659457822740396502841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39673106305215160264335227 59509659457822740396502841)
        ·
          refine ⟨44632244593367055297377131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59509659457822740396502841 44632244593367055297377131)
          ·
            refine ⟨66948366890050582946065697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44632244593367055297377131 66948366890050582946065697)
            ·
              refine ⟨50211275167537937209549273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66948366890050582946065697 50211275167537937209549273)
              ·
                refine ⟨37658456375653452907161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50211275167537937209549273 37658456375653452907161955)
                ·
                  refine ⟨56487684563480179360742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37658456375653452907161955 56487684563480179360742933)
                  ·
                    refine ⟨2647860213913133407534825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56487684563480179360742933 2647860213913133407534825)
                    ·
                      refine ⟨1985895160434850055651119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647860213913133407534825 1985895160434850055651119)
                      ·
                        rfl

theorem cell23_3867517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_3867517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867517 prefixEnd_3867517 := by exact prefixLift 3867517
  have htrace : WordTrace (prefixWord ++ tailWord_3867517) baseStart_3867517 baseEnd_3867517 := by
    simpa [prefixWord, tailWord_3867517, baseEnd_3867517] using wordTrace_append hprefix tailTrace_3867517
  have hstable : (prefixWord ++ tailWord_3867517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867517).length < 2 ^ (prefixWord ++ tailWord_3867517).sum := by decide
  have hdescent : baseEnd_3867517 < baseStart_3867517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867518 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_3867518 : Nat := 118140960795 + 3867518 * 2 ^ 59
def prefixEnd_3867518 : Nat := 4983230072969 + 3 ^ 40 * 3867518 * 2
def baseEnd_3867518 : Nat := 220655074879500505748735

theorem tailTrace_3867518 : CollatzResearch.WordTrace tailWord_3867518 prefixEnd_3867518 220655074879500505748735 := by
  unfold tailWord_3867518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632496250331285041608401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94039980001766853555244805 17632496250331285041608401)
  ·
    refine ⟨13224372187748463781206301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17632496250331285041608401 13224372187748463781206301)
    ·
      refine ⟨4959139570405673917952363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13224372187748463781206301 4959139570405673917952363)
      ·
        refine ⟨7438709355608510876928545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959139570405673917952363 7438709355608510876928545)
        ·
          refine ⟨5579032016706383157696409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438709355608510876928545 5579032016706383157696409)
          ·
            refine ⟨4184274012529787368272307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5579032016706383157696409 4184274012529787368272307)
            ·
              refine ⟨6276411018794681052408461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184274012529787368272307 6276411018794681052408461)
              ·
                refine ⟨2353654132048005394653173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6276411018794681052408461 2353654132048005394653173)
                ·
                  refine ⟨220655074879500505748735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353654132048005394653173 220655074879500505748735)
                  ·
                    rfl

theorem cell23_3867518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_3867518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867518 prefixEnd_3867518 := by exact prefixLift 3867518
  have htrace : WordTrace (prefixWord ++ tailWord_3867518) baseStart_3867518 baseEnd_3867518 := by
    simpa [prefixWord, tailWord_3867518, baseEnd_3867518] using wordTrace_append hprefix tailTrace_3867518
  have hstable : (prefixWord ++ tailWord_3867518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867518).length < 2 ^ (prefixWord ++ tailWord_3867518).sum := by decide
  have hdescent : baseEnd_3867518 < baseStart_3867518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867600 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_3867600 : Nat := 118140960795 + 3867600 * 2 ^ 59
def prefixEnd_3867600 : Nat := 4983230072969 + 3 ^ 40 * 3867600 * 2
def baseEnd_3867600 : Nat := 661979259776391076971079

theorem tailTrace_3867600 : CollatzResearch.WordTrace tailWord_3867600 prefixEnd_3867600 661979259776391076971079 := by
  unfold tailWord_3867600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70531480394176604168676127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94041973858902138891568169 70531480394176604168676127)
  ·
    refine ⟨105797220591264906253014191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70531480394176604168676127 105797220591264906253014191)
    ·
      refine ⟨158695830886897359379521287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105797220591264906253014191 158695830886897359379521287)
      ·
        refine ⟨238043746330346039069281931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158695830886897359379521287 238043746330346039069281931)
        ·
          refine ⟨357065619495519058603922897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238043746330346039069281931 357065619495519058603922897)
          ·
            refine ⟨267799214621639293952942173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357065619495519058603922897 267799214621639293952942173)
            ·
              refine ⟨100424705483114735232353315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267799214621639293952942173 100424705483114735232353315)
              ·
                refine ⟨150637058224672102848529973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100424705483114735232353315 150637058224672102848529973)
                ·
                  refine ⟨14122224208563009642049685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150637058224672102848529973 14122224208563009642049685)
                  ·
                    refine ⟨661979259776391076971079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14122224208563009642049685 661979259776391076971079)
                    ·
                      rfl

theorem cell23_3867600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_3867600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867600 prefixEnd_3867600 := by exact prefixLift 3867600
  have htrace : WordTrace (prefixWord ++ tailWord_3867600) baseStart_3867600 baseEnd_3867600 := by
    simpa [prefixWord, tailWord_3867600, baseEnd_3867600] using wordTrace_append hprefix tailTrace_3867600
  have hstable : (prefixWord ++ tailWord_3867600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867600).length < 2 ^ (prefixWord ++ tailWord_3867600).sum := by decide
  have hdescent : baseEnd_3867600 < baseStart_3867600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867601 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_3867601 : Nat := 118140960795 + 3867601 * 2 ^ 59
def prefixEnd_3867601 : Nat := 4983230072969 + 3 ^ 40 * 3867601 * 2
def baseEnd_3867601 : Nat := 1985938292809827727000733

theorem tailTrace_3867601 : CollatzResearch.WordTrace tailWord_3867601 prefixEnd_3867601 1985938292809827727000733 := by
  unfold tailWord_3867601
  simp only [CollatzResearch.WordTrace]
  refine ⟨141062997261349585508138657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94041998174233057005425771 141062997261349585508138657)
  ·
    refine ⟨105797247946012189131103993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141062997261349585508138657 105797247946012189131103993)
    ·
      refine ⟨79347935959509141848327995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105797247946012189131103993 79347935959509141848327995)
      ·
        refine ⟨119021903939263712772491993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79347935959509141848327995 119021903939263712772491993)
        ·
          refine ⟨89266427954447784579368995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119021903939263712772491993 89266427954447784579368995)
          ·
            refine ⟨133899641931671676869053493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89266427954447784579368995 133899641931671676869053493)
            ·
              refine ⟨12553091431094219706473765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133899641931671676869053493 12553091431094219706473765)
              ·
                refine ⟨2353704643330166194963831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12553091431094219706473765 2353704643330166194963831)
                ·
                  refine ⟨3530556964995249292445747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353704643330166194963831 3530556964995249292445747)
                  ·
                    refine ⟨5295835447492873938668621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530556964995249292445747 5295835447492873938668621)
                    ·
                      refine ⟨1985938292809827727000733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5295835447492873938668621 1985938292809827727000733)
                      ·
                        rfl

theorem cell23_3867601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_3867601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867601 prefixEnd_3867601 := by exact prefixLift 3867601
  have htrace : WordTrace (prefixWord ++ tailWord_3867601) baseStart_3867601 baseEnd_3867601 := by
    simpa [prefixWord, tailWord_3867601, baseEnd_3867601] using wordTrace_append hprefix tailTrace_3867601
  have hstable : (prefixWord ++ tailWord_3867601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867601).length < 2 ^ (prefixWord ++ tailWord_3867601).sum := by decide
  have hdescent : baseEnd_3867601 < baseStart_3867601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867617 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3867617 : Nat := 118140960795 + 3867617 * 2 ^ 59
def prefixEnd_3867617 : Nat := 4983230072969 + 3 ^ 40 * 3867617 * 2
def baseEnd_3867617 : Nat := 661982169500099888133553

theorem tailTrace_3867617 : CollatzResearch.WordTrace tailWord_3867617 prefixEnd_3867617 661982169500099888133553 := by
  unfold tailWord_3867617
  simp only [CollatzResearch.WordTrace]
  refine ⟨141063580829291620240721105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94042387219527746827147403 141063580829291620240721105)
  ·
    refine ⟨105797685621968715180540829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141063580829291620240721105 105797685621968715180540829)
    ·
      refine ⟨39674132108238268192702811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105797685621968715180540829 39674132108238268192702811)
      ·
        refine ⟨59511198162357402289054217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39674132108238268192702811 59511198162357402289054217)
        ·
          refine ⟨44633398621768051716790663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59511198162357402289054217 44633398621768051716790663)
          ·
            refine ⟨66950097932652077575185995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44633398621768051716790663 66950097932652077575185995)
            ·
              refine ⟨100425146898978116362778993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66950097932652077575185995 100425146898978116362778993)
              ·
                refine ⟨75318860174233587272084245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100425146898978116362778993 75318860174233587272084245)
                ·
                  refine ⟨3530571570667199403378949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75318860174233587272084245 3530571570667199403378949)
                  ·
                    refine ⟨661982169500099888133553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530571570667199403378949 661982169500099888133553)
                    ·
                      rfl

theorem cell23_3867617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3867617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867617 prefixEnd_3867617 := by exact prefixLift 3867617
  have htrace : WordTrace (prefixWord ++ tailWord_3867617) baseStart_3867617 baseEnd_3867617 := by
    simpa [prefixWord, tailWord_3867617, baseEnd_3867617] using wordTrace_append hprefix tailTrace_3867617
  have hstable : (prefixWord ++ tailWord_3867617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867617).length < 2 ^ (prefixWord ++ tailWord_3867617).sum := by decide
  have hdescent : baseEnd_3867617 < baseStart_3867617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867618 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3867618 : Nat := 118140960795 + 3867618 * 2 ^ 59
def prefixEnd_3867618 : Nat := 4983230072969 + 3 ^ 40 * 3867618 * 2
def baseEnd_3867618 : Nat := 1985947021980954160488155

theorem tailTrace_3867618 : CollatzResearch.WordTrace tailWord_3867618 prefixEnd_3867618 1985947021980954160488155 := by
  unfold tailWord_3867618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265904325571999352876877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94042411534858664941005005 35265904325571999352876877)
  ·
    refine ⟨13224714122089499757328829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35265904325571999352876877 13224714122089499757328829)
    ·
      refine ⟨4959267795783562408998311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13224714122089499757328829 4959267795783562408998311)
      ·
        refine ⟨7438901693675343613497467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959267795783562408998311 7438901693675343613497467)
        ·
          refine ⟨11158352540513015420246201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438901693675343613497467 11158352540513015420246201)
          ·
            refine ⟨8368764405384761565184651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158352540513015420246201 8368764405384761565184651)
            ·
              refine ⟨12553146608077142347776977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368764405384761565184651 12553146608077142347776977)
              ·
                refine ⟨9414859956057856760832733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12553146608077142347776977 9414859956057856760832733)
                ·
                  refine ⟨3530572483521696285312275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9414859956057856760832733 3530572483521696285312275)
                  ·
                    refine ⟨5295858725282544427968413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530572483521696285312275 5295858725282544427968413)
                    ·
                      refine ⟨1985947021980954160488155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5295858725282544427968413 1985947021980954160488155)
                      ·
                        rfl

theorem cell23_3867618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3867618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867618 prefixEnd_3867618 := by exact prefixLift 3867618
  have htrace : WordTrace (prefixWord ++ tailWord_3867618) baseStart_3867618 baseEnd_3867618 := by
    simpa [prefixWord, tailWord_3867618, baseEnd_3867618] using wordTrace_append hprefix tailTrace_3867618
  have hstable : (prefixWord ++ tailWord_3867618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867618).length < 2 ^ (prefixWord ++ tailWord_3867618).sum := by decide
  have hdescent : baseEnd_3867618 < baseStart_3867618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867638 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_3867638 : Nat := 118140960795 + 3867638 * 2 ^ 59
def prefixEnd_3867638 : Nat := 4983230072969 + 3 ^ 40 * 3867638 * 2
def baseEnd_3867638 : Nat := 661985763864681360746021

theorem tailTrace_3867638 : CollatzResearch.WordTrace tailWord_3867638 prefixEnd_3867638 661985763864681360746021 := by
  unfold tailWord_3867638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816521672638471301702223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94042897841477027218157045 8816521672638471301702223)
  ·
    refine ⟨13224782508957706952553335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816521672638471301702223 13224782508957706952553335)
    ·
      refine ⟨19837173763436560428830003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224782508957706952553335 19837173763436560428830003)
      ·
        refine ⟨29755760645154840643245005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837173763436560428830003 29755760645154840643245005)
        ·
          refine ⟨11158410241933065241216877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29755760645154840643245005 11158410241933065241216877)
          ·
            refine ⟨4184403840724899465456329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11158410241933065241216877 4184403840724899465456329)
            ·
              refine ⟨3138302880543674599092247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184403840724899465456329 3138302880543674599092247)
              ·
                refine ⟨4707454320815511898638371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138302880543674599092247 4707454320815511898638371)
                ·
                  refine ⟨7061181481223267847957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707454320815511898638371 7061181481223267847957557)
                  ·
                    refine ⟨661985763864681360746021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7061181481223267847957557 661985763864681360746021)
                    ·
                      rfl

theorem cell23_3867638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_3867638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867638 prefixEnd_3867638 := by exact prefixLift 3867638
  have htrace : WordTrace (prefixWord ++ tailWord_3867638) baseStart_3867638 baseEnd_3867638 := by
    simpa [prefixWord, tailWord_3867638, baseEnd_3867638] using wordTrace_append hprefix tailTrace_3867638
  have hstable : (prefixWord ++ tailWord_3867638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867638).length < 2 ^ (prefixWord ++ tailWord_3867638).sum := by decide
  have hdescent : baseEnd_3867638 < baseStart_3867638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867657 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_3867657 : Nat := 118140960795 + 3867657 * 2 ^ 59
def prefixEnd_3867657 : Nat := 4983230072969 + 3 ^ 40 * 3867657 * 2
def baseEnd_3867657 : Nat := 1985967047726479507900475

theorem tailTrace_3867657 : CollatzResearch.WordTrace tailWord_3867657 prefixEnd_3867657 1985967047726479507900475 := by
  unfold tailWord_3867657
  simp only [CollatzResearch.WordTrace]
  refine ⟨141065039749146707072177225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94043359832764471381451483 141065039749146707072177225)
  ·
    refine ⟨105798779811860030304132919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141065039749146707072177225 105798779811860030304132919)
    ·
      refine ⟨158698169717790045456199379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105798779811860030304132919 158698169717790045456199379)
      ·
        refine ⟨238047254576685068184299069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158698169717790045456199379 238047254576685068184299069)
        ·
          refine ⟨89267720466256900569112151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238047254576685068184299069 89267720466256900569112151)
          ·
            refine ⟨133901580699385350853668227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89267720466256900569112151 133901580699385350853668227)
            ·
              refine ⟨200852371049078026280502341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133901580699385350853668227 200852371049078026280502341)
              ·
                refine ⟨37659819571702129927594189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200852371049078026280502341 37659819571702129927594189)
                ·
                  refine ⟨14122432339388298722847821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37659819571702129927594189 14122432339388298722847821)
                  ·
                    refine ⟨5295912127270612021067933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14122432339388298722847821 5295912127270612021067933)
                    ·
                      refine ⟨1985967047726479507900475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5295912127270612021067933 1985967047726479507900475)
                      ·
                        rfl

theorem cell23_3867657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_3867657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867657 prefixEnd_3867657 := by exact prefixLift 3867657
  have htrace : WordTrace (prefixWord ++ tailWord_3867657) baseStart_3867657 baseEnd_3867657 := by
    simpa [prefixWord, tailWord_3867657, baseEnd_3867657] using wordTrace_append hprefix tailTrace_3867657
  have hstable : (prefixWord ++ tailWord_3867657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867657).length < 2 ^ (prefixWord ++ tailWord_3867657).sum := by decide
  have hdescent : baseEnd_3867657 < baseStart_3867657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867658 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_3867658 : Nat := 118140960795 + 3867658 * 2 ^ 59
def prefixEnd_3867658 : Nat := 4983230072969 + 3 ^ 40 * 3867658 * 2
def baseEnd_3867658 : Nat := 1985967561207134003987971

theorem tailTrace_3867658 : CollatzResearch.WordTrace tailWord_3867658 prefixEnd_3867658 1985967561207134003987971 := by
  unfold tailWord_3867658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266269055535771060740907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94043384148095389495309085 35266269055535771060740907)
  ·
    refine ⟨52899403583303656591111361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266269055535771060740907 52899403583303656591111361)
    ·
      refine ⟨39674552687477742443333521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52899403583303656591111361 39674552687477742443333521)
      ·
        refine ⟨29755914515608306832500141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39674552687477742443333521 29755914515608306832500141)
        ·
          refine ⟨11158467943353115062187553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29755914515608306832500141 11158467943353115062187553)
          ·
            refine ⟨8368850957514836296640665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158467943353115062187553 8368850957514836296640665)
            ·
              refine ⟨6276638218136127222480499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8368850957514836296640665 6276638218136127222480499)
              ·
                refine ⟨9414957327204190833720749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276638218136127222480499 9414957327204190833720749)
                ·
                  refine ⟨3530608997701571562645281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9414957327204190833720749 3530608997701571562645281)
                  ·
                    refine ⟨2647956748276178671983961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530608997701571562645281 2647956748276178671983961)
                    ·
                      refine ⟨1985967561207134003987971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2647956748276178671983961 1985967561207134003987971)
                      ·
                        rfl

theorem cell23_3867658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_3867658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867658 prefixEnd_3867658 := by exact prefixLift 3867658
  have htrace : WordTrace (prefixWord ++ tailWord_3867658) baseStart_3867658 baseEnd_3867658 := by
    simpa [prefixWord, tailWord_3867658, baseEnd_3867658] using wordTrace_append hprefix tailTrace_3867658
  have hstable : (prefixWord ++ tailWord_3867658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867658).length < 2 ^ (prefixWord ++ tailWord_3867658).sum := by decide
  have hdescent : baseEnd_3867658 < baseStart_3867658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867671 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3867671 : Nat := 118140960795 + 3867671 * 2 ^ 59
def prefixEnd_3867671 : Nat := 4983230072969 + 3 ^ 40 * 3867671 * 2
def baseEnd_3867671 : Nat := 1985974236455642453125411

theorem tailTrace_3867671 : CollatzResearch.WordTrace tailWord_3867671 prefixEnd_3867671 1985974236455642453125411 := by
  unfold tailWord_3867671
  simp only [CollatzResearch.WordTrace]
  refine ⟨141065550371095987463186867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94043700247397324975457911 141065550371095987463186867)
  ·
    refine ⟨211598325556643981194780301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141065550371095987463186867 211598325556643981194780301)
    ·
      refine ⟨79349372083741492948042613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211598325556643981194780301 79349372083741492948042613)
      ·
        refine ⟨7439003632850764963878995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79349372083741492948042613 7439003632850764963878995)
        ·
          refine ⟨11158505449276147445818493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439003632850764963878995 11158505449276147445818493)
          ·
            refine ⟨4184439543478555292181935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11158505449276147445818493 4184439543478555292181935)
            ·
              refine ⟨6276659315217832938272903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184439543478555292181935 6276659315217832938272903)
              ·
                refine ⟨9414988972826749407409355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276659315217832938272903 9414988972826749407409355)
                ·
                  refine ⟨14122483459240124111114033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414988972826749407409355 14122483459240124111114033)
                  ·
                    refine ⟨10591862594430093083335525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14122483459240124111114033 10591862594430093083335525)
                    ·
                      refine ⟨1985974236455642453125411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10591862594430093083335525 1985974236455642453125411)
                      ·
                        rfl

theorem cell23_3867671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3867671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867671 prefixEnd_3867671 := by exact prefixLift 3867671
  have htrace : WordTrace (prefixWord ++ tailWord_3867671) baseStart_3867671 baseEnd_3867671 := by
    simpa [prefixWord, tailWord_3867671, baseEnd_3867671] using wordTrace_append hprefix tailTrace_3867671
  have hstable : (prefixWord ++ tailWord_3867671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867671).length < 2 ^ (prefixWord ++ tailWord_3867671).sum := by decide
  have hdescent : baseEnd_3867671 < baseStart_3867671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867725 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_3867725 : Nat := 118140960795 + 3867725 * 2 ^ 59
def prefixEnd_3867725 : Nat := 4983230072969 + 3 ^ 40 * 3867725 * 2
def baseEnd_3867725 : Nat := 1986001964410985241850163

theorem tailTrace_3867725 : CollatzResearch.WordTrace tailWord_3867725 prefixEnd_3867725 1986001964410985241850163 := by
  unfold tailWord_3867725
  simp only [CollatzResearch.WordTrace]
  refine ⟨141067519912900354685652629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94045013275266903123768419 141067519912900354685652629)
  ·
    refine ⟨6612539995917204125889967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141067519912900354685652629 6612539995917204125889967)
    ·
      refine ⟨9918809993875806188834951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6612539995917204125889967 9918809993875806188834951)
      ·
        refine ⟨14878214990813709283252427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9918809993875806188834951 14878214990813709283252427)
        ·
          refine ⟨22317322486220563924878641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14878214990813709283252427 22317322486220563924878641)
          ·
            refine ⟨16737991864665422943658981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22317322486220563924878641 16737991864665422943658981)
            ·
              refine ⟨3138373474624766801936059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16737991864665422943658981 3138373474624766801936059)
              ·
                refine ⟨4707560211937150202904089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138373474624766801936059 4707560211937150202904089)
                ·
                  refine ⟨3530670158952862652178067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707560211937150202904089 3530670158952862652178067)
                  ·
                    refine ⟨5296005238429293978267101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530670158952862652178067 5296005238429293978267101)
                    ·
                      refine ⟨1986001964410985241850163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296005238429293978267101 1986001964410985241850163)
                      ·
                        rfl

theorem cell23_3867725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_3867725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867725 prefixEnd_3867725 := by exact prefixLift 3867725
  have htrace : WordTrace (prefixWord ++ tailWord_3867725) baseStart_3867725 baseEnd_3867725 := by
    simpa [prefixWord, tailWord_3867725, baseEnd_3867725] using wordTrace_append hprefix tailTrace_3867725
  have hstable : (prefixWord ++ tailWord_3867725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867725).length < 2 ^ (prefixWord ++ tailWord_3867725).sum := by decide
  have hdescent : baseEnd_3867725 < baseStart_3867725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867752 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3867752 : Nat := 118140960795 + 3867752 * 2 ^ 59
def prefixEnd_3867752 : Nat := 4983230072969 + 3 ^ 40 * 3867752 * 2
def baseEnd_3867752 : Nat := 1986015828388656636212539

theorem tailTrace_3867752 : CollatzResearch.WordTrace tailWord_3867752 prefixEnd_3867752 1986015828388656636212539 := by
  unfold tailWord_3867752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70534252341901269148442755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94045669789201692197923673 70534252341901269148442755)
  ·
    refine ⟨105801378512851903722664133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70534252341901269148442755 105801378512851903722664133)
    ·
      refine ⟨19837758471159731947999525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105801378512851903722664133 19837758471159731947999525)
      ·
        refine ⟨3719579713342449740249911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19837758471159731947999525 3719579713342449740249911)
        ·
          refine ⟨5579369570013674610374867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719579713342449740249911 5579369570013674610374867)
          ·
            refine ⟨8369054355020511915562301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579369570013674610374867 8369054355020511915562301)
            ·
              refine ⟨3138395383132691968335863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8369054355020511915562301 3138395383132691968335863)
              ·
                refine ⟨4707593074699037952503795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138395383132691968335863 4707593074699037952503795)
                ·
                  refine ⟨7061389612048556928755693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707593074699037952503795 7061389612048556928755693)
                  ·
                    refine ⟨2648021104518208848283385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7061389612048556928755693 2648021104518208848283385)
                    ·
                      refine ⟨1986015828388656636212539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648021104518208848283385 1986015828388656636212539)
                      ·
                        rfl

theorem cell23_3867752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3867752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867752 prefixEnd_3867752 := by exact prefixLift 3867752
  have htrace : WordTrace (prefixWord ++ tailWord_3867752) baseStart_3867752 baseEnd_3867752 := by
    simpa [prefixWord, tailWord_3867752, baseEnd_3867752] using wordTrace_append hprefix tailTrace_3867752
  have hstable : (prefixWord ++ tailWord_3867752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867752).length < 2 ^ (prefixWord ++ tailWord_3867752).sum := by decide
  have hdescent : baseEnd_3867752 < baseStart_3867752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867781 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_3867781 : Nat := 118140960795 + 3867781 * 2 ^ 59
def prefixEnd_3867781 : Nat := 4983230072969 + 3 ^ 40 * 3867781 * 2
def baseEnd_3867781 : Nat := 1986030719327637022749905

theorem tailTrace_3867781 : CollatzResearch.WordTrace tailWord_3867781 prefixEnd_3867781 1986030719327637022749905 := by
  unfold tailWord_3867781
  simp only [CollatzResearch.WordTrace]
  refine ⟨141069562400697476249691197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94046374933798317499794131 141069562400697476249691197)
  ·
    refine ⟨52901085900261553593634199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141069562400697476249691197 52901085900261553593634199)
    ·
      refine ⟨79351628850392330390451299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52901085900261553593634199 79351628850392330390451299)
      ·
        refine ⟨119027443275588495585676949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79351628850392330390451299 119027443275588495585676949)
        ·
          refine ⟨5579411403543210730578607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119027443275588495585676949 5579411403543210730578607)
          ·
            refine ⟨8369117105314816095867911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579411403543210730578607 8369117105314816095867911)
            ·
              refine ⟨12553675657972224143801867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369117105314816095867911 12553675657972224143801867)
              ·
                refine ⟨18830513486958336215702801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12553675657972224143801867 18830513486958336215702801)
                ·
                  refine ⟨14122885115218752161777101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18830513486958336215702801 14122885115218752161777101)
                  ·
                    refine ⟨5296081918207032060666413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14122885115218752161777101 5296081918207032060666413)
                    ·
                      refine ⟨1986030719327637022749905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296081918207032060666413 1986030719327637022749905)
                      ·
                        rfl

theorem cell23_3867781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_3867781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867781 prefixEnd_3867781 := by exact prefixLift 3867781
  have htrace : WordTrace (prefixWord ++ tailWord_3867781) baseStart_3867781 baseEnd_3867781 := by
    simpa [prefixWord, tailWord_3867781, baseEnd_3867781] using wordTrace_append hprefix tailTrace_3867781
  have hstable : (prefixWord ++ tailWord_3867781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867781).length < 2 ^ (prefixWord ++ tailWord_3867781).sum := by decide
  have hdescent : baseEnd_3867781 < baseStart_3867781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867797 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3867797 : Nat := 118140960795 + 3867797 * 2 ^ 59
def prefixEnd_3867797 : Nat := 4983230072969 + 3 ^ 40 * 3867797 * 2
def baseEnd_3867797 : Nat := 662012978339369653383277

theorem tailTrace_3867797 : CollatzResearch.WordTrace tailWord_3867797 prefixEnd_3867797 662012978339369653383277 := by
  unfold tailWord_3867797
  simp only [CollatzResearch.WordTrace]
  refine ⟨141070145968639510982273645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94046763979093007321515763 141070145968639510982273645)
  ·
    refine ⟨52901304738239816618352617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141070145968639510982273645 52901304738239816618352617)
    ·
      refine ⟨39675978553679862463764463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52901304738239816618352617 39675978553679862463764463)
      ·
        refine ⟨59513967830519793695646695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39675978553679862463764463 59513967830519793695646695)
        ·
          refine ⟨89270951745779690543470043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59513967830519793695646695 89270951745779690543470043)
          ·
            refine ⟨133906427618669535815205065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89270951745779690543470043 133906427618669535815205065)
            ·
              refine ⟨100429820714002151861403799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133906427618669535815205065 100429820714002151861403799)
              ·
                refine ⟨150644731071003227792105699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100429820714002151861403799 150644731071003227792105699)
                ·
                  refine ⟨225967096606504841688158549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150644731071003227792105699 225967096606504841688158549)
                  ·
                    refine ⟨662012978339369653383277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 225967096606504841688158549 662012978339369653383277)
                    ·
                      rfl

theorem cell23_3867797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3867797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867797 prefixEnd_3867797 := by exact prefixLift 3867797
  have htrace : WordTrace (prefixWord ++ tailWord_3867797) baseStart_3867797 baseEnd_3867797 := by
    simpa [prefixWord, tailWord_3867797, baseEnd_3867797] using wordTrace_append hprefix tailTrace_3867797
  have hstable : (prefixWord ++ tailWord_3867797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867797).length < 2 ^ (prefixWord ++ tailWord_3867797).sum := by decide
  have hdescent : baseEnd_3867797 < baseStart_3867797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867831 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 3, 4]
def baseStart_3867831 : Nat := 118140960795 + 3867831 * 2 ^ 59
def prefixEnd_3867831 : Nat := 4983230072969 + 3 ^ 40 * 3867831 * 2
def baseEnd_3867831 : Nat := 662018797786787275708225

theorem tailTrace_3867831 : CollatzResearch.WordTrace tailWord_3867831 prefixEnd_3867831 662018797786787275708225 := by
  unfold tailWord_3867831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141071386050516334789011347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94047590700344223192674231 141071386050516334789011347)
  ·
    refine ⟨211607079075774502183517021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141071386050516334789011347 211607079075774502183517021)
    ·
      refine ⟨79352654653415438318818883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211607079075774502183517021 79352654653415438318818883)
      ·
        refine ⟨119028981980123157478228325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79352654653415438318818883 119028981980123157478228325)
        ·
          refine ⟨22317934121273092027167811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119028981980123157478228325 22317934121273092027167811)
          ·
            refine ⟨33476901181909638040751717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22317934121273092027167811 33476901181909638040751717)
            ·
              refine ⟨6276918971608057132640947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33476901181909638040751717 6276918971608057132640947)
              ·
                refine ⟨9415378457412085698961421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276918971608057132640947 9415378457412085698961421)
                ·
                  refine ⟨3530766921529532137110533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9415378457412085698961421 3530766921529532137110533)
                  ·
                    refine ⟨662018797786787275708225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530766921529532137110533 662018797786787275708225)
                    ·
                      rfl

theorem cell23_3867831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_3867831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867831 prefixEnd_3867831 := by exact prefixLift 3867831
  have htrace : WordTrace (prefixWord ++ tailWord_3867831) baseStart_3867831 baseEnd_3867831 := by
    simpa [prefixWord, tailWord_3867831, baseEnd_3867831] using wordTrace_append hprefix tailTrace_3867831
  have hstable : (prefixWord ++ tailWord_3867831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867831).length < 2 ^ (prefixWord ++ tailWord_3867831).sum := by decide
  have hdescent : baseEnd_3867831 < baseStart_3867831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867838 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_3867838 : Nat := 118140960795 + 3867838 * 2 ^ 59
def prefixEnd_3867838 : Nat := 4983230072969 + 3 ^ 40 * 3867838 * 2
def baseEnd_3867838 : Nat := 1986059987724943299737143

theorem tailTrace_3867838 : CollatzResearch.WordTrace tailWord_3867838 prefixEnd_3867838 1986059987724943299737143 := by
  unfold tailWord_3867838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17633955170186371873064521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94047760907660649989677445 17633955170186371873064521)
  ·
    refine ⟨13225466377639778904798391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17633955170186371873064521 13225466377639778904798391)
    ·
      refine ⟨19838199566459668357197587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13225466377639778904798391 19838199566459668357197587)
      ·
        refine ⟨29757299349689502535796381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19838199566459668357197587 29757299349689502535796381)
        ·
          refine ⟨11158987256133563450923643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29757299349689502535796381 11158987256133563450923643)
          ·
            refine ⟨16738480884200345176385465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158987256133563450923643 16738480884200345176385465)
            ·
              refine ⟨12553860663150258882289099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16738480884200345176385465 12553860663150258882289099)
              ·
                refine ⟨18830790994725388323433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12553860663150258882289099 18830790994725388323433649)
                ·
                  refine ⟨14123093246044041242575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18830790994725388323433649 14123093246044041242575237)
                  ·
                    refine ⟨2648079983633257732982857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14123093246044041242575237 2648079983633257732982857)
                    ·
                      refine ⟨1986059987724943299737143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648079983633257732982857 1986059987724943299737143)
                      ·
                        rfl

theorem cell23_3867838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_3867838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867838 prefixEnd_3867838 := by exact prefixLift 3867838
  have htrace : WordTrace (prefixWord ++ tailWord_3867838) baseStart_3867838 baseEnd_3867838 := by
    simpa [prefixWord, tailWord_3867838, baseEnd_3867838] using wordTrace_append hprefix tailTrace_3867838
  have hstable : (prefixWord ++ tailWord_3867838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867838).length < 2 ^ (prefixWord ++ tailWord_3867838).sum := by decide
  have hdescent : baseEnd_3867838 < baseStart_3867838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867871 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_3867871 : Nat := 118140960795 + 3867871 * 2 ^ 59
def prefixEnd_3867871 : Nat := 4983230072969 + 3 ^ 40 * 3867871 * 2
def baseEnd_3867871 : Nat := 1986076932586541670624491

theorem tailTrace_3867871 : CollatzResearch.WordTrace tailWord_3867871 prefixEnd_3867871 1986076932586541670624491 := by
  unfold tailWord_3867871
  simp only [CollatzResearch.WordTrace]
  refine ⟨141072844970371421620467467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94048563313580947746978311 141072844970371421620467467)
  ·
    refine ⟨211609267455557132430701201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141072844970371421620467467 211609267455557132430701201)
    ·
      refine ⟨158706950591667849323025901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211609267455557132430701201 158706950591667849323025901)
      ·
        refine ⟨59515106471875443496134713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158706950591667849323025901 59515106471875443496134713)
        ·
          refine ⟨44636329853906582622101035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59515106471875443496134713 44636329853906582622101035)
          ·
            refine ⟨66954494780859873933151553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44636329853906582622101035 66954494780859873933151553)
            ·
              refine ⟨50215871085644905449863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66954494780859873933151553 50215871085644905449863665)
              ·
                refine ⟨37661903314233679087397749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50215871085644905449863665 37661903314233679087397749)
                ·
                  refine ⟨3530803435709407414443539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37661903314233679087397749 3530803435709407414443539)
                  ·
                    refine ⟨5296205153564111121665309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530803435709407414443539 5296205153564111121665309)
                    ·
                      refine ⟨1986076932586541670624491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296205153564111121665309 1986076932586541670624491)
                      ·
                        rfl

theorem cell23_3867871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_3867871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867871 prefixEnd_3867871 := by exact prefixLift 3867871
  have htrace : WordTrace (prefixWord ++ tailWord_3867871) baseStart_3867871 baseEnd_3867871 := by
    simpa [prefixWord, tailWord_3867871, baseEnd_3867871] using wordTrace_append hprefix tailTrace_3867871
  have hstable : (prefixWord ++ tailWord_3867871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867871).length < 2 ^ (prefixWord ++ tailWord_3867871).sum := by decide
  have hdescent : baseEnd_3867871 < baseStart_3867871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867904 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_3867904 : Nat := 118140960795 + 3867904 * 2 ^ 59
def prefixEnd_3867904 : Nat := 4983230072969 + 3 ^ 40 * 3867904 * 2
def baseEnd_3867904 : Nat := 662031292482713347170613

theorem tailTrace_3867904 : CollatzResearch.WordTrace tailWord_3867904 prefixEnd_3867904 662031292482713347170613 := by
  unfold tailWord_3867904
  simp only [CollatzResearch.WordTrace]
  refine ⟨70537024289625934128209383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94049365719501245504279177 70537024289625934128209383)
  ·
    refine ⟨105805536434438901192314075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70537024289625934128209383 105805536434438901192314075)
    ·
      refine ⟨158708304651658351788471113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105805536434438901192314075 158708304651658351788471113)
      ·
        refine ⟨119031228488743763841353335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158708304651658351788471113 119031228488743763841353335)
        ·
          refine ⟨178546842733115645762030003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119031228488743763841353335 178546842733115645762030003)
          ·
            refine ⟨267820264099673468643045005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178546842733115645762030003 267820264099673468643045005)
            ·
              refine ⟨100432599037377550741141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267820264099673468643045005 100432599037377550741141877)
              ·
                refine ⟨9415556159754145381982051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100432599037377550741141877 9415556159754145381982051)
                ·
                  refine ⟨14123334239631218072973077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415556159754145381982051 14123334239631218072973077)
                  ·
                    refine ⟨662031292482713347170613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14123334239631218072973077 662031292482713347170613)
                    ·
                      rfl

theorem cell23_3867904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_3867904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867904 prefixEnd_3867904 := by exact prefixLift 3867904
  have htrace : WordTrace (prefixWord ++ tailWord_3867904) baseStart_3867904 baseEnd_3867904 := by
    simpa [prefixWord, tailWord_3867904, baseEnd_3867904] using wordTrace_append hprefix tailTrace_3867904
  have hstable : (prefixWord ++ tailWord_3867904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867904).length < 2 ^ (prefixWord ++ tailWord_3867904).sum := by decide
  have hdescent : baseEnd_3867904 < baseStart_3867904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3867908 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_3867908 : Nat := 118140960795 + 3867908 * 2 ^ 59
def prefixEnd_3867908 : Nat := 4983230072969 + 3 ^ 40 * 3867908 * 2
def baseEnd_3867908 : Nat := 662031977123586008620607

theorem tailTrace_3867908 : CollatzResearch.WordTrace tailWord_3867908 prefixEnd_3867908 662031977123586008620607 := by
  unfold tailWord_3867908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70537097235618688469782189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94049462980824917959709585 70537097235618688469782189)
  ·
    refine ⟨26451411463357008176168321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70537097235618688469782189 26451411463357008176168321)
    ·
      refine ⟨19838558597517756132126241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26451411463357008176168321 19838558597517756132126241)
      ·
        refine ⟨14878918948138317099094681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19838558597517756132126241 14878918948138317099094681)
        ·
          refine ⟨11159189211103737824321011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14878918948138317099094681 11159189211103737824321011)
          ·
            refine ⟨16738783816655606736481517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159189211103737824321011 16738783816655606736481517)
            ·
              refine ⟨6277043931245852526180569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16738783816655606736481517 6277043931245852526180569)
              ·
                refine ⟨4707782948434389394635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277043931245852526180569 4707782948434389394635427)
                ·
                  refine ⟨7061674422651584091953141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707782948434389394635427 7061674422651584091953141)
                  ·
                    refine ⟨662031977123586008620607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7061674422651584091953141 662031977123586008620607)
                    ·
                      rfl

theorem cell23_3867908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_3867908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3867908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3867908 prefixEnd_3867908 := by exact prefixLift 3867908
  have htrace : WordTrace (prefixWord ++ tailWord_3867908) baseStart_3867908 baseEnd_3867908 := by
    simpa [prefixWord, tailWord_3867908, baseEnd_3867908] using wordTrace_append hprefix tailTrace_3867908
  have hstable : (prefixWord ++ tailWord_3867908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3867908).length < 2 ^ (prefixWord ++ tailWord_3867908).sum := by decide
  have hdescent : baseEnd_3867908 < baseStart_3867908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3867908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868012 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_3868012 : Nat := 118140960795 + 3868012 * 2 ^ 59
def prefixEnd_3868012 : Nat := 4983230072969 + 3 ^ 40 * 3868012 * 2
def baseEnd_3868012 : Nat := 1986149333358825618961343

theorem tailTrace_3868012 : CollatzResearch.WordTrace tailWord_3868012 prefixEnd_3868012 1986149333358825618961343 := by
  unfold tailWord_3868012
  simp only [CollatzResearch.WordTrace]
  refine ⟨70538993831430301350675145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94051991775240401800900193 70538993831430301350675145)
  ·
    refine ⟨52904245373572726013006359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70538993831430301350675145 52904245373572726013006359)
    ·
      refine ⟨79356368060359089019509539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52904245373572726013006359 79356368060359089019509539)
      ·
        refine ⟨119034552090538633529264309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79356368060359089019509539 119034552090538633529264309)
        ·
          refine ⟨11159489258487996893368529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119034552090538633529264309 11159489258487996893368529)
          ·
            refine ⟨8369616943865997670026397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11159489258487996893368529 8369616943865997670026397)
            ·
              refine ⟨3138606353949749126259899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8369616943865997670026397 3138606353949749126259899)
              ·
                refine ⟨4707909530924623689389849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138606353949749126259899 4707909530924623689389849)
                ·
                  refine ⟨3530932148193467767042387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707909530924623689389849 3530932148193467767042387)
                  ·
                    refine ⟨5296398222290201650563581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530932148193467767042387 5296398222290201650563581)
                    ·
                      refine ⟨1986149333358825618961343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296398222290201650563581 1986149333358825618961343)
                      ·
                        rfl

theorem cell23_3868012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_3868012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868012 prefixEnd_3868012 := by exact prefixLift 3868012
  have htrace : WordTrace (prefixWord ++ tailWord_3868012) baseStart_3868012 baseEnd_3868012 := by
    simpa [prefixWord, tailWord_3868012, baseEnd_3868012] using wordTrace_append hprefix tailTrace_3868012
  have hstable : (prefixWord ++ tailWord_3868012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868012).length < 2 ^ (prefixWord ++ tailWord_3868012).sum := by decide
  have hdescent : baseEnd_3868012 < baseStart_3868012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868030 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3868030 : Nat := 118140960795 + 3868030 * 2 ^ 59
def prefixEnd_3868030 : Nat := 4983230072969 + 3 ^ 40 * 3868030 * 2
def baseEnd_3868030 : Nat := 1986158576010606548536261

theorem tailTrace_3868030 : CollatzResearch.WordTrace tailWord_3868030 prefixEnd_3868030 1986158576010606548536261 := by
  unfold tailWord_3868030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17634830522099423971938193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94052429451196927850337029 17634830522099423971938193)
  ·
    refine ⟨13226122891574567978953645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17634830522099423971938193 13226122891574567978953645)
    ·
      refine ⟨4959796084340462992107617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13226122891574567978953645 4959796084340462992107617)
      ·
        refine ⟨3719847063255347244080713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4959796084340462992107617 3719847063255347244080713)
        ·
          refine ⟨2789885297441510433060535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3719847063255347244080713 2789885297441510433060535)
          ·
            refine ⟨4184827946162265649590803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789885297441510433060535 4184827946162265649590803)
            ·
              refine ⟨6277241919243398474386205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184827946162265649590803 6277241919243398474386205)
              ·
                refine ⟨2353965719716274427894827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6277241919243398474386205 2353965719716274427894827)
                ·
                  refine ⟨3530948579574411641842241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353965719716274427894827 3530948579574411641842241)
                  ·
                    refine ⟨2648211434680808731381681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530948579574411641842241 2648211434680808731381681)
                    ·
                      refine ⟨1986158576010606548536261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648211434680808731381681 1986158576010606548536261)
                      ·
                        rfl

theorem cell23_3868030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3868030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868030 prefixEnd_3868030 := by exact prefixLift 3868030
  have htrace : WordTrace (prefixWord ++ tailWord_3868030) baseStart_3868030 baseEnd_3868030 := by
    simpa [prefixWord, tailWord_3868030, baseEnd_3868030] using wordTrace_append hprefix tailTrace_3868030
  have hstable : (prefixWord ++ tailWord_3868030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868030).length < 2 ^ (prefixWord ++ tailWord_3868030).sum := by decide
  have hdescent : baseEnd_3868030 < baseStart_3868030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868035 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 4, 2, 2]
def baseStart_3868035 : Nat := 118140960795 + 3868035 * 2 ^ 59
def prefixEnd_3868035 : Nat := 4983230072969 + 3 ^ 40 * 3868035 * 2
def baseEnd_3868035 : Nat := 1986161143413879028973737

theorem tailTrace_3868035 : CollatzResearch.WordTrace tailWord_3868035 prefixEnd_3868035 1986161143413879028973737 := by
  unfold tailWord_3868035
  simp only [CollatzResearch.WordTrace]
  refine ⟨141078826541777277629437559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94052551027851518419625039 141078826541777277629437559)
  ·
    refine ⟨211618239812665916444156339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141078826541777277629437559 211618239812665916444156339)
    ·
      refine ⟨317427359718998874666234509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211618239812665916444156339 317427359718998874666234509)
      ·
        refine ⟨119035259894624577999837941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317427359718998874666234509 119035259894624577999837941)
        ·
          refine ⟨11159555615121054187484807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119035259894624577999837941 11159555615121054187484807)
          ·
            refine ⟨16739333422681581281227211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159555615121054187484807 16739333422681581281227211)
            ·
              refine ⟨25109000134022371921840817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16739333422681581281227211 25109000134022371921840817)
              ·
                refine ⟨18831750100516778941380613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25109000134022371921840817 18831750100516778941380613)
                ·
                  refine ⟨3530953143846896051508865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18831750100516778941380613 3530953143846896051508865)
                  ·
                    refine ⟨2648214857885172038631649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530953143846896051508865 2648214857885172038631649)
                    ·
                      refine ⟨1986161143413879028973737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648214857885172038631649 1986161143413879028973737)
                      ·
                        rfl

theorem cell23_3868035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_3868035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868035 prefixEnd_3868035 := by exact prefixLift 3868035
  have htrace : WordTrace (prefixWord ++ tailWord_3868035) baseStart_3868035 baseEnd_3868035 := by
    simpa [prefixWord, tailWord_3868035, baseEnd_3868035] using wordTrace_append hprefix tailTrace_3868035
  have hstable : (prefixWord ++ tailWord_3868035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868035).length < 2 ^ (prefixWord ++ tailWord_3868035).sum := by decide
  have hdescent : baseEnd_3868035 < baseStart_3868035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868052 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3868052 : Nat := 118140960795 + 3868052 * 2 ^ 59
def prefixEnd_3868052 : Nat := 4983230072969 + 3 ^ 40 * 3868052 * 2
def baseEnd_3868052 : Nat := 1986169872585005462461159

theorem tailTrace_3868052 : CollatzResearch.WordTrace tailWord_3868052 prefixEnd_3868052 1986169872585005462461159 := by
  unfold tailWord_3868052
  simp only [CollatzResearch.WordTrace]
  refine ⟨70539723291357844766403205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94052964388477126355204273 70539723291357844766403205)
  ·
    refine ⟨13226198117129595893700601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70539723291357844766403205 13226198117129595893700601)
    ·
      refine ⟨9919648587847196920275451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13226198117129595893700601 9919648587847196920275451)
      ·
        refine ⟨14879472881770795380413177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919648587847196920275451 14879472881770795380413177)
        ·
          refine ⟨11159604661328096535309883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879472881770795380413177 11159604661328096535309883)
          ·
            refine ⟨16739406991992144802964825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159604661328096535309883 16739406991992144802964825)
            ·
              refine ⟨12554555243994108602223619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16739406991992144802964825 12554555243994108602223619)
              ·
                refine ⟨18831832865991162903335429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554555243994108602223619 18831832865991162903335429)
                ·
                  refine ⟨3530968662373343044375393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18831832865991162903335429 3530968662373343044375393)
                  ·
                    refine ⟨2648226496780007283281545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530968662373343044375393 2648226496780007283281545)
                    ·
                      refine ⟨1986169872585005462461159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648226496780007283281545 1986169872585005462461159)
                      ·
                        rfl

theorem cell23_3868052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3868052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868052 prefixEnd_3868052 := by exact prefixLift 3868052
  have htrace : WordTrace (prefixWord ++ tailWord_3868052) baseStart_3868052 baseEnd_3868052 := by
    simpa [prefixWord, tailWord_3868052, baseEnd_3868052] using wordTrace_append hprefix tailTrace_3868052
  have hstable : (prefixWord ++ tailWord_3868052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868052).length < 2 ^ (prefixWord ++ tailWord_3868052).sum := by decide
  have hdescent : baseEnd_3868052 < baseStart_3868052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868081 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3868081 : Nat := 118140960795 + 3868081 * 2 ^ 59
def prefixEnd_3868081 : Nat := 4983230072969 + 3 ^ 40 * 3868081 * 2
def baseEnd_3868081 : Nat := 1986184763523985848998525

theorem tailTrace_3868081 : CollatzResearch.WordTrace tailWord_3868081 prefixEnd_3868081 1986184763523985848998525 := by
  unfold tailWord_3868081
  simp only [CollatzResearch.WordTrace]
  refine ⟨141080504299610627485612097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94053669533073751657074731 141080504299610627485612097)
  ·
    refine ⟨105810378224707970614209073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141080504299610627485612097 105810378224707970614209073)
    ·
      refine ⟨79357783668530977960656805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105810378224707970614209073 79357783668530977960656805)
      ·
        refine ⟨14879584437849558367623151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79357783668530977960656805 14879584437849558367623151)
        ·
          refine ⟨22319376656774337551434727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879584437849558367623151 22319376656774337551434727)
          ·
            refine ⟨33479064985161506327152091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22319376656774337551434727 33479064985161506327152091)
            ·
              refine ⟨50218597477742259490728137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33479064985161506327152091 50218597477742259490728137)
              ·
                refine ⟨37663948108306694618046103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50218597477742259490728137 37663948108306694618046103)
                ·
                  refine ⟨56495922162460041927069155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37663948108306694618046103 56495922162460041927069155)
                  ·
                    refine ⟨84743883243690062890603733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56495922162460041927069155 84743883243690062890603733)
                    ·
                      refine ⟨1986184763523985848998525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84743883243690062890603733 1986184763523985848998525)
                      ·
                        rfl

theorem cell23_3868081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3868081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868081 prefixEnd_3868081 := by exact prefixLift 3868081
  have htrace : WordTrace (prefixWord ++ tailWord_3868081) baseStart_3868081 baseEnd_3868081 := by
    simpa [prefixWord, tailWord_3868081, baseEnd_3868081] using wordTrace_append hprefix tailTrace_3868081
  have hstable : (prefixWord ++ tailWord_3868081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868081).length < 2 ^ (prefixWord ++ tailWord_3868081).sum := by decide
  have hdescent : baseEnd_3868081 < baseStart_3868081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868125 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3868125 : Nat := 118140960795 + 3868125 * 2 ^ 59
def prefixEnd_3868125 : Nat := 4983230072969 + 3 ^ 40 * 3868125 * 2
def baseEnd_3868125 : Nat := 1986207356672783676848323

theorem tailTrace_3868125 : CollatzResearch.WordTrace tailWord_3868125 prefixEnd_3868125 1986207356672783676848323 := by
  unfold tailWord_3868125
  simp only [CollatzResearch.WordTrace]
  refine ⟨141082109111451223000213829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94054739407634148666809219 141082109111451223000213829)
  ·
    refine ⟨26452895458397104312540093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141082109111451223000213829 26452895458397104312540093)
    ·
      refine ⟨9919835796898914117202535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26452895458397104312540093 9919835796898914117202535)
      ·
        refine ⟨14879753695348371175803803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919835796898914117202535 14879753695348371175803803)
        ·
          refine ⟨22319630543022556763705705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879753695348371175803803 22319630543022556763705705)
          ·
            refine ⟨16739722907266917572779279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22319630543022556763705705 16739722907266917572779279)
            ·
              refine ⟨25109584360900376359168919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16739722907266917572779279 25109584360900376359168919)
              ·
                refine ⟨37664376541350564538753379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25109584360900376359168919 37664376541350564538753379)
                ·
                  refine ⟨56496564812025846808130069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37664376541350564538753379 56496564812025846808130069)
                  ·
                    refine ⟨2648276475563711569131097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56496564812025846808130069 2648276475563711569131097)
                    ·
                      refine ⟨1986207356672783676848323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648276475563711569131097 1986207356672783676848323)
                      ·
                        rfl

theorem cell23_3868125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3868125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868125 prefixEnd_3868125 := by exact prefixLift 3868125
  have htrace : WordTrace (prefixWord ++ tailWord_3868125) baseStart_3868125 baseEnd_3868125 := by
    simpa [prefixWord, tailWord_3868125, baseEnd_3868125] using wordTrace_append hprefix tailTrace_3868125
  have hstable : (prefixWord ++ tailWord_3868125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868125).length < 2 ^ (prefixWord ++ tailWord_3868125).sum := by decide
  have hdescent : baseEnd_3868125 < baseStart_3868125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868135 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3868135 : Nat := 118140960795 + 3868135 * 2 ^ 59
def prefixEnd_3868135 : Nat := 4983230072969 + 3 ^ 40 * 3868135 * 2
def baseEnd_3868135 : Nat := 662070830493109545907759

theorem tailTrace_3868135 : CollatzResearch.WordTrace tailWord_3868135 prefixEnd_3868135 662070830493109545907759 := by
  unfold tailWord_3868135
  simp only [CollatzResearch.WordTrace]
  refine ⟨141082473841414994708077859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94054982560943329805385239 141082473841414994708077859)
  ·
    refine ⟨211623710762122492062116789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141082473841414994708077859 211623710762122492062116789)
    ·
      refine ⟨19839722883948983630823449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211623710762122492062116789 19839722883948983630823449)
      ·
        refine ⟨14879792162961737723117587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19839722883948983630823449 14879792162961737723117587)
        ·
          refine ⟨22319688244442606584676381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879792162961737723117587 22319688244442606584676381)
          ·
            refine ⟨8369883091665977469253643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22319688244442606584676381 8369883091665977469253643)
            ·
              refine ⟨12554824637498966203880465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369883091665977469253643 12554824637498966203880465)
              ·
                refine ⟨9416118478124224652910349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12554824637498966203880465 9416118478124224652910349)
                ·
                  refine ⟨3531044429296584244841381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9416118478124224652910349 3531044429296584244841381)
                  ·
                    refine ⟨662070830493109545907759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531044429296584244841381 662070830493109545907759)
                    ·
                      rfl

theorem cell23_3868135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3868135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868135 prefixEnd_3868135 := by exact prefixLift 3868135
  have htrace : WordTrace (prefixWord ++ tailWord_3868135) baseStart_3868135 baseEnd_3868135 := by
    simpa [prefixWord, tailWord_3868135, baseEnd_3868135] using wordTrace_append hprefix tailTrace_3868135
  have hstable : (prefixWord ++ tailWord_3868135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868135).length < 2 ^ (prefixWord ++ tailWord_3868135).sum := by decide
  have hdescent : baseEnd_3868135 < baseStart_3868135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868145 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_3868145 : Nat := 118140960795 + 3868145 * 2 ^ 59
def prefixEnd_3868145 : Nat := 4983230072969 + 3 ^ 40 * 3868145 * 2
def baseEnd_3868145 : Nat := 1986217626285873598598231

theorem tailTrace_3868145 : CollatzResearch.WordTrace tailWord_3868145 prefixEnd_3868145 1986217626285873598598231 := by
  unfold tailWord_3868145
  simp only [CollatzResearch.WordTrace]
  refine ⟨141082838571378766415941889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94055225714252510943961259 141082838571378766415941889)
  ·
    refine ⟨105812128928534074811956417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141082838571378766415941889 105812128928534074811956417)
    ·
      refine ⟨79359096696400556108967313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105812128928534074811956417 79359096696400556108967313)
      ·
        refine ⟨59519322522300417081725485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79359096696400556108967313 59519322522300417081725485)
        ·
          refine ⟨22319745945862656405647057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59519322522300417081725485 22319745945862656405647057)
          ·
            refine ⟨16739809459396992304235293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22319745945862656405647057 16739809459396992304235293)
            ·
              refine ⟨6277428547273872114088235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16739809459396992304235293 6277428547273872114088235)
              ·
                refine ⟨9416142820910808171132353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277428547273872114088235 9416142820910808171132353)
                ·
                  refine ⟨7062107115683106128349265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416142820910808171132353 7062107115683106128349265)
                  ·
                    refine ⟨5296580336762329596261949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062107115683106128349265 5296580336762329596261949)
                    ·
                      refine ⟨1986217626285873598598231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296580336762329596261949 1986217626285873598598231)
                      ·
                        rfl

theorem cell23_3868145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_3868145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868145 prefixEnd_3868145 := by exact prefixLift 3868145
  have htrace : WordTrace (prefixWord ++ tailWord_3868145) baseStart_3868145 baseEnd_3868145 := by
    simpa [prefixWord, tailWord_3868145, baseEnd_3868145] using wordTrace_append hprefix tailTrace_3868145
  have hstable : (prefixWord ++ tailWord_3868145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868145).length < 2 ^ (prefixWord ++ tailWord_3868145).sum := by decide
  have hdescent : baseEnd_3868145 < baseStart_3868145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868152 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 1, 4]
def baseStart_3868152 : Nat := 118140960795 + 3868152 * 2 ^ 59
def prefixEnd_3868152 : Nat := 4983230072969 + 3 ^ 40 * 3868152 * 2
def baseEnd_3868152 : Nat := 662073740216818357070233

theorem tailTrace_3868152 : CollatzResearch.WordTrace tailWord_3868152 prefixEnd_3868152 662073740216818357070233 := by
  unfold tailWord_3868152
  simp only [CollatzResearch.WordTrace]
  refine ⟨70541546941176703305723355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94055395921568937740964473 70541546941176703305723355)
  ·
    refine ⟨105812320411765054958585033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70541546941176703305723355 105812320411765054958585033)
    ·
      refine ⟨79359240308823791218938775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105812320411765054958585033 79359240308823791218938775)
      ·
        refine ⟨119038860463235686828408163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79359240308823791218938775 119038860463235686828408163)
        ·
          refine ⟨178558290694853530242612245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119038860463235686828408163 178558290694853530242612245)
          ·
            refine ⟨8369919876321259230122449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178558290694853530242612245 8369919876321259230122449)
            ·
              refine ⟨6277439907240944422591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8369919876321259230122449 6277439907240944422591837)
              ·
                refine ⟨2354039965215354158471939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6277439907240944422591837 2354039965215354158471939)
                ·
                  refine ⟨3531059947823031237707909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354039965215354158471939 3531059947823031237707909)
                  ·
                    refine ⟨662073740216818357070233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531059947823031237707909 662073740216818357070233)
                    ·
                      rfl

theorem cell23_3868152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_3868152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868152 prefixEnd_3868152 := by exact prefixLift 3868152
  have htrace : WordTrace (prefixWord ++ tailWord_3868152) baseStart_3868152 baseEnd_3868152 := by
    simpa [prefixWord, tailWord_3868152, baseEnd_3868152] using wordTrace_append hprefix tailTrace_3868152
  have hstable : (prefixWord ++ tailWord_3868152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868152).length < 2 ^ (prefixWord ++ tailWord_3868152).sum := by decide
  have hdescent : baseEnd_3868152 < baseStart_3868152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868192 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3868192 : Nat := 118140960795 + 3868192 * 2 ^ 59
def prefixEnd_3868192 : Nat := 4983230072969 + 3 ^ 40 * 3868192 * 2
def baseEnd_3868192 : Nat := 1986241759876634914710515

theorem tailTrace_3868192 : CollatzResearch.WordTrace tailWord_3868192 prefixEnd_3868192 1986241759876634914710515 := by
  unfold tailWord_3868192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70542276401104246721451415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94056368534805662295268553 70542276401104246721451415)
  ·
    refine ⟨105813414601656370082177123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70542276401104246721451415 105813414601656370082177123)
    ·
      refine ⟨158720121902484555123265685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105813414601656370082177123 158720121902484555123265685)
      ·
        refine ⟨7440005714178963521403079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158720121902484555123265685 7440005714178963521403079)
        ·
          refine ⟨11160008571268445282104619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440005714178963521403079 11160008571268445282104619)
          ·
            refine ⟨16740012856902667923156929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160008571268445282104619 16740012856902667923156929)
            ·
              refine ⟨12555009642677000942367697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16740012856902667923156929 12555009642677000942367697)
              ·
                refine ⟨9416257232007750706775773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12555009642677000942367697 9416257232007750706775773)
                ·
                  refine ⟨3531096462002906515040915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9416257232007750706775773 3531096462002906515040915)
                  ·
                    refine ⟨5296644693004359772561373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531096462002906515040915 5296644693004359772561373)
                    ·
                      refine ⟨1986241759876634914710515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296644693004359772561373 1986241759876634914710515)
                      ·
                        rfl

theorem cell23_3868192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3868192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868192 prefixEnd_3868192 := by exact prefixLift 3868192
  have htrace : WordTrace (prefixWord ++ tailWord_3868192) baseStart_3868192 baseEnd_3868192 := by
    simpa [prefixWord, tailWord_3868192, baseEnd_3868192] using wordTrace_append hprefix tailTrace_3868192
  have hstable : (prefixWord ++ tailWord_3868192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868192).length < 2 ^ (prefixWord ++ tailWord_3868192).sum := by decide
  have hdescent : baseEnd_3868192 < baseStart_3868192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868202 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3868202 : Nat := 118140960795 + 3868202 * 2 ^ 59
def prefixEnd_3868202 : Nat := 4983230072969 + 3 ^ 40 * 3868202 * 2
def baseEnd_3868202 : Nat := 1986246894683179875585469

theorem tailTrace_3868202 : CollatzResearch.WordTrace tailWord_3868202 prefixEnd_3868202 1986246894683179875585469 := by
  unfold tailWord_3868202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271229383043066287691715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94056611688114843433844573 35271229383043066287691715)
  ·
    refine ⟨52906844074564599431537573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35271229383043066287691715 52906844074564599431537573)
    ·
      refine ⟨9920033263980862393413295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52906844074564599431537573 9920033263980862393413295)
      ·
        refine ⟨14880049895971293590119943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920033263980862393413295 14880049895971293590119943)
        ·
          refine ⟨22320074843956940385179915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14880049895971293590119943 22320074843956940385179915)
          ·
            refine ⟨33480112265935410577769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22320074843956940385179915 33480112265935410577769873)
            ·
              refine ⟨25110084199451557933327405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33480112265935410577769873 25110084199451557933327405)
              ·
                refine ⟨9416281574794334224997777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25110084199451557933327405 9416281574794334224997777)
                ·
                  refine ⟨7062211181095750668748333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416281574794334224997777 7062211181095750668748333)
                  ·
                    refine ⟨2648329192910906500780625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7062211181095750668748333 2648329192910906500780625)
                    ·
                      refine ⟨1986246894683179875585469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648329192910906500780625 1986246894683179875585469)
                      ·
                        rfl

theorem cell23_3868202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3868202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868202 prefixEnd_3868202 := by exact prefixLift 3868202
  have htrace : WordTrace (prefixWord ++ tailWord_3868202) baseStart_3868202 baseEnd_3868202 := by
    simpa [prefixWord, tailWord_3868202, baseEnd_3868202] using wordTrace_append hprefix tailTrace_3868202
  have hstable : (prefixWord ++ tailWord_3868202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868202).length < 2 ^ (prefixWord ++ tailWord_3868202).sum := by decide
  have hdescent : baseEnd_3868202 < baseStart_3868202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868215 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_3868215 : Nat := 118140960795 + 3868215 * 2 ^ 59
def prefixEnd_3868215 : Nat := 4983230072969 + 3 ^ 40 * 3868215 * 2
def baseEnd_3868215 : Nat := 1986253569931688324722909

theorem tailTrace_3868215 : CollatzResearch.WordTrace tailWord_3868215 prefixEnd_3868215 1986253569931688324722909 := by
  unfold tailWord_3868215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141085391681125168370990099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94056927787416778913993399 141085391681125168370990099)
  ·
    refine ⟨211628087521687752556485149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141085391681125168370990099 211628087521687752556485149)
    ·
      refine ⟨79360532820632907208681931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211628087521687752556485149 79360532820632907208681931)
      ·
        refine ⟨119040799230949360813022897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79360532820632907208681931 119040799230949360813022897)
        ·
          refine ⟨89280599423212020609767173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119040799230949360813022897 89280599423212020609767173)
          ·
            refine ⟨16740112391852253864331345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89280599423212020609767173 16740112391852253864331345)
            ·
              refine ⟨12555084293889190398248509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16740112391852253864331345 12555084293889190398248509)
              ·
                refine ⟨4708156610208446399343191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12555084293889190398248509 4708156610208446399343191)
                ·
                  refine ⟨7062234915312669599014787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708156610208446399343191 7062234915312669599014787)
                  ·
                    refine ⟨10593352372969004398522181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7062234915312669599014787 10593352372969004398522181)
                    ·
                      refine ⟨1986253569931688324722909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10593352372969004398522181 1986253569931688324722909)
                      ·
                        rfl

theorem cell23_3868215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_3868215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868215 prefixEnd_3868215 := by exact prefixLift 3868215
  have htrace : WordTrace (prefixWord ++ tailWord_3868215) baseStart_3868215 baseEnd_3868215 := by
    simpa [prefixWord, tailWord_3868215, baseEnd_3868215] using wordTrace_append hprefix tailTrace_3868215
  have hstable : (prefixWord ++ tailWord_3868215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868215).length < 2 ^ (prefixWord ++ tailWord_3868215).sum := by decide
  have hdescent : baseEnd_3868215 < baseStart_3868215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868225 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3868225 : Nat := 118140960795 + 3868225 * 2 ^ 59
def prefixEnd_3868225 : Nat := 4983230072969 + 3 ^ 40 * 3868225 * 2
def baseEnd_3868225 : Nat := 662086234912744428532621

theorem tailTrace_3868225 : CollatzResearch.WordTrace tailWord_3868225 prefixEnd_3868225 662086234912744428532621 := by
  unfold tailWord_3868225
  simp only [CollatzResearch.WordTrace]
  refine ⟨141085756411088940078854129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94057170940725960052569419 141085756411088940078854129)
  ·
    refine ⟨105814317308316705059140597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141085756411088940078854129 105814317308316705059140597)
    ·
      refine ⟨9920092247654691099294431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105814317308316705059140597 9920092247654691099294431)
      ·
        refine ⟨14880138371482036648941647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920092247654691099294431 14880138371482036648941647)
        ·
          refine ⟨22320207557223054973412471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14880138371482036648941647 22320207557223054973412471)
          ·
            refine ⟨33480311335834582460118707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22320207557223054973412471 33480311335834582460118707)
            ·
              refine ⟨50220467003751873690178061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33480311335834582460118707 50220467003751873690178061)
              ·
                refine ⟨18832675126406952633816773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50220467003751873690178061 18832675126406952633816773)
                ·
                  refine ⟨3531126586201303618840645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18832675126406952633816773 3531126586201303618840645)
                  ·
                    refine ⟨662086234912744428532621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531126586201303618840645 662086234912744428532621)
                    ·
                      rfl

theorem cell23_3868225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3868225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868225 prefixEnd_3868225 := by exact prefixLift 3868225
  have htrace : WordTrace (prefixWord ++ tailWord_3868225) baseStart_3868225 baseEnd_3868225 := by
    simpa [prefixWord, tailWord_3868225, baseEnd_3868225] using wordTrace_append hprefix tailTrace_3868225
  have hstable : (prefixWord ++ tailWord_3868225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868225).length < 2 ^ (prefixWord ++ tailWord_3868225).sum := by decide
  have hdescent : baseEnd_3868225 < baseStart_3868225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868242 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3868242 : Nat := 118140960795 + 3868242 * 2 ^ 59
def prefixEnd_3868242 : Nat := 4983230072969 + 3 ^ 40 * 3868242 * 2
def baseEnd_3868242 : Nat := 662089144636453239695095

theorem tailTrace_3868242 : CollatzResearch.WordTrace tailWord_3868242 prefixEnd_3868242 662089144636453239695095 := by
  unfold tailWord_3868242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271594113006837995555745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94057584301351567988148653 35271594113006837995555745)
  ·
    refine ⟨26453695584755128496666809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35271594113006837995555745 26453695584755128496666809)
    ·
      refine ⟨19840271688566346372500107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26453695584755128496666809 19840271688566346372500107)
      ·
        refine ⟨29760407532849519558750161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19840271688566346372500107 29760407532849519558750161)
        ·
          refine ⟨22320305649637139669062621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29760407532849519558750161 22320305649637139669062621)
          ·
            refine ⟨8370114618613927375898483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22320305649637139669062621 8370114618613927375898483)
            ·
              refine ⟨12555171927920891063847725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370114618613927375898483 12555171927920891063847725)
              ·
                refine ⟨4708189472970334148942897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12555171927920891063847725 4708189472970334148942897)
                ·
                  refine ⟨3531142104727750611707173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708189472970334148942897 3531142104727750611707173)
                  ·
                    refine ⟨662089144636453239695095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531142104727750611707173 662089144636453239695095)
                    ·
                      rfl

theorem cell23_3868242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3868242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868242 prefixEnd_3868242 := by exact prefixLift 3868242
  have htrace : WordTrace (prefixWord ++ tailWord_3868242) baseStart_3868242 baseEnd_3868242 := by
    simpa [prefixWord, tailWord_3868242, baseEnd_3868242] using wordTrace_append hprefix tailTrace_3868242
  have hstable : (prefixWord ++ tailWord_3868242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868242).length < 2 ^ (prefixWord ++ tailWord_3868242).sum := by decide
  have hdescent : baseEnd_3868242 < baseStart_3868242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868252 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3868252 : Nat := 118140960795 + 3868252 * 2 ^ 59
def prefixEnd_3868252 : Nat := 4983230072969 + 3 ^ 40 * 3868252 * 2
def baseEnd_3868252 : Nat := 1986272568715904679960239

theorem tailTrace_3868252 : CollatzResearch.WordTrace tailWord_3868252 prefixEnd_3868252 1986272568715904679960239 := by
  unfold tailWord_3868252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70543370590995561845043505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94057827454660749126724673 70543370590995561845043505)
  ·
    refine ⟨52907527943246671383782629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70543370590995561845043505 52907527943246671383782629)
    ·
      refine ⟨9920161489358750884459243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52907527943246671383782629 9920161489358750884459243)
      ·
        refine ⟨14880242234038126326688865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920161489358750884459243 14880242234038126326688865)
        ·
          refine ⟨11160181675528594745016649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14880242234038126326688865 11160181675528594745016649)
          ·
            refine ⟨8370136256646446058762487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11160181675528594745016649 8370136256646446058762487)
            ·
              refine ⟨12555204384969669088143731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370136256646446058762487 12555204384969669088143731)
              ·
                refine ⟨18832806577454503632215597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555204384969669088143731 18832806577454503632215597)
                ·
                  refine ⟨7062302466545438862080849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18832806577454503632215597 7062302466545438862080849)
                  ·
                    refine ⟨5296726849909079146560637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062302466545438862080849 5296726849909079146560637)
                    ·
                      refine ⟨1986272568715904679960239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296726849909079146560637 1986272568715904679960239)
                      ·
                        rfl

theorem cell23_3868252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3868252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868252 prefixEnd_3868252 := by exact prefixLift 3868252
  have htrace : WordTrace (prefixWord ++ tailWord_3868252) baseStart_3868252 baseEnd_3868252 := by
    simpa [prefixWord, tailWord_3868252, baseEnd_3868252] using wordTrace_append hprefix tailTrace_3868252
  have hstable : (prefixWord ++ tailWord_3868252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868252).length < 2 ^ (prefixWord ++ tailWord_3868252).sum := by decide
  have hdescent : baseEnd_3868252 < baseStart_3868252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868265 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_3868265 : Nat := 118140960795 + 3868265 * 2 ^ 59
def prefixEnd_3868265 : Nat := 4983230072969 + 3 ^ 40 * 3868265 * 2
def baseEnd_3868265 : Nat := 1986279243964413129097679

theorem tailTrace_3868265 : CollatzResearch.WordTrace tailWord_3868265 prefixEnd_3868265 1986279243964413129097679 := by
  unfold tailWord_3868265
  simp only [CollatzResearch.WordTrace]
  refine ⟨141087215330944026910310249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94058143553962684606873499 141087215330944026910310249)
  ·
    refine ⟨105815411498208020182732687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141087215330944026910310249 105815411498208020182732687)
    ·
      refine ⟨158723117247312030274099031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105815411498208020182732687 158723117247312030274099031)
      ·
        refine ⟨238084675870968045411148547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158723117247312030274099031 238084675870968045411148547)
        ·
          refine ⟨357127013806452068116722821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238084675870968045411148547 357127013806452068116722821)
          ·
            refine ⟨66961315088709762771885529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357127013806452068116722821 66961315088709762771885529)
            ·
              refine ⟨50220986316532322078914147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66961315088709762771885529 50220986316532322078914147)
              ·
                refine ⟨75331479474798483118371221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50220986316532322078914147 75331479474798483118371221)
                ·
                  refine ⟨3531163100381178896173651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75331479474798483118371221 3531163100381178896173651)
                  ·
                    refine ⟨5296744650571768344260477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531163100381178896173651 5296744650571768344260477)
                    ·
                      refine ⟨1986279243964413129097679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296744650571768344260477 1986279243964413129097679)
                      ·
                        rfl

theorem cell23_3868265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_3868265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868265 prefixEnd_3868265 := by exact prefixLift 3868265
  have htrace : WordTrace (prefixWord ++ tailWord_3868265) baseStart_3868265 baseEnd_3868265 := by
    simpa [prefixWord, tailWord_3868265, baseEnd_3868265] using wordTrace_append hprefix tailTrace_3868265
  have hstable : (prefixWord ++ tailWord_3868265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868265).length < 2 ^ (prefixWord ++ tailWord_3868265).sum := by decide
  have hdescent : baseEnd_3868265 < baseStart_3868265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868269 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_3868269 : Nat := 118140960795 + 3868269 * 2 ^ 59
def prefixEnd_3868269 : Nat := 4983230072969 + 3 ^ 40 * 3868269 * 2
def baseEnd_3868269 : Nat := 1986281297887031113447661

theorem tailTrace_3868269 : CollatzResearch.WordTrace tailWord_3868269 prefixEnd_3868269 1986281297887031113447661 := by
  unfold tailWord_3868269
  simp only [CollatzResearch.WordTrace]
  refine ⟨141087361222929535593455861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94058240815286357062303907 141087361222929535593455861)
  ·
    refine ⟨13226940114649643961886487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141087361222929535593455861 13226940114649643961886487)
    ·
      refine ⟨19840410171974465942829731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13226940114649643961886487 19840410171974465942829731)
      ·
        refine ⟨29760615257961698914244597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19840410171974465942829731 29760615257961698914244597)
        ·
          refine ⟨2790057680433909273210431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29760615257961698914244597 2790057680433909273210431)
          ·
            refine ⟨4185086520650863909815647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790057680433909273210431 4185086520650863909815647)
            ·
              refine ⟨6277629780976295864723471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185086520650863909815647 6277629780976295864723471)
              ·
                refine ⟨9416444671464443797085207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277629780976295864723471 9416444671464443797085207)
                ·
                  refine ⟨14124667007196665695627811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9416444671464443797085207 14124667007196665695627811)
                  ·
                    refine ⟨21187000510794998543441717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14124667007196665695627811 21187000510794998543441717)
                    ·
                      refine ⟨1986281297887031113447661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21187000510794998543441717 1986281297887031113447661)
                      ·
                        rfl

theorem cell23_3868269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_3868269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868269 prefixEnd_3868269 := by exact prefixLift 3868269
  have htrace : WordTrace (prefixWord ++ tailWord_3868269) baseStart_3868269 baseEnd_3868269 := by
    simpa [prefixWord, tailWord_3868269, baseEnd_3868269] using wordTrace_append hprefix tailTrace_3868269
  have hstable : (prefixWord ++ tailWord_3868269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868269).length < 2 ^ (prefixWord ++ tailWord_3868269).sum := by decide
  have hdescent : baseEnd_3868269 < baseStart_3868269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868288 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3868288 : Nat := 118140960795 + 3868288 * 2 ^ 59
def prefixEnd_3868288 : Nat := 4983230072969 + 3 ^ 40 * 3868288 * 2
def baseEnd_3868288 : Nat := 1986291054019466539110073

theorem tailTrace_3868288 : CollatzResearch.WordTrace tailWord_3868288 prefixEnd_3868288 1986291054019466539110073 := by
  unfold tailWord_3868288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544027104930350919198759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94058702806573801225598345 70544027104930350919198759)
  ·
    refine ⟨105816040657395526378798139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70544027104930350919198759 105816040657395526378798139)
    ·
      refine ⟨158724060986093289568197209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105816040657395526378798139 158724060986093289568197209)
      ·
        refine ⟨119043045739569967176147907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158724060986093289568197209 119043045739569967176147907)
        ·
          refine ⟨178564568609354950764221861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119043045739569967176147907 178564568609354950764221861)
          ·
            refine ⟨33480856614254053268291599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178564568609354950764221861 33480856614254053268291599)
            ·
              refine ⟨50221284921381079902437399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33480856614254053268291599 50221284921381079902437399)
              ·
                refine ⟨75331927382071619853656099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50221284921381079902437399 75331927382071619853656099)
                ·
                  refine ⟨112997891073107429780484149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75331927382071619853656099 112997891073107429780484149)
                  ·
                    refine ⟨10593552288103821541920389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112997891073107429780484149 10593552288103821541920389)
                    ·
                      refine ⟨1986291054019466539110073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10593552288103821541920389 1986291054019466539110073)
                      ·
                        rfl

theorem cell23_3868288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3868288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868288 prefixEnd_3868288 := by exact prefixLift 3868288
  have htrace : WordTrace (prefixWord ++ tailWord_3868288) baseStart_3868288 baseEnd_3868288 := by
    simpa [prefixWord, tailWord_3868288, baseEnd_3868288] using wordTrace_append hprefix tailTrace_3868288
  have hstable : (prefixWord ++ tailWord_3868288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868288).length < 2 ^ (prefixWord ++ tailWord_3868288).sum := by decide
  have hdescent : baseEnd_3868288 < baseStart_3868288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868368 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_3868368 : Nat := 118140960795 + 3868368 * 2 ^ 59
def prefixEnd_3868368 : Nat := 4983230072969 + 3 ^ 40 * 3868368 * 2
def baseEnd_3868368 : Nat := 1986332132471826226109705

theorem tailTrace_3868368 : CollatzResearch.WordTrace tailWord_3868368 prefixEnd_3868368 1986332132471826226109705 := by
  unfold tailWord_3868368
  simp only [CollatzResearch.WordTrace]
  refine ⟨70545486024785437750654879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94060648033047250334206505 70545486024785437750654879)
  ·
    refine ⟨105818229037178156625982319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70545486024785437750654879 105818229037178156625982319)
    ·
      refine ⟨158727343555767234938973479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105818229037178156625982319 158727343555767234938973479)
      ·
        refine ⟨238091015333650852408460219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158727343555767234938973479 238091015333650852408460219)
        ·
          refine ⟨357136523000476278612690329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238091015333650852408460219 357136523000476278612690329)
          ·
            refine ⟨267852392250357208959517747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357136523000476278612690329 267852392250357208959517747)
            ·
              refine ⟨401778588375535813439276621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267852392250357208959517747 401778588375535813439276621)
              ·
                refine ⟨150666970640825930039728733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401778588375535813439276621 150666970640825930039728733)
                ·
                  refine ⟨56500113990309723764898275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150666970640825930039728733 56500113990309723764898275)
                  ·
                    refine ⟨84750170985464585647347413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56500113990309723764898275 84750170985464585647347413)
                    ·
                      refine ⟨1986332132471826226109705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84750170985464585647347413 1986332132471826226109705)
                      ·
                        rfl

theorem cell23_3868368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_3868368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868368 prefixEnd_3868368 := by exact prefixLift 3868368
  have htrace : WordTrace (prefixWord ++ tailWord_3868368) baseStart_3868368 baseEnd_3868368 := by
    simpa [prefixWord, tailWord_3868368, baseEnd_3868368] using wordTrace_append hprefix tailTrace_3868368
  have hstable : (prefixWord ++ tailWord_3868368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868368).length < 2 ^ (prefixWord ++ tailWord_3868368).sum := by decide
  have hdescent : baseEnd_3868368 < baseStart_3868368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868375 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 2, 5]
def baseStart_3868375 : Nat := 118140960795 + 3868375 * 2 ^ 59
def prefixEnd_3868375 : Nat := 4983230072969 + 3 ^ 40 * 3868375 * 2
def baseEnd_3868375 : Nat := 662111908945469232907391

theorem tailTrace_3868375 : CollatzResearch.WordTrace tailWord_3868375 prefixEnd_3868375 662111908945469232907391 := by
  unfold tailWord_3868375
  simp only [CollatzResearch.WordTrace]
  refine ⟨141091227360545515696814579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94060818240363677131209719 141091227360545515696814579)
  ·
    refine ⟨211636841040818273545221869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141091227360545515696814579 211636841040818273545221869)
    ·
      refine ⟨79363815390306852579458201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211636841040818273545221869 79363815390306852579458201)
      ·
        refine ⟨59522861542730139434593651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79363815390306852579458201 59522861542730139434593651)
        ·
          refine ⟨89284292314095209151890477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59522861542730139434593651 89284292314095209151890477)
          ·
            refine ⟨33481609617785703431958929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89284292314095209151890477 33481609617785703431958929)
            ·
              refine ⟨25111207213339277573969197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33481609617785703431958929 25111207213339277573969197)
              ·
                refine ⟨9416702705002229090238449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25111207213339277573969197 9416702705002229090238449)
                ·
                  refine ⟨7062527028751671817678837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416702705002229090238449 7062527028751671817678837)
                  ·
                    refine ⟨662111908945469232907391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7062527028751671817678837 662111908945469232907391)
                    ·
                      rfl

theorem cell23_3868375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_3868375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868375 prefixEnd_3868375 := by exact prefixLift 3868375
  have htrace : WordTrace (prefixWord ++ tailWord_3868375) baseStart_3868375 baseEnd_3868375 := by
    simpa [prefixWord, tailWord_3868375, baseEnd_3868375] using wordTrace_append hprefix tailTrace_3868375
  have hstable : (prefixWord ++ tailWord_3868375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868375).length < 2 ^ (prefixWord ++ tailWord_3868375).sum := by decide
  have hdescent : baseEnd_3868375 < baseStart_3868375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868392 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3868392 : Nat := 118140960795 + 3868392 * 2 ^ 59
def prefixEnd_3868392 : Nat := 4983230072969 + 3 ^ 40 * 3868392 * 2
def baseEnd_3868392 : Nat := 662114818669178044069865

theorem tailTrace_3868392 : CollatzResearch.WordTrace tailWord_3868392 prefixEnd_3868392 662114818669178044069865 := by
  unfold tailWord_3868392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70545923700741963800091715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94061231600989285066788953 70545923700741963800091715)
  ·
    refine ⟨105818885551112945700137573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70545923700741963800091715 105818885551112945700137573)
    ·
      refine ⟨19841041040833677318775795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105818885551112945700137573 19841041040833677318775795)
      ·
        refine ⟨29761561561250515978163693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841041040833677318775795 29761561561250515978163693)
        ·
          refine ⟨11160585585468943491811385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29761561561250515978163693 11160585585468943491811385)
          ·
            refine ⟨8370439189101707618858539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11160585585468943491811385 8370439189101707618858539)
            ·
              refine ⟨12555658783652561428287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370439189101707618858539 12555658783652561428287809)
              ·
                refine ⟨9416744087739421071215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12555658783652561428287809 9416744087739421071215857)
                ·
                  refine ⟨7062558065804565803411893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416744087739421071215857 7062558065804565803411893)
                  ·
                    refine ⟨662114818669178044069865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7062558065804565803411893 662114818669178044069865)
                    ·
                      rfl

theorem cell23_3868392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3868392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868392 prefixEnd_3868392 := by exact prefixLift 3868392
  have htrace : WordTrace (prefixWord ++ tailWord_3868392) baseStart_3868392 baseEnd_3868392 := by
    simpa [prefixWord, tailWord_3868392, baseEnd_3868392] using wordTrace_append hprefix tailTrace_3868392
  have hstable : (prefixWord ++ tailWord_3868392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868392).length < 2 ^ (prefixWord ++ tailWord_3868392).sum := by decide
  have hdescent : baseEnd_3868392 < baseStart_3868392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868395 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4]
def baseStart_3868395 : Nat := 118140960795 + 3868395 * 2 ^ 59
def prefixEnd_3868395 : Nat := 4983230072969 + 3 ^ 40 * 3868395 * 2
def baseEnd_3868395 : Nat := 1986345996449497620472081

theorem tailTrace_3868395 : CollatzResearch.WordTrace tailWord_3868395 prefixEnd_3868395 1986345996449497620472081 := by
  unfold tailWord_3868395
  simp only [CollatzResearch.WordTrace]
  refine ⟨141091956820473059112542639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94061304546982039408361759 141091956820473059112542639)
  ·
    refine ⟨211637935230709588668813959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141091956820473059112542639 211637935230709588668813959)
    ·
      refine ⟨317456902846064383003220939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211637935230709588668813959 317456902846064383003220939)
      ·
        refine ⟨476185354269096574504831409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317456902846064383003220939 476185354269096574504831409)
        ·
          refine ⟨357139015701822430878623557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476185354269096574504831409 357139015701822430878623557)
          ·
            refine ⟨66963565444091705789741917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357139015701822430878623557 66963565444091705789741917)
            ·
              refine ⟨25111337041534389671153219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66963565444091705789741917 25111337041534389671153219)
              ·
                refine ⟨37667005562301584506729829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25111337041534389671153219 37667005562301584506729829)
                ·
                  refine ⟨7062563542931547095011843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37667005562301584506729829 7062563542931547095011843)
                  ·
                    refine ⟨10593845314397320642517765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7062563542931547095011843 10593845314397320642517765)
                    ·
                      refine ⟨1986345996449497620472081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10593845314397320642517765 1986345996449497620472081)
                      ·
                        rfl

theorem cell23_3868395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_3868395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868395 prefixEnd_3868395 := by exact prefixLift 3868395
  have htrace : WordTrace (prefixWord ++ tailWord_3868395) baseStart_3868395 baseEnd_3868395 := by
    simpa [prefixWord, tailWord_3868395, baseEnd_3868395] using wordTrace_append hprefix tailTrace_3868395
  have hstable : (prefixWord ++ tailWord_3868395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868395).length < 2 ^ (prefixWord ++ tailWord_3868395).sum := by decide
  have hdescent : baseEnd_3868395 < baseStart_3868395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868412 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_3868412 : Nat := 118140960795 + 3868412 * 2 ^ 59
def prefixEnd_3868412 : Nat := 4983230072969 + 3 ^ 40 * 3868412 * 2
def baseEnd_3868412 : Nat := 1986354725620624053959503

theorem tailTrace_3868412 : CollatzResearch.WordTrace tailWord_3868412 prefixEnd_3868412 1986354725620624053959503 := by
  unfold tailWord_3868412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70546288430705735507955745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94061717907607647343940993 70546288430705735507955745)
  ·
    refine ⟨52909716323029301630966809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70546288430705735507955745 52909716323029301630966809)
    ·
      refine ⟨39682287242271976223225107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52909716323029301630966809 39682287242271976223225107)
      ·
        refine ⟨59523430863407964334837661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39682287242271976223225107 59523430863407964334837661)
        ·
          refine ⟨22321286573777986625564123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59523430863407964334837661 22321286573777986625564123)
          ·
            refine ⟨33481929860666979938346185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321286573777986625564123 33481929860666979938346185)
            ·
              refine ⟨25111447395500234953759639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33481929860666979938346185 25111447395500234953759639)
              ·
                refine ⟨37667171093250352430639459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25111447395500234953759639 37667171093250352430639459)
                ·
                  refine ⟨56500756639875528645959189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37667171093250352430639459 56500756639875528645959189)
                  ·
                    refine ⟨2648472967494165405279337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56500756639875528645959189 2648472967494165405279337)
                    ·
                      refine ⟨1986354725620624053959503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648472967494165405279337 1986354725620624053959503)
                      ·
                        rfl

theorem cell23_3868412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_3868412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868412 prefixEnd_3868412 := by exact prefixLift 3868412
  have htrace : WordTrace (prefixWord ++ tailWord_3868412) baseStart_3868412 baseEnd_3868412 := by
    simpa [prefixWord, tailWord_3868412, baseEnd_3868412] using wordTrace_append hprefix tailTrace_3868412
  have hstable : (prefixWord ++ tailWord_3868412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868412).length < 2 ^ (prefixWord ++ tailWord_3868412).sum := by decide
  have hdescent : baseEnd_3868412 < baseStart_3868412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868415 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_3868415 : Nat := 118140960795 + 3868415 * 2 ^ 59
def prefixEnd_3868415 : Nat := 4983230072969 + 3 ^ 40 * 3868415 * 2
def baseEnd_3868415 : Nat := 1986356266062587542221989

theorem tailTrace_3868415 : CollatzResearch.WordTrace tailWord_3868415 prefixEnd_3868415 1986356266062587542221989 := by
  unfold tailWord_3868415
  simp only [CollatzResearch.WordTrace]
  refine ⟨141092686280400602528270699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94061790853600401685513799 141092686280400602528270699)
  ·
    refine ⟨211639029420600903792406049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141092686280400602528270699 211639029420600903792406049)
    ·
      refine ⟨158729272065450677844304537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211639029420600903792406049 158729272065450677844304537)
      ·
        refine ⟨119046954049088008383228403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158729272065450677844304537 119046954049088008383228403)
        ·
          refine ⟨178570431073632012574842605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119046954049088008383228403 178570431073632012574842605)
          ·
            refine ⟨66963911652612004715565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178570431073632012574842605 66963911652612004715565977)
            ·
              refine ⟨50222933739459003536674483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66963911652612004715565977 50222933739459003536674483)
              ·
                refine ⟨75334400609188505305011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50222933739459003536674483 75334400609188505305011725)
                ·
                  refine ⟨28250400228445689489379397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75334400609188505305011725 28250400228445689489379397)
                  ·
                    refine ⟨5296950042833566779258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28250400228445689489379397 5296950042833566779258637)
                    ·
                      refine ⟨1986356266062587542221989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5296950042833566779258637 1986356266062587542221989)
                      ·
                        rfl

theorem cell23_3868415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_3868415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868415 prefixEnd_3868415 := by exact prefixLift 3868415
  have htrace : WordTrace (prefixWord ++ tailWord_3868415) baseStart_3868415 baseEnd_3868415 := by
    simpa [prefixWord, tailWord_3868415, baseEnd_3868415] using wordTrace_append hprefix tailTrace_3868415
  have hstable : (prefixWord ++ tailWord_3868415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868415).length < 2 ^ (prefixWord ++ tailWord_3868415).sum := by decide
  have hdescent : baseEnd_3868415 < baseStart_3868415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868452 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 6]
def baseStart_3868452 : Nat := 118140960795 + 3868452 * 2 ^ 59
def prefixEnd_3868452 : Nat := 4983230072969 + 3 ^ 40 * 3868452 * 2
def baseEnd_3868452 : Nat := 220708362760755988606591

theorem tailTrace_3868452 : CollatzResearch.WordTrace tailWord_3868452 prefixEnd_3868452 220708362760755988606591 := by
  unfold tailWord_3868452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70547017890633278923683805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94062690520844371898245073 70547017890633278923683805)
  ·
    refine ⟨26455131708987479596381427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70547017890633278923683805 26455131708987479596381427)
    ·
      refine ⟨39682697563481219394572141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26455131708987479596381427 39682697563481219394572141)
      ·
        refine ⟨14881011586305457272964553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39682697563481219394572141 14881011586305457272964553)
        ·
          refine ⟨11160758689729092954723415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881011586305457272964553 11160758689729092954723415)
          ·
            refine ⟨16741138034593639432085123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160758689729092954723415 16741138034593639432085123)
            ·
              refine ⟨25111707051890459148127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16741138034593639432085123 25111707051890459148127685)
              ·
                refine ⟨4708445072229461090273941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25111707051890459148127685 4708445072229461090273941)
                ·
                  refine ⟨220708362760755988606591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4708445072229461090273941 220708362760755988606591)
                  ·
                    rfl

theorem cell23_3868452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_3868452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868452 prefixEnd_3868452 := by exact prefixLift 3868452
  have htrace : WordTrace (prefixWord ++ tailWord_3868452) baseStart_3868452 baseEnd_3868452 := by
    simpa [prefixWord, tailWord_3868452, baseEnd_3868452] using wordTrace_append hprefix tailTrace_3868452
  have hstable : (prefixWord ++ tailWord_3868452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868452).length < 2 ^ (prefixWord ++ tailWord_3868452).sum := by decide
  have hdescent : baseEnd_3868452 < baseStart_3868452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868456 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3868456 : Nat := 118140960795 + 3868456 * 2 ^ 59
def prefixEnd_3868456 : Nat := 4983230072969 + 3 ^ 40 * 3868456 * 2
def baseEnd_3868456 : Nat := 662125772923140627269767

theorem tailTrace_3868456 : CollatzResearch.WordTrace tailWord_3868456 prefixEnd_3868456 662125772923140627269767 := by
  unfold tailWord_3868456
  simp only [CollatzResearch.WordTrace]
  refine ⟨70547090836626033265256611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94062787782168044353675481 70547090836626033265256611)
  ·
    refine ⟨105820636254939049897884917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70547090836626033265256611 105820636254939049897884917)
    ·
      refine ⟨9920684648900535927926711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105820636254939049897884917 9920684648900535927926711)
      ·
        refine ⟨14881026973350803891890067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920684648900535927926711 14881026973350803891890067)
        ·
          refine ⟨22321540460026205837835101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881026973350803891890067 22321540460026205837835101)
          ·
            refine ⟨8370577672509827189188163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22321540460026205837835101 8370577672509827189188163)
            ·
              refine ⟨12555866508764740783782245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370577672509827189188163 12555866508764740783782245)
              ·
                refine ⟨2354224970393388896959171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12555866508764740783782245 2354224970393388896959171)
                ·
                  refine ⟨3531337455590083345438757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354224970393388896959171 3531337455590083345438757)
                  ·
                    refine ⟨662125772923140627269767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531337455590083345438757 662125772923140627269767)
                    ·
                      rfl

theorem cell23_3868456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3868456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868456 prefixEnd_3868456 := by exact prefixLift 3868456
  have htrace : WordTrace (prefixWord ++ tailWord_3868456) baseStart_3868456 baseEnd_3868456 := by
    simpa [prefixWord, tailWord_3868456, baseEnd_3868456] using wordTrace_append hprefix tailTrace_3868456
  have hstable : (prefixWord ++ tailWord_3868456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868456).length < 2 ^ (prefixWord ++ tailWord_3868456).sum := by decide
  have hdescent : baseEnd_3868456 < baseStart_3868456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868555 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 9]
def baseStart_3868555 : Nat := 118140960795 + 3868555 * 2 ^ 59
def prefixEnd_3868555 : Nat := 4983230072969 + 3 ^ 40 * 3868555 * 2
def baseEnd_3868555 : Nat := 662142717784738998157115

theorem tailTrace_3868555 : CollatzResearch.WordTrace tailWord_3868555 prefixEnd_3868555 662142717784738998157115 := by
  unfold tailWord_3868555
  simp only [CollatzResearch.WordTrace]
  refine ⟨141097792499893406438367119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94065194999928937625578079 141097792499893406438367119)
  ·
    refine ⟨211646688749840109657550679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141097792499893406438367119 211646688749840109657550679)
    ·
      refine ⟨317470033124760164486326019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211646688749840109657550679 317470033124760164486326019)
      ·
        refine ⟨476205049687140246729489029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317470033124760164486326019 476205049687140246729489029)
        ·
          refine ⟨89288446816338796261779193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476205049687140246729489029 89288446816338796261779193)
          ·
            refine ⟨66966335112254097196334395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89288446816338796261779193 66966335112254097196334395)
            ·
              refine ⟨100449502668381145794501593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66966335112254097196334395 100449502668381145794501593)
              ·
                refine ⟨75337127001285859345876195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100449502668381145794501593 75337127001285859345876195)
                ·
                  refine ⟨113005690501928789018814293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75337127001285859345876195 113005690501928789018814293)
                  ·
                    refine ⟨662142717784738998157115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113005690501928789018814293 662142717784738998157115)
                    ·
                      rfl

theorem cell23_3868555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_3868555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868555 prefixEnd_3868555 := by exact prefixLift 3868555
  have htrace : WordTrace (prefixWord ++ tailWord_3868555) baseStart_3868555 baseEnd_3868555 := by
    simpa [prefixWord, tailWord_3868555, baseEnd_3868555] using wordTrace_append hprefix tailTrace_3868555
  have hstable : (prefixWord ++ tailWord_3868555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868555).length < 2 ^ (prefixWord ++ tailWord_3868555).sum := by decide
  have hdescent : baseEnd_3868555 < baseStart_3868555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868569 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_3868569 : Nat := 118140960795 + 3868569 * 2 ^ 59
def prefixEnd_3868569 : Nat := 4983230072969 + 3 ^ 40 * 3868569 * 2
def baseEnd_3868569 : Nat := 1986435342083379939696281

theorem tailTrace_3868569 : CollatzResearch.WordTrace tailWord_3868569 prefixEnd_3868569 1986435342083379939696281 := by
  unfold tailWord_3868569
  simp only [CollatzResearch.WordTrace]
  refine ⟨141098303121842686829376761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94065535414561791219584507 141098303121842686829376761)
  ·
    refine ⟨105823727341382015122032571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141098303121842686829376761 105823727341382015122032571)
    ·
      refine ⟨158735591012073022683048857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105823727341382015122032571 158735591012073022683048857)
      ·
        refine ⟨119051693259054767012286643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158735591012073022683048857 119051693259054767012286643)
        ·
          refine ⟨178577539888582150518429965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119051693259054767012286643 178577539888582150518429965)
          ·
            refine ⟨66966577458218306444411237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178577539888582150518429965 66966577458218306444411237)
            ·
              refine ⟨12556233273415932458327107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66966577458218306444411237 12556233273415932458327107)
              ·
                refine ⟨18834349910123898687490661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556233273415932458327107 18834349910123898687490661)
                ·
                  refine ⟨3531440608148231003904499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18834349910123898687490661 3531440608148231003904499)
                  ·
                    refine ⟨5297160912222346505856749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531440608148231003904499 5297160912222346505856749)
                    ·
                      refine ⟨1986435342083379939696281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297160912222346505856749 1986435342083379939696281)
                      ·
                        rfl

theorem cell23_3868569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_3868569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868569 prefixEnd_3868569 := by exact prefixLift 3868569
  have htrace : WordTrace (prefixWord ++ tailWord_3868569) baseStart_3868569 baseEnd_3868569 := by
    simpa [prefixWord, tailWord_3868569, baseEnd_3868569] using wordTrace_append hprefix tailTrace_3868569
  have hstable : (prefixWord ++ tailWord_3868569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868569).length < 2 ^ (prefixWord ++ tailWord_3868569).sum := by decide
  have hdescent : baseEnd_3868569 < baseStart_3868569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868579 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 3, 3, 2]
def baseStart_3868579 : Nat := 118140960795 + 3868579 * 2 ^ 59
def prefixEnd_3868579 : Nat := 4983230072969 + 3 ^ 40 * 3868579 * 2
def baseEnd_3868579 : Nat := 1986440476889924900571235

theorem tailTrace_3868579 : CollatzResearch.WordTrace tailWord_3868579 prefixEnd_3868579 1986440476889924900571235 := by
  unfold tailWord_3868579
  simp only [CollatzResearch.WordTrace]
  refine ⟨141098667851806458537240791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94065778567870972358160527 141098667851806458537240791)
  ·
    refine ⟨211648001777709687805861187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141098667851806458537240791 211648001777709687805861187)
    ·
      refine ⟨317472002666564531708791781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211648001777709687805861187 317472002666564531708791781)
      ·
        refine ⟨59526000499980849695398459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317472002666564531708791781 59526000499980849695398459)
        ·
          refine ⟨89289000749971274543097689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59526000499980849695398459 89289000749971274543097689)
          ·
            refine ⟨66966750562478455907323267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89289000749971274543097689 66966750562478455907323267)
            ·
              refine ⟨100450125843717683860984901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66966750562478455907323267 100450125843717683860984901)
              ·
                refine ⟨18834398595697065723934669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100450125843717683860984901 18834398595697065723934669)
                ·
                  refine ⟨7062899473386399646475501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18834398595697065723934669 7062899473386399646475501)
                  ·
                    refine ⟨2648587302519899867428313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7062899473386399646475501 2648587302519899867428313)
                    ·
                      refine ⟨1986440476889924900571235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648587302519899867428313 1986440476889924900571235)
                      ·
                        rfl

theorem cell23_3868579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_3868579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868579 prefixEnd_3868579 := by exact prefixLift 3868579
  have htrace : WordTrace (prefixWord ++ tailWord_3868579) baseStart_3868579 baseEnd_3868579 := by
    simpa [prefixWord, tailWord_3868579, baseEnd_3868579] using wordTrace_append hprefix tailTrace_3868579
  have hstable : (prefixWord ++ tailWord_3868579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868579).length < 2 ^ (prefixWord ++ tailWord_3868579).sum := by decide
  have hdescent : baseEnd_3868579 < baseStart_3868579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868590 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3868590 : Nat := 118140960795 + 3868590 * 2 ^ 59
def prefixEnd_3868590 : Nat := 4983230072969 + 3 ^ 40 * 3868590 * 2
def baseEnd_3868590 : Nat := 1986446125177124357533685

theorem tailTrace_3868590 : CollatzResearch.WordTrace tailWord_3868590 prefixEnd_3868590 1986446125177124357533685 := by
  unfold tailWord_3868590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637383631845825926986403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94066046036511071610594149 17637383631845825926986403)
  ·
    refine ⟨26456075447768738890479605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637383631845825926986403 26456075447768738890479605)
    ·
      refine ⟨2480257073228319270982463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26456075447768738890479605 2480257073228319270982463)
      ·
        refine ⟨3720385609842478906473695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480257073228319270982463 3720385609842478906473695)
        ·
          refine ⟨5580578414763718359710543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720385609842478906473695 5580578414763718359710543)
          ·
            refine ⟨8370867622145577539565815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580578414763718359710543 8370867622145577539565815)
            ·
              refine ⟨12556301433218366309348723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370867622145577539565815 12556301433218366309348723)
              ·
                refine ⟨18834452149827549464023085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556301433218366309348723 18834452149827549464023085)
                ·
                  refine ⟨7062919556185331049008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18834452149827549464023085 7062919556185331049008657)
                  ·
                    refine ⟨5297189667138998286756493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062919556185331049008657 5297189667138998286756493)
                    ·
                      refine ⟨1986446125177124357533685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297189667138998286756493 1986446125177124357533685)
                      ·
                        rfl

theorem cell23_3868590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3868590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868590 prefixEnd_3868590 := by exact prefixLift 3868590
  have htrace : WordTrace (prefixWord ++ tailWord_3868590) baseStart_3868590 baseEnd_3868590 := by
    simpa [prefixWord, tailWord_3868590, baseEnd_3868590] using wordTrace_append hprefix tailTrace_3868590
  have hstable : (prefixWord ++ tailWord_3868590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868590).length < 2 ^ (prefixWord ++ tailWord_3868590).sum := by decide
  have hdescent : baseEnd_3868590 < baseStart_3868590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868629 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3868629 : Nat := 118140960795 + 3868629 * 2 ^ 59
def prefixEnd_3868629 : Nat := 4983230072969 + 3 ^ 40 * 3868629 * 2
def baseEnd_3868629 : Nat := 1986466150922649704946005

theorem tailTrace_3868629 : CollatzResearch.WordTrace tailWord_3868629 prefixEnd_3868629 1986466150922649704946005 := by
  unfold tailWord_3868629
  simp only [CollatzResearch.WordTrace]
  refine ⟨141100491501625317076560941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94066994334416878051040627 141100491501625317076560941)
  ·
    refine ⟨52912684313109493903710353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141100491501625317076560941 52912684313109493903710353)
    ·
      refine ⟨39684513234832120427782765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52912684313109493903710353 39684513234832120427782765)
      ·
        refine ⟨14881692463062045160418537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39684513234832120427782765 14881692463062045160418537)
        ·
          refine ⟨11161269347296533870313903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881692463062045160418537 11161269347296533870313903)
          ·
            refine ⟨16741904020944800805470855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161269347296533870313903 16741904020944800805470855)
            ·
              refine ⟨25112856031417201208206283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16741904020944800805470855 25112856031417201208206283)
              ·
                refine ⟨37669284047125801812309425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25112856031417201208206283 37669284047125801812309425)
                ·
                  refine ⟨28251963035344351359232069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37669284047125801812309425 28251963035344351359232069)
                  ·
                    refine ⟨5297243069127065879856013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28251963035344351359232069 5297243069127065879856013)
                    ·
                      refine ⟨1986466150922649704946005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297243069127065879856013 1986466150922649704946005)
                      ·
                        rfl

theorem cell23_3868629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3868629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868629 prefixEnd_3868629 := by exact prefixLift 3868629
  have htrace : WordTrace (prefixWord ++ tailWord_3868629) baseStart_3868629 baseEnd_3868629 := by
    simpa [prefixWord, tailWord_3868629, baseEnd_3868629] using wordTrace_append hprefix tailTrace_3868629
  have hstable : (prefixWord ++ tailWord_3868629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868629).length < 2 ^ (prefixWord ++ tailWord_3868629).sum := by decide
  have hdescent : baseEnd_3868629 < baseStart_3868629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868632 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 7]
def baseStart_3868632 : Nat := 118140960795 + 3868632 * 2 ^ 59
def prefixEnd_3868632 : Nat := 4983230072969 + 3 ^ 40 * 3868632 * 2
def baseEnd_3868632 : Nat := 220718632373845910356499

theorem tailTrace_3868632 : CollatzResearch.WordTrace tailWord_3868632 prefixEnd_3868632 220718632373845910356499 := by
  unfold tailWord_3868632
  simp only [CollatzResearch.WordTrace]
  refine ⟨70550300460307224294460075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94067067280409632392613433 70550300460307224294460075)
  ·
    refine ⟨105825450690460836441690113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70550300460307224294460075 105825450690460836441690113)
    ·
      refine ⟨79369088017845627331267585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105825450690460836441690113 79369088017845627331267585)
      ·
        refine ⟨59526816013384220498450689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79369088017845627331267585 59526816013384220498450689)
        ·
          refine ⟨44645112010038165373838017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59526816013384220498450689 44645112010038165373838017)
          ·
            refine ⟨33483834007528624030378513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44645112010038165373838017 33483834007528624030378513)
            ·
              refine ⟨25112875505646468022783885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33483834007528624030378513 25112875505646468022783885)
              ·
                refine ⟨9417328314617425508543957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25112875505646468022783885 9417328314617425508543957)
                ·
                  refine ⟨220718632373845910356499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9417328314617425508543957 220718632373845910356499)
                  ·
                    rfl

theorem cell23_3868632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_3868632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868632 prefixEnd_3868632 := by exact prefixLift 3868632
  have htrace : WordTrace (prefixWord ++ tailWord_3868632) baseStart_3868632 baseEnd_3868632 := by
    simpa [prefixWord, tailWord_3868632, baseEnd_3868632] using wordTrace_append hprefix tailTrace_3868632
  have hstable : (prefixWord ++ tailWord_3868632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868632).length < 2 ^ (prefixWord ++ tailWord_3868632).sum := by decide
  have hdescent : baseEnd_3868632 < baseStart_3868632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868639 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_3868639 : Nat := 118140960795 + 3868639 * 2 ^ 59
def prefixEnd_3868639 : Nat := 4983230072969 + 3 ^ 40 * 3868639 * 2
def baseEnd_3868639 : Nat := 1986471285729194665820959

theorem tailTrace_3868639 : CollatzResearch.WordTrace tailWord_3868639 prefixEnd_3868639 1986471285729194665820959 := by
  unfold tailWord_3868639
  simp only [CollatzResearch.WordTrace]
  refine ⟨141100856231589088784424971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94067237487726059189616647 141100856231589088784424971)
  ·
    refine ⟨211651284347383633176637457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141100856231589088784424971 211651284347383633176637457)
    ·
      refine ⟨158738463260537724882478093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211651284347383633176637457 158738463260537724882478093)
      ·
        refine ⟨59526923722701646830929285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158738463260537724882478093 59526923722701646830929285)
        ·
          refine ⟨11161298198006558780799241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59526923722701646830929285 11161298198006558780799241)
          ·
            refine ⟨8370973648504919085599431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11161298198006558780799241 8370973648504919085599431)
            ·
              refine ⟨12556460472757378628399147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370973648504919085599431 12556460472757378628399147)
              ·
                refine ⟨18834690709136067942598721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556460472757378628399147 18834690709136067942598721)
                ·
                  refine ⟨14126018031852050956949041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18834690709136067942598721 14126018031852050956949041)
                  ·
                    refine ⟨10594513523889038217711781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14126018031852050956949041 10594513523889038217711781)
                    ·
                      refine ⟨1986471285729194665820959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10594513523889038217711781 1986471285729194665820959)
                      ·
                        rfl

theorem cell23_3868639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_3868639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868639 prefixEnd_3868639 := by exact prefixLift 3868639
  have htrace : WordTrace (prefixWord ++ tailWord_3868639) baseStart_3868639 baseEnd_3868639 := by
    simpa [prefixWord, tailWord_3868639, baseEnd_3868639] using wordTrace_append hprefix tailTrace_3868639
  have hstable : (prefixWord ++ tailWord_3868639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868639).length < 2 ^ (prefixWord ++ tailWord_3868639).sum := by decide
  have hdescent : baseEnd_3868639 < baseStart_3868639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868643 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3868643 : Nat := 118140960795 + 3868643 * 2 ^ 59
def prefixEnd_3868643 : Nat := 4983230072969 + 3 ^ 40 * 3868643 * 2
def baseEnd_3868643 : Nat := 1986473339651812650170941

theorem tailTrace_3868643 : CollatzResearch.WordTrace tailWord_3868643 prefixEnd_3868643 1986473339651812650170941 := by
  unfold tailWord_3868643
  simp only [CollatzResearch.WordTrace]
  refine ⟨141101002123574597467570583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94067334749049731645047055 141101002123574597467570583)
  ·
    refine ⟨211651503185361896201355875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141101002123574597467570583 211651503185361896201355875)
    ·
      refine ⟨317477254778042844302033813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211651503185361896201355875 317477254778042844302033813)
      ·
        refine ⟨14881746317720758326657835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317477254778042844302033813 14881746317720758326657835)
        ·
          refine ⟨22322619476581137489986753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881746317720758326657835 22322619476581137489986753)
          ·
            refine ⟨16741964607435853117490065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22322619476581137489986753 16741964607435853117490065)
            ·
              refine ⟨12556473455576889838117549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16741964607435853117490065 12556473455576889838117549)
              ·
                refine ⟨4708677545841333689294081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12556473455576889838117549 4708677545841333689294081)
                ·
                  refine ⟨3531508159381000266970561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708677545841333689294081 3531508159381000266970561)
                  ·
                    refine ⟨2648631119535750200227921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3531508159381000266970561 2648631119535750200227921)
                    ·
                      refine ⟨1986473339651812650170941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648631119535750200227921 1986473339651812650170941)
                      ·
                        rfl

theorem cell23_3868643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3868643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868643 prefixEnd_3868643 := by exact prefixLift 3868643
  have htrace : WordTrace (prefixWord ++ tailWord_3868643) baseStart_3868643 baseEnd_3868643 := by
    simpa [prefixWord, tailWord_3868643, baseEnd_3868643] using wordTrace_append hprefix tailTrace_3868643
  have hstable : (prefixWord ++ tailWord_3868643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868643).length < 2 ^ (prefixWord ++ tailWord_3868643).sum := by decide
  have hdescent : baseEnd_3868643 < baseStart_3868643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868672 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3868672 : Nat := 118140960795 + 3868672 * 2 ^ 59
def prefixEnd_3868672 : Nat := 4983230072969 + 3 ^ 40 * 3868672 * 2
def baseEnd_3868672 : Nat := 1986488230590793036708307

theorem tailTrace_3868672 : CollatzResearch.WordTrace tailWord_3868672 prefixEnd_3868672 1986488230590793036708307 := by
  unfold tailWord_3868672
  simp only [CollatzResearch.WordTrace]
  refine ⟨70551029920234767710188135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94068039893646356946917513 70551029920234767710188135)
  ·
    refine ⟨105826544880352151565282203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70551029920234767710188135 105826544880352151565282203)
    ·
      refine ⟨158739817320528227347923305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105826544880352151565282203 158739817320528227347923305)
      ·
        refine ⟨119054862990396170510942479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158739817320528227347923305 119054862990396170510942479)
        ·
          refine ⟨178582294485594255766413719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119054862990396170510942479 178582294485594255766413719)
          ·
            refine ⟨267873441728391383649620579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178582294485594255766413719 267873441728391383649620579)
            ·
              refine ⟨401810162592587075474430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267873441728391383649620579 401810162592587075474430869)
              ·
                refine ⟨18834851371527519162863947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401810162592587075474430869 18834851371527519162863947)
                ·
                  refine ⟨28252277057291278744295921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18834851371527519162863947 28252277057291278744295921)
                  ·
                    refine ⟨21189207792968459058221941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28252277057291278744295921 21189207792968459058221941)
                    ·
                      refine ⟨1986488230590793036708307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21189207792968459058221941 1986488230590793036708307)
                      ·
                        rfl

theorem cell23_3868672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3868672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868672 prefixEnd_3868672 := by exact prefixLift 3868672
  have htrace : WordTrace (prefixWord ++ tailWord_3868672) baseStart_3868672 baseEnd_3868672 := by
    simpa [prefixWord, tailWord_3868672, baseEnd_3868672] using wordTrace_append hprefix tailTrace_3868672
  have hstable : (prefixWord ++ tailWord_3868672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868672).length < 2 ^ (prefixWord ++ tailWord_3868672).sum := by decide
  have hdescent : baseEnd_3868672 < baseStart_3868672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868699 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 6, 2]
def baseStart_3868699 : Nat := 118140960795 + 3868699 * 2 ^ 59
def prefixEnd_3868699 : Nat := 4983230072969 + 3 ^ 40 * 3868699 * 2
def baseEnd_3868699 : Nat := 1986502094568464431070683

theorem tailTrace_3868699 : CollatzResearch.WordTrace tailWord_3868699 prefixEnd_3868699 1986502094568464431070683 := by
  unfold tailWord_3868699
  simp only [CollatzResearch.WordTrace]
  refine ⟨141103044611371719031609151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94068696407581146021072767 141103044611371719031609151)
  ·
    refine ⟨211654566917057578547413727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141103044611371719031609151 211654566917057578547413727)
    ·
      refine ⟨317481850375586367821120591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211654566917057578547413727 317481850375586367821120591)
      ·
        refine ⟨476222775563379551731680887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317481850375586367821120591 476222775563379551731680887)
        ·
          refine ⟨714334163345069327597521331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476222775563379551731680887 714334163345069327597521331)
          ·
            refine ⟨1071501245017603991396281997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714334163345069327597521331 1071501245017603991396281997)
            ·
              refine ⟨401812966881601496773605749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071501245017603991396281997 401812966881601496773605749)
              ·
                refine ⟨37669965645150140322525539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401812966881601496773605749 37669965645150140322525539)
                ·
                  refine ⟨56504948467725210483788309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37669965645150140322525539 56504948467725210483788309)
                  ·
                    refine ⟨2648669459424619241427577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56504948467725210483788309 2648669459424619241427577)
                    ·
                      refine ⟨1986502094568464431070683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648669459424619241427577 1986502094568464431070683)
                      ·
                        rfl

theorem cell23_3868699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6, 2].length) (baseStart_3868699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868699 prefixEnd_3868699 := by exact prefixLift 3868699
  have htrace : WordTrace (prefixWord ++ tailWord_3868699) baseStart_3868699 baseEnd_3868699 := by
    simpa [prefixWord, tailWord_3868699, baseEnd_3868699] using wordTrace_append hprefix tailTrace_3868699
  have hstable : (prefixWord ++ tailWord_3868699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868699).length < 2 ^ (prefixWord ++ tailWord_3868699).sum := by decide
  have hdescent : baseEnd_3868699 < baseStart_3868699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868736 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_3868736 : Nat := 118140960795 + 3868736 * 2 ^ 59
def prefixEnd_3868736 : Nat := 4983230072969 + 3 ^ 40 * 3868736 * 2
def baseEnd_3868736 : Nat := 1986521093352680786308013

theorem tailTrace_3868736 : CollatzResearch.WordTrace tailWord_3868736 prefixEnd_3868736 1986521093352680786308013 := by
  unfold tailWord_3868736
  simp only [CollatzResearch.WordTrace]
  refine ⟨70552197056118837175353031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94069596074825116233804041 70552197056118837175353031)
  ·
    refine ⟨105828295584178255763029547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70552197056118837175353031 105828295584178255763029547)
    ·
      refine ⟨158742443376267383644544321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105828295584178255763029547 158742443376267383644544321)
      ·
        refine ⟨119056832532200537733408241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158742443376267383644544321 119056832532200537733408241)
        ·
          refine ⟨89292624399150403300056181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119056832532200537733408241 89292624399150403300056181)
          ·
            refine ⟨8371183537420350309380267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89292624399150403300056181 8371183537420350309380267)
            ·
              refine ⟨12556775306130525464070401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371183537420350309380267 12556775306130525464070401)
              ·
                refine ⟨9417581479597894098052801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12556775306130525464070401 9417581479597894098052801)
                ·
                  refine ⟨7063186109698420573539601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9417581479597894098052801 7063186109698420573539601)
                  ·
                    refine ⟨5297389582273815430154701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063186109698420573539601 5297389582273815430154701)
                    ·
                      refine ⟨1986521093352680786308013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297389582273815430154701 1986521093352680786308013)
                      ·
                        rfl

theorem cell23_3868736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_3868736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868736 prefixEnd_3868736 := by exact prefixLift 3868736
  have htrace : WordTrace (prefixWord ++ tailWord_3868736) baseStart_3868736 baseEnd_3868736 := by
    simpa [prefixWord, tailWord_3868736, baseEnd_3868736] using wordTrace_append hprefix tailTrace_3868736
  have hstable : (prefixWord ++ tailWord_3868736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868736).length < 2 ^ (prefixWord ++ tailWord_3868736).sum := by decide
  have hdescent : baseEnd_3868736 < baseStart_3868736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868752 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_3868752 : Nat := 118140960795 + 3868752 * 2 ^ 59
def prefixEnd_3868752 : Nat := 4983230072969 + 3 ^ 40 * 3868752 * 2
def baseEnd_3868752 : Nat := 662176436347717574569313

theorem tailTrace_3868752 : CollatzResearch.WordTrace tailWord_3868752 prefixEnd_3868752 662176436347717574569313 := by
  unfold tailWord_3868752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70552488840089854541644255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94069985120119806055525673 70552488840089854541644255)
  ·
    refine ⟨105828733260134781812466383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70552488840089854541644255 105828733260134781812466383)
    ·
      refine ⟨158743099890202172718699575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105828733260134781812466383 158743099890202172718699575)
      ·
        refine ⟨238114649835303259078049363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158743099890202172718699575 238114649835303259078049363)
        ·
          refine ⟨357171974752954888617074045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238114649835303259078049363 357171974752954888617074045)
          ·
            refine ⟨133939490532358083231402767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357171974752954888617074045 133939490532358083231402767)
            ·
              refine ⟨200909235798537124847104151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133939490532358083231402767 200909235798537124847104151)
              ·
                refine ⟨301363853697805687270656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200909235798537124847104151 301363853697805687270656227)
                ·
                  refine ⟨452045780546708530905984341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301363853697805687270656227 452045780546708530905984341)
                  ·
                    refine ⟨662176436347717574569313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 452045780546708530905984341 662176436347717574569313)
                    ·
                      rfl

theorem cell23_3868752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_3868752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868752 prefixEnd_3868752 := by exact prefixLift 3868752
  have htrace : WordTrace (prefixWord ++ tailWord_3868752) baseStart_3868752 baseEnd_3868752 := by
    simpa [prefixWord, tailWord_3868752, baseEnd_3868752] using wordTrace_append hprefix tailTrace_3868752
  have hstable : (prefixWord ++ tailWord_3868752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868752).length < 2 ^ (prefixWord ++ tailWord_3868752).sum := by decide
  have hdescent : baseEnd_3868752 < baseStart_3868752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868770 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3868770 : Nat := 118140960795 + 3868770 * 2 ^ 59
def prefixEnd_3868770 : Nat := 4983230072969 + 3 ^ 40 * 3868770 * 2
def baseEnd_3868770 : Nat := 1986538551694933653282857

theorem tailTrace_3868770 : CollatzResearch.WordTrace tailWord_3868770 prefixEnd_3868770 1986538551694933653282857 := by
  unfold tailWord_3868770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35276408548528624539360941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94070422796076332104962509 35276408548528624539360941)
  ·
    refine ⟨13228653205698234202260353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35276408548528624539360941 13228653205698234202260353)
    ·
      refine ⟨9921489904273675651695265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13228653205698234202260353 9921489904273675651695265)
      ·
        refine ⟨7441117428205256738771449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9921489904273675651695265 7441117428205256738771449)
        ·
          refine ⟨5580838071153942554078587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441117428205256738771449 5580838071153942554078587)
          ·
            refine ⟨8371257106730913831117881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580838071153942554078587 8371257106730913831117881)
            ·
              refine ⟨6278442830048185373338411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8371257106730913831117881 6278442830048185373338411)
              ·
                refine ⟨9417664245072278060007617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278442830048185373338411 9417664245072278060007617)
                ·
                  refine ⟨7063248183804208545005713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9417664245072278060007617 7063248183804208545005713)
                  ·
                    refine ⟨5297436137853156408754285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063248183804208545005713 5297436137853156408754285)
                    ·
                      refine ⟨1986538551694933653282857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297436137853156408754285 1986538551694933653282857)
                      ·
                        rfl

theorem cell23_3868770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3868770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868770 prefixEnd_3868770 := by exact prefixLift 3868770
  have htrace : WordTrace (prefixWord ++ tailWord_3868770) baseStart_3868770 baseEnd_3868770 := by
    simpa [prefixWord, tailWord_3868770, baseEnd_3868770] using wordTrace_append hprefix tailTrace_3868770
  have hstable : (prefixWord ++ tailWord_3868770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868770).length < 2 ^ (prefixWord ++ tailWord_3868770).sum := by decide
  have hdescent : baseEnd_3868770 < baseStart_3868770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868793 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 2, 3, 2]
def baseStart_3868793 : Nat := 118140960795 + 3868793 * 2 ^ 59
def prefixEnd_3868793 : Nat := 4983230072969 + 3 ^ 40 * 3868793 * 2
def baseEnd_3868793 : Nat := 1986550361749987063295251

theorem tailTrace_3868793 : CollatzResearch.WordTrace tailWord_3868793 prefixEnd_3868793 1986550361749987063295251 := by
  unfold tailWord_3868793
  simp only [CollatzResearch.WordTrace]
  refine ⟨141106473073031173085531033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94070982048687448723687355 141106473073031173085531033)
  ·
    refine ⟨105829854804773379814148275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141106473073031173085531033 105829854804773379814148275)
    ·
      refine ⟨158744782207160069721222413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105829854804773379814148275 158744782207160069721222413)
      ·
        refine ⟨59529293327685026145458405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158744782207160069721222413 59529293327685026145458405)
        ·
          refine ⟨11161742498940942402273451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59529293327685026145458405 11161742498940942402273451)
          ·
            refine ⟨16742613748411413603410177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161742498940942402273451 16742613748411413603410177)
            ·
              refine ⟨12556960311308560202557633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16742613748411413603410177 12556960311308560202557633)
              ·
                refine ⟨9417720233481420151918225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12556960311308560202557633 9417720233481420151918225)
                ·
                  refine ⟨7063290175111065113938669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9417720233481420151918225 7063290175111065113938669)
                  ·
                    refine ⟨2648733815666649417727001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7063290175111065113938669 2648733815666649417727001)
                    ·
                      refine ⟨1986550361749987063295251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2648733815666649417727001 1986550361749987063295251)
                      ·
                        rfl

theorem cell23_3868793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_3868793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868793 prefixEnd_3868793 := by exact prefixLift 3868793
  have htrace : WordTrace (prefixWord ++ tailWord_3868793) baseStart_3868793 baseEnd_3868793 := by
    simpa [prefixWord, tailWord_3868793, baseEnd_3868793] using wordTrace_append hprefix tailTrace_3868793
  have hstable : (prefixWord ++ tailWord_3868793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868793).length < 2 ^ (prefixWord ++ tailWord_3868793).sum := by decide
  have hdescent : baseEnd_3868793 < baseStart_3868793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868809 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_3868809 : Nat := 118140960795 + 3868809 * 2 ^ 59
def prefixEnd_3868809 : Nat := 4983230072969 + 3 ^ 40 * 3868809 * 2
def baseEnd_3868809 : Nat := 1986558577440459000695177

theorem tailTrace_3868809 : CollatzResearch.WordTrace tailWord_3868809 prefixEnd_3868809 1986558577440459000695177 := by
  unfold tailWord_3868809
  simp only [CollatzResearch.WordTrace]
  refine ⟨141107056640973207818113481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94071371093982138545408987 141107056640973207818113481)
  ·
    refine ⟨105830292480729905863585111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141107056640973207818113481 105830292480729905863585111)
    ·
      refine ⟨158745438721094858795377667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105830292480729905863585111 158745438721094858795377667)
      ·
        refine ⟨238118158081642288193066501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158745438721094858795377667 238118158081642288193066501)
        ·
          refine ⟨44647154640307929036199969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238118158081642288193066501 44647154640307929036199969)
          ·
            refine ⟨33485365980230946777149977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44647154640307929036199969 33485365980230946777149977)
            ·
              refine ⟨25114024485173210082862483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33485365980230946777149977 25114024485173210082862483)
              ·
                refine ⟨37671036727759815124293725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25114024485173210082862483 37671036727759815124293725)
                ·
                  refine ⟨14126638772909930671610147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37671036727759815124293725 14126638772909930671610147)
                  ·
                    refine ⟨21189958159364896007415221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14126638772909930671610147 21189958159364896007415221)
                    ·
                      refine ⟨1986558577440459000695177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21189958159364896007415221 1986558577440459000695177)
                      ·
                        rfl

theorem cell23_3868809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_3868809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868809 prefixEnd_3868809 := by exact prefixLift 3868809
  have htrace : WordTrace (prefixWord ++ tailWord_3868809) baseStart_3868809 baseEnd_3868809 := by
    simpa [prefixWord, tailWord_3868809, baseEnd_3868809] using wordTrace_append hprefix tailTrace_3868809
  have hstable : (prefixWord ++ tailWord_3868809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868809).length < 2 ^ (prefixWord ++ tailWord_3868809).sum := by decide
  have hdescent : baseEnd_3868809 < baseStart_3868809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868816 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_3868816 : Nat := 118140960795 + 3868816 * 2 ^ 59
def prefixEnd_3868816 : Nat := 4983230072969 + 3 ^ 40 * 3868816 * 2
def baseEnd_3868816 : Nat := 662187390601680157769215

theorem tailTrace_3868816 : CollatzResearch.WordTrace tailWord_3868816 prefixEnd_3868816 662187390601680157769215 := by
  unfold tailWord_3868816
  simp only [CollatzResearch.WordTrace]
  refine ⟨70553655975973924006809151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94071541301298565342412201 70553655975973924006809151)
  ·
    refine ⟨105830483963960886010213727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70553655975973924006809151 105830483963960886010213727)
    ·
      refine ⟨158745725945941329015320591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105830483963960886010213727 158745725945941329015320591)
      ·
        refine ⟨238118588918911993522980887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158745725945941329015320591 238118588918911993522980887)
        ·
          refine ⟨357177883378367990284471331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238118588918911993522980887 357177883378367990284471331)
          ·
            refine ⟨535766825067551985426706997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357177883378367990284471331 535766825067551985426706997)
            ·
              refine ⟨50228139850082998633753781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535766825067551985426706997 50228139850082998633753781)
              ·
                refine ⟨4708888110945281121914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50228139850082998633753781 4708888110945281121914417)
                ·
                  refine ⟨3531666083208960841435813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708888110945281121914417 3531666083208960841435813)
                  ·
                    refine ⟨662187390601680157769215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531666083208960841435813 662187390601680157769215)
                    ·
                      rfl

theorem cell23_3868816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_3868816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868816 prefixEnd_3868816 := by exact prefixLift 3868816
  have htrace : WordTrace (prefixWord ++ tailWord_3868816) baseStart_3868816 baseEnd_3868816 := by
    simpa [prefixWord, tailWord_3868816, baseEnd_3868816] using wordTrace_append hprefix tailTrace_3868816
  have hstable : (prefixWord ++ tailWord_3868816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868816).length < 2 ^ (prefixWord ++ tailWord_3868816).sum := by decide
  have hdescent : baseEnd_3868816 < baseStart_3868816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868889 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_3868889 : Nat := 118140960795 + 3868889 * 2 ^ 59
def prefixEnd_3868889 : Nat := 4983230072969 + 3 ^ 40 * 3868889 * 2
def baseEnd_3868889 : Nat := 662199885297606229231603

theorem tailTrace_3868889 : CollatzResearch.WordTrace tailWord_3868889 prefixEnd_3868889 662199885297606229231603 := by
  unfold tailWord_3868889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141109974480683381481025721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94073316320455587654017147 141109974480683381481025721)
  ·
    refine ⟨105832480860512536110769291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141109974480683381481025721 105832480860512536110769291)
    ·
      refine ⟨158748721290768804166153937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105832480860512536110769291 158748721290768804166153937)
      ·
        refine ⟨119061540968076603124615453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158748721290768804166153937 119061540968076603124615453)
        ·
          refine ⟨44648077863028726171730795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119061540968076603124615453 44648077863028726171730795)
          ·
            refine ⟨66972116794543089257596193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44648077863028726171730795 66972116794543089257596193)
            ·
              refine ⟨50229087595907316943197145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66972116794543089257596193 50229087595907316943197145)
              ·
                refine ⟨37671815696930487707397859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50229087595907316943197145 37671815696930487707397859)
                ·
                  refine ⟨56507723545395731561096789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37671815696930487707397859 56507723545395731561096789)
                  ·
                    refine ⟨662199885297606229231603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56507723545395731561096789 662199885297606229231603)
                    ·
                      rfl

theorem cell23_3868889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_3868889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868889 prefixEnd_3868889 := by exact prefixLift 3868889
  have htrace : WordTrace (prefixWord ++ tailWord_3868889) baseStart_3868889 baseEnd_3868889 := by
    simpa [prefixWord, tailWord_3868889, baseEnd_3868889] using wordTrace_append hprefix tailTrace_3868889
  have hstable : (prefixWord ++ tailWord_3868889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868889).length < 2 ^ (prefixWord ++ tailWord_3868889).sum := by decide
  have hdescent : baseEnd_3868889 < baseStart_3868889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868980 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3868980 : Nat := 118140960795 + 3868980 * 2 ^ 59
def prefixEnd_3868980 : Nat := 4983230072969 + 3 ^ 40 * 3868980 * 2
def baseEnd_3868980 : Nat := 1986646382632377831656891

theorem tailTrace_3868980 : CollatzResearch.WordTrace tailWord_3868980 prefixEnd_3868980 1986646382632377831656891 := by
  unfold tailWord_3868980
  simp only [CollatzResearch.WordTrace]
  refine ⟨70556646761676852011294197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94075529015569136015058929 70556646761676852011294197)
  ·
    refine ⟨6614685633907204876058831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70556646761676852011294197 6614685633907204876058831)
    ·
      refine ⟨9922028450860807314088247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6614685633907204876058831 9922028450860807314088247)
      ·
        refine ⟨14883042676291210971132371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922028450860807314088247 14883042676291210971132371)
        ·
          refine ⟨22324564014436816456698557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883042676291210971132371 22324564014436816456698557)
          ·
            refine ⟨8371711505413806171261959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22324564014436816456698557 8371711505413806171261959)
            ·
              refine ⟨12557567258120709256892939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371711505413806171261959 12557567258120709256892939)
              ·
                refine ⟨18836350887181063885339409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557567258120709256892939 18836350887181063885339409)
                ·
                  refine ⟨14127263165385797914004557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18836350887181063885339409 14127263165385797914004557)
                  ·
                    refine ⟨5297723687019674217751709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14127263165385797914004557 5297723687019674217751709)
                    ·
                      refine ⟨1986646382632377831656891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297723687019674217751709 1986646382632377831656891)
                      ·
                        rfl

theorem cell23_3868980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3868980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3868980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3868980 prefixEnd_3868980 := by exact prefixLift 3868980
  have htrace : WordTrace (prefixWord ++ tailWord_3868980) baseStart_3868980 baseEnd_3868980 := by
    simpa [prefixWord, tailWord_3868980, baseEnd_3868980] using wordTrace_append hprefix tailTrace_3868980
  have hstable : (prefixWord ++ tailWord_3868980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868980).length < 2 ^ (prefixWord ++ tailWord_3868980).sum := by decide
  have hdescent : baseEnd_3868980 < baseStart_3868980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869006 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3869006 : Nat := 118140960795 + 3869006 * 2 ^ 59
def prefixEnd_3869006 : Nat := 4983230072969 + 3 ^ 40 * 3869006 * 2
def baseEnd_3869006 : Nat := 1986659733129394729931771

theorem tailTrace_3869006 : CollatzResearch.WordTrace tailWord_3869006 prefixEnd_3869006 1986659733129394729931771 := by
  unfold tailWord_3869006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639280227657438807879359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94076161214173006975356581 17639280227657438807879359)
  ·
    refine ⟨26458920341486158211819039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17639280227657438807879359 26458920341486158211819039)
    ·
      refine ⟨39688380512229237317728559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26458920341486158211819039 39688380512229237317728559)
      ·
        refine ⟨59532570768343855976592839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39688380512229237317728559 59532570768343855976592839)
        ·
          refine ⟨89298856152515783964889259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59532570768343855976592839 89298856152515783964889259)
          ·
            refine ⟨133948284228773675947333889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89298856152515783964889259 133948284228773675947333889)
            ·
              refine ⟨100461213171580256960500417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133948284228773675947333889 100461213171580256960500417)
              ·
                refine ⟨75345909878685192720375313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100461213171580256960500417 75345909878685192720375313)
                ·
                  refine ⟨56509432409013894540281485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75345909878685192720375313 56509432409013894540281485)
                  ·
                    refine ⟨21191037153380210452605557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56509432409013894540281485 21191037153380210452605557)
                    ·
                      refine ⟨1986659733129394729931771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21191037153380210452605557 1986659733129394729931771)
                      ·
                        rfl

theorem cell23_3869006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3869006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869006 prefixEnd_3869006 := by exact prefixLift 3869006
  have htrace : WordTrace (prefixWord ++ tailWord_3869006) baseStart_3869006 baseEnd_3869006 := by
    simpa [prefixWord, tailWord_3869006, baseEnd_3869006] using wordTrace_append hprefix tailTrace_3869006
  have hstable : (prefixWord ++ tailWord_3869006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869006).length < 2 ^ (prefixWord ++ tailWord_3869006).sum := by decide
  have hdescent : baseEnd_3869006 < baseStart_3869006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869023 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_3869023 : Nat := 118140960795 + 3869023 * 2 ^ 59
def prefixEnd_3869023 : Nat := 4983230072969 + 3 ^ 40 * 3869023 * 2
def baseEnd_3869023 : Nat := 1986668462300521163419193

theorem tailTrace_3869023 : CollatzResearch.WordTrace tailWord_3869023 prefixEnd_3869023 1986668462300521163419193 := by
  unfold tailWord_3869023
  simp only [CollatzResearch.WordTrace]
  refine ⟨141114861862197922366403723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94076574574798614910935815 141114861862197922366403723)
  ·
    refine ⟨211672292793296883549605585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141114861862197922366403723 211672292793296883549605585)
    ·
      refine ⟨158754219594972662662204189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211672292793296883549605585 158754219594972662662204189)
      ·
        refine ⟨59532832348114748498326571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158754219594972662662204189 59532832348114748498326571)
        ·
          refine ⟨89299248522172122747489857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59532832348114748498326571 89299248522172122747489857)
          ·
            refine ⟨66974436391629092060617393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89299248522172122747489857 66974436391629092060617393)
            ·
              refine ⟨50230827293721819045463045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66974436391629092060617393 50230827293721819045463045)
              ·
                refine ⟨9418280117572841071024321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50230827293721819045463045 9418280117572841071024321)
                ·
                  refine ⟨7063710088179630803268241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418280117572841071024321 7063710088179630803268241)
                  ·
                    refine ⟨5297782566134723102451181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063710088179630803268241 5297782566134723102451181)
                    ·
                      refine ⟨1986668462300521163419193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297782566134723102451181 1986668462300521163419193)
                      ·
                        rfl

theorem cell23_3869023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_3869023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869023 prefixEnd_3869023 := by exact prefixLift 3869023
  have htrace : WordTrace (prefixWord ++ tailWord_3869023) baseStart_3869023 baseEnd_3869023 := by
    simpa [prefixWord, tailWord_3869023, baseEnd_3869023] using wordTrace_append hprefix tailTrace_3869023
  have hstable : (prefixWord ++ tailWord_3869023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869023).length < 2 ^ (prefixWord ++ tailWord_3869023).sum := by decide
  have hdescent : baseEnd_3869023 < baseStart_3869023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869093 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3869093 : Nat := 118140960795 + 3869093 * 2 ^ 59
def prefixEnd_3869093 : Nat := 4983230072969 + 3 ^ 40 * 3869093 * 2
def baseEnd_3869093 : Nat := 1986704405946335889543871

theorem tailTrace_3869093 : CollatzResearch.WordTrace tailWord_3869093 prefixEnd_3869093 1986704405946335889543871 := by
  unfold tailWord_3869093
  simp only [CollatzResearch.WordTrace]
  refine ⟨141117414971944324321451933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94078276647962882880967955 141117414971944324321451933)
  ·
    refine ⟨52919030614479121620544475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141117414971944324321451933 52919030614479121620544475)
    ·
      refine ⟨79378545921718682430816713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52919030614479121620544475 79378545921718682430816713)
      ·
        refine ⟨59533909441289011823112535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79378545921718682430816713 59533909441289011823112535)
        ·
          refine ⟨89300864161933517734668803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59533909441289011823112535 89300864161933517734668803)
          ·
            refine ⟨133951296242900276602003205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89300864161933517734668803 133951296242900276602003205)
            ·
              refine ⟨25115868045543801862875601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133951296242900276602003205 25115868045543801862875601)
              ·
                refine ⟨18836901034157851397156701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25115868045543801862875601 18836901034157851397156701)
                ·
                  refine ⟨7063837887809194273933763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18836901034157851397156701 7063837887809194273933763)
                  ·
                    refine ⟨10595756831713791410900645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7063837887809194273933763 10595756831713791410900645)
                    ·
                      refine ⟨1986704405946335889543871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10595756831713791410900645 1986704405946335889543871)
                      ·
                        rfl

theorem cell23_3869093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3869093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869093 prefixEnd_3869093 := by exact prefixLift 3869093
  have htrace : WordTrace (prefixWord ++ tailWord_3869093) baseStart_3869093 baseEnd_3869093 := by
    simpa [prefixWord, tailWord_3869093, baseEnd_3869093] using wordTrace_append hprefix tailTrace_3869093
  have hstable : (prefixWord ++ tailWord_3869093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869093).length < 2 ^ (prefixWord ++ tailWord_3869093).sum := by decide
  have hdescent : baseEnd_3869093 < baseStart_3869093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869124 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3869124 : Nat := 118140960795 + 3869124 * 2 ^ 59
def prefixEnd_3869124 : Nat := 4983230072969 + 3 ^ 40 * 3869124 * 2
def baseEnd_3869124 : Nat := 662240107948875089418743

theorem tailTrace_3869124 : CollatzResearch.WordTrace tailWord_3869124 prefixEnd_3869124 662240107948875089418743 := by
  unfold tailWord_3869124
  simp only [CollatzResearch.WordTrace]
  refine ⟨70559272817416008307915213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94079030423221344410553617 70559272817416008307915213)
  ·
    refine ⟨26459727306531003115468205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70559272817416008307915213 26459727306531003115468205)
    ·
      refine ⟨9922397739949126168300577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26459727306531003115468205 9922397739949126168300577)
      ·
        refine ⟨7441798304961844626225433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9922397739949126168300577 7441798304961844626225433)
        ·
          refine ⟨5581348728721383469669075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441798304961844626225433 5581348728721383469669075)
          ·
            refine ⟨8372023093082075204503613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581348728721383469669075 8372023093082075204503613)
            ·
              refine ⟨3139508659905778201688855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372023093082075204503613 3139508659905778201688855)
              ·
                refine ⟨4709262989858667302533283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139508659905778201688855 4709262989858667302533283)
                ·
                  refine ⟨7063894484788000953799925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709262989858667302533283 7063894484788000953799925)
                  ·
                    refine ⟨662240107948875089418743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7063894484788000953799925 662240107948875089418743)
                    ·
                      rfl

theorem cell23_3869124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3869124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869124 prefixEnd_3869124 := by exact prefixLift 3869124
  have htrace : WordTrace (prefixWord ++ tailWord_3869124) baseStart_3869124 baseEnd_3869124 := by
    simpa [prefixWord, tailWord_3869124, baseEnd_3869124] using wordTrace_append hprefix tailTrace_3869124
  have hstable : (prefixWord ++ tailWord_3869124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869124).length < 2 ^ (prefixWord ++ tailWord_3869124).sum := by decide
  have hdescent : baseEnd_3869124 < baseStart_3869124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869127 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_3869127 : Nat := 118140960795 + 3869127 * 2 ^ 59
def prefixEnd_3869127 : Nat := 4983230072969 + 3 ^ 40 * 3869127 * 2
def baseEnd_3869127 : Nat := 1986721864288588756518715

theorem tailTrace_3869127 : CollatzResearch.WordTrace tailWord_3869127 prefixEnd_3869127 1986721864288588756518715 := by
  unfold tailWord_3869127
  simp only [CollatzResearch.WordTrace]
  refine ⟨141118655053821148128189635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94079103369214098752126423 141118655053821148128189635)
  ·
    refine ⟨211677982580731722192284453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141118655053821148128189635 211677982580731722192284453)
    ·
      refine ⟨39689621733887197911053335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211677982580731722192284453 39689621733887197911053335)
      ·
        refine ⟨59534432600830796866580003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39689621733887197911053335 59534432600830796866580003)
        ·
          refine ⟨89301648901246195299870005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59534432600830796866580003 89301648901246195299870005)
          ·
            refine ⟨8372029584491830809362813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89301648901246195299870005 8372029584491830809362813)
            ·
              refine ⟨3139511094184436553511055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372029584491830809362813 3139511094184436553511055)
              ·
                refine ⟨4709266641276654830266583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139511094184436553511055 4709266641276654830266583)
                ·
                  refine ⟨7063899961914982245399875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709266641276654830266583 7063899961914982245399875)
                  ·
                    refine ⟨10595849942872473368099813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7063899961914982245399875 10595849942872473368099813)
                    ·
                      refine ⟨1986721864288588756518715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10595849942872473368099813 1986721864288588756518715)
                      ·
                        rfl

theorem cell23_3869127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_3869127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869127 prefixEnd_3869127 := by exact prefixLift 3869127
  have htrace : WordTrace (prefixWord ++ tailWord_3869127) baseStart_3869127 baseEnd_3869127 := by
    simpa [prefixWord, tailWord_3869127, baseEnd_3869127] using wordTrace_append hprefix tailTrace_3869127
  have hstable : (prefixWord ++ tailWord_3869127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869127).length < 2 ^ (prefixWord ++ tailWord_3869127).sum := by decide
  have hdescent : baseEnd_3869127 < baseStart_3869127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869154 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3869154 : Nat := 118140960795 + 3869154 * 2 ^ 59
def prefixEnd_3869154 : Nat := 4983230072969 + 3 ^ 40 * 3869154 * 2
def baseEnd_3869154 : Nat := 662245242755420050293697

theorem tailTrace_3869154 : CollatzResearch.WordTrace tailWord_3869154 prefixEnd_3869154 662245242755420050293697 := by
  unfold tailWord_3869154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35279909956180832934855629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94079759883148887826281677 35279909956180832934855629)
  ·
    refine ⟨13229966233567812350570861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35279909956180832934855629 13229966233567812350570861)
    ·
      refine ⟨4961237337587929631464073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13229966233567812350570861 4961237337587929631464073)
      ·
        refine ⟨3720928003190947223598055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4961237337587929631464073 3720928003190947223598055)
        ·
          refine ⟨5581392004786420835397083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720928003190947223598055 5581392004786420835397083)
          ·
            refine ⟨8372088007179631253095625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581392004786420835397083 8372088007179631253095625)
            ·
              refine ⟨6279066005384723439821719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372088007179631253095625 6279066005384723439821719)
              ·
                refine ⟨9418599008077085159732579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279066005384723439821719 9418599008077085159732579)
                ·
                  refine ⟨14127898512115627739598869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418599008077085159732579 14127898512115627739598869)
                  ·
                    refine ⟨662245242755420050293697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14127898512115627739598869 662245242755420050293697)
                    ·
                      rfl

theorem cell23_3869154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3869154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869154 prefixEnd_3869154 := by exact prefixLift 3869154
  have htrace : WordTrace (prefixWord ++ tailWord_3869154) baseStart_3869154 baseEnd_3869154 := by
    simpa [prefixWord, tailWord_3869154, baseEnd_3869154] using wordTrace_append hprefix tailTrace_3869154
  have hstable : (prefixWord ++ tailWord_3869154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869154).length < 2 ^ (prefixWord ++ tailWord_3869154).sum := by decide
  have hdescent : baseEnd_3869154 < baseStart_3869154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869157 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3869157 : Nat := 118140960795 + 3869157 * 2 ^ 59
def prefixEnd_3869157 : Nat := 4983230072969 + 3 ^ 40 * 3869157 * 2
def baseEnd_3869157 : Nat := 1986737268708223639143577

theorem tailTrace_3869157 : CollatzResearch.WordTrace tailWord_3869157 prefixEnd_3869157 1986737268708223639143577 := by
  unfold tailWord_3869157
  simp only [CollatzResearch.WordTrace]
  refine ⟨141119749243712463251781725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94079832829141642167854483 141119749243712463251781725)
  ·
    refine ⟨52919905966392173719418147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141119749243712463251781725 52919905966392173719418147)
    ·
      refine ⟨79379858949588260579127221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52919905966392173719418147 79379858949588260579127221)
      ·
        refine ⟨7441861776523899429293177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79379858949588260579127221 7441861776523899429293177)
        ·
          refine ⟨5581396332392924571969883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441861776523899429293177 5581396332392924571969883)
          ·
            refine ⟨8372094498589386857954825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581396332392924571969883 8372094498589386857954825)
            ·
              refine ⟨6279070873942040143466119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372094498589386857954825 6279070873942040143466119)
              ·
                refine ⟨9418606310913060215199179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279070873942040143466119 9418606310913060215199179)
                ·
                  refine ⟨14127909466369590322798769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418606310913060215199179 14127909466369590322798769)
                  ·
                    refine ⟨10595932099777192742099077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14127909466369590322798769 10595932099777192742099077)
                    ·
                      refine ⟨1986737268708223639143577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10595932099777192742099077 1986737268708223639143577)
                      ·
                        rfl

theorem cell23_3869157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3869157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869157 prefixEnd_3869157 := by exact prefixLift 3869157
  have htrace : WordTrace (prefixWord ++ tailWord_3869157) baseStart_3869157 baseEnd_3869157 := by
    simpa [prefixWord, tailWord_3869157, baseEnd_3869157] using wordTrace_append hprefix tailTrace_3869157
  have hstable : (prefixWord ++ tailWord_3869157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869157).length < 2 ^ (prefixWord ++ tailWord_3869157).sum := by decide
  have hdescent : baseEnd_3869157 < baseStart_3869157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869160 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3869160 : Nat := 118140960795 + 3869160 * 2 ^ 59
def prefixEnd_3869160 : Nat := 4983230072969 + 3 ^ 40 * 3869160 * 2
def baseEnd_3869160 : Nat := 1986738809150187127406063

theorem tailTrace_3869160 : CollatzResearch.WordTrace tailWord_3869160 prefixEnd_3869160 1986738809150187127406063 := by
  unfold tailWord_3869160
  simp only [CollatzResearch.WordTrace]
  refine ⟨70559929331350797382070467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94079905775134396509427289 70559929331350797382070467)
  ·
    refine ⟨105839893997026196073105701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70559929331350797382070467 105839893997026196073105701)
    ·
      refine ⟨19844980124442411763707319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105839893997026196073105701 19844980124442411763707319)
      ·
        refine ⟨29767470186663617645560979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19844980124442411763707319 29767470186663617645560979)
        ·
          refine ⟨44651205279995426468341469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29767470186663617645560979 44651205279995426468341469)
          ·
            refine ⟨16744201979998284925628051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44651205279995426468341469 16744201979998284925628051)
            ·
              refine ⟨25116302969997427388442077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16744201979998284925628051 25116302969997427388442077)
              ·
                refine ⟨9418613613749035270665779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25116302969997427388442077 9418613613749035270665779)
                ·
                  refine ⟨14127920420623552905998669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418613613749035270665779 14127920420623552905998669)
                  ·
                    refine ⟨5297970157733832339749501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14127920420623552905998669 5297970157733832339749501)
                    ·
                      refine ⟨1986738809150187127406063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5297970157733832339749501 1986738809150187127406063)
                      ·
                        rfl

theorem cell23_3869160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3869160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869160 prefixEnd_3869160 := by exact prefixLift 3869160
  have htrace : WordTrace (prefixWord ++ tailWord_3869160) baseStart_3869160 baseEnd_3869160 := by
    simpa [prefixWord, tailWord_3869160, baseEnd_3869160] using wordTrace_append hprefix tailTrace_3869160
  have hstable : (prefixWord ++ tailWord_3869160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869160).length < 2 ^ (prefixWord ++ tailWord_3869160).sum := by decide
  have hdescent : baseEnd_3869160 < baseStart_3869160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869187 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 1, 3, 2]
def baseStart_3869187 : Nat := 118140960795 + 3869187 * 2 ^ 59
def prefixEnd_3869187 : Nat := 4983230072969 + 3 ^ 40 * 3869187 * 2
def baseEnd_3869187 : Nat := 1986752673127858521768439

theorem tailTrace_3869187 : CollatzResearch.WordTrace tailWord_3869187 prefixEnd_3869187 1986752673127858521768439 := by
  unfold tailWord_3869187
  simp only [CollatzResearch.WordTrace]
  refine ⟨141120843433603778375373815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94080562289069185583582543 141120843433603778375373815)
  ·
    refine ⟨211681265150405667563060723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141120843433603778375373815 211681265150405667563060723)
    ·
      refine ⟨317521897725608501344591085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211681265150405667563060723 317521897725608501344591085)
      ·
        refine ⟨119070711647103188004221657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317521897725608501344591085 119070711647103188004221657)
        ·
          refine ⟨89303033735327391003166243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119070711647103188004221657 89303033735327391003166243)
          ·
            refine ⟨133954550602991086504749365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89303033735327391003166243 133954550602991086504749365)
            ·
              refine ⟨12558239119030414359820253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133954550602991086504749365 12558239119030414359820253)
              ·
                refine ⟨4709339669636405384932595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12558239119030414359820253 4709339669636405384932595)
                ·
                  refine ⟨7064009504454608077398893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709339669636405384932595 7064009504454608077398893)
                  ·
                    refine ⟨2649003564170478029024585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7064009504454608077398893 2649003564170478029024585)
                    ·
                      refine ⟨1986752673127858521768439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649003564170478029024585 1986752673127858521768439)
                      ·
                        rfl

theorem cell23_3869187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_3869187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869187 prefixEnd_3869187 := by exact prefixLift 3869187
  have htrace : WordTrace (prefixWord ++ tailWord_3869187) baseStart_3869187 baseEnd_3869187 := by
    simpa [prefixWord, tailWord_3869187, baseEnd_3869187] using wordTrace_append hprefix tailTrace_3869187
  have hstable : (prefixWord ++ tailWord_3869187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869187).length < 2 ^ (prefixWord ++ tailWord_3869187).sum := by decide
  have hdescent : baseEnd_3869187 < baseStart_3869187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869229 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3869229 : Nat := 118140960795 + 3869229 * 2 ^ 59
def prefixEnd_3869229 : Nat := 4983230072969 + 3 ^ 40 * 3869229 * 2
def baseEnd_3869229 : Nat := 1986774239315347357443247

theorem tailTrace_3869229 : CollatzResearch.WordTrace tailWord_3869229 prefixEnd_3869229 1986774239315347357443247 := by
  unfold tailWord_3869229
  simp only [CollatzResearch.WordTrace]
  refine ⟨141122375299451619548402741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94081583532967746365601827 141122375299451619548402741)
  ·
    refine ⟨13230222684323589332662757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141122375299451619548402741 13230222684323589332662757)
    ·
      refine ⟨2480666753310672999874267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13230222684323589332662757 2480666753310672999874267)
      ·
        refine ⟨3721000129966009499811401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480666753310672999874267 3721000129966009499811401)
        ·
          refine ⟨2790750097474507124858551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721000129966009499811401 2790750097474507124858551)
          ·
            refine ⟨4186125146211760687287827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790750097474507124858551 4186125146211760687287827)
            ·
              refine ⟨6279187719317641030931741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186125146211760687287827 6279187719317641030931741)
              ·
                refine ⟨2354695394744115386599403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279187719317641030931741 2354695394744115386599403)
                ·
                  refine ⟨3532043092116173079899105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354695394744115386599403 3532043092116173079899105)
                  ·
                    refine ⟨2649032319087129809924329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532043092116173079899105 2649032319087129809924329)
                    ·
                      refine ⟨1986774239315347357443247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649032319087129809924329 1986774239315347357443247)
                      ·
                        rfl

theorem cell23_3869229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3869229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869229 prefixEnd_3869229 := by exact prefixLift 3869229
  have htrace : WordTrace (prefixWord ++ tailWord_3869229) baseStart_3869229 baseEnd_3869229 := by
    simpa [prefixWord, tailWord_3869229, baseEnd_3869229] using wordTrace_append hprefix tailTrace_3869229
  have hstable : (prefixWord ++ tailWord_3869229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869229).length < 2 ^ (prefixWord ++ tailWord_3869229).sum := by decide
  have hdescent : baseEnd_3869229 < baseStart_3869229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869263 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_3869263 : Nat := 118140960795 + 3869263 * 2 ^ 59
def prefixEnd_3869263 : Nat := 4983230072969 + 3 ^ 40 * 3869263 * 2
def baseEnd_3869263 : Nat := 1986791697657600224418089

theorem tailTrace_3869263 : CollatzResearch.WordTrace tailWord_3869263 prefixEnd_3869263 1986791697657600224418089 := by
  unfold tailWord_3869263
  simp only [CollatzResearch.WordTrace]
  refine ⟨141123615381328443355140443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94082410254218962236760295 141123615381328443355140443)
  ·
    refine ⟨211685423071992665032710665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141123615381328443355140443 211685423071992665032710665)
    ·
      refine ⟨158764067303994498774532999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211685423071992665032710665 158764067303994498774532999)
      ·
        refine ⟨238146100955991748161799499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158764067303994498774532999 238146100955991748161799499)
        ·
          refine ⟨357219151433987622242699249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238146100955991748161799499 357219151433987622242699249)
          ·
            refine ⟨267914363575490716682024437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357219151433987622242699249 267914363575490716682024437)
            ·
              refine ⟨25116971585202254688939791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267914363575490716682024437 25116971585202254688939791)
              ·
                refine ⟨37675457377803382033409687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25116971585202254688939791 37675457377803382033409687)
                ·
                  refine ⟨56513186066705073050114531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37675457377803382033409687 56513186066705073050114531)
                  ·
                    refine ⟨84769779100057609575171797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56513186066705073050114531 84769779100057609575171797)
                    ·
                      refine ⟨1986791697657600224418089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84769779100057609575171797 1986791697657600224418089)
                      ·
                        rfl

theorem cell23_3869263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_3869263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869263 prefixEnd_3869263 := by exact prefixLift 3869263
  have htrace : WordTrace (prefixWord ++ tailWord_3869263) baseStart_3869263 baseEnd_3869263 := by
    simpa [prefixWord, tailWord_3869263, baseEnd_3869263] using wordTrace_append hprefix tailTrace_3869263
  have hstable : (prefixWord ++ tailWord_3869263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869263).length < 2 ^ (prefixWord ++ tailWord_3869263).sum := by decide
  have hdescent : baseEnd_3869263 < baseStart_3869263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869268 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_3869268 : Nat := 118140960795 + 3869268 * 2 ^ 59
def prefixEnd_3869268 : Nat := 4983230072969 + 3 ^ 40 * 3869268 * 2
def baseEnd_3869268 : Nat := 1986794265060872704855567

theorem tailTrace_3869268 : CollatzResearch.WordTrace tailWord_3869268 prefixEnd_3869268 1986794265060872704855567 := by
  unfold tailWord_3869268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70561898873155164604536229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94082531830873552806048305 70561898873155164604536229)
  ·
    refine ⟨13230356038716593363350543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70561898873155164604536229 13230356038716593363350543)
    ·
      refine ⟨19845534058074890045025815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230356038716593363350543 19845534058074890045025815)
      ·
        refine ⟨29768301087112335067538723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19845534058074890045025815 29768301087112335067538723)
        ·
          refine ⟨44652451630668502601308085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29768301087112335067538723 44652451630668502601308085)
          ·
            refine ⟨4186167340375172118872633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44652451630668502601308085 4186167340375172118872633)
            ·
              refine ⟨3139625505281379089154475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186167340375172118872633 3139625505281379089154475)
              ·
                refine ⟨4709438257922068633731713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139625505281379089154475 4709438257922068633731713)
                ·
                  refine ⟨3532078693441551475298785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709438257922068633731713 3532078693441551475298785)
                  ·
                    refine ⟨2649059020081163606474089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532078693441551475298785 2649059020081163606474089)
                    ·
                      refine ⟨1986794265060872704855567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649059020081163606474089 1986794265060872704855567)
                      ·
                        rfl

theorem cell23_3869268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_3869268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869268 prefixEnd_3869268 := by exact prefixLift 3869268
  have htrace : WordTrace (prefixWord ++ tailWord_3869268) baseStart_3869268 baseEnd_3869268 := by
    simpa [prefixWord, tailWord_3869268, baseEnd_3869268] using wordTrace_append hprefix tailTrace_3869268
  have hstable : (prefixWord ++ tailWord_3869268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869268).length < 2 ^ (prefixWord ++ tailWord_3869268).sum := by decide
  have hdescent : baseEnd_3869268 < baseStart_3869268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869407 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 4, 4]
def baseStart_3869407 : Nat := 118140960795 + 3869407 * 2 ^ 59
def prefixEnd_3869407 : Nat := 4983230072969 + 3 ^ 40 * 3869407 * 2
def baseEnd_3869407 : Nat := 662288546290615887005809

theorem tailTrace_3869407 : CollatzResearch.WordTrace tailWord_3869407 prefixEnd_3869407 662288546290615887005809 := by
  unfold tailWord_3869407
  simp only [CollatzResearch.WordTrace]
  refine ⟨141128867492806755948382475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94085911661871170632254983 141128867492806755948382475)
  ·
    refine ⟨211693301239210133922573713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141128867492806755948382475 211693301239210133922573713)
    ·
      refine ⟨158769975929407600441930285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211693301239210133922573713 158769975929407600441930285)
      ·
        refine ⟨59538740973527850165723857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158769975929407600441930285 59538740973527850165723857)
        ·
          refine ⟨44654055730145887624292893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59538740973527850165723857 44654055730145887624292893)
          ·
            refine ⟨16745270898804707859109835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44654055730145887624292893 16745270898804707859109835)
            ·
              refine ⟨25117906348207061788664753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16745270898804707859109835 25117906348207061788664753)
              ·
                refine ⟨18838429761155296341498565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25117906348207061788664753 18838429761155296341498565)
                ·
                  refine ⟨3532205580216618064030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18838429761155296341498565 3532205580216618064030981)
                  ·
                    refine ⟨662288546290615887005809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3532205580216618064030981 662288546290615887005809)
                    ·
                      rfl

theorem cell23_3869407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_3869407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869407 prefixEnd_3869407 := by exact prefixLift 3869407
  have htrace : WordTrace (prefixWord ++ tailWord_3869407) baseStart_3869407 baseEnd_3869407 := by
    simpa [prefixWord, tailWord_3869407, baseEnd_3869407] using wordTrace_append hprefix tailTrace_3869407
  have hstable : (prefixWord ++ tailWord_3869407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869407).length < 2 ^ (prefixWord ++ tailWord_3869407).sum := by decide
  have hdescent : baseEnd_3869407 < baseStart_3869407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869482 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3869482 : Nat := 118140960795 + 3869482 * 2 ^ 59
def prefixEnd_3869482 : Nat := 4983230072969 + 3 ^ 40 * 3869482 * 2
def baseEnd_3869482 : Nat := 1986904149920934867579583

theorem tailTrace_3869482 : CollatzResearch.WordTrace tailWord_3869482 prefixEnd_3869482 1986904149920934867579583 := by
  unfold tailWord_3869482
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282900741883760939340675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94087735311690029171575133 35282900741883760939340675)
  ·
    refine ⟨52924351112825641409011013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35282900741883760939340675 52924351112825641409011013)
    ·
      refine ⟨9923315833654807764189565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52924351112825641409011013 9923315833654807764189565)
      ·
        refine ⟨3721243437620552911571087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9923315833654807764189565 3721243437620552911571087)
        ·
          refine ⟨5581865156430829367356631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721243437620552911571087 5581865156430829367356631)
          ·
            refine ⟨8372797734646244051034947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581865156430829367356631 8372797734646244051034947)
            ·
              refine ⟨12559196601969366076552421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372797734646244051034947 12559196601969366076552421)
              ·
                refine ⟨2354849362869256139353579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12559196601969366076552421 2354849362869256139353579)
                ·
                  refine ⟨3532274044303884209030369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354849362869256139353579 3532274044303884209030369)
                  ·
                    refine ⟨2649205533227913156772777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532274044303884209030369 2649205533227913156772777)
                    ·
                      refine ⟨1986904149920934867579583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649205533227913156772777 1986904149920934867579583)
                      ·
                        rfl

theorem cell23_3869482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3869482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869482 prefixEnd_3869482 := by exact prefixLift 3869482
  have htrace : WordTrace (prefixWord ++ tailWord_3869482) baseStart_3869482 baseEnd_3869482 := by
    simpa [prefixWord, tailWord_3869482, baseEnd_3869482] using wordTrace_append hprefix tailTrace_3869482
  have hstable : (prefixWord ++ tailWord_3869482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869482).length < 2 ^ (prefixWord ++ tailWord_3869482).sum := by decide
  have hdescent : baseEnd_3869482 < baseStart_3869482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869507 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3]
def baseStart_3869507 : Nat := 118140960795 + 3869507 * 2 ^ 59
def prefixEnd_3869507 : Nat := 4983230072969 + 3 ^ 40 * 3869507 * 2
def baseEnd_3869507 : Nat := 1986916986937297269766967

theorem tailTrace_3869507 : CollatzResearch.WordTrace tailWord_3869507 prefixEnd_3869507 1986916986937297269766967 := by
  unfold tailWord_3869507
  simp only [CollatzResearch.WordTrace]
  refine ⟨141132514792444473027022775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94088343194962982018015183 141132514792444473027022775)
  ·
    refine ⟨211698772188666709540534163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141132514792444473027022775 211698772188666709540534163)
    ·
      refine ⟨317548158283000064310801245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211698772188666709540534163 317548158283000064310801245)
      ·
        refine ⟨119080559356125024116550467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317548158283000064310801245 119080559356125024116550467)
        ·
          refine ⟨178620839034187536174825701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119080559356125024116550467 178620839034187536174825701)
          ·
            refine ⟨33491407318910163032779819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178620839034187536174825701 33491407318910163032779819)
            ·
              refine ⟨50237110978365244549169729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33491407318910163032779819 50237110978365244549169729)
              ·
                refine ⟨37677833233773933411877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50237110978365244549169729 37677833233773933411877297)
                ·
                  refine ⟨28258374925330450058907973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37677833233773933411877297 28258374925330450058907973)
                  ·
                    refine ⟨5298445298499459386045245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28258374925330450058907973 5298445298499459386045245)
                    ·
                      refine ⟨1986916986937297269766967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5298445298499459386045245 1986916986937297269766967)
                      ·
                        rfl

theorem cell23_3869507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_3869507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869507 prefixEnd_3869507 := by exact prefixLift 3869507
  have htrace : WordTrace (prefixWord ++ tailWord_3869507) baseStart_3869507 baseEnd_3869507 := by
    simpa [prefixWord, tailWord_3869507, baseEnd_3869507] using wordTrace_append hprefix tailTrace_3869507
  have hstable : (prefixWord ++ tailWord_3869507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869507).length < 2 ^ (prefixWord ++ tailWord_3869507).sum := by decide
  have hdescent : baseEnd_3869507 < baseStart_3869507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869544 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 7]
def baseStart_3869544 : Nat := 118140960795 + 3869544 * 2 ^ 59
def prefixEnd_3869544 : Nat := 4983230072969 + 3 ^ 40 * 3869544 * 2
def baseEnd_3869544 : Nat := 220770665080168180556033

theorem tailTrace_3869544 : CollatzResearch.WordTrace tailWord_3869544 prefixEnd_3869544 220770665080168180556033 := by
  unfold tailWord_3869544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70566932146655214173059843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94089242862206952230746457 70566932146655214173059843)
  ·
    refine ⟨105850398219982821259589765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70566932146655214173059843 105850398219982821259589765)
    ·
      refine ⟨19846949666246778986173081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105850398219982821259589765 19846949666246778986173081)
      ·
        refine ⟨14885212249685084239629811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19846949666246778986173081 14885212249685084239629811)
        ·
          refine ⟨22327818374527626359444717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885212249685084239629811 22327818374527626359444717)
          ·
            refine ⟨8372931890447859884791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22327818374527626359444717 8372931890447859884791769)
            ·
              refine ⟨6279698917835894913593827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372931890447859884791769 6279698917835894913593827)
              ·
                refine ⟨9419548376753842370390741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279698917835894913593827 9419548376753842370390741)
                ·
                  refine ⟨220770665080168180556033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9419548376753842370390741 220770665080168180556033)
                  ·
                    rfl

theorem cell23_3869544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_3869544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869544 prefixEnd_3869544 := by exact prefixLift 3869544
  have htrace : WordTrace (prefixWord ++ tailWord_3869544) baseStart_3869544 baseEnd_3869544 := by
    simpa [prefixWord, tailWord_3869544, baseEnd_3869544] using wordTrace_append hprefix tailTrace_3869544
  have hstable : (prefixWord ++ tailWord_3869544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869544).length < 2 ^ (prefixWord ++ tailWord_3869544).sum := by decide
  have hdescent : baseEnd_3869544 < baseStart_3869544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869554 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3869554 : Nat := 118140960795 + 3869554 * 2 ^ 59
def prefixEnd_3869554 : Nat := 4983230072969 + 3 ^ 40 * 3869554 * 2
def baseEnd_3869554 : Nat := 1986941120528058585879251

theorem tailTrace_3869554 : CollatzResearch.WordTrace tailWord_3869554 prefixEnd_3869554 1986941120528058585879251 := by
  unfold tailWord_3869554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35283557255818550013495929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94089486015516133369322477 35283557255818550013495929)
  ·
    refine ⟨26462667941863912510121947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35283557255818550013495929 26462667941863912510121947)
    ·
      refine ⟨39694001912795868765182921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26462667941863912510121947 39694001912795868765182921)
      ·
        refine ⟨29770501434596901573887191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39694001912795868765182921 29770501434596901573887191)
        ·
          refine ⟨44655752151895352360830787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29770501434596901573887191 44655752151895352360830787)
          ·
            refine ⟨66983628227843028541246181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44655752151895352360830787 66983628227843028541246181)
            ·
              refine ⟨12559430292720567851483659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66983628227843028541246181 12559430292720567851483659)
              ·
                refine ⟨18839145439080851777225489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559430292720567851483659 18839145439080851777225489)
                ·
                  refine ⟨14129359079310638832919117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18839145439080851777225489 14129359079310638832919117)
                  ·
                    refine ⟨5298509654741489562344669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14129359079310638832919117 5298509654741489562344669)
                    ·
                      refine ⟨1986941120528058585879251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5298509654741489562344669 1986941120528058585879251)
                      ·
                        rfl

theorem cell23_3869554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3869554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869554 prefixEnd_3869554 := by exact prefixLift 3869554
  have htrace : WordTrace (prefixWord ++ tailWord_3869554) baseStart_3869554 baseEnd_3869554 := by
    simpa [prefixWord, tailWord_3869554, baseEnd_3869554] using wordTrace_append hprefix tailTrace_3869554
  have hstable : (prefixWord ++ tailWord_3869554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869554).length < 2 ^ (prefixWord ++ tailWord_3869554).sum := by decide
  have hdescent : baseEnd_3869554 < baseStart_3869554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869564 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_3869564 : Nat := 118140960795 + 3869564 * 2 ^ 59
def prefixEnd_3869564 : Nat := 4983230072969 + 3 ^ 40 * 3869564 * 2
def baseEnd_3869564 : Nat := 1986946255334603546754205

theorem tailTrace_3869564 : CollatzResearch.WordTrace tailWord_3869564 prefixEnd_3869564 1986946255334603546754205 := by
  unfold tailWord_3869564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70567296876618985880923873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94089729168825314507898497 70567296876618985880923873)
  ·
    refine ⟨52925472657464239410692905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70567296876618985880923873 52925472657464239410692905)
    ·
      refine ⟨39694104493098179558019679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52925472657464239410692905 39694104493098179558019679)
      ·
        refine ⟨59541156739647269337029519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39694104493098179558019679 59541156739647269337029519)
        ·
          refine ⟨89311735109470904005544279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59541156739647269337029519 89311735109470904005544279)
          ·
            refine ⟨133967602664206356008316419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89311735109470904005544279 133967602664206356008316419)
            ·
              refine ⟨200951403996309534012474629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133967602664206356008316419 200951403996309534012474629)
              ·
                refine ⟨37678388249308037627338993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200951403996309534012474629 37678388249308037627338993)
                ·
                  refine ⟨28258791186981028220504245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37678388249308037627338993 28258791186981028220504245)
                  ·
                    refine ⟨2649261673779471395672273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28258791186981028220504245 2649261673779471395672273)
                    ·
                      refine ⟨1986946255334603546754205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649261673779471395672273 1986946255334603546754205)
                      ·
                        rfl

theorem cell23_3869564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_3869564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869564 prefixEnd_3869564 := by exact prefixLift 3869564
  have htrace : WordTrace (prefixWord ++ tailWord_3869564) baseStart_3869564 baseEnd_3869564 := by
    simpa [prefixWord, tailWord_3869564, baseEnd_3869564] using wordTrace_append hprefix tailTrace_3869564
  have hstable : (prefixWord ++ tailWord_3869564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869564).length < 2 ^ (prefixWord ++ tailWord_3869564).sum := by decide
  have hdescent : baseEnd_3869564 < baseStart_3869564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869578 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_3869578 : Nat := 118140960795 + 3869578 * 2 ^ 59
def prefixEnd_3869578 : Nat := 4983230072969 + 3 ^ 40 * 3869578 * 2
def baseEnd_3869578 : Nat := 220772604895974054664349

theorem tailTrace_3869578 : CollatzResearch.WordTrace tailWord_3869578 prefixEnd_3869578 220772604895974054664349 := by
  unfold tailWord_3869578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35283776093796813038214347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94090069583458168101904925 35283776093796813038214347)
  ·
    refine ⟨52925664140695219557321521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35283776093796813038214347 52925664140695219557321521)
    ·
      refine ⟨39694248105521414667991141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52925664140695219557321521 39694248105521414667991141)
      ·
        refine ⟨7442671519785265250248339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39694248105521414667991141 7442671519785265250248339)
        ·
          refine ⟨11164007279677897875372509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442671519785265250248339 11164007279677897875372509)
          ·
            refine ⟨4186502729879211703264691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11164007279677897875372509 4186502729879211703264691)
            ·
              refine ⟨6279754094818817554897037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186502729879211703264691 6279754094818817554897037)
              ·
                refine ⟨2354907785557056583086389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279754094818817554897037 2354907785557056583086389)
                ·
                  refine ⟨220772604895974054664349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2354907785557056583086389 220772604895974054664349)
                  ·
                    rfl

theorem cell23_3869578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_3869578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869578 prefixEnd_3869578 := by exact prefixLift 3869578
  have htrace : WordTrace (prefixWord ++ tailWord_3869578) baseStart_3869578 baseEnd_3869578 := by
    simpa [prefixWord, tailWord_3869578, baseEnd_3869578] using wordTrace_append hprefix tailTrace_3869578
  have hstable : (prefixWord ++ tailWord_3869578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869578).length < 2 ^ (prefixWord ++ tailWord_3869578).sum := by decide
  have hdescent : baseEnd_3869578 < baseStart_3869578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869682 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3869682 : Nat := 118140960795 + 3869682 * 2 ^ 59
def prefixEnd_3869682 : Nat := 4983230072969 + 3 ^ 40 * 3869682 * 2
def baseEnd_3869682 : Nat := 1987006846051834085078663

theorem tailTrace_3869682 : CollatzResearch.WordTrace tailWord_3869682 prefixEnd_3869682 1987006846051834085078663 := by
  unfold tailWord_3869682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35284724391702619478660825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94092598377873651943095533 35284724391702619478660825)
  ·
    refine ⟨26463543293776964608995619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35284724391702619478660825 26463543293776964608995619)
    ·
      refine ⟨39695314940665446913493429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463543293776964608995619 39695314940665446913493429)
      ·
        refine ⟨3721435775687385648140009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39695314940665446913493429 3721435775687385648140009)
        ·
          refine ⟨2791076831765539236105007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721435775687385648140009 2791076831765539236105007)
          ·
            refine ⟨4186615247648308854157511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791076831765539236105007 4186615247648308854157511)
            ·
              refine ⟨6279922871472463281236267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186615247648308854157511 6279922871472463281236267)
              ·
                refine ⟨9419884307208694921854401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279922871472463281236267 9419884307208694921854401)
                ·
                  refine ⟨7064913230406521191390801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9419884307208694921854401 7064913230406521191390801)
                  ·
                    refine ⟨5298684922804890893543101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7064913230406521191390801 5298684922804890893543101)
                    ·
                      refine ⟨1987006846051834085078663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5298684922804890893543101 1987006846051834085078663)
                      ·
                        rfl

theorem cell23_3869682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3869682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869682 prefixEnd_3869682 := by exact prefixLift 3869682
  have htrace : WordTrace (prefixWord ++ tailWord_3869682) baseStart_3869682 baseEnd_3869682 := by
    simpa [prefixWord, tailWord_3869682, baseEnd_3869682] using wordTrace_append hprefix tailTrace_3869682
  have hstable : (prefixWord ++ tailWord_3869682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869682).length < 2 ^ (prefixWord ++ tailWord_3869682).sum := by decide
  have hdescent : baseEnd_3869682 < baseStart_3869682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869701 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_3869701 : Nat := 118140960795 + 3869701 * 2 ^ 59
def prefixEnd_3869701 : Nat := 4983230072969 + 3 ^ 40 * 3869701 * 2
def baseEnd_3869701 : Nat := 1987016602184269510741075

theorem tailTrace_3869701 : CollatzResearch.WordTrace tailWord_3869701 prefixEnd_3869701 1987016602184269510741075 := by
  unfold tailWord_3869701
  simp only [CollatzResearch.WordTrace]
  refine ⟨141139590553741644159584957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94093060369161096106389971 141139590553741644159584957)
  ·
    refine ⟨52927346457653116559844359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141139590553741644159584957 52927346457653116559844359)
    ·
      refine ⟨79391019686479674839766539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52927346457653116559844359 79391019686479674839766539)
      ·
        refine ⟨119086529529719512259649809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79391019686479674839766539 119086529529719512259649809)
        ·
          refine ⟨89314897147289634194737357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119086529529719512259649809 89314897147289634194737357)
          ·
            refine ⟨33493086430233612823026509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89314897147289634194737357 33493086430233612823026509)
            ·
              refine ⟨12559907411337604808634941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33493086430233612823026509 12559907411337604808634941)
              ·
                refine ⟨4709965279251601803238103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12559907411337604808634941 4709965279251601803238103)
                ·
                  refine ⟨7064947918877402704857155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709965279251601803238103 7064947918877402704857155)
                  ·
                    refine ⟨10597421878316104057285733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7064947918877402704857155 10597421878316104057285733)
                    ·
                      refine ⟨1987016602184269510741075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10597421878316104057285733 1987016602184269510741075)
                      ·
                        rfl

theorem cell23_3869701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_3869701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869701 prefixEnd_3869701 := by exact prefixLift 3869701
  have htrace : WordTrace (prefixWord ++ tailWord_3869701) baseStart_3869701 baseEnd_3869701 := by
    simpa [prefixWord, tailWord_3869701, baseEnd_3869701] using wordTrace_append hprefix tailTrace_3869701
  have hstable : (prefixWord ++ tailWord_3869701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869701).length < 2 ^ (prefixWord ++ tailWord_3869701).sum := by decide
  have hdescent : baseEnd_3869701 < baseStart_3869701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869731 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4]
def baseStart_3869731 : Nat := 118140960795 + 3869731 * 2 ^ 59
def prefixEnd_3869731 : Nat := 4983230072969 + 3 ^ 40 * 3869731 * 2
def baseEnd_3869731 : Nat := 1987032006603904393365937

theorem tailTrace_3869731 : CollatzResearch.WordTrace tailWord_3869731 prefixEnd_3869731 1987032006603904393365937 := by
  unfold tailWord_3869731
  simp only [CollatzResearch.WordTrace]
  refine ⟨141140684743632959283177047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94093789829088639522118031 141140684743632959283177047)
  ·
    refine ⟨211711027115449438924765571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141140684743632959283177047 211711027115449438924765571)
    ·
      refine ⟨317566540673174158387148357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211711027115449438924765571 317566540673174158387148357)
      ·
        refine ⟨59543726376220154697590317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317566540673174158387148357 59543726376220154697590317)
        ·
          refine ⟨22328897391082558011596369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59543726376220154697590317 22328897391082558011596369)
          ·
            refine ⟨16746673043311918508697277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22328897391082558011596369 16746673043311918508697277)
            ·
              refine ⟨6280002391241969440761479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16746673043311918508697277 6280002391241969440761479)
              ·
                refine ⟨9420003586862954161142219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280002391241969440761479 9420003586862954161142219)
                ·
                  refine ⟨14130005380294431241713329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9420003586862954161142219 14130005380294431241713329)
                  ·
                    refine ⟨10597504035220823431284997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14130005380294431241713329 10597504035220823431284997)
                    ·
                      refine ⟨1987032006603904393365937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10597504035220823431284997 1987032006603904393365937)
                      ·
                        rfl

theorem cell23_3869731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_3869731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869731 prefixEnd_3869731 := by exact prefixLift 3869731
  have htrace : WordTrace (prefixWord ++ tailWord_3869731) baseStart_3869731 baseEnd_3869731 := by
    simpa [prefixWord, tailWord_3869731, baseEnd_3869731] using wordTrace_append hprefix tailTrace_3869731
  have hstable : (prefixWord ++ tailWord_3869731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869731).length < 2 ^ (prefixWord ++ tailWord_3869731).sum := by decide
  have hdescent : baseEnd_3869731 < baseStart_3869731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869735 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3869735 : Nat := 118140960795 + 3869735 * 2 ^ 59
def prefixEnd_3869735 : Nat := 4983230072969 + 3 ^ 40 * 3869735 * 2
def baseEnd_3869735 : Nat := 1987034060526522377715919

theorem tailTrace_3869735 : CollatzResearch.WordTrace tailWord_3869735 prefixEnd_3869735 1987034060526522377715919 := by
  unfold tailWord_3869735
  simp only [CollatzResearch.WordTrace]
  refine ⟨141140830635618467966322659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94093887090412311977548439 141140830635618467966322659)
  ·
    refine ⟨211711245953427701949483989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141140830635618467966322659 211711245953427701949483989)
    ·
      refine ⟨4961982327033461764441031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 211711245953427701949483989 4961982327033461764441031)
      ·
        refine ⟨7442973490550192646661547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961982327033461764441031 7442973490550192646661547)
        ·
          refine ⟨11164460235825288969992321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442973490550192646661547 11164460235825288969992321)
          ·
            refine ⟨8373345176868966727494241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164460235825288969992321 8373345176868966727494241)
            ·
              refine ⟨6280008882651725045620681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373345176868966727494241 6280008882651725045620681)
              ·
                refine ⟨4710006661988793784215511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280008882651725045620681 4710006661988793784215511)
                ·
                  refine ⟨7065009992983190676323267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710006661988793784215511 7065009992983190676323267)
                  ·
                    refine ⟨10597514989474786014484901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065009992983190676323267 10597514989474786014484901)
                    ·
                      refine ⟨1987034060526522377715919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10597514989474786014484901 1987034060526522377715919)
                      ·
                        rfl

theorem cell23_3869735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3869735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869735 prefixEnd_3869735 := by exact prefixLift 3869735
  have htrace : WordTrace (prefixWord ++ tailWord_3869735) baseStart_3869735 baseEnd_3869735 := by
    simpa [prefixWord, tailWord_3869735, baseEnd_3869735] using wordTrace_append hprefix tailTrace_3869735
  have hstable : (prefixWord ++ tailWord_3869735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869735).length < 2 ^ (prefixWord ++ tailWord_3869735).sum := by decide
  have hdescent : baseEnd_3869735 < baseStart_3869735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869752 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_3869752 : Nat := 118140960795 + 3869752 * 2 ^ 59
def prefixEnd_3869752 : Nat := 4983230072969 + 3 ^ 40 * 3869752 * 2
def baseEnd_3869752 : Nat := 1987042789697648811203341

theorem tailTrace_3869752 : CollatzResearch.WordTrace tailWord_3869752 prefixEnd_3869752 1987042789697648811203341 := by
  unfold tailWord_3869752
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570725338278439934845755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94094300451037919913127673 70570725338278439934845755)
  ·
    refine ⟨105856088007417659902268633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70570725338278439934845755 105856088007417659902268633)
    ·
      refine ⟨79392066005563244926701475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105856088007417659902268633 79392066005563244926701475)
      ·
        refine ⟨119088099008344867390052213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79392066005563244926701475 119088099008344867390052213)
        ·
          refine ⟨11164509282032331317817395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119088099008344867390052213 11164509282032331317817395)
          ·
            refine ⟨16746763923048496976726093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164509282032331317817395 16746763923048496976726093)
            ·
              refine ⟨6280036471143186366272285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16746763923048496976726093 6280036471143186366272285)
              ·
                refine ⟨2355013676678694887352107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6280036471143186366272285 2355013676678694887352107)
                ·
                  refine ⟨3532520515018042331028161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355013676678694887352107 3532520515018042331028161)
                  ·
                    refine ⟨2649390386263531748271121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532520515018042331028161 2649390386263531748271121)
                    ·
                      refine ⟨1987042789697648811203341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649390386263531748271121 1987042789697648811203341)
                      ·
                        rfl

theorem cell23_3869752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_3869752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869752 prefixEnd_3869752 := by exact prefixLift 3869752
  have htrace : WordTrace (prefixWord ++ tailWord_3869752) baseStart_3869752 baseEnd_3869752 := by
    simpa [prefixWord, tailWord_3869752, baseEnd_3869752] using wordTrace_append hprefix tailTrace_3869752
  have hstable : (prefixWord ++ tailWord_3869752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869752).length < 2 ^ (prefixWord ++ tailWord_3869752).sum := by decide
  have hdescent : baseEnd_3869752 < baseStart_3869752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869768 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_3869768 : Nat := 118140960795 + 3869768 * 2 ^ 59
def prefixEnd_3869768 : Nat := 4983230072969 + 3 ^ 40 * 3869768 * 2
def baseEnd_3869768 : Nat := 1987051005388120748603267

theorem tailTrace_3869768 : CollatzResearch.WordTrace tailWord_3869768 prefixEnd_3869768 1987051005388120748603267 := by
  unfold tailWord_3869768
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571017122249457301136979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94094689496332609734849305 70571017122249457301136979)
  ·
    refine ⟨105856525683374185951705469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70571017122249457301136979 105856525683374185951705469)
    ·
      refine ⟨39696197131265319731889551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105856525683374185951705469 39696197131265319731889551)
      ·
        refine ⟨59544295696897979597834327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39696197131265319731889551 59544295696897979597834327)
        ·
          refine ⟨89316443545346969396751491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59544295696897979597834327 89316443545346969396751491)
          ·
            refine ⟨133974665318020454095127237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89316443545346969396751491 133974665318020454095127237)
            ·
              refine ⟨25120249747128835142836357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133974665318020454095127237 25120249747128835142836357)
              ·
                refine ⟨4710046827586656589281817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25120249747128835142836357 4710046827586656589281817)
                ·
                  refine ⟨3532535120689992441961363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710046827586656589281817 3532535120689992441961363)
                  ·
                    refine ⟨5298802681034988662942045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3532535120689992441961363 5298802681034988662942045)
                    ·
                      refine ⟨1987051005388120748603267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5298802681034988662942045 1987051005388120748603267)
                      ·
                        rfl

theorem cell23_3869768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_3869768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869768 prefixEnd_3869768 := by exact prefixLift 3869768
  have htrace : WordTrace (prefixWord ++ tailWord_3869768) baseStart_3869768 baseEnd_3869768 := by
    simpa [prefixWord, tailWord_3869768, baseEnd_3869768] using wordTrace_append hprefix tailTrace_3869768
  have hstable : (prefixWord ++ tailWord_3869768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869768).length < 2 ^ (prefixWord ++ tailWord_3869768).sum := by decide
  have hdescent : baseEnd_3869768 < baseStart_3869768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869784 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_3869784 : Nat := 118140960795 + 3869784 * 2 ^ 59
def prefixEnd_3869784 : Nat := 4983230072969 + 3 ^ 40 * 3869784 * 2
def baseEnd_3869784 : Nat := 662353073692864228667731

theorem tailTrace_3869784 : CollatzResearch.WordTrace tailWord_3869784 prefixEnd_3869784 662353073692864228667731 := by
  unfold tailWord_3869784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571308906220474667428203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94095078541627299556570937 70571308906220474667428203)
  ·
    refine ⟨105856963359330712001142305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70571308906220474667428203 105856963359330712001142305)
    ·
      refine ⟨79392722519498034000856729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105856963359330712001142305 79392722519498034000856729)
      ·
        refine ⟨59544541889623525500642547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79392722519498034000856729 59544541889623525500642547)
        ·
          refine ⟨89316812834435288250963821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59544541889623525500642547 89316812834435288250963821)
          ·
            refine ⟨33493804812913233094111433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89316812834435288250963821 33493804812913233094111433)
            ·
              refine ⟨25120353609684924820583575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33493804812913233094111433 25120353609684924820583575)
              ·
                refine ⟨37680530414527387230875363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25120353609684924820583575 37680530414527387230875363)
                ·
                  refine ⟨56520795621791080846313045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37680530414527387230875363 56520795621791080846313045)
                  ·
                    refine ⟨662353073692864228667731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56520795621791080846313045 662353073692864228667731)
                    ·
                      rfl

theorem cell23_3869784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_3869784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869784 prefixEnd_3869784 := by exact prefixLift 3869784
  have htrace : WordTrace (prefixWord ++ tailWord_3869784) baseStart_3869784 baseEnd_3869784 := by
    simpa [prefixWord, tailWord_3869784, baseEnd_3869784] using wordTrace_append hprefix tailTrace_3869784
  have hstable : (prefixWord ++ tailWord_3869784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869784).length < 2 ^ (prefixWord ++ tailWord_3869784).sum := by decide
  have hdescent : baseEnd_3869784 < baseStart_3869784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869789 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3869789 : Nat := 118140960795 + 3869789 * 2 ^ 59
def prefixEnd_3869789 : Nat := 4983230072969 + 3 ^ 40 * 3869789 * 2
def baseEnd_3869789 : Nat := 1987061788481865166440671

theorem tailTrace_3869789 : CollatzResearch.WordTrace tailWord_3869789 prefixEnd_3869789 1987061788481865166440671 := by
  unfold tailWord_3869789
  simp only [CollatzResearch.WordTrace]
  refine ⟨141142800177422835188788421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94095200118281890125858947 141142800177422835188788421)
  ·
    refine ⟨26464275033266781597897829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141142800177422835188788421 26464275033266781597897829)
    ·
      refine ⟨4962051568737521549605843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26464275033266781597897829 4962051568737521549605843)
      ·
        refine ⟨7443077353106282324408765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962051568737521549605843 7443077353106282324408765)
        ·
          refine ⟨2791154007414855871653287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443077353106282324408765 2791154007414855871653287)
          ·
            refine ⟨4186731011122283807479931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791154007414855871653287 4186731011122283807479931)
            ·
              refine ⟨6280096516683425711219897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186731011122283807479931 6280096516683425711219897)
              ·
                refine ⟨4710072387512569283414923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280096516683425711219897 4710072387512569283414923)
                ·
                  refine ⟨7065108581268853925122385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710072387512569283414923 7065108581268853925122385)
                  ·
                    refine ⟨5298831435951640443841789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065108581268853925122385 5298831435951640443841789)
                    ·
                      refine ⟨1987061788481865166440671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5298831435951640443841789 1987061788481865166440671)
                      ·
                        rfl

theorem cell23_3869789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3869789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869789 prefixEnd_3869789 := by exact prefixLift 3869789
  have htrace : WordTrace (prefixWord ++ tailWord_3869789) baseStart_3869789 baseEnd_3869789 := by
    simpa [prefixWord, tailWord_3869789, baseEnd_3869789] using wordTrace_append hprefix tailTrace_3869789
  have hstable : (prefixWord ++ tailWord_3869789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869789).length < 2 ^ (prefixWord ++ tailWord_3869789).sum := by decide
  have hdescent : baseEnd_3869789 < baseStart_3869789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869808 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2]
def baseStart_3869808 : Nat := 118140960795 + 3869808 * 2 ^ 59
def prefixEnd_3869808 : Nat := 4983230072969 + 3 ^ 40 * 3869808 * 2
def baseEnd_3869808 : Nat := 1987071544614300592103083

theorem tailTrace_3869808 : CollatzResearch.WordTrace tailWord_3869808 prefixEnd_3869808 1987071544614300592103083 := by
  unfold tailWord_3869808
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571746582177000716865039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94095662109569334289153385 70571746582177000716865039)
  ·
    refine ⟨105857619873265501075297559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70571746582177000716865039 105857619873265501075297559)
    ·
      refine ⟨158786429809898251612946339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105857619873265501075297559 158786429809898251612946339)
      ·
        refine ⟨238179644714847377419419509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158786429809898251612946339 238179644714847377419419509)
        ·
          refine ⟨22329341692016941633070579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238179644714847377419419509 22329341692016941633070579)
          ·
            refine ⟨33494012538025412449605869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22329341692016941633070579 33494012538025412449605869)
            ·
              refine ⟨12560254701759529668602201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33494012538025412449605869 12560254701759529668602201)
              ·
                refine ⟨9420191026319647251451651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12560254701759529668602201 9420191026319647251451651)
                ·
                  refine ⟨14130286539479470877177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9420191026319647251451651 14130286539479470877177477)
                  ·
                    refine ⟨2649428726152400789470777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14130286539479470877177477 2649428726152400789470777)
                    ·
                      refine ⟨1987071544614300592103083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649428726152400789470777 1987071544614300592103083)
                      ·
                        rfl

theorem cell23_3869808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 4, 2].length) (baseStart_3869808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869808 prefixEnd_3869808 := by exact prefixLift 3869808
  have htrace : WordTrace (prefixWord ++ tailWord_3869808) baseStart_3869808 baseEnd_3869808 := by
    simpa [prefixWord, tailWord_3869808, baseEnd_3869808] using wordTrace_append hprefix tailTrace_3869808
  have hstable : (prefixWord ++ tailWord_3869808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869808).length < 2 ^ (prefixWord ++ tailWord_3869808).sum := by decide
  have hdescent : baseEnd_3869808 < baseStart_3869808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869821 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3869821 : Nat := 118140960795 + 3869821 * 2 ^ 59
def prefixEnd_3869821 : Nat := 4983230072969 + 3 ^ 40 * 3869821 * 2
def baseEnd_3869821 : Nat := 1987078219862809041240523

theorem tailTrace_3869821 : CollatzResearch.WordTrace tailWord_3869821 prefixEnd_3869821 1987078219862809041240523 := by
  unfold tailWord_3869821
  simp only [CollatzResearch.WordTrace]
  refine ⟨141143967313306904653953317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94095978208871269769302211 141143967313306904653953317)
  ·
    refine ⟨26464493871245044622616247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141143967313306904653953317 26464493871245044622616247)
    ·
      refine ⟨39696740806867566933924371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26464493871245044622616247 39696740806867566933924371)
      ·
        refine ⟨59545111210301350400886557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39696740806867566933924371 59545111210301350400886557)
        ·
          refine ⟨22329416703863006400332459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59545111210301350400886557 22329416703863006400332459)
          ·
            refine ⟨33494125055794509600498689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22329416703863006400332459 33494125055794509600498689)
            ·
              refine ⟨25120593791845882200374017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33494125055794509600498689 25120593791845882200374017)
              ·
                refine ⟨18840445343884411650280513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25120593791845882200374017 18840445343884411650280513)
                ·
                  refine ⟨14130334007913308737710385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18840445343884411650280513 14130334007913308737710385)
                  ·
                    refine ⟨10597750505934981553282789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14130334007913308737710385 10597750505934981553282789)
                    ·
                      refine ⟨1987078219862809041240523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10597750505934981553282789 1987078219862809041240523)
                      ·
                        rfl

theorem cell23_3869821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3869821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869821 prefixEnd_3869821 := by exact prefixLift 3869821
  have htrace : WordTrace (prefixWord ++ tailWord_3869821) baseStart_3869821 baseEnd_3869821 := by
    simpa [prefixWord, tailWord_3869821, baseEnd_3869821] using wordTrace_append hprefix tailTrace_3869821
  have hstable : (prefixWord ++ tailWord_3869821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869821).length < 2 ^ (prefixWord ++ tailWord_3869821).sum := by decide
  have hdescent : baseEnd_3869821 < baseStart_3869821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869824 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3869824 : Nat := 118140960795 + 3869824 * 2 ^ 59
def prefixEnd_3869824 : Nat := 4983230072969 + 3 ^ 40 * 3869824 * 2
def baseEnd_3869824 : Nat := 1987079760304772529503009

theorem tailTrace_3869824 : CollatzResearch.WordTrace tailWord_3869824 prefixEnd_3869824 1987079760304772529503009 := by
  unfold tailWord_3869824
  simp only [CollatzResearch.WordTrace]
  refine ⟨70572038366148018083156263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94096051154864024110875017 70572038366148018083156263)
  ·
    refine ⟨105858057549222027124734395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70572038366148018083156263 105858057549222027124734395)
    ·
      refine ⟨158787086323833040687101593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105858057549222027124734395 158787086323833040687101593)
      ·
        refine ⟨119090314742874780515326195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158787086323833040687101593 119090314742874780515326195)
        ·
          refine ⟨178635472114312170772989293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119090314742874780515326195 178635472114312170772989293)
          ·
            refine ⟨66988302042867064039870985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178635472114312170772989293 66988302042867064039870985)
            ·
              refine ⟨50241226532150298029903239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66988302042867064039870985 50241226532150298029903239)
              ·
                refine ⟨75361839798225447044854859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50241226532150298029903239 75361839798225447044854859)
                ·
                  refine ⟨113042759697338170567282289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75361839798225447044854859 113042759697338170567282289)
                  ·
                    refine ⟨84782069773003627925461717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113042759697338170567282289 84782069773003627925461717)
                    ·
                      refine ⟨1987079760304772529503009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84782069773003627925461717 1987079760304772529503009)
                      ·
                        rfl

theorem cell23_3869824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3869824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869824 prefixEnd_3869824 := by exact prefixLift 3869824
  have htrace : WordTrace (prefixWord ++ tailWord_3869824) baseStart_3869824 baseEnd_3869824 := by
    simpa [prefixWord, tailWord_3869824, baseEnd_3869824] using wordTrace_append hprefix tailTrace_3869824
  have hstable : (prefixWord ++ tailWord_3869824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869824).length < 2 ^ (prefixWord ++ tailWord_3869824).sum := by decide
  have hdescent : baseEnd_3869824 < baseStart_3869824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869838 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3869838 : Nat := 118140960795 + 3869838 * 2 ^ 59
def prefixEnd_3869838 : Nat := 4983230072969 + 3 ^ 40 * 3869838 * 2
def baseEnd_3869838 : Nat := 1987086949033935474727945

theorem tailTrace_3869838 : CollatzResearch.WordTrace tailWord_3869838 prefixEnd_3869838 1987086949033935474727945 := by
  unfold tailWord_3869838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643073419280664569665271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94096391569496877704881445 17643073419280664569665271)
  ·
    refine ⟨26464610128920996854497907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17643073419280664569665271 26464610128920996854497907)
    ·
      refine ⟨39696915193381495281746861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26464610128920996854497907 39696915193381495281746861)
      ·
        refine ⟨14886343197518060730655073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39696915193381495281746861 14886343197518060730655073)
        ·
          refine ⟨11164757398138545547991305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14886343197518060730655073 11164757398138545547991305)
          ·
            refine ⟨8373568048603909160993479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164757398138545547991305 8373568048603909160993479)
            ·
              refine ⟨12560352072905863741490219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373568048603909160993479 12560352072905863741490219)
              ·
                refine ⟨18840528109358795612235329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560352072905863741490219 18840528109358795612235329)
                ·
                  refine ⟨14130396082019096709176497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18840528109358795612235329 14130396082019096709176497)
                  ·
                    refine ⟨10597797061514322531882373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14130396082019096709176497 10597797061514322531882373)
                    ·
                      refine ⟨1987086949033935474727945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10597797061514322531882373 1987086949033935474727945)
                      ·
                        rfl

theorem cell23_3869838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3869838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869838 prefixEnd_3869838 := by exact prefixLift 3869838
  have htrace : WordTrace (prefixWord ++ tailWord_3869838) baseStart_3869838 baseEnd_3869838 := by
    simpa [prefixWord, tailWord_3869838, baseEnd_3869838] using wordTrace_append hprefix tailTrace_3869838
  have hstable : (prefixWord ++ tailWord_3869838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869838).length < 2 ^ (prefixWord ++ tailWord_3869838).sum := by decide
  have hdescent : baseEnd_3869838 < baseStart_3869838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869842 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3869842 : Nat := 118140960795 + 3869842 * 2 ^ 59
def prefixEnd_3869842 : Nat := 4983230072969 + 3 ^ 40 * 3869842 * 2
def baseEnd_3869842 : Nat := 1987089002956553459077927

theorem tailTrace_3869842 : CollatzResearch.WordTrace tailWord_3869842 prefixEnd_3869842 1987089002956553459077927 := by
  unfold tailWord_3869842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35286183311557706310116945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94096488830820550160311853 35286183311557706310116945)
  ·
    refine ⟨26464637483668279732587709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35286183311557706310116945 26464637483668279732587709)
    ·
      refine ⟨9924239056375604899720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26464637483668279732587709 9924239056375604899720391)
      ·
        refine ⟨14886358584563407349580587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924239056375604899720391 14886358584563407349580587)
        ·
          refine ⟨22329537876845111024370881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886358584563407349580587 22329537876845111024370881)
          ·
            refine ⟨16747153407633833268278161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22329537876845111024370881 16747153407633833268278161)
            ·
              refine ⟨12560365055725374951208621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16747153407633833268278161 12560365055725374951208621)
              ·
                refine ⟨4710136895897015606703233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560365055725374951208621 4710136895897015606703233)
                ·
                  refine ⟨3532602671922761705027425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710136895897015606703233 3532602671922761705027425)
                  ·
                    refine ⟨2649452003942071278770569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532602671922761705027425 2649452003942071278770569)
                    ·
                      refine ⟨1987089002956553459077927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649452003942071278770569 1987089002956553459077927)
                      ·
                        rfl

theorem cell23_3869842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3869842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869842 prefixEnd_3869842 := by exact prefixLift 3869842
  have htrace : WordTrace (prefixWord ++ tailWord_3869842) baseStart_3869842 baseEnd_3869842 := by
    simpa [prefixWord, tailWord_3869842, baseEnd_3869842] using wordTrace_append hprefix tailTrace_3869842
  have hstable : (prefixWord ++ tailWord_3869842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869842).length < 2 ^ (prefixWord ++ tailWord_3869842).sum := by decide
  have hdescent : baseEnd_3869842 < baseStart_3869842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869861 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3869861 : Nat := 118140960795 + 3869861 * 2 ^ 59
def prefixEnd_3869861 : Nat := 4983230072969 + 3 ^ 40 * 3869861 * 2
def baseEnd_3869861 : Nat := 662366253029662961580113

theorem tailTrace_3869861 : CollatzResearch.WordTrace tailWord_3869861 prefixEnd_3869861 662366253029662961580113 := by
  unfold tailWord_3869861
  simp only [CollatzResearch.WordTrace]
  refine ⟨141145426233161991485409437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94096950822107994323606291 141145426233161991485409437)
  ·
    refine ⟨52929534837435746807028539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141145426233161991485409437 52929534837435746807028539)
    ·
      refine ⟨79394302256153620210542809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52929534837435746807028539 79394302256153620210542809)
      ·
        refine ⟨59545726692115215157907107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79394302256153620210542809 59545726692115215157907107)
        ·
          refine ⟨89318590038172822736860661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59545726692115215157907107 89318590038172822736860661)
          ·
            refine ⟨8373617816078702131580687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89318590038172822736860661 8373617816078702131580687)
            ·
              refine ⟨12560426724118053197371031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373617816078702131580687 12560426724118053197371031)
              ·
                refine ⟨18840640086177079796056547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560426724118053197371031 18840640086177079796056547)
                ·
                  refine ⟨28260960129265619694084821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18840640086177079796056547 28260960129265619694084821)
                  ·
                    refine ⟨662366253029662961580113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28260960129265619694084821 662366253029662961580113)
                    ·
                      rfl

theorem cell23_3869861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3869861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869861 prefixEnd_3869861 := by exact prefixLift 3869861
  have htrace : WordTrace (prefixWord ++ tailWord_3869861) baseStart_3869861 baseEnd_3869861 := by
    simpa [prefixWord, tailWord_3869861, baseEnd_3869861] using wordTrace_append hprefix tailTrace_3869861
  have hstable : (prefixWord ++ tailWord_3869861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869861).length < 2 ^ (prefixWord ++ tailWord_3869861).sum := by decide
  have hdescent : baseEnd_3869861 < baseStart_3869861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869921 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 8]
def baseStart_3869921 : Nat := 118140960795 + 3869921 * 2 ^ 59
def prefixEnd_3869921 : Nat := 4983230072969 + 3 ^ 40 * 3869921 * 2
def baseEnd_3869921 : Nat := 220792174214250961110007

theorem tailTrace_3869921 : CollatzResearch.WordTrace tailWord_3869921 prefixEnd_3869921 220792174214250961110007 := by
  unfold tailWord_3869921
  simp only [CollatzResearch.WordTrace]
  refine ⟨141147614612944621732593617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94098409741963081155062411 141147614612944621732593617)
  ·
    refine ⟨105860710959708466299445213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141147614612944621732593617 105860710959708466299445213)
    ·
      refine ⟨39697766609890674862291955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105860710959708466299445213 39697766609890674862291955)
      ·
        refine ⟨59546649914836012293437933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39697766609890674862291955 59546649914836012293437933)
        ·
          refine ⟨22329993718063504610039225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59546649914836012293437933 22329993718063504610039225)
          ·
            refine ⟨16747495288547628457529419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22329993718063504610039225 16747495288547628457529419)
            ·
              refine ⟨25121242932821442686294129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747495288547628457529419 25121242932821442686294129)
              ·
                refine ⟨18840932199616082014720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25121242932821442686294129 18840932199616082014720597)
                ·
                  refine ⟨220792174214250961110007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18840932199616082014720597 220792174214250961110007)
                  ·
                    rfl

theorem cell23_3869921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_3869921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869921 prefixEnd_3869921 := by exact prefixLift 3869921
  have htrace : WordTrace (prefixWord ++ tailWord_3869921) baseStart_3869921 baseEnd_3869921 := by
    simpa [prefixWord, tailWord_3869921, baseEnd_3869921] using wordTrace_append hprefix tailTrace_3869921
  have hstable : (prefixWord ++ tailWord_3869921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869921).length < 2 ^ (prefixWord ++ tailWord_3869921).sum := by decide
  have hdescent : baseEnd_3869921 < baseStart_3869921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869935 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_3869935 : Nat := 118140960795 + 3869935 * 2 ^ 59
def prefixEnd_3869935 : Nat := 4983230072969 + 3 ^ 40 * 3869935 * 2
def baseEnd_3869935 : Nat := 1987136756657421595214999

theorem tailTrace_3869935 : CollatzResearch.WordTrace tailWord_3869935 prefixEnd_3869935 1987136756657421595214999 := by
  unfold tailWord_3869935
  simp only [CollatzResearch.WordTrace]
  refine ⟨141148125234893902123603259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94098750156595934749068839 141148125234893902123603259)
  ·
    refine ⟨211722187852340853185404889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141148125234893902123603259 211722187852340853185404889)
    ·
      refine ⟨158791640889255639889053667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211722187852340853185404889 158791640889255639889053667)
      ·
        refine ⟨238187461333883459833580501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158791640889255639889053667 238187461333883459833580501)
        ·
          refine ⟨5582518625012893589849543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238187461333883459833580501 5582518625012893589849543)
          ·
            refine ⟨8373777937519340384774315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582518625012893589849543 8373777937519340384774315)
            ·
              refine ⟨12560666906279010577161473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373777937519340384774315 12560666906279010577161473)
              ·
                refine ⟨9420500179709257932871105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12560666906279010577161473 9420500179709257932871105)
                ·
                  refine ⟨7065375134781943449653329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420500179709257932871105 7065375134781943449653329)
                  ·
                    refine ⟨5299031351086457587239997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065375134781943449653329 5299031351086457587239997)
                    ·
                      refine ⟨1987136756657421595214999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299031351086457587239997 1987136756657421595214999)
                      ·
                        rfl

theorem cell23_3869935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_3869935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869935 prefixEnd_3869935 := by exact prefixLift 3869935
  have htrace : WordTrace (prefixWord ++ tailWord_3869935) baseStart_3869935 baseEnd_3869935 := by
    simpa [prefixWord, tailWord_3869935, baseEnd_3869935] using wordTrace_append hprefix tailTrace_3869935
  have hstable : (prefixWord ++ tailWord_3869935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869935).length < 2 ^ (prefixWord ++ tailWord_3869935).sum := by decide
  have hdescent : baseEnd_3869935 < baseStart_3869935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869955 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 6]
def baseStart_3869955 : Nat := 118140960795 + 3869955 * 2 ^ 59
def prefixEnd_3869955 : Nat := 4983230072969 + 3 ^ 40 * 3869955 * 2
def baseEnd_3869955 : Nat := 220794114030056835218323

theorem tailTrace_3869955 : CollatzResearch.WordTrace tailWord_3869955 prefixEnd_3869955 220794114030056835218323 := by
  unfold tailWord_3869955
  simp only [CollatzResearch.WordTrace]
  refine ⟨141148854694821445539331319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94099236463214297026220879 141148854694821445539331319)
  ·
    refine ⟨211723282042232168308996979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141148854694821445539331319 211723282042232168308996979)
    ·
      refine ⟨317584923063348252463495469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211723282042232168308996979 317584923063348252463495469)
      ·
        refine ⟨119094346148755594673810801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317584923063348252463495469 119094346148755594673810801)
        ·
          refine ⟨89320759611566696005358101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119094346148755594673810801 89320759611566696005358101)
          ·
            refine ⟨4186910606792188875251161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89320759611566696005358101 4186910606792188875251161)
            ·
              refine ⟨3140182955094141656438371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186910606792188875251161 3140182955094141656438371)
              ·
                refine ⟨4710274432641212484657557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140182955094141656438371 4710274432641212484657557)
                ·
                  refine ⟨220794114030056835218323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4710274432641212484657557 220794114030056835218323)
                  ·
                    rfl

theorem cell23_3869955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 6].length) (baseStart_3869955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869955 prefixEnd_3869955 := by exact prefixLift 3869955
  have htrace : WordTrace (prefixWord ++ tailWord_3869955) baseStart_3869955 baseEnd_3869955 := by
    simpa [prefixWord, tailWord_3869955, baseEnd_3869955] using wordTrace_append hprefix tailTrace_3869955
  have hstable : (prefixWord ++ tailWord_3869955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869955).length < 2 ^ (prefixWord ++ tailWord_3869955).sum := by decide
  have hdescent : baseEnd_3869955 < baseStart_3869955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869992 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3869992 : Nat := 118140960795 + 3869992 * 2 ^ 59
def prefixEnd_3869992 : Nat := 4983230072969 + 3 ^ 40 * 3869992 * 2
def baseEnd_3869992 : Nat := 1987166025054727872202237

theorem tailTrace_3869992 : CollatzResearch.WordTrace tailWord_3869992 prefixEnd_3869992 1987166025054727872202237 := by
  unfold tailWord_3869992
  simp only [CollatzResearch.WordTrace]
  refine ⟨70575102097843700429214115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94100136130458267238952153 70575102097843700429214115)
  ·
    refine ⟨105862653146765550643821173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70575102097843700429214115 105862653146765550643821173)
    ·
      refine ⟨9924623732509270372858235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105862653146765550643821173 9924623732509270372858235)
      ·
        refine ⟨14886935598763905559287353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924623732509270372858235 14886935598763905559287353)
        ·
          refine ⟨11165201699072929169465515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14886935598763905559287353 11165201699072929169465515)
          ·
            refine ⟨16747802548609393754198273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165201699072929169465515 16747802548609393754198273)
            ·
              refine ⟨12560851911457045315648705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16747802548609393754198273 12560851911457045315648705)
              ·
                refine ⟨9420638933592783986736529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12560851911457045315648705 9420638933592783986736529)
                ·
                  refine ⟨7065479200194587990052397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420638933592783986736529 7065479200194587990052397)
                  ·
                    refine ⟨2649554700072970496269649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7065479200194587990052397 2649554700072970496269649)
                    ·
                      refine ⟨1987166025054727872202237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649554700072970496269649 1987166025054727872202237)
                      ·
                        rfl

theorem cell23_3869992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3869992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3869992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3869992 prefixEnd_3869992 := by exact prefixLift 3869992
  have htrace : WordTrace (prefixWord ++ tailWord_3869992) baseStart_3869992 baseEnd_3869992 := by
    simpa [prefixWord, tailWord_3869992, baseEnd_3869992] using wordTrace_append hprefix tailTrace_3869992
  have hstable : (prefixWord ++ tailWord_3869992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869992).length < 2 ^ (prefixWord ++ tailWord_3869992).sum := by decide
  have hdescent : baseEnd_3869992 < baseStart_3869992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870015 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 2, 4]
def baseStart_3870015 : Nat := 118140960795 + 3870015 * 2 ^ 59
def prefixEnd_3870015 : Nat := 4983230072969 + 3 ^ 40 * 3870015 * 2
def baseEnd_3870015 : Nat := 662392611703260427404877

theorem tailTrace_3870015 : CollatzResearch.WordTrace tailWord_3870015 prefixEnd_3870015 662392611703260427404877 := by
  unfold tailWord_3870015
  simp only [CollatzResearch.WordTrace]
  refine ⟨141151043074604075786515499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94100695383069383857676999 141151043074604075786515499)
  ·
    refine ⟨211726564611906113679773249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141151043074604075786515499 211726564611906113679773249)
    ·
      refine ⟨158794923458929585259829937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211726564611906113679773249 158794923458929585259829937)
      ·
        refine ⟨119096192594197188944872453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158794923458929585259829937 119096192594197188944872453)
        ·
          refine ⟨22330536111411972927163585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119096192594197188944872453 22330536111411972927163585)
          ·
            refine ⟨16747902083558979695372689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22330536111411972927163585 16747902083558979695372689)
            ·
              refine ⟨12560926562669234771529517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16747902083558979695372689 12560926562669234771529517)
              ·
                refine ⟨4710347461000963039323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560926562669234771529517 4710347461000963039323569)
                ·
                  refine ⟨3532760595750722279492677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710347461000963039323569 3532760595750722279492677)
                  ·
                    refine ⟨662392611703260427404877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3532760595750722279492677 662392611703260427404877)
                    ·
                      rfl

theorem cell23_3870015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_3870015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870015 prefixEnd_3870015 := by exact prefixLift 3870015
  have htrace : WordTrace (prefixWord ++ tailWord_3870015) baseStart_3870015 baseEnd_3870015 := by
    simpa [prefixWord, tailWord_3870015, baseEnd_3870015] using wordTrace_append hprefix tailTrace_3870015
  have hstable : (prefixWord ++ tailWord_3870015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870015).length < 2 ^ (prefixWord ++ tailWord_3870015).sum := by decide
  have hdescent : baseEnd_3870015 < baseStart_3870015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3870021 : Nat := 118140960795 + 3870021 * 2 ^ 59
def prefixEnd_3870021 : Nat := 4983230072969 + 3 ^ 40 * 3870021 * 2
def baseEnd_3870021 : Nat := 1987180915993708258739603

theorem tailTrace_3870021 : CollatzResearch.WordTrace tailWord_3870021 prefixEnd_3870021 1987180915993708258739603 := by
  unfold tailWord_3870021
  simp only [CollatzResearch.WordTrace]
  refine ⟨141151261912582338811233917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94100841275054892540822611 141151261912582338811233917)
  ·
    refine ⟨52931723217218377054212719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141151261912582338811233917 52931723217218377054212719)
    ·
      refine ⟨79397584825827565581319079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52931723217218377054212719 79397584825827565581319079)
      ·
        refine ⟨119096377238741348371978619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79397584825827565581319079 119096377238741348371978619)
        ·
          refine ⟨178644565858112022557967929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119096377238741348371978619 178644565858112022557967929)
          ·
            refine ⟨133983424393584016918475947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178644565858112022557967929 133983424393584016918475947)
            ·
              refine ⟨200975136590376025377713921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133983424393584016918475947 200975136590376025377713921)
              ·
                refine ⟨150731352442782019033285441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200975136590376025377713921 150731352442782019033285441)
                ·
                  refine ⟨113048514332086514274964081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150731352442782019033285441 113048514332086514274964081)
                  ·
                    refine ⟨84786385749064885706223061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113048514332086514274964081 84786385749064885706223061)
                    ·
                      refine ⟨1987180915993708258739603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84786385749064885706223061 1987180915993708258739603)
                      ·
                        rfl

theorem cell23_3870021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3870021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870021 prefixEnd_3870021 := by exact prefixLift 3870021
  have htrace : WordTrace (prefixWord ++ tailWord_3870021) baseStart_3870021 baseEnd_3870021 := by
    simpa [prefixWord, tailWord_3870021, baseEnd_3870021] using wordTrace_append hprefix tailTrace_3870021
  have hstable : (prefixWord ++ tailWord_3870021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870021).length < 2 ^ (prefixWord ++ tailWord_3870021).sum := by decide
  have hdescent : baseEnd_3870021 < baseStart_3870021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870031 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_3870031 : Nat := 118140960795 + 3870031 * 2 ^ 59
def prefixEnd_3870031 : Nat := 4983230072969 + 3 ^ 40 * 3870031 * 2
def baseEnd_3870031 : Nat := 1987186050800253219614557

theorem tailTrace_3870031 : CollatzResearch.WordTrace tailWord_3870031 prefixEnd_3870031 1987186050800253219614557 := by
  unfold tailWord_3870031
  simp only [CollatzResearch.WordTrace]
  refine ⟨141151626642546110519097947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94101084428364073679398631 141151626642546110519097947)
  ·
    refine ⟨211727439963819165778646921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141151626642546110519097947 211727439963819165778646921)
    ·
      refine ⟨158795579972864374333985191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211727439963819165778646921 158795579972864374333985191)
      ·
        refine ⟨238193369959296561500977787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158795579972864374333985191 238193369959296561500977787)
        ·
          refine ⟨357290054938944842251466681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238193369959296561500977787 357290054938944842251466681)
          ·
            refine ⟨267967541204208631688600011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357290054938944842251466681 267967541204208631688600011)
            ·
              refine ⟨401951311806312947532900017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267967541204208631688600011 401951311806312947532900017)
              ·
                refine ⟨301463483854734710649675013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401951311806312947532900017 301463483854734710649675013)
                ·
                  refine ⟨56524403222762758246814065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301463483854734710649675013 56524403222762758246814065)
                  ·
                    refine ⟨42393302417072068685110549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56524403222762758246814065 42393302417072068685110549)
                    ·
                      refine ⟨1987186050800253219614557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42393302417072068685110549 1987186050800253219614557)
                      ·
                        rfl

theorem cell23_3870031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_3870031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870031 prefixEnd_3870031 := by exact prefixLift 3870031
  have htrace : WordTrace (prefixWord ++ tailWord_3870031) baseStart_3870031 baseEnd_3870031 := by
    simpa [prefixWord, tailWord_3870031, baseEnd_3870031] using wordTrace_append hprefix tailTrace_3870031
  have hstable : (prefixWord ++ tailWord_3870031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870031).length < 2 ^ (prefixWord ++ tailWord_3870031).sum := by decide
  have hdescent : baseEnd_3870031 < baseStart_3870031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870039 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_3870039 : Nat := 118140960795 + 3870039 * 2 ^ 59
def prefixEnd_3870039 : Nat := 4983230072969 + 3 ^ 40 * 3870039 * 2
def baseEnd_3870039 : Nat := 1987190158645489188314521

theorem tailTrace_3870039 : CollatzResearch.WordTrace tailWord_3870039 prefixEnd_3870039 1987190158645489188314521 := by
  unfold tailWord_3870039
  simp only [CollatzResearch.WordTrace]
  refine ⟨141151918426517127885389171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94101278951011418590259447 141151918426517127885389171)
  ·
    refine ⟨211727877639775691828083757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141151918426517127885389171 211727877639775691828083757)
    ·
      refine ⟨79397954114915884435531409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211727877639775691828083757 79397954114915884435531409)
      ·
        refine ⟨59548465586186913326648557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79397954114915884435531409 59548465586186913326648557)
        ·
          refine ⟨22330674594820092497493209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59548465586186913326648557 22330674594820092497493209)
          ·
            refine ⟨16748005946115069373119907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22330674594820092497493209 16748005946115069373119907)
            ·
              refine ⟨25122008919172604059679861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16748005946115069373119907 25122008919172604059679861)
              ·
                refine ⟨2355188336172431630594987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25122008919172604059679861 2355188336172431630594987)
                ·
                  refine ⟨3532782504258647445892481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355188336172431630594987 3532782504258647445892481)
                  ·
                    refine ⟨2649586878193985584419361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532782504258647445892481 2649586878193985584419361)
                    ·
                      refine ⟨1987190158645489188314521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649586878193985584419361 1987190158645489188314521)
                      ·
                        rfl

theorem cell23_3870039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_3870039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870039 prefixEnd_3870039 := by exact prefixLift 3870039
  have htrace : WordTrace (prefixWord ++ tailWord_3870039) baseStart_3870039 baseEnd_3870039 := by
    simpa [prefixWord, tailWord_3870039, baseEnd_3870039] using wordTrace_append hprefix tailTrace_3870039
  have hstable : (prefixWord ++ tailWord_3870039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870039).length < 2 ^ (prefixWord ++ tailWord_3870039).sum := by decide
  have hdescent : baseEnd_3870039 < baseStart_3870039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870042 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_3870042 : Nat := 118140960795 + 3870042 * 2 ^ 59
def prefixEnd_3870042 : Nat := 4983230072969 + 3 ^ 40 * 3870042 * 2
def baseEnd_3870042 : Nat := 1987191699087452676577007

theorem tailTrace_3870042 : CollatzResearch.WordTrace tailWord_3870042 prefixEnd_3870042 1987191699087452676577007 := by
  unfold tailWord_3870042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35288006961376564849437095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94101351897004172931832253 35288006961376564849437095)
  ·
    refine ⟨52932010442064847274155643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35288006961376564849437095 52932010442064847274155643)
    ·
      refine ⟨79398015663097270911233465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52932010442064847274155643 79398015663097270911233465)
      ·
        refine ⟨59548511747322953183425099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79398015663097270911233465 59548511747322953183425099)
        ·
          refine ⟨89322767620984429775137649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59548511747322953183425099 89322767620984429775137649)
          ·
            refine ⟨66992075715738322331353237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89322767620984429775137649 66992075715738322331353237)
            ·
              refine ⟨3140253549175233859282183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66992075715738322331353237 3140253549175233859282183)
              ·
                refine ⟨4710380323762850788923275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140253549175233859282183 4710380323762850788923275)
                ·
                  refine ⟨7065570485644276183384913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710380323762850788923275 7065570485644276183384913)
                  ·
                    refine ⟨5299177864233207137538685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065570485644276183384913 5299177864233207137538685)
                    ·
                      refine ⟨1987191699087452676577007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299177864233207137538685 1987191699087452676577007)
                      ·
                        rfl

theorem cell23_3870042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_3870042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870042 prefixEnd_3870042 := by exact prefixLift 3870042
  have htrace : WordTrace (prefixWord ++ tailWord_3870042) baseStart_3870042 baseEnd_3870042 := by
    simpa [prefixWord, tailWord_3870042, baseEnd_3870042] using wordTrace_append hprefix tailTrace_3870042
  have hstable : (prefixWord ++ tailWord_3870042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870042).length < 2 ^ (prefixWord ++ tailWord_3870042).sum := by decide
  have hdescent : baseEnd_3870042 < baseStart_3870042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870065 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_3870065 : Nat := 118140960795 + 3870065 * 2 ^ 59
def prefixEnd_3870065 : Nat := 4983230072969 + 3 ^ 40 * 3870065 * 2
def baseEnd_3870065 : Nat := 1987203509142506086589401

theorem tailTrace_3870065 : CollatzResearch.WordTrace tailWord_3870065 prefixEnd_3870065 1987203509142506086589401 := by
  unfold tailWord_3870065
  simp only [CollatzResearch.WordTrace]
  refine ⟨141152866724422934325835649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94101911149615289550557099 141152866724422934325835649)
  ·
    refine ⟨105864650043317200744376737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141152866724422934325835649 105864650043317200744376737)
    ·
      refine ⟨79398487532487900558282553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105864650043317200744376737 79398487532487900558282553)
      ·
        refine ⟨59548865649365925418711915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79398487532487900558282553 59548865649365925418711915)
        ·
          refine ⟨89323298474048888128067873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59548865649365925418711915 89323298474048888128067873)
          ·
            refine ⟨66992473855536666096050905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89323298474048888128067873 66992473855536666096050905)
            ·
              refine ⟨50244355391652499572038179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66992473855536666096050905 50244355391652499572038179)
              ·
                refine ⟨75366533087478749358057269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50244355391652499572038179 75366533087478749358057269)
                ·
                  refine ⟨7065612476951132752317869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75366533087478749358057269 7065612476951132752317869)
                  ·
                    refine ⟨2649604678856674782119201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7065612476951132752317869 2649604678856674782119201)
                    ·
                      refine ⟨1987203509142506086589401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649604678856674782119201 1987203509142506086589401)
                      ·
                        rfl

theorem cell23_3870065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_3870065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870065 prefixEnd_3870065 := by exact prefixLift 3870065
  have htrace : WordTrace (prefixWord ++ tailWord_3870065) baseStart_3870065 baseEnd_3870065 := by
    simpa [prefixWord, tailWord_3870065, baseEnd_3870065] using wordTrace_append hprefix tailTrace_3870065
  have hstable : (prefixWord ++ tailWord_3870065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870065).length < 2 ^ (prefixWord ++ tailWord_3870065).sum := by decide
  have hdescent : baseEnd_3870065 < baseStart_3870065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870069 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3870069 : Nat := 118140960795 + 3870069 * 2 ^ 59
def prefixEnd_3870069 : Nat := 4983230072969 + 3 ^ 40 * 3870069 * 2
def baseEnd_3870069 : Nat := 1987205563065124070939383

theorem tailTrace_3870069 : CollatzResearch.WordTrace tailWord_3870069 prefixEnd_3870069 1987205563065124070939383 := by
  unfold tailWord_3870069
  simp only [CollatzResearch.WordTrace]
  refine ⟨141153012616408443008981261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94102008410938962005987507 141153012616408443008981261)
  ·
    refine ⟨52932379731153166128367973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141153012616408443008981261 52932379731153166128367973)
    ·
      refine ⟨9924821199591218649068995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52932379731153166128367973 9924821199591218649068995)
      ·
        refine ⟨14887231799386827973603493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924821199591218649068995 14887231799386827973603493)
        ·
          refine ⟨2791355962385030245050655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14887231799386827973603493 2791355962385030245050655)
          ·
            refine ⟨4187033943577545367575983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791355962385030245050655 4187033943577545367575983)
            ·
              refine ⟨6280550915366318051363975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187033943577545367575983 6280550915366318051363975)
              ·
                refine ⟨9420826373049477077045963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280550915366318051363975 9420826373049477077045963)
                ·
                  refine ⟨14131239559574215615568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9420826373049477077045963 14131239559574215615568945)
                  ·
                    refine ⟨10598429669680661711676709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14131239559574215615568945 10598429669680661711676709)
                    ·
                      refine ⟨1987205563065124070939383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10598429669680661711676709 1987205563065124070939383)
                      ·
                        rfl

theorem cell23_3870069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3870069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870069 prefixEnd_3870069 := by exact prefixLift 3870069
  have htrace : WordTrace (prefixWord ++ tailWord_3870069) baseStart_3870069 baseEnd_3870069 := by
    simpa [prefixWord, tailWord_3870069, baseEnd_3870069] using wordTrace_append hprefix tailTrace_3870069
  have hstable : (prefixWord ++ tailWord_3870069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870069).length < 2 ^ (prefixWord ++ tailWord_3870069).sum := by decide
  have hdescent : baseEnd_3870069 < baseStart_3870069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870112 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2]
def baseStart_3870112 : Nat := 118140960795 + 3870112 * 2 ^ 59
def prefixEnd_3870112 : Nat := 4983230072969 + 3 ^ 40 * 3870112 * 2
def baseEnd_3870112 : Nat := 1987227642733267402701685

theorem tailTrace_3870112 : CollatzResearch.WordTrace tailWord_3870112 prefixEnd_3870112 1987227642733267402701685 := by
  unfold tailWord_3870112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70577290477626330676398295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94103053970168440901864393 70577290477626330676398295)
  ·
    refine ⟨105865935716439496014597443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70577290477626330676398295 105865935716439496014597443)
    ·
      refine ⟨158798903574659244021896165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105865935716439496014597443 158798903574659244021896165)
      ·
        refine ⟨29774794420248608254105531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158798903574659244021896165 29774794420248608254105531)
        ·
          refine ⟨44662191630372912381158297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29774794420248608254105531 44662191630372912381158297)
          ·
            refine ⟨33496643722779684285868723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44662191630372912381158297 33496643722779684285868723)
            ·
              refine ⟨50244965584169526428803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33496643722779684285868723 50244965584169526428803085)
              ·
                refine ⟨18841862094063572410801157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50244965584169526428803085 18841862094063572410801157)
                ·
                  refine ⟨3532849142636919827025217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18841862094063572410801157 3532849142636919827025217)
                  ·
                    refine ⟨2649636856977689870268913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532849142636919827025217 2649636856977689870268913)
                    ·
                      refine ⟨1987227642733267402701685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649636856977689870268913 1987227642733267402701685)
                      ·
                        rfl

theorem cell23_3870112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_3870112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870112 prefixEnd_3870112 := by exact prefixLift 3870112
  have htrace : WordTrace (prefixWord ++ tailWord_3870112) baseStart_3870112 baseEnd_3870112 := by
    simpa [prefixWord, tailWord_3870112, baseEnd_3870112] using wordTrace_append hprefix tailTrace_3870112
  have hstable : (prefixWord ++ tailWord_3870112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870112).length < 2 ^ (prefixWord ++ tailWord_3870112).sum := by decide
  have hdescent : baseEnd_3870112 < baseStart_3870112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870129 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3870129 : Nat := 118140960795 + 3870129 * 2 ^ 59
def prefixEnd_3870129 : Nat := 4983230072969 + 3 ^ 40 * 3870129 * 2
def baseEnd_3870129 : Nat := 1987236371904393836189107

theorem tailTrace_3870129 : CollatzResearch.WordTrace tailWord_3870129 prefixEnd_3870129 1987236371904393836189107 := by
  unfold tailWord_3870129
  simp only [CollatzResearch.WordTrace]
  refine ⟨141155200996191073256165441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94103467330794048837443627 141155200996191073256165441)
  ·
    refine ⟨105866400747143304942124081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141155200996191073256165441 105866400747143304942124081)
    ·
      refine ⟨79399800560357478706593061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105866400747143304942124081 79399800560357478706593061)
      ·
        refine ⟨14887462605067027257486199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79399800560357478706593061 14887462605067027257486199)
        ·
          refine ⟨22331193907600540886229299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887462605067027257486199 22331193907600540886229299)
          ·
            refine ⟨33496790861400811329343949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22331193907600540886229299 33496790861400811329343949)
            ·
              refine ⟨12561296573025304248503981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33496790861400811329343949 12561296573025304248503981)
              ·
                refine ⟨4710486214884489093188993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12561296573025304248503981 4710486214884489093188993)
                ·
                  refine ⟨3532864661163366819891745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710486214884489093188993 3532864661163366819891745)
                  ·
                    refine ⟨2649648495872525114918809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532864661163366819891745 2649648495872525114918809)
                    ·
                      refine ⟨1987236371904393836189107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649648495872525114918809 1987236371904393836189107)
                      ·
                        rfl

theorem cell23_3870129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3870129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870129 prefixEnd_3870129 := by exact prefixLift 3870129
  have htrace : WordTrace (prefixWord ++ tailWord_3870129) baseStart_3870129 baseEnd_3870129 := by
    simpa [prefixWord, tailWord_3870129, baseEnd_3870129] using wordTrace_append hprefix tailTrace_3870129
  have hstable : (prefixWord ++ tailWord_3870129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870129).length < 2 ^ (prefixWord ++ tailWord_3870129).sum := by decide
  have hdescent : baseEnd_3870129 < baseStart_3870129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870165 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3870165 : Nat := 118140960795 + 3870165 * 2 ^ 59
def prefixEnd_3870165 : Nat := 4983230072969 + 3 ^ 40 * 3870165 * 2
def baseEnd_3870165 : Nat := 662418285735985231779647

theorem tailTrace_3870165 : CollatzResearch.WordTrace tailWord_3870165 prefixEnd_3870165 662418285735985231779647 := by
  unfold tailWord_3870165
  simp only [CollatzResearch.WordTrace]
  refine ⟨141156514024060651404475949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94104342682707100936317299 141156514024060651404475949)
  ·
    refine ⟨52933692759022744276678481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141156514024060651404475949 52933692759022744276678481)
    ·
      refine ⟨39700269569267058207508861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52933692759022744276678481 39700269569267058207508861)
      ·
        refine ⟨14887601088475146827815823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39700269569267058207508861 14887601088475146827815823)
        ·
          refine ⟨22331401632712720241723735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887601088475146827815823 22331401632712720241723735)
          ·
            refine ⟨33497102449069080362585603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22331401632712720241723735 33497102449069080362585603)
            ·
              refine ⟨50245653673603620543878405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33497102449069080362585603 50245653673603620543878405)
              ·
                refine ⟨9421060063800678851977201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50245653673603620543878405 9421060063800678851977201)
                ·
                  refine ⟨7065795047850509138982901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421060063800678851977201 7065795047850509138982901)
                  ·
                    refine ⟨662418285735985231779647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7065795047850509138982901 662418285735985231779647)
                    ·
                      rfl

theorem cell23_3870165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3870165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870165 prefixEnd_3870165 := by exact prefixLift 3870165
  have htrace : WordTrace (prefixWord ++ tailWord_3870165) baseStart_3870165 baseEnd_3870165 := by
    simpa [prefixWord, tailWord_3870165, baseEnd_3870165] using wordTrace_append hprefix tailTrace_3870165
  have hstable : (prefixWord ++ tailWord_3870165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870165).length < 2 ^ (prefixWord ++ tailWord_3870165).sum := by decide
  have hdescent : baseEnd_3870165 < baseStart_3870165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870169 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 5]
def baseStart_3870169 : Nat := 118140960795 + 3870169 * 2 ^ 59
def prefixEnd_3870169 : Nat := 4983230072969 + 3 ^ 40 * 3870169 * 2
def baseEnd_3870169 : Nat := 220806323458952631076547

theorem tailTrace_3870169 : CollatzResearch.WordTrace tailWord_3870169 prefixEnd_3870169 220806323458952631076547 := by
  unfold tailWord_3870169
  simp only [CollatzResearch.WordTrace]
  refine ⟨141156659916046160087621561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94104439944030773391747707 141156659916046160087621561)
  ·
    refine ⟨105867494937034620065716171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141156659916046160087621561 105867494937034620065716171)
    ·
      refine ⟨158801242405551930098574257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105867494937034620065716171 158801242405551930098574257)
      ·
        refine ⟨119100931804163947573930693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158801242405551930098574257 119100931804163947573930693)
        ·
          refine ⟨22331424713280740170112005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119100931804163947573930693 22331424713280740170112005)
          ·
            refine ⟨4187142133740138781896001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22331424713280740170112005 4187142133740138781896001)
            ·
              refine ⟨3140356600305104086422001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187142133740138781896001 3140356600305104086422001)
              ·
                refine ⟨2355267450228828064816501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140356600305104086422001 2355267450228828064816501)
                ·
                  refine ⟨220806323458952631076547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2355267450228828064816501 220806323458952631076547)
                  ·
                    rfl

theorem cell23_3870169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 5].length) (baseStart_3870169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870169 prefixEnd_3870169 := by exact prefixLift 3870169
  have htrace : WordTrace (prefixWord ++ tailWord_3870169) baseStart_3870169 baseEnd_3870169 := by
    simpa [prefixWord, tailWord_3870169, baseEnd_3870169] using wordTrace_append hprefix tailTrace_3870169
  have hstable : (prefixWord ++ tailWord_3870169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870169).length < 2 ^ (prefixWord ++ tailWord_3870169).sum := by decide
  have hdescent : baseEnd_3870169 < baseStart_3870169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870214 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3870214 : Nat := 118140960795 + 3870214 * 2 ^ 59
def prefixEnd_3870214 : Nat := 4983230072969 + 3 ^ 40 * 3870214 * 2
def baseEnd_3870214 : Nat := 1987280017760026003626217

theorem tailTrace_3870214 : CollatzResearch.WordTrace tailWord_3870214 prefixEnd_3870214 1987280017760026003626217 := by
  unfold tailWord_3870214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411196912527597899156553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94105534133922088515339797 4411196912527597899156553)
  ·
    refine ⟨3308397684395698424367415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4411196912527597899156553 3308397684395698424367415)
    ·
      refine ⟨4962596526593547636551123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308397684395698424367415 4962596526593547636551123)
      ·
        refine ⟨7443894789890321454826685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962596526593547636551123 7443894789890321454826685)
        ·
          refine ⟨2791460546208870545560007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443894789890321454826685 2791460546208870545560007)
          ·
            refine ⟨4187190819313305818340011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791460546208870545560007 4187190819313305818340011)
            ·
              refine ⟨6280786228969958727510017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187190819313305818340011 6280786228969958727510017)
              ·
                refine ⟨4710589671727469045632513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280786228969958727510017 4710589671727469045632513)
                ·
                  refine ⟨3532942253795601784224385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710589671727469045632513 3532942253795601784224385)
                  ·
                    refine ⟨2649706690346701338168289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532942253795601784224385 2649706690346701338168289)
                    ·
                      refine ⟨1987280017760026003626217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649706690346701338168289 1987280017760026003626217)
                      ·
                        rfl

theorem cell23_3870214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3870214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870214 prefixEnd_3870214 := by exact prefixLift 3870214
  have htrace : WordTrace (prefixWord ++ tailWord_3870214) baseStart_3870214 baseEnd_3870214 := by
    simpa [prefixWord, tailWord_3870214, baseEnd_3870214] using wordTrace_append hprefix tailTrace_3870214
  have hstable : (prefixWord ++ tailWord_3870214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870214).length < 2 ^ (prefixWord ++ tailWord_3870214).sum := by decide
  have hdescent : baseEnd_3870214 < baseStart_3870214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870215 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3870215 : Nat := 118140960795 + 3870215 * 2 ^ 59
def prefixEnd_3870215 : Nat := 4983230072969 + 3 ^ 40 * 3870215 * 2
def baseEnd_3870215 : Nat := 1987280531240680499713711

theorem tailTrace_3870215 : CollatzResearch.WordTrace tailWord_3870215 prefixEnd_3870215 1987280531240680499713711 := by
  unfold tailWord_3870215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141158337673879509943796099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94105558449253006629197399 141158337673879509943796099)
  ·
    refine ⟨211737506510819264915694149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141158337673879509943796099 211737506510819264915694149)
    ·
      refine ⟨39700782470778612171692653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211737506510819264915694149 39700782470778612171692653)
      ·
        refine ⟨14887793426541979564384745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39700782470778612171692653 14887793426541979564384745)
        ·
          refine ⟨11165845069906484673288559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14887793426541979564384745 11165845069906484673288559)
          ·
            refine ⟨16748767604859727009932839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165845069906484673288559 16748767604859727009932839)
            ·
              refine ⟨25123151407289590514899259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16748767604859727009932839 25123151407289590514899259)
              ·
                refine ⟨37684727110934385772348889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25123151407289590514899259 37684727110934385772348889)
                ·
                  refine ⟨28263545333200789329261667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37684727110934385772348889 28263545333200789329261667)
                  ·
                    refine ⟨42395317999801183993892501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28263545333200789329261667 42395317999801183993892501)
                    ·
                      refine ⟨1987280531240680499713711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42395317999801183993892501 1987280531240680499713711)
                      ·
                        rfl

theorem cell23_3870215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3870215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870215 prefixEnd_3870215 := by exact prefixLift 3870215
  have htrace : WordTrace (prefixWord ++ tailWord_3870215) baseStart_3870215 baseEnd_3870215 := by
    simpa [prefixWord, tailWord_3870215, baseEnd_3870215] using wordTrace_append hprefix tailTrace_3870215
  have hstable : (prefixWord ++ tailWord_3870215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870215).length < 2 ^ (prefixWord ++ tailWord_3870215).sum := by decide
  have hdescent : baseEnd_3870215 < baseStart_3870215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870229 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3870229 : Nat := 118140960795 + 3870229 * 2 ^ 59
def prefixEnd_3870229 : Nat := 4983230072969 + 3 ^ 40 * 3870229 * 2
def baseEnd_3870229 : Nat := 662429239989947814979549

theorem tailTrace_3870229 : CollatzResearch.WordTrace tailWord_3870229 prefixEnd_3870229 662429239989947814979549 := by
  unfold tailWord_3870229
  simp only [CollatzResearch.WordTrace]
  refine ⟨141158848295828790334805741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94105898863885860223203827 141158848295828790334805741)
  ·
    refine ⟨52934568110935796375552153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141158848295828790334805741 52934568110935796375552153)
    ·
      refine ⟨39700926083201847281664115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52934568110935796375552153 39700926083201847281664115)
      ·
        refine ⟨59551389124802770922496173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39700926083201847281664115 59551389124802770922496173)
        ·
          refine ⟨22331770921801039095936065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59551389124802770922496173 22331770921801039095936065)
          ·
            refine ⟨16748828191350779321952049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22331770921801039095936065 16748828191350779321952049)
            ·
              refine ⟨12561621143513084491464037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16748828191350779321952049 12561621143513084491464037)
              ·
                refine ⟨2355303964408703342149507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12561621143513084491464037 2355303964408703342149507)
                ·
                  refine ⟨3532955946613055013224261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355303964408703342149507 3532955946613055013224261)
                  ·
                    refine ⟨662429239989947814979549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3532955946613055013224261 662429239989947814979549)
                    ·
                      rfl

theorem cell23_3870229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3870229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870229 prefixEnd_3870229 := by exact prefixLift 3870229
  have htrace : WordTrace (prefixWord ++ tailWord_3870229) baseStart_3870229 baseEnd_3870229 := by
    simpa [prefixWord, tailWord_3870229, baseEnd_3870229] using wordTrace_append hprefix tailTrace_3870229
  have hstable : (prefixWord ++ tailWord_3870229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870229).length < 2 ^ (prefixWord ++ tailWord_3870229).sum := by decide
  have hdescent : baseEnd_3870229 < baseStart_3870229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870275 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4]
def baseStart_3870275 : Nat := 118140960795 + 3870275 * 2 ^ 59
def prefixEnd_3870275 : Nat := 4983230072969 + 3 ^ 40 * 3870275 * 2
def baseEnd_3870275 : Nat := 1987311340079950264963435

theorem tailTrace_3870275 : CollatzResearch.WordTrace tailWord_3870275 prefixEnd_3870275 1987311340079950264963435 := by
  unfold tailWord_3870275
  simp only [CollatzResearch.WordTrace]
  refine ⟨141160526053662140190980279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94107017369108093460653519 141160526053662140190980279)
  ·
    refine ⟨211740789080493210286470419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141160526053662140190980279 211740789080493210286470419)
    ·
      refine ⟨317611183620739815429705629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211740789080493210286470419 317611183620739815429705629)
      ·
        refine ⟨119104193857777430786139611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317611183620739815429705629 119104193857777430786139611)
        ·
          refine ⟨178656290786666146179209417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119104193857777430786139611 178656290786666146179209417)
          ·
            refine ⟨133992218089999609634407063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178656290786666146179209417 133992218089999609634407063)
            ·
              refine ⟨200988327134999414451610595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133992218089999609634407063 200988327134999414451610595)
              ·
                refine ⟨301482490702499121677415893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200988327134999414451610595 301482490702499121677415893)
                ·
                  refine ⟨7065995875839823164314435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301482490702499121677415893 7065995875839823164314435)
                  ·
                    refine ⟨10598993813759734746471653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065995875839823164314435 10598993813759734746471653)
                    ·
                      refine ⟨1987311340079950264963435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10598993813759734746471653 1987311340079950264963435)
                      ·
                        rfl

theorem cell23_3870275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_3870275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870275 prefixEnd_3870275 := by exact prefixLift 3870275
  have htrace : WordTrace (prefixWord ++ tailWord_3870275) baseStart_3870275 baseEnd_3870275 := by
    simpa [prefixWord, tailWord_3870275, baseEnd_3870275] using wordTrace_append hprefix tailTrace_3870275
  have hstable : (prefixWord ++ tailWord_3870275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870275).length < 2 ^ (prefixWord ++ tailWord_3870275).sum := by decide
  have hdescent : baseEnd_3870275 < baseStart_3870275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870292 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3870292 : Nat := 118140960795 + 3870292 * 2 ^ 59
def prefixEnd_3870292 : Nat := 4983230072969 + 3 ^ 40 * 3870292 * 2
def baseEnd_3870292 : Nat := 1987320069251076698450857

theorem tailTrace_3870292 : CollatzResearch.WordTrace tailWord_3870292 prefixEnd_3870292 1987320069251076698450857 := by
  unfold tailWord_3870292
  simp only [CollatzResearch.WordTrace]
  refine ⟨70580573047300276047174565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94107430729733701396232753 70580573047300276047174565)
  ·
    refine ⟨13233857446368801758845231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70580573047300276047174565 13233857446368801758845231)
    ·
      refine ⟨19850786169553202638267847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13233857446368801758845231 19850786169553202638267847)
      ·
        refine ⟨29776179254329803957401771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19850786169553202638267847 29776179254329803957401771)
        ·
          refine ⟨44664268881494705936102657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29776179254329803957401771 44664268881494705936102657)
          ·
            refine ⟨33498201661121029452076993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44664268881494705936102657 33498201661121029452076993)
            ·
              refine ⟨25123651245840772089057745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33498201661121029452076993 25123651245840772089057745)
              ·
                refine ⟨18842738434380579066793309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25123651245840772089057745 18842738434380579066793309)
                ·
                  refine ⟨7066026912892717150047491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18842738434380579066793309 7066026912892717150047491)
                  ·
                    refine ⟨10599040369339075725071237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066026912892717150047491 10599040369339075725071237)
                    ·
                      refine ⟨1987320069251076698450857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599040369339075725071237 1987320069251076698450857)
                      ·
                        rfl

theorem cell23_3870292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3870292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870292 prefixEnd_3870292 := by exact prefixLift 3870292
  have htrace : WordTrace (prefixWord ++ tailWord_3870292) baseStart_3870292 baseEnd_3870292 := by
    simpa [prefixWord, tailWord_3870292, baseEnd_3870292] using wordTrace_append hprefix tailTrace_3870292
  have hstable : (prefixWord ++ tailWord_3870292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870292).length < 2 ^ (prefixWord ++ tailWord_3870292).sum := by decide
  have hdescent : baseEnd_3870292 < baseStart_3870292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870305 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3870305 : Nat := 118140960795 + 3870305 * 2 ^ 59
def prefixEnd_3870305 : Nat := 4983230072969 + 3 ^ 40 * 3870305 * 2
def baseEnd_3870305 : Nat := 1987326744499585147588297

theorem tailTrace_3870305 : CollatzResearch.WordTrace tailWord_3870305 prefixEnd_3870305 1987326744499585147588297 := by
  unfold tailWord_3870305
  simp only [CollatzResearch.WordTrace]
  refine ⟨141161620243553455314572369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94107746829035636876381579 141161620243553455314572369)
  ·
    refine ⟨105871215182665091485929277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141161620243553455314572369 105871215182665091485929277)
    ·
      refine ⟨39701705693499409307223479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105871215182665091485929277 39701705693499409307223479)
      ·
        refine ⟨59552558540249113960835219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39701705693499409307223479 59552558540249113960835219)
        ·
          refine ⟨89328837810373670941252829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59552558540249113960835219 89328837810373670941252829)
          ·
            refine ⟨33498314178890126602969811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89328837810373670941252829 33498314178890126602969811)
            ·
              refine ⟨50247471268335189904454717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33498314178890126602969811 50247471268335189904454717)
              ·
                refine ⟨18842801725625696214170519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50247471268335189904454717 18842801725625696214170519)
                ·
                  refine ⟨28264202588438544321255779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18842801725625696214170519 28264202588438544321255779)
                  ·
                    refine ⟨42396303882657816481883669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28264202588438544321255779 42396303882657816481883669)
                    ·
                      refine ⟨1987326744499585147588297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42396303882657816481883669 1987326744499585147588297)
                      ·
                        rfl

theorem cell23_3870305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3870305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870305 prefixEnd_3870305 := by exact prefixLift 3870305
  have htrace : WordTrace (prefixWord ++ tailWord_3870305) baseStart_3870305 baseEnd_3870305 := by
    simpa [prefixWord, tailWord_3870305, baseEnd_3870305] using wordTrace_append hprefix tailTrace_3870305
  have hstable : (prefixWord ++ tailWord_3870305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870305).length < 2 ^ (prefixWord ++ tailWord_3870305).sum := by decide
  have hdescent : baseEnd_3870305 < baseStart_3870305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870309 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3870309 : Nat := 118140960795 + 3870309 * 2 ^ 59
def prefixEnd_3870309 : Nat := 4983230072969 + 3 ^ 40 * 3870309 * 2
def baseEnd_3870309 : Nat := 1987328798422203131938279

theorem tailTrace_3870309 : CollatzResearch.WordTrace tailWord_3870309 prefixEnd_3870309 1987328798422203131938279 := by
  unfold tailWord_3870309
  simp only [CollatzResearch.WordTrace]
  refine ⟨141161766135538963997717981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94107844090359309331811987 141161766135538963997717981)
  ·
    refine ⟨52935662300827111499144243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141161766135538963997717981 52935662300827111499144243)
    ·
      refine ⟨79403493451240667248716365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52935662300827111499144243 79403493451240667248716365)
      ·
        refine ⟨29776310044215250218268637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79403493451240667248716365 29776310044215250218268637)
        ·
          refine ⟨11166116266580718831850739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29776310044215250218268637 11166116266580718831850739)
          ·
            refine ⟨16749174399871078247776109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166116266580718831850739 16749174399871078247776109)
            ·
              refine ⟨6280940399951654342916041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16749174399871078247776109 6280940399951654342916041)
              ·
                refine ⟨4710705299963740757187031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280940399951654342916041 4710705299963740757187031)
                ·
                  refine ⟨7066057949945611135780547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710705299963740757187031 7066057949945611135780547)
                  ·
                    refine ⟨10599086924918416703670821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066057949945611135780547 10599086924918416703670821)
                    ·
                      refine ⟨1987328798422203131938279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599086924918416703670821 1987328798422203131938279)
                      ·
                        rfl

theorem cell23_3870309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3870309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870309 prefixEnd_3870309 := by exact prefixLift 3870309
  have htrace : WordTrace (prefixWord ++ tailWord_3870309) baseStart_3870309 baseEnd_3870309 := by
    simpa [prefixWord, tailWord_3870309, baseEnd_3870309] using wordTrace_append hprefix tailTrace_3870309
  have hstable : (prefixWord ++ tailWord_3870309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870309).length < 2 ^ (prefixWord ++ tailWord_3870309).sum := by decide
  have hdescent : baseEnd_3870309 < baseStart_3870309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870322 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3870322 : Nat := 118140960795 + 3870322 * 2 ^ 59
def prefixEnd_3870322 : Nat := 4983230072969 + 3 ^ 40 * 3870322 * 2
def baseEnd_3870322 : Nat := 1987335473670711581075719

theorem tailTrace_3870322 : CollatzResearch.WordTrace tailWord_3870322 prefixEnd_3870322 1987335473670711581075719 := by
  unfold tailWord_3870322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35290560071122966804485305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94108160189661244811960813 35290560071122966804485305)
  ·
    refine ⟨26467920053342225103363979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35290560071122966804485305 26467920053342225103363979)
    ·
      refine ⟨39701880080013337655045969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26467920053342225103363979 39701880080013337655045969)
      ·
        refine ⟨29776410060010003241284477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39701880080013337655045969 29776410060010003241284477)
        ·
          refine ⟨11166153772503751215481679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29776410060010003241284477 11166153772503751215481679)
          ·
            refine ⟨16749230658755626823222519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166153772503751215481679 16749230658755626823222519)
            ·
              refine ⟨25123845988133440234833779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16749230658755626823222519 25123845988133440234833779)
              ·
                refine ⟨37685768982200160352250669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25123845988133440234833779 37685768982200160352250669)
                ·
                  refine ⟨14132163368325060132094001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37685768982200160352250669 14132163368325060132094001)
                  ·
                    refine ⟨10599122526243795099070501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14132163368325060132094001 10599122526243795099070501)
                    ·
                      refine ⟨1987335473670711581075719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599122526243795099070501 1987335473670711581075719)
                      ·
                        rfl

theorem cell23_3870322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3870322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870322 prefixEnd_3870322 := by exact prefixLift 3870322
  have htrace : WordTrace (prefixWord ++ tailWord_3870322) baseStart_3870322 baseEnd_3870322 := by
    simpa [prefixWord, tailWord_3870322, baseEnd_3870322] using wordTrace_append hprefix tailTrace_3870322
  have hstable : (prefixWord ++ tailWord_3870322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870322).length < 2 ^ (prefixWord ++ tailWord_3870322).sum := by decide
  have hdescent : baseEnd_3870322 < baseStart_3870322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870343 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_3870343 : Nat := 118140960795 + 3870343 * 2 ^ 59
def prefixEnd_3870343 : Nat := 4983230072969 + 3 ^ 40 * 3870343 * 2
def baseEnd_3870343 : Nat := 1987346256764455998913123

theorem tailTrace_3870343 : CollatzResearch.WordTrace tailWord_3870343 prefixEnd_3870343 1987346256764455998913123 := by
  unfold tailWord_3870343
  simp only [CollatzResearch.WordTrace]
  refine ⟨141163006217415787804455683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94108670811610525202970455 141163006217415787804455683)
  ·
    refine ⟨211744509326123681706683525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141163006217415787804455683 211744509326123681706683525)
    ·
      refine ⟨39702095498648190320003161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211744509326123681706683525 39702095498648190320003161)
      ·
        refine ⟨29776571623986142740002371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39702095498648190320003161 29776571623986142740002371)
        ·
          refine ⟨44664857435979214110003557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29776571623986142740002371 44664857435979214110003557)
          ·
            refine ⟨8374660769246102645625667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44664857435979214110003557 8374660769246102645625667)
            ·
              refine ⟨12561991153869153968438501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374660769246102645625667 12561991153869153968438501)
              ·
                refine ⟨2355373341350466369082219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12561991153869153968438501 2355373341350466369082219)
                ·
                  refine ⟨3533060012025699553623329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355373341350466369082219 3533060012025699553623329)
                  ·
                    refine ⟨2649795009019274665217497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533060012025699553623329 2649795009019274665217497)
                    ·
                      refine ⟨1987346256764455998913123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2649795009019274665217497 1987346256764455998913123)
                      ·
                        rfl

theorem cell23_3870343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_3870343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870343 prefixEnd_3870343 := by exact prefixLift 3870343
  have htrace : WordTrace (prefixWord ++ tailWord_3870343) baseStart_3870343 baseEnd_3870343 := by
    simpa [prefixWord, tailWord_3870343, baseEnd_3870343] using wordTrace_append hprefix tailTrace_3870343
  have hstable : (prefixWord ++ tailWord_3870343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870343).length < 2 ^ (prefixWord ++ tailWord_3870343).sum := by decide
  have hdescent : baseEnd_3870343 < baseStart_3870343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870345 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_3870345 : Nat := 118140960795 + 3870345 * 2 ^ 59
def prefixEnd_3870345 : Nat := 4983230072969 + 3 ^ 40 * 3870345 * 2
def baseEnd_3870345 : Nat := 662449094575254997029371

theorem tailTrace_3870345 : CollatzResearch.WordTrace tailWord_3870345 prefixEnd_3870345 662449094575254997029371 := by
  unfold tailWord_3870345
  simp only [CollatzResearch.WordTrace]
  refine ⟨141163079163408542146028489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94108719442272361430685659 141163079163408542146028489)
  ·
    refine ⟨105872309372556406609521367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141163079163408542146028489 105872309372556406609521367)
    ·
      refine ⟨158808464058834609914282051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105872309372556406609521367 158808464058834609914282051)
      ·
        refine ⟨238212696088251914871423077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158808464058834609914282051 238212696088251914871423077)
        ·
          refine ⟨44664880516547234038391827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238212696088251914871423077 44664880516547234038391827)
          ·
            refine ⟨66997320774820851057587741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44664880516547234038391827 66997320774820851057587741)
            ·
              refine ⟨25123995290557819146595403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66997320774820851057587741 25123995290557819146595403)
              ·
                refine ⟨37685992935836728719893105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25123995290557819146595403 37685992935836728719893105)
                ·
                  refine ⟨28264494701877546539919829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37685992935836728719893105 28264494701877546539919829)
                  ·
                    refine ⟨662449094575254997029371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28264494701877546539919829 662449094575254997029371)
                    ·
                      rfl

theorem cell23_3870345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_3870345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870345 prefixEnd_3870345 := by exact prefixLift 3870345
  have htrace : WordTrace (prefixWord ++ tailWord_3870345) baseStart_3870345 baseEnd_3870345 := by
    simpa [prefixWord, tailWord_3870345, baseEnd_3870345] using wordTrace_append hprefix tailTrace_3870345
  have hstable : (prefixWord ++ tailWord_3870345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870345).length < 2 ^ (prefixWord ++ tailWord_3870345).sum := by decide
  have hdescent : baseEnd_3870345 < baseStart_3870345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870356 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3870356 : Nat := 118140960795 + 3870356 * 2 ^ 59
def prefixEnd_3870356 : Nat := 4983230072969 + 3 ^ 40 * 3870356 * 2
def baseEnd_3870356 : Nat := 1987352932012964448050563

theorem tailTrace_3870356 : CollatzResearch.WordTrace tailWord_3870356 prefixEnd_3870356 1987352932012964448050563 := by
  unfold tailWord_3870356
  simp only [CollatzResearch.WordTrace]
  refine ⟨70581740183184345512339461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94108986910912460683119281 70581740183184345512339461)
  ·
    refine ⟨13234076284347064783563649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70581740183184345512339461 13234076284347064783563649)
    ·
      refine ⟨9925557213260298587672737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13234076284347064783563649 9925557213260298587672737)
      ·
        refine ⟨7444167909945223940754553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9925557213260298587672737 7444167909945223940754553)
        ·
          refine ⟨5583125932458917955565915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444167909945223940754553 5583125932458917955565915)
          ·
            refine ⟨8374688898688376933348873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583125932458917955565915 8374688898688376933348873)
            ·
              refine ⟨6281016674016282700011655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374688898688376933348873 6281016674016282700011655)
              ·
                refine ⟨9421525011024424050017483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281016674016282700011655 9421525011024424050017483)
                ·
                  refine ⟨14132287516536636075026225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421525011024424050017483 14132287516536636075026225)
                  ·
                    refine ⟨10599215637402477056269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14132287516536636075026225 10599215637402477056269669)
                    ·
                      refine ⟨1987352932012964448050563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599215637402477056269669 1987352932012964448050563)
                      ·
                        rfl

theorem cell23_3870356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3870356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870356 prefixEnd_3870356 := by exact prefixLift 3870356
  have htrace : WordTrace (prefixWord ++ tailWord_3870356) baseStart_3870356 baseEnd_3870356 := by
    simpa [prefixWord, tailWord_3870356, baseEnd_3870356] using wordTrace_append hprefix tailTrace_3870356
  have hstable : (prefixWord ++ tailWord_3870356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870356).length < 2 ^ (prefixWord ++ tailWord_3870356).sum := by decide
  have hdescent : baseEnd_3870356 < baseStart_3870356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870359 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3870359 : Nat := 118140960795 + 3870359 * 2 ^ 59
def prefixEnd_3870359 : Nat := 4983230072969 + 3 ^ 40 * 3870359 * 2
def baseEnd_3870359 : Nat := 1987354472454927936313049

theorem tailTrace_3870359 : CollatzResearch.WordTrace tailWord_3870359 prefixEnd_3870359 1987354472454927936313049 := by
  unfold tailWord_3870359
  simp only [CollatzResearch.WordTrace]
  refine ⟨141163589785357822537038131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94109059856905215024692087 141163589785357822537038131)
  ·
    refine ⟨211745384678036733805557197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141163589785357822537038131 211745384678036733805557197)
    ·
      refine ⟨79404519254263775177083949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211745384678036733805557197 79404519254263775177083949)
      ·
        refine ⟨29776694720348915691406481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79404519254263775177083949 29776694720348915691406481)
        ·
          refine ⟨22332521040261686768554861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29776694720348915691406481 22332521040261686768554861)
          ·
            refine ⟨8374695390098132538208073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22332521040261686768554861 8374695390098132538208073)
            ·
              refine ⟨6281021542573599403656055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374695390098132538208073 6281021542573599403656055)
              ·
                refine ⟨9421532313860399105484083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281021542573599403656055 9421532313860399105484083)
                ·
                  refine ⟨14132298470790598658226125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421532313860399105484083 14132298470790598658226125)
                  ·
                    refine ⟨5299611926546474496834797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14132298470790598658226125 5299611926546474496834797)
                    ·
                      refine ⟨1987354472454927936313049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299611926546474496834797 1987354472454927936313049)
                      ·
                        rfl

theorem cell23_3870359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3870359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870359 prefixEnd_3870359 := by exact prefixLift 3870359
  have htrace : WordTrace (prefixWord ++ tailWord_3870359) baseStart_3870359 baseEnd_3870359 := by
    simpa [prefixWord, tailWord_3870359, baseEnd_3870359] using wordTrace_append hprefix tailTrace_3870359
  have hstable : (prefixWord ++ tailWord_3870359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870359).length < 2 ^ (prefixWord ++ tailWord_3870359).sum := by decide
  have hdescent : baseEnd_3870359 < baseStart_3870359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870405 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 11]
def baseStart_3870405 : Nat := 118140960795 + 3870405 * 2 ^ 59
def prefixEnd_3870405 : Nat := 4983230072969 + 3 ^ 40 * 3870405 * 2
def baseEnd_3870405 : Nat := 220819788062781639593093

theorem tailTrace_3870405 : CollatzResearch.WordTrace tailWord_3870405 prefixEnd_3870405 220819788062781639593093 := by
  unfold tailWord_3870405
  simp only [CollatzResearch.WordTrace]
  refine ⟨141165267543191172393212669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94110178362127448262141779 141165267543191172393212669)
  ·
    refine ⟨52936975328696689647454751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141165267543191172393212669 52936975328696689647454751)
    ·
      refine ⟨79405462993045034471182127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52936975328696689647454751 79405462993045034471182127)
      ·
        refine ⟨119108194489567551706773191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79405462993045034471182127 119108194489567551706773191)
        ·
          refine ⟨178662291734351327560159787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119108194489567551706773191 178662291734351327560159787)
          ·
            refine ⟨267993437601526991340239681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178662291734351327560159787 267993437601526991340239681)
            ·
              refine ⟨200995078201145243505179761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267993437601526991340239681 200995078201145243505179761)
              ·
                refine ⟨150746308650858932628884821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200995078201145243505179761 150746308650858932628884821)
                ·
                  refine ⟨220819788062781639593093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 150746308650858932628884821 220819788062781639593093)
                  ·
                    rfl

theorem cell23_3870405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_3870405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870405 prefixEnd_3870405 := by exact prefixLift 3870405
  have htrace : WordTrace (prefixWord ++ tailWord_3870405) baseStart_3870405 baseEnd_3870405 := by
    simpa [prefixWord, tailWord_3870405, baseEnd_3870405] using wordTrace_append hprefix tailTrace_3870405
  have hstable : (prefixWord ++ tailWord_3870405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870405).length < 2 ^ (prefixWord ++ tailWord_3870405).sum := by decide
  have hdescent : baseEnd_3870405 < baseStart_3870405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870415 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_3870415 : Nat := 118140960795 + 3870415 * 2 ^ 59
def prefixEnd_3870415 : Nat := 4983230072969 + 3 ^ 40 * 3870415 * 2
def baseEnd_3870415 : Nat := 1987383227371579717212791

theorem tailTrace_3870415 : CollatzResearch.WordTrace tailWord_3870415 prefixEnd_3870415 1987383227371579717212791 := by
  unfold tailWord_3870415
  simp only [CollatzResearch.WordTrace]
  refine ⟨141165632273154944101076699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94110421515436629400717799 141165632273154944101076699)
  ·
    refine ⟨211748448409732416151615049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141165632273154944101076699 211748448409732416151615049)
    ·
      refine ⟨158811336307299312113711287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211748448409732416151615049 158811336307299312113711287)
      ·
        refine ⟨238217004460948968170566931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158811336307299312113711287 238217004460948968170566931)
        ·
          refine ⟨357325506691423452255850397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238217004460948968170566931 357325506691423452255850397)
          ·
            refine ⟨133997065009283794595943899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357325506691423452255850397 133997065009283794595943899)
            ·
              refine ⟨200995597513925691893915849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133997065009283794595943899 200995597513925691893915849)
              ·
                refine ⟨150746698135444268920436887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200995597513925691893915849 150746698135444268920436887)
                ·
                  refine ⟨226120047203166403380655331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150746698135444268920436887 226120047203166403380655331)
                  ·
                    refine ⟨339180070804749605070982997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226120047203166403380655331 339180070804749605070982997)
                    ·
                      refine ⟨1987383227371579717212791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 339180070804749605070982997 1987383227371579717212791)
                      ·
                        rfl

theorem cell23_3870415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_3870415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870415 prefixEnd_3870415 := by exact prefixLift 3870415
  have htrace : WordTrace (prefixWord ++ tailWord_3870415) baseStart_3870415 baseEnd_3870415 := by
    simpa [prefixWord, tailWord_3870415, baseEnd_3870415] using wordTrace_append hprefix tailTrace_3870415
  have hstable : (prefixWord ++ tailWord_3870415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870415).length < 2 ^ (prefixWord ++ tailWord_3870415).sum := by decide
  have hdescent : baseEnd_3870415 < baseStart_3870415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870432 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3870432 : Nat := 118140960795 + 3870432 * 2 ^ 59
def prefixEnd_3870432 : Nat := 4983230072969 + 3 ^ 40 * 3870432 * 2
def baseEnd_3870432 : Nat := 1987391956542706150700213

theorem tailTrace_3870432 : CollatzResearch.WordTrace tailWord_3870432 prefixEnd_3870432 1987391956542706150700213 := by
  unfold tailWord_3870432
  simp only [CollatzResearch.WordTrace]
  refine ⟨70583126157046678002222775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94110834876062237336297033 70583126157046678002222775)
  ·
    refine ⟨105874689235570017003334163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70583126157046678002222775 105874689235570017003334163)
    ·
      refine ⟨158812033853355025505001245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105874689235570017003334163 158812033853355025505001245)
      ·
        refine ⟨59554512695008134564375467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158812033853355025505001245 59554512695008134564375467)
        ·
          refine ⟨89331769042512201846563201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59554512695008134564375467 89331769042512201846563201)
          ·
            refine ⟨66998826781884151384922401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89331769042512201846563201 66998826781884151384922401)
            ·
              refine ⟨50249120086413113538691801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66998826781884151384922401 50249120086413113538691801)
              ·
                refine ⟨37686840064809835154018851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50249120086413113538691801 37686840064809835154018851)
                ·
                  refine ⟨56530260097214752731028277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37686840064809835154018851 56530260097214752731028277)
                  ·
                    refine ⟨5299711884113883068533901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56530260097214752731028277 5299711884113883068533901)
                    ·
                      refine ⟨1987391956542706150700213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299711884113883068533901 1987391956542706150700213)
                      ·
                        rfl

theorem cell23_3870432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3870432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870432 prefixEnd_3870432 := by exact prefixLift 3870432
  have htrace : WordTrace (prefixWord ++ tailWord_3870432) baseStart_3870432 baseEnd_3870432 := by
    simpa [prefixWord, tailWord_3870432, baseEnd_3870432] using wordTrace_append hprefix tailTrace_3870432
  have hstable : (prefixWord ++ tailWord_3870432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870432).length < 2 ^ (prefixWord ++ tailWord_3870432).sum := by decide
  have hdescent : baseEnd_3870432 < baseStart_3870432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870552 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3870552 : Nat := 118140960795 + 3870552 * 2 ^ 59
def prefixEnd_3870552 : Nat := 4983230072969 + 3 ^ 40 * 3870552 * 2
def baseEnd_3870552 : Nat := 1987453574221245681199661

theorem tailTrace_3870552 : CollatzResearch.WordTrace tailWord_3870552 prefixEnd_3870552 1987453574221245681199661 := by
  unfold tailWord_3870552
  simp only [CollatzResearch.WordTrace]
  refine ⟨70585314536829308249406955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94113752715772410999209273 70585314536829308249406955)
  ·
    refine ⟨105877971805243962374110433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70585314536829308249406955 105877971805243962374110433)
    ·
      refine ⟨79408478853932971780582825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105877971805243962374110433 79408478853932971780582825)
      ·
        refine ⟨59556359140449728835437119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79408478853932971780582825 59556359140449728835437119)
        ·
          refine ⟨89334538710674593253155679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59556359140449728835437119 89334538710674593253155679)
          ·
            refine ⟨134001808066011889879733519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89334538710674593253155679 134001808066011889879733519)
            ·
              refine ⟨201002712099017834819600279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134001808066011889879733519 201002712099017834819600279)
              ·
                refine ⟨301504068148526752229400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201002712099017834819600279 301504068148526752229400419)
                ·
                  refine ⟨452256102222790128344100629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301504068148526752229400419 452256102222790128344100629)
                  ·
                    refine ⟨21199504791693287266129717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 452256102222790128344100629 21199504791693287266129717)
                    ·
                      refine ⟨1987453574221245681199661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21199504791693287266129717 1987453574221245681199661)
                      ·
                        rfl

theorem cell23_3870552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3870552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870552 prefixEnd_3870552 := by exact prefixLift 3870552
  have htrace : WordTrace (prefixWord ++ tailWord_3870552) baseStart_3870552 baseEnd_3870552 := by
    simpa [prefixWord, tailWord_3870552, baseEnd_3870552] using wordTrace_append hprefix tailTrace_3870552
  have hstable : (prefixWord ++ tailWord_3870552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870552).length < 2 ^ (prefixWord ++ tailWord_3870552).sum := by decide
  have hdescent : baseEnd_3870552 < baseStart_3870552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870563 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 6]
def baseStart_3870563 : Nat := 118140960795 + 3870563 * 2 ^ 59
def prefixEnd_3870563 : Nat := 4983230072969 + 3 ^ 40 * 3870563 * 2
def baseEnd_3870563 : Nat := 220828802500938348684679

theorem tailTrace_3870563 : CollatzResearch.WordTrace tailWord_3870563 prefixEnd_3870563 220828802500938348684679 := by
  unfold tailWord_3870563
  simp only [CollatzResearch.WordTrace]
  refine ⟨141171030276618765377464343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94114020184412510251642895 141171030276618765377464343)
  ·
    refine ⟨211756545414928148066196515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141171030276618765377464343 211756545414928148066196515)
    ·
      refine ⟨317634818122392222099294773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211756545414928148066196515 317634818122392222099294773)
      ·
        refine ⟨29778264198974270821808885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317634818122392222099294773 29778264198974270821808885)
        ·
          refine ⟨2791712268653837889544583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29778264198974270821808885 2791712268653837889544583)
          ·
            refine ⟨4187568402980756834316875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791712268653837889544583 4187568402980756834316875)
            ·
              refine ⟨6281352604471135251475313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187568402980756834316875 6281352604471135251475313)
              ·
                refine ⟨4711014453353351438606485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6281352604471135251475313 4711014453353351438606485)
                ·
                  refine ⟨220828802500938348684679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4711014453353351438606485 220828802500938348684679)
                  ·
                    rfl

theorem cell23_3870563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 6].length) (baseStart_3870563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870563 prefixEnd_3870563 := by exact prefixLift 3870563
  have htrace : WordTrace (prefixWord ++ tailWord_3870563) baseStart_3870563 baseEnd_3870563 := by
    simpa [prefixWord, tailWord_3870563, baseEnd_3870563] using wordTrace_append hprefix tailTrace_3870563
  have hstable : (prefixWord ++ tailWord_3870563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870563).length < 2 ^ (prefixWord ++ tailWord_3870563).sum := by decide
  have hdescent : baseEnd_3870563 < baseStart_3870563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870590 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3870590 : Nat := 118140960795 + 3870590 * 2 ^ 59
def prefixEnd_3870590 : Nat := 4983230072969 + 3 ^ 40 * 3870590 * 2
def baseEnd_3870590 : Nat := 1987473086486116532524487

theorem tailTrace_3870590 : CollatzResearch.WordTrace tailWord_3870590 prefixEnd_3870590 1987473086486116532524487 := by
  unfold tailWord_3870590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646501880940118623587153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94114676698347299325798149 17646501880940118623587153)
  ·
    refine ⟨13234876410705088967690365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17646501880940118623587153 13234876410705088967690365)
    ·
      refine ⟨4963078654014408362883887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13234876410705088967690365 4963078654014408362883887)
      ·
        refine ⟨7444617981021612544325831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963078654014408362883887 7444617981021612544325831)
        ·
          refine ⟨11166926971532418816488747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444617981021612544325831 11166926971532418816488747)
          ·
            refine ⟨16750390457298628224733121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166926971532418816488747 16750390457298628224733121)
            ·
              refine ⟨12562792842973971168549841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16750390457298628224733121 12562792842973971168549841)
              ·
                refine ⟨9422094632230478376412381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562792842973971168549841 9422094632230478376412381)
                ·
                  refine ⟨3533285487086429391154643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9422094632230478376412381 3533285487086429391154643)
                  ·
                    refine ⟨5299928230629644086731965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3533285487086429391154643 5299928230629644086731965)
                    ·
                      refine ⟨1987473086486116532524487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5299928230629644086731965 1987473086486116532524487)
                      ·
                        rfl

theorem cell23_3870590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3870590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870590 prefixEnd_3870590 := by exact prefixLift 3870590
  have htrace : WordTrace (prefixWord ++ tailWord_3870590) baseStart_3870590 baseEnd_3870590 := by
    simpa [prefixWord, tailWord_3870590, baseEnd_3870590] using wordTrace_append hprefix tailTrace_3870590
  have hstable : (prefixWord ++ tailWord_3870590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870590).length < 2 ^ (prefixWord ++ tailWord_3870590).sum := by decide
  have hdescent : baseEnd_3870590 < baseStart_3870590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870596 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3870596 : Nat := 118140960795 + 3870596 * 2 ^ 59
def prefixEnd_3870596 : Nat := 4983230072969 + 3 ^ 40 * 3870596 * 2
def baseEnd_3870596 : Nat := 1987476167370043509049459

theorem tailTrace_3870596 : CollatzResearch.WordTrace tailWord_3870596 prefixEnd_3870596 1987476167370043509049459 := by
  unfold tailWord_3870596
  simp only [CollatzResearch.WordTrace]
  refine ⟨70586116942749606006707821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94114822590332808008943761 70586116942749606006707821)
  ·
    refine ⟨26469793853531102252515433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70586116942749606006707821 26469793853531102252515433)
    ·
      refine ⟨19852345390148326689386575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26469793853531102252515433 19852345390148326689386575)
      ·
        refine ⟨29778518085222490034079863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852345390148326689386575 29778518085222490034079863)
        ·
          refine ⟨44667777127833735051119795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778518085222490034079863 44667777127833735051119795)
          ·
            refine ⟨67001665691750602576679693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667777127833735051119795 67001665691750602576679693)
            ·
              refine ⟨25125624634406475966254885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67001665691750602576679693 25125624634406475966254885)
              ·
                refine ⟨4711054618951214243672791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25125624634406475966254885 4711054618951214243672791)
                ·
                  refine ⟨7066581928426821365509187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711054618951214243672791 7066581928426821365509187)
                  ·
                    refine ⟨10599872892640232048263781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066581928426821365509187 10599872892640232048263781)
                    ·
                      refine ⟨1987476167370043509049459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599872892640232048263781 1987476167370043509049459)
                      ·
                        rfl

theorem cell23_3870596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3870596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870596 prefixEnd_3870596 := by exact prefixLift 3870596
  have htrace : WordTrace (prefixWord ++ tailWord_3870596) baseStart_3870596 baseEnd_3870596 := by
    simpa [prefixWord, tailWord_3870596, baseEnd_3870596] using wordTrace_append hprefix tailTrace_3870596
  have hstable : (prefixWord ++ tailWord_3870596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870596).length < 2 ^ (prefixWord ++ tailWord_3870596).sum := by decide
  have hdescent : baseEnd_3870596 < baseStart_3870596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870609 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_3870609 : Nat := 118140960795 + 3870609 * 2 ^ 59
def prefixEnd_3870609 : Nat := 4983230072969 + 3 ^ 40 * 3870609 * 2
def baseEnd_3870609 : Nat := 1987482842618551958186899

theorem tailTrace_3870609 : CollatzResearch.WordTrace tailWord_3870609 prefixEnd_3870609 1987482842618551958186899 := by
  unfold tailWord_3870609
  simp only [CollatzResearch.WordTrace]
  refine ⟨141172708034452115233638881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94115138689634743489092587 141172708034452115233638881)
  ·
    refine ⟨105879531025839086425229161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141172708034452115233638881 105879531025839086425229161)
    ·
      refine ⟨79409648269379314818921871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105879531025839086425229161 79409648269379314818921871)
      ·
        refine ⟨119114472404068972228382807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79409648269379314818921871 119114472404068972228382807)
        ·
          refine ⟨178671708606103458342574211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119114472404068972228382807 178671708606103458342574211)
          ·
            refine ⟨268007562909155187513861317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178671708606103458342574211 268007562909155187513861317)
            ·
              refine ⟨50251418045466597658848997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268007562909155187513861317 50251418045466597658848997)
              ·
                refine ⟨9422140883524987061034187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50251418045466597658848997 9422140883524987061034187)
                ·
                  refine ⟨14133211325287480591551281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422140883524987061034187 14133211325287480591551281)
                  ·
                    refine ⟨10599908493965610443663461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14133211325287480591551281 10599908493965610443663461)
                    ·
                      refine ⟨1987482842618551958186899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10599908493965610443663461 1987482842618551958186899)
                      ·
                        rfl

theorem cell23_3870609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_3870609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870609 prefixEnd_3870609 := by exact prefixLift 3870609
  have htrace : WordTrace (prefixWord ++ tailWord_3870609) baseStart_3870609 baseEnd_3870609 := by
    simpa [prefixWord, tailWord_3870609, baseEnd_3870609] using wordTrace_append hprefix tailTrace_3870609
  have hstable : (prefixWord ++ tailWord_3870609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870609).length < 2 ^ (prefixWord ++ tailWord_3870609).sum := by decide
  have hdescent : baseEnd_3870609 < baseStart_3870609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870679 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 6]
def baseStart_3870679 : Nat := 118140960795 + 3870679 * 2 ^ 59
def prefixEnd_3870679 : Nat := 4983230072969 + 3 ^ 40 * 3870679 * 2
def baseEnd_3870679 : Nat := 662506262088122228103859

theorem tailTrace_3870679 : CollatzResearch.WordTrace tailWord_3870679 prefixEnd_3870679 662506262088122228103859 := by
  unfold tailWord_3870679
  simp only [CollatzResearch.WordTrace]
  refine ⟨141175261144198517188687091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94116840762799011459124727 141175261144198517188687091)
  ·
    refine ⟨211762891716297775783030637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141175261144198517188687091 211762891716297775783030637)
    ·
      refine ⟨79411084393611665918636489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211762891716297775783030637 79411084393611665918636489)
      ·
        refine ⟨59558313295208749438977367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79411084393611665918636489 59558313295208749438977367)
        ·
          refine ⟨89337469942813124158466051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59558313295208749438977367 89337469942813124158466051)
          ·
            refine ⟨134006204914219686237699077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89337469942813124158466051 134006204914219686237699077)
            ·
              refine ⟨25126163421416191169568577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134006204914219686237699077 25126163421416191169568577)
              ·
                refine ⟨18844622566062143377176433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25126163421416191169568577 18844622566062143377176433)
                ·
                  refine ⟨14133466924546607532882325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18844622566062143377176433 14133466924546607532882325)
                  ·
                    refine ⟨662506262088122228103859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14133466924546607532882325 662506262088122228103859)
                    ·
                      rfl

theorem cell23_3870679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_3870679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870679 prefixEnd_3870679 := by exact prefixLift 3870679
  have htrace : WordTrace (prefixWord ++ tailWord_3870679) baseStart_3870679 baseEnd_3870679 := by
    simpa [prefixWord, tailWord_3870679, baseEnd_3870679] using wordTrace_append hprefix tailTrace_3870679
  have hstable : (prefixWord ++ tailWord_3870679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870679).length < 2 ^ (prefixWord ++ tailWord_3870679).sum := by decide
  have hdescent : baseEnd_3870679 < baseStart_3870679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870681 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 1, 2, 2]
def baseStart_3870681 : Nat := 118140960795 + 3870681 * 2 ^ 59
def prefixEnd_3870681 : Nat := 4983230072969 + 3 ^ 40 * 3870681 * 2
def baseEnd_3870681 : Nat := 1987519813225675676486569

theorem tailTrace_3870681 : CollatzResearch.WordTrace tailWord_3870681 prefixEnd_3870681 1987519813225675676486569 := by
  unfold tailWord_3870681
  simp only [CollatzResearch.WordTrace]
  refine ⟨141175334090191271530259897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94116889393460847686839931 141175334090191271530259897)
  ·
    refine ⟨105881500567643453647694923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141175334090191271530259897 105881500567643453647694923)
    ·
      refine ⟨158822250851465180471542385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105881500567643453647694923 158822250851465180471542385)
      ·
        refine ⟨119116688138598885353656789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158822250851465180471542385 119116688138598885353656789)
        ·
          refine ⟨2791797378248411375476331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119116688138598885353656789 2791797378248411375476331)
          ·
            refine ⟨4187696067372617063214497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791797378248411375476331 4187696067372617063214497)
            ·
              refine ⟨3140772050529462797410873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187696067372617063214497 3140772050529462797410873)
              ·
                refine ⟨2355579037897097098058155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140772050529462797410873 2355579037897097098058155)
                ·
                  refine ⟨3533368556845645647087233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355579037897097098058155 3533368556845645647087233)
                  ·
                    refine ⟨2650026417634234235315425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533368556845645647087233 2650026417634234235315425)
                    ·
                      refine ⟨1987519813225675676486569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650026417634234235315425 1987519813225675676486569)
                      ·
                        rfl

theorem cell23_3870681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_3870681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870681 prefixEnd_3870681 := by exact prefixLift 3870681
  have htrace : WordTrace (prefixWord ++ tailWord_3870681) baseStart_3870681 baseEnd_3870681 := by
    simpa [prefixWord, tailWord_3870681, baseEnd_3870681] using wordTrace_append hprefix tailTrace_3870681
  have hstable : (prefixWord ++ tailWord_3870681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870681).length < 2 ^ (prefixWord ++ tailWord_3870681).sum := by decide
  have hdescent : baseEnd_3870681 < baseStart_3870681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870689 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3870689 : Nat := 118140960795 + 3870689 * 2 ^ 59
def prefixEnd_3870689 : Nat := 4983230072969 + 3 ^ 40 * 3870689 * 2
def baseEnd_3870689 : Nat := 1987523921070911645186531

theorem tailTrace_3870689 : CollatzResearch.WordTrace tailWord_3870689 prefixEnd_3870689 1987523921070911645186531 := by
  unfold tailWord_3870689
  simp only [CollatzResearch.WordTrace]
  refine ⟨141175625874162288896551121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94117083916108192597700747 141175625874162288896551121)
  ·
    refine ⟨105881719405621716672413341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141175625874162288896551121 105881719405621716672413341)
    ·
      refine ⟨39705644777108143752155003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105881719405621716672413341 39705644777108143752155003)
      ·
        refine ⟨59558467165662215628232505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39705644777108143752155003 59558467165662215628232505)
        ·
          refine ⟨44668850374246661721174379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59558467165662215628232505 44668850374246661721174379)
          ·
            refine ⟨67003275561369992581761569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44668850374246661721174379 67003275561369992581761569)
            ·
              refine ⟨50252456671027494436321177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67003275561369992581761569 50252456671027494436321177)
              ·
                refine ⟨37689342503270620827240883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50252456671027494436321177 37689342503270620827240883)
                ·
                  refine ⟨56534013754905931240861325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37689342503270620827240883 56534013754905931240861325)
                  ·
                    refine ⟨21200255158089724215322997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56534013754905931240861325 21200255158089724215322997)
                    ·
                      refine ⟨1987523921070911645186531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21200255158089724215322997 1987523921070911645186531)
                      ·
                        rfl

theorem cell23_3870689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3870689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870689 prefixEnd_3870689 := by exact prefixLift 3870689
  have htrace : WordTrace (prefixWord ++ tailWord_3870689) baseStart_3870689 baseEnd_3870689 := by
    simpa [prefixWord, tailWord_3870689, baseEnd_3870689] using wordTrace_append hprefix tailTrace_3870689
  have hstable : (prefixWord ++ tailWord_3870689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870689).length < 2 ^ (prefixWord ++ tailWord_3870689).sum := by decide
  have hdescent : baseEnd_3870689 < baseStart_3870689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870703 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 4, 2]
def baseStart_3870703 : Nat := 118140960795 + 3870703 * 2 ^ 59
def prefixEnd_3870703 : Nat := 4983230072969 + 3 ^ 40 * 3870703 * 2
def baseEnd_3870703 : Nat := 1987531109800074590411467

theorem tailTrace_3870703 : CollatzResearch.WordTrace tailWord_3870703 prefixEnd_3870703 1987531109800074590411467 := by
  unfold tailWord_3870703
  simp only [CollatzResearch.WordTrace]
  refine ⟨141176136496111569287560763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94117424330741046191707175 141176136496111569287560763)
  ·
    refine ⟨211764204744167353931341145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141176136496111569287560763 211764204744167353931341145)
    ·
      refine ⟨158823153558125515448505859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211764204744167353931341145 158823153558125515448505859)
      ·
        refine ⟨238234730337188273172758789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158823153558125515448505859 238234730337188273172758789)
        ·
          refine ⟨44669011938222801219892273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238234730337188273172758789 44669011938222801219892273)
          ·
            refine ⟨33501758953667100914919205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44669011938222801219892273 33501758953667100914919205)
            ·
              refine ⟨6281579803812581421547351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33501758953667100914919205 6281579803812581421547351)
              ·
                refine ⟨9422369705718872132321027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281579803812581421547351 9422369705718872132321027)
                ·
                  refine ⟨14133554558578308198481541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422369705718872132321027 14133554558578308198481541)
                  ·
                    refine ⟨2650041479733432787215289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14133554558578308198481541 2650041479733432787215289)
                    ·
                      refine ⟨1987531109800074590411467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650041479733432787215289 1987531109800074590411467)
                      ·
                        rfl

theorem cell23_3870703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4, 2].length) (baseStart_3870703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870703 prefixEnd_3870703 := by exact prefixLift 3870703
  have htrace : WordTrace (prefixWord ++ tailWord_3870703) baseStart_3870703 baseEnd_3870703 := by
    simpa [prefixWord, tailWord_3870703, baseEnd_3870703] using wordTrace_append hprefix tailTrace_3870703
  have hstable : (prefixWord ++ tailWord_3870703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870703).length < 2 ^ (prefixWord ++ tailWord_3870703).sum := by decide
  have hdescent : baseEnd_3870703 < baseStart_3870703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870743 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 7]
def baseStart_3870743 : Nat := 118140960795 + 3870743 * 2 ^ 59
def prefixEnd_3870743 : Nat := 4983230072969 + 3 ^ 40 * 3870743 * 2
def baseEnd_3870743 : Nat := 220839072114028270434587

theorem tailTrace_3870743 : CollatzResearch.WordTrace tailWord_3870743 prefixEnd_3870743 220839072114028270434587 := by
  unfold tailWord_3870743
  simp only [CollatzResearch.WordTrace]
  refine ⟨141177595415966656119016883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94118396943977770746011255 141177595415966656119016883)
  ·
    refine ⟨211766393123949984178525325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141177595415966656119016883 211766393123949984178525325)
    ·
      refine ⟨79412397421481244066946997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211766393123949984178525325 79412397421481244066946997)
      ·
        refine ⟨7444912258263866631276281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79412397421481244066946997 7444912258263866631276281)
        ·
          refine ⟨5583684193697899973457211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444912258263866631276281 5583684193697899973457211)
          ·
            refine ⟨8375526290546849960185817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583684193697899973457211 8375526290546849960185817)
            ·
              refine ⟨6281644717910137470139363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375526290546849960185817 6281644717910137470139363)
              ·
                refine ⟨9422467076865206205209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281644717910137470139363 9422467076865206205209045)
                ·
                  refine ⟨220839072114028270434587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9422467076865206205209045 220839072114028270434587)
                  ·
                    rfl

theorem cell23_3870743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 7].length) (baseStart_3870743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870743 prefixEnd_3870743 := by exact prefixLift 3870743
  have htrace : WordTrace (prefixWord ++ tailWord_3870743) baseStart_3870743 baseEnd_3870743 := by
    simpa [prefixWord, tailWord_3870743, baseEnd_3870743] using wordTrace_append hprefix tailTrace_3870743
  have hstable : (prefixWord ++ tailWord_3870743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870743).length < 2 ^ (prefixWord ++ tailWord_3870743).sum := by decide
  have hdescent : baseEnd_3870743 < baseStart_3870743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870777 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 5]
def baseStart_3870777 : Nat := 118140960795 + 3870777 * 2 ^ 59
def prefixEnd_3870777 : Nat := 4983230072969 + 3 ^ 40 * 3870777 * 2
def baseEnd_3870777 : Nat := 220841011929834144542903

theorem tailTrace_3870777 : CollatzResearch.WordTrace tailWord_3870777 prefixEnd_3870777 220841011929834144542903 := by
  unfold tailWord_3870777
  simp only [CollatzResearch.WordTrace]
  refine ⟨141178835497843479925754585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94119223665228986617169723 141178835497843479925754585)
  ·
    refine ⟨105884126623382609944315939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141178835497843479925754585 105884126623382609944315939)
    ·
      refine ⟨158826189935073914916473909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105884126623382609944315939 158826189935073914916473909)
      ·
        refine ⟨14889955306413179523419429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158826189935073914916473909 14889955306413179523419429)
        ·
          refine ⟨2791866619952471160641143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14889955306413179523419429 2791866619952471160641143)
          ·
            refine ⟨4187799929928706740961715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791866619952471160641143 4187799929928706740961715)
            ·
              refine ⟨6281699894893060111442573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187799929928706740961715 6281699894893060111442573)
              ·
                refine ⟨2355637460584897541790965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6281699894893060111442573 2355637460584897541790965)
                ·
                  refine ⟨220841011929834144542903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2355637460584897541790965 220841011929834144542903)
                  ·
                    rfl

theorem cell23_3870777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 5].length) (baseStart_3870777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870777 prefixEnd_3870777 := by exact prefixLift 3870777
  have htrace : WordTrace (prefixWord ++ tailWord_3870777) baseStart_3870777 baseEnd_3870777 := by
    simpa [prefixWord, tailWord_3870777, baseEnd_3870777] using wordTrace_append hprefix tailTrace_3870777
  have hstable : (prefixWord ++ tailWord_3870777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870777).length < 2 ^ (prefixWord ++ tailWord_3870777).sum := by decide
  have hdescent : baseEnd_3870777 < baseStart_3870777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870790 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3870790 : Nat := 118140960795 + 3870790 * 2 ^ 59
def prefixEnd_3870790 : Nat := 4983230072969 + 3 ^ 40 * 3870790 * 2
def baseEnd_3870790 : Nat := 662525260872338583341189

theorem tailTrace_3870790 : CollatzResearch.WordTrace tailWord_3870790 prefixEnd_3870790 662525260872338583341189 := by
  unfold tailWord_3870790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411853426462386973311807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94119539764530922097318549 4411853426462386973311807)
  ·
    refine ⟨6617780139693580459967711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4411853426462386973311807 6617780139693580459967711)
    ·
      refine ⟨9926670209540370689951567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6617780139693580459967711 9926670209540370689951567)
      ·
        refine ⟨14890005314310556034927351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9926670209540370689951567 14890005314310556034927351)
        ·
          refine ⟨22335007971465834052391027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890005314310556034927351 22335007971465834052391027)
          ·
            refine ⟨33502511957198751078586541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22335007971465834052391027 33502511957198751078586541)
            ·
              refine ⟨12563441983949531654469953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33502511957198751078586541 12563441983949531654469953)
              ·
                refine ⟨9422581487962148740852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563441983949531654469953 9422581487962148740852465)
                ·
                  refine ⟨7066936115971611555639349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422581487962148740852465 7066936115971611555639349)
                  ·
                    refine ⟨662525260872338583341189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7066936115971611555639349 662525260872338583341189)
                    ·
                      rfl

theorem cell23_3870790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3870790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870790 prefixEnd_3870790 := by exact prefixLift 3870790
  have htrace : WordTrace (prefixWord ++ tailWord_3870790) baseStart_3870790 baseEnd_3870790 := by
    simpa [prefixWord, tailWord_3870790, baseEnd_3870790] using wordTrace_append hprefix tailTrace_3870790
  have hstable : (prefixWord ++ tailWord_3870790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870790).length < 2 ^ (prefixWord ++ tailWord_3870790).sum := by decide
  have hdescent : baseEnd_3870790 < baseStart_3870790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870830 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3870830 : Nat := 118140960795 + 3870830 * 2 ^ 59
def prefixEnd_3870830 : Nat := 4983230072969 + 3 ^ 40 * 3870830 * 2
def baseEnd_3870830 : Nat := 1987596321843195593523383

theorem tailTrace_3870830 : CollatzResearch.WordTrace tailWord_3870830 prefixEnd_3870830 1987596321843195593523383 := by
  unfold tailWord_3870830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647596070831433747179243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94120512377767646651622629 17647596070831433747179243)
  ·
    refine ⟨26471394106247150620768865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17647596070831433747179243 26471394106247150620768865)
    ·
      refine ⟨19853545579685362965576649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26471394106247150620768865 19853545579685362965576649)
      ·
        refine ⟨14890159184764022224182487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19853545579685362965576649 14890159184764022224182487)
        ·
          refine ⟨22335238777146033336273731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890159184764022224182487 22335238777146033336273731)
          ·
            refine ⟨33502858165719050004410597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22335238777146033336273731 33502858165719050004410597)
            ·
              refine ⟨6281785906072321875826987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33502858165719050004410597 6281785906072321875826987)
              ·
                refine ⟨9422678859108482813740481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281785906072321875826987 9422678859108482813740481)
                ·
                  refine ⟨7067009144331362110305361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422678859108482813740481 7067009144331362110305361)
                  ·
                    refine ⟨5300256858248521582729021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067009144331362110305361 5300256858248521582729021)
                    ·
                      refine ⟨1987596321843195593523383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300256858248521582729021 1987596321843195593523383)
                      ·
                        rfl

theorem cell23_3870830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3870830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870830 prefixEnd_3870830 := by exact prefixLift 3870830
  have htrace : WordTrace (prefixWord ++ tailWord_3870830) baseStart_3870830 baseEnd_3870830 := by
    simpa [prefixWord, tailWord_3870830, baseEnd_3870830] using wordTrace_append hprefix tailTrace_3870830
  have hstable : (prefixWord ++ tailWord_3870830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870830).length < 2 ^ (prefixWord ++ tailWord_3870830).sum := by decide
  have hdescent : baseEnd_3870830 < baseStart_3870830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870887 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3870887 : Nat := 118140960795 + 3870887 * 2 ^ 59
def prefixEnd_3870887 : Nat := 4983230072969 + 3 ^ 40 * 3870887 * 2
def baseEnd_3870887 : Nat := 1987625590240501870510621

theorem tailTrace_3870887 : CollatzResearch.WordTrace tailWord_3870887 prefixEnd_3870887 1987625590240501870510621 := by
  unfold tailWord_3870887
  simp only [CollatzResearch.WordTrace]
  refine ⟨141182847527444968712258915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94121898351629979141505943 141182847527444968712258915)
  ·
    refine ⟨211774271291167453068388373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141182847527444968712258915 211774271291167453068388373)
    ·
      refine ⟨9926918966773474362580705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211774271291167453068388373 9926918966773474362580705)
      ·
        refine ⟨7445189225080105771935529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9926918966773474362580705 7445189225080105771935529)
        ·
          refine ⟨5583891918810079328951647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445189225080105771935529 5583891918810079328951647)
          ·
            refine ⟨8375837878215118993427471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583891918810079328951647 8375837878215118993427471)
            ·
              refine ⟨12563756817322678490141207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375837878215118993427471 12563756817322678490141207)
              ·
                refine ⟨18845635225984017735211811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563756817322678490141207 18845635225984017735211811)
                ·
                  refine ⟨28268452838976026602817717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18845635225984017735211811 28268452838976026602817717)
                  ·
                    refine ⟨2650167453654002494014161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28268452838976026602817717 2650167453654002494014161)
                    ·
                      refine ⟨1987625590240501870510621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650167453654002494014161 1987625590240501870510621)
                      ·
                        rfl

theorem cell23_3870887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3870887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870887 prefixEnd_3870887 := by exact prefixLift 3870887
  have htrace : WordTrace (prefixWord ++ tailWord_3870887) baseStart_3870887 baseEnd_3870887 := by
    simpa [prefixWord, tailWord_3870887, baseEnd_3870887] using wordTrace_append hprefix tailTrace_3870887
  have hstable : (prefixWord ++ tailWord_3870887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870887).length < 2 ^ (prefixWord ++ tailWord_3870887).sum := by decide
  have hdescent : baseEnd_3870887 < baseStart_3870887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870930 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3870930 : Nat := 118140960795 + 3870930 * 2 ^ 59
def prefixEnd_3870930 : Nat := 4983230072969 + 3 ^ 40 * 3870930 * 2
def baseEnd_3870930 : Nat := 1987647669908645202272923

theorem tailTrace_3870930 : CollatzResearch.WordTrace tailWord_3870930 prefixEnd_3870930 1987647669908645202272923 := by
  unfold tailWord_3870930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296103966572296764018561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94122943910859458037382829 35296103966572296764018561)
  ·
    refine ⟨26472077974929222573013921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35296103966572296764018561 26472077974929222573013921)
    ·
      refine ⟨19854058481196916929760441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26472077974929222573013921 19854058481196916929760441)
      ·
        refine ⟨14890543860897687697320331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19854058481196916929760441 14890543860897687697320331)
        ·
          refine ⟨22335815791346531545980497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14890543860897687697320331 22335815791346531545980497)
          ·
            refine ⟨16751861843509898659485373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22335815791346531545980497 16751861843509898659485373)
            ·
              refine ⟨6281948191316211997307015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16751861843509898659485373 6281948191316211997307015)
              ·
                refine ⟨9422922286974317995960523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281948191316211997307015 9422922286974317995960523)
                ·
                  refine ⟨14134383430461476993940785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422922286974317995960523 14134383430461476993940785)
                  ·
                    refine ⟨10600787572846107745455589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14134383430461476993940785 10600787572846107745455589)
                    ·
                      refine ⟨1987647669908645202272923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10600787572846107745455589 1987647669908645202272923)
                      ·
                        rfl

theorem cell23_3870930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3870930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870930 prefixEnd_3870930 := by exact prefixLift 3870930
  have htrace : WordTrace (prefixWord ++ tailWord_3870930) baseStart_3870930 baseEnd_3870930 := by
    simpa [prefixWord, tailWord_3870930, baseEnd_3870930] using wordTrace_append hprefix tailTrace_3870930
  have hstable : (prefixWord ++ tailWord_3870930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870930).length < 2 ^ (prefixWord ++ tailWord_3870930).sum := by decide
  have hdescent : baseEnd_3870930 < baseStart_3870930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870934 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3870934 : Nat := 118140960795 + 3870934 * 2 ^ 59
def prefixEnd_3870934 : Nat := 4983230072969 + 3 ^ 40 * 3870934 * 2
def baseEnd_3870934 : Nat := 1987649723831263186622905

theorem tailTrace_3870934 : CollatzResearch.WordTrace tailWord_3870934 prefixEnd_3870934 1987649723831263186622905 := by
  unfold tailWord_3870934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824035109892168483701241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94123041172183130492813237 8824035109892168483701241)
  ·
    refine ⟨6618026332419126362775931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8824035109892168483701241 6618026332419126362775931)
    ·
      refine ⟨9927039498628689544163897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618026332419126362775931 9927039498628689544163897)
      ·
        refine ⟨7445279623971517158122923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927039498628689544163897 7445279623971517158122923)
        ·
          refine ⟨11167919435957275737184385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445279623971517158122923 11167919435957275737184385)
          ·
            refine ⟨8375939576967956802888289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11167919435957275737184385 8375939576967956802888289)
            ·
              refine ⟨6281954682725967602166217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375939576967956802888289 6281954682725967602166217)
              ·
                refine ⟨4711466012044475701624663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6281954682725967602166217 4711466012044475701624663)
                ·
                  refine ⟨7067199018066713552436995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711466012044475701624663 7067199018066713552436995)
                  ·
                    refine ⟨10600798527100070328655493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7067199018066713552436995 10600798527100070328655493)
                    ·
                      refine ⟨1987649723831263186622905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10600798527100070328655493 1987649723831263186622905)
                      ·
                        rfl

theorem cell23_3870934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3870934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870934 prefixEnd_3870934 := by exact prefixLift 3870934
  have htrace : WordTrace (prefixWord ++ tailWord_3870934) baseStart_3870934 baseEnd_3870934 := by
    simpa [prefixWord, tailWord_3870934, baseEnd_3870934] using wordTrace_append hprefix tailTrace_3870934
  have hstable : (prefixWord ++ tailWord_3870934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870934).length < 2 ^ (prefixWord ++ tailWord_3870934).sum := by decide
  have hdescent : baseEnd_3870934 < baseStart_3870934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870951 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3870951 : Nat := 118140960795 + 3870951 * 2 ^ 59
def prefixEnd_3870951 : Nat := 4983230072969 + 3 ^ 40 * 3870951 * 2
def baseEnd_3870951 : Nat := 1987658453002389620110327

theorem tailTrace_3870951 : CollatzResearch.WordTrace tailWord_3870951 prefixEnd_3870951 1987658453002389620110327 := by
  unfold tailWord_3870951
  simp only [CollatzResearch.WordTrace]
  refine ⟨141185181799213107642588707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94123454532808738428392471 141185181799213107642588707)
  ·
    refine ⟨211777772698819661463883061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141185181799213107642588707 211777772698819661463883061)
    ·
      refine ⟨19854166190514343262239037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211777772698819661463883061 19854166190514343262239037)
      ·
        refine ⟨7445312321442878723339639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19854166190514343262239037 7445312321442878723339639)
        ·
          refine ⟨11167968482164318085009459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445312321442878723339639 11167968482164318085009459)
          ·
            refine ⟨16751952723246477127514189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167968482164318085009459 16751952723246477127514189)
            ·
              refine ⟨6281982271217428922817821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16751952723246477127514189 6281982271217428922817821)
              ·
                refine ⟨2355743351706535846056683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6281982271217428922817821 2355743351706535846056683)
                ·
                  refine ⟨3533615027559803769085025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355743351706535846056683 3533615027559803769085025)
                  ·
                    refine ⟨2650211270669852826813769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533615027559803769085025 2650211270669852826813769)
                    ·
                      refine ⟨1987658453002389620110327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650211270669852826813769 1987658453002389620110327)
                      ·
                        rfl

theorem cell23_3870951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3870951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870951 prefixEnd_3870951 := by exact prefixLift 3870951
  have htrace : WordTrace (prefixWord ++ tailWord_3870951) baseStart_3870951 baseEnd_3870951 := by
    simpa [prefixWord, tailWord_3870951, baseEnd_3870951] using wordTrace_append hprefix tailTrace_3870951
  have hstable : (prefixWord ++ tailWord_3870951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870951).length < 2 ^ (prefixWord ++ tailWord_3870951).sum := by decide
  have hdescent : baseEnd_3870951 < baseStart_3870951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870984 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_3870984 : Nat := 118140960795 + 3870984 * 2 ^ 59
def prefixEnd_3870984 : Nat := 4983230072969 + 3 ^ 40 * 3870984 * 2
def baseEnd_3870984 : Nat := 1987675397863987990997675

theorem tailTrace_3870984 : CollatzResearch.WordTrace tailWord_3870984 prefixEnd_3870984 1987675397863987990997675 := by
  unfold tailWord_3870984
  simp only [CollatzResearch.WordTrace]
  refine ⟨70593192704046777139270003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94124256938729036185693337 70593192704046777139270003)
  ·
    refine ⟨105889789056070165708905005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70593192704046777139270003 105889789056070165708905005)
    ·
      refine ⟨39708670896026312140839377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105889789056070165708905005 39708670896026312140839377)
      ·
        refine ⟨29781503172019734105629533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39708670896026312140839377 29781503172019734105629533)
        ·
          refine ⟨11168063689507400289611075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29781503172019734105629533 11168063689507400289611075)
          ·
            refine ⟨16752095534261100434416613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168063689507400289611075 16752095534261100434416613)
            ·
              refine ⟨3141017912673956331453115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16752095534261100434416613 3141017912673956331453115)
              ·
                refine ⟨4711526869010934497179673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141017912673956331453115 4711526869010934497179673)
                ·
                  refine ⟨3533645151758200872884755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711526869010934497179673 3533645151758200872884755)
                  ·
                    refine ⟨5300467727637301309327133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3533645151758200872884755 5300467727637301309327133)
                    ·
                      refine ⟨1987675397863987990997675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300467727637301309327133 1987675397863987990997675)
                      ·
                        rfl

theorem cell23_3870984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_3870984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870984 prefixEnd_3870984 := by exact prefixLift 3870984
  have htrace : WordTrace (prefixWord ++ tailWord_3870984) baseStart_3870984 baseEnd_3870984 := by
    simpa [prefixWord, tailWord_3870984, baseEnd_3870984] using wordTrace_append hprefix tailTrace_3870984
  have hstable : (prefixWord ++ tailWord_3870984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870984).length < 2 ^ (prefixWord ++ tailWord_3870984).sum := by decide
  have hdescent : baseEnd_3870984 < baseStart_3870984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870993 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_3870993 : Nat := 118140960795 + 3870993 * 2 ^ 59
def prefixEnd_3870993 : Nat := 4983230072969 + 3 ^ 40 * 3870993 * 2
def baseEnd_3870993 : Nat := 1987680019189878455785133

theorem tailTrace_3870993 : CollatzResearch.WordTrace tailWord_3870993 prefixEnd_3870993 1987680019189878455785133 := by
  unfold tailWord_3870993
  simp only [CollatzResearch.WordTrace]
  refine ⟨141186713665060948815617633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94124475776707299210411755 141186713665060948815617633)
  ·
    refine ⟨105890035248795711611713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141186713665060948815617633 105890035248795711611713225)
    ·
      refine ⟨79417526436596783708784919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105890035248795711611713225 79417526436596783708784919)
      ·
        refine ⟨119126289654895175563177379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79417526436596783708784919 119126289654895175563177379)
        ·
          refine ⟨178689434482342763344766069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119126289654895175563177379 178689434482342763344766069)
          ·
            refine ⟨16752134482719634063571819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178689434482342763344766069 16752134482719634063571819)
            ·
              refine ⟨25128201724079451095357729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752134482719634063571819 25128201724079451095357729)
              ·
                refine ⟨18846151293059588321518297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25128201724079451095357729 18846151293059588321518297)
                ·
                  refine ⟨14134613469794691241138723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18846151293059588321518297 14134613469794691241138723)
                  ·
                    refine ⟨21201920204692036861708085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14134613469794691241138723 21201920204692036861708085)
                    ·
                      refine ⟨1987680019189878455785133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21201920204692036861708085 1987680019189878455785133)
                      ·
                        rfl

theorem cell23_3870993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_3870993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3870993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3870993 prefixEnd_3870993 := by exact prefixLift 3870993
  have htrace : WordTrace (prefixWord ++ tailWord_3870993) baseStart_3870993 baseEnd_3870993 := by
    simpa [prefixWord, tailWord_3870993, baseEnd_3870993] using wordTrace_append hprefix tailTrace_3870993
  have hstable : (prefixWord ++ tailWord_3870993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870993).length < 2 ^ (prefixWord ++ tailWord_3870993).sum := by decide
  have hdescent : baseEnd_3870993 < baseStart_3870993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871007 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 4, 2]
def baseStart_3871007 : Nat := 118140960795 + 3871007 * 2 ^ 59
def prefixEnd_3871007 : Nat := 4983230072969 + 3 ^ 40 * 3871007 * 2
def baseEnd_3871007 : Nat := 1987687207919041401010069

theorem tailTrace_3871007 : CollatzResearch.WordTrace tailWord_3871007 prefixEnd_3871007 1987687207919041401010069 := by
  unfold tailWord_3871007
  simp only [CollatzResearch.WordTrace]
  refine ⟨141187224287010229206627275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94124816191340152804418183 141187224287010229206627275)
  ·
    refine ⟨211780836430515343809940913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141187224287010229206627275 211780836430515343809940913)
    ·
      refine ⟨158835627322886507857455685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211780836430515343809940913 158835627322886507857455685)
      ·
        refine ⟨29781680123041220223272941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158835627322886507857455685 29781680123041220223272941)
        ·
          refine ⟨11168130046140457583727353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29781680123041220223272941 11168130046140457583727353)
          ·
            refine ⟨8376097534605343187795515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11168130046140457583727353 8376097534605343187795515)
            ·
              refine ⟨12564146301908014781693273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376097534605343187795515 12564146301908014781693273)
              ·
                refine ⟨9423109726431011086269955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12564146301908014781693273 9423109726431011086269955)
                ·
                  refine ⟨14134664589646516629404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423109726431011086269955 14134664589646516629404933)
                  ·
                    refine ⟨2650249610558721868013425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14134664589646516629404933 2650249610558721868013425)
                    ·
                      refine ⟨1987687207919041401010069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650249610558721868013425 1987687207919041401010069)
                      ·
                        rfl

theorem cell23_3871007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_3871007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871007 prefixEnd_3871007 := by exact prefixLift 3871007
  have htrace : WordTrace (prefixWord ++ tailWord_3871007) baseStart_3871007 baseEnd_3871007 := by
    simpa [prefixWord, tailWord_3871007, baseEnd_3871007] using wordTrace_append hprefix tailTrace_3871007
  have hstable : (prefixWord ++ tailWord_3871007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871007).length < 2 ^ (prefixWord ++ tailWord_3871007).sum := by decide
  have hdescent : baseEnd_3871007 < baseStart_3871007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871010 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3871010 : Nat := 118140960795 + 3871010 * 2 ^ 59
def prefixEnd_3871010 : Nat := 4983230072969 + 3 ^ 40 * 3871010 * 2
def baseEnd_3871010 : Nat := 1987688748361004889272555

theorem tailTrace_3871010 : CollatzResearch.WordTrace tailWord_3871010 prefixEnd_3871010 1987688748361004889272555 := by
  unfold tailWord_3871010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296833426499840179746621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94124889137332907145990989 35296833426499840179746621)
  ·
    refine ⟨13236312534937440067404983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35296833426499840179746621 13236312534937440067404983)
    ·
      refine ⟨19854468802406160101107475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236312534937440067404983 19854468802406160101107475)
      ·
        refine ⟨29781703203609240151661213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19854468802406160101107475 29781703203609240151661213)
        ·
          refine ⟨11168138701353465056872955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29781703203609240151661213 11168138701353465056872955)
          ·
            refine ⟨16752208052030197585309433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168138701353465056872955 16752208052030197585309433)
            ·
              refine ⟨12564156039022648188982075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16752208052030197585309433 12564156039022648188982075)
              ·
                refine ⟨18846234058533972283473113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564156039022648188982075 18846234058533972283473113)
                ·
                  refine ⟨14134675543900479212604835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18846234058533972283473113 14134675543900479212604835)
                  ·
                    refine ⟨21202013315850718818907253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14134675543900479212604835 21202013315850718818907253)
                    ·
                      refine ⟨1987688748361004889272555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21202013315850718818907253 1987688748361004889272555)
                      ·
                        rfl

theorem cell23_3871010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3871010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871010 prefixEnd_3871010 := by exact prefixLift 3871010
  have htrace : WordTrace (prefixWord ++ tailWord_3871010) baseStart_3871010 baseEnd_3871010 := by
    simpa [prefixWord, tailWord_3871010, baseEnd_3871010] using wordTrace_append hprefix tailTrace_3871010
  have hstable : (prefixWord ++ tailWord_3871010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871010).length < 2 ^ (prefixWord ++ tailWord_3871010).sum := by decide
  have hdescent : baseEnd_3871010 < baseStart_3871010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871043 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 4, 5]
def baseStart_3871043 : Nat := 118140960795 + 3871043 * 2 ^ 59
def prefixEnd_3871043 : Nat := 4983230072969 + 3 ^ 40 * 3871043 * 2
def baseEnd_3871043 : Nat := 662568564407534420053301

theorem tailTrace_3871043 : CollatzResearch.WordTrace tailWord_3871043 prefixEnd_3871043 662568564407534420053301 := by
  unfold tailWord_3871043
  simp only [CollatzResearch.WordTrace]
  refine ⟨141188537314879807354937783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94125691543253204903291855 141188537314879807354937783)
  ·
    refine ⟨211782805972319711032406675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141188537314879807354937783 211782805972319711032406675)
    ·
      refine ⟨317674208958479566548610013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211782805972319711032406675 317674208958479566548610013)
      ·
        refine ⟨119127828359429837455728755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317674208958479566548610013 119127828359429837455728755)
        ·
          refine ⟨178691742539144756183593133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119127828359429837455728755 178691742539144756183593133)
          ·
            refine ⟨67009403452179283568847425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178691742539144756183593133 67009403452179283568847425)
            ·
              refine ⟨50257052589134462676635569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67009403452179283568847425 50257052589134462676635569)
              ·
                refine ⟨37692789441850847007476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50257052589134462676635569 37692789441850847007476677)
                ·
                  refine ⟨7067398020347033813901877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37692789441850847007476677 7067398020347033813901877)
                  ·
                    refine ⟨662568564407534420053301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7067398020347033813901877 662568564407534420053301)
                    ·
                      rfl

theorem cell23_3871043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].length) (baseStart_3871043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871043 prefixEnd_3871043 := by exact prefixLift 3871043
  have htrace : WordTrace (prefixWord ++ tailWord_3871043) baseStart_3871043 baseEnd_3871043 := by
    simpa [prefixWord, tailWord_3871043, baseEnd_3871043] using wordTrace_append hprefix tailTrace_3871043
  have hstable : (prefixWord ++ tailWord_3871043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871043).length < 2 ^ (prefixWord ++ tailWord_3871043).sum := by decide
  have hdescent : baseEnd_3871043 < baseStart_3871043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871060 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3871060 : Nat := 118140960795 + 3871060 * 2 ^ 59
def prefixEnd_3871060 : Nat := 4983230072969 + 3 ^ 40 * 3871060 * 2
def baseEnd_3871060 : Nat := 662571474131243231215775

theorem tailTrace_3871060 : CollatzResearch.WordTrace tailWord_3871060 prefixEnd_3871060 662571474131243231215775 := by
  unfold tailWord_3871060
  simp only [CollatzResearch.WordTrace]
  refine ⟨70594578677909109629153317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94126104903878812838871089 70594578677909109629153317)
  ·
    refine ⟨13236483502107958055466247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70594578677909109629153317 13236483502107958055466247)
    ·
      refine ⟨19854725253161937083199371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236483502107958055466247 19854725253161937083199371)
      ·
        refine ⟨29782087879742905624799057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19854725253161937083199371 29782087879742905624799057)
        ·
          refine ⟨22336565909807179218599293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29782087879742905624799057 22336565909807179218599293)
          ·
            refine ⟨8376212216177692206974735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22336565909807179218599293 8376212216177692206974735)
            ·
              refine ⟨12564318324266538310462103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376212216177692206974735 12564318324266538310462103)
              ·
                refine ⟨18846477486399807465693155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564318324266538310462103 18846477486399807465693155)
                ·
                  refine ⟨28269716229599711198539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18846477486399807465693155 28269716229599711198539733)
                  ·
                    refine ⟨662571474131243231215775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28269716229599711198539733 662571474131243231215775)
                    ·
                      rfl

theorem cell23_3871060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3871060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871060 prefixEnd_3871060 := by exact prefixLift 3871060
  have htrace : WordTrace (prefixWord ++ tailWord_3871060) baseStart_3871060 baseEnd_3871060 := by
    simpa [prefixWord, tailWord_3871060, baseEnd_3871060] using wordTrace_append hprefix tailTrace_3871060
  have hstable : (prefixWord ++ tailWord_3871060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871060).length < 2 ^ (prefixWord ++ tailWord_3871060).sum := by decide
  have hdescent : baseEnd_3871060 < baseStart_3871060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871100 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3871100 : Nat := 118140960795 + 3871100 * 2 ^ 59
def prefixEnd_3871100 : Nat := 4983230072969 + 3 ^ 40 * 3871100 * 2
def baseEnd_3871100 : Nat := 1987734961619909537147141

theorem tailTrace_3871100 : CollatzResearch.WordTrace tailWord_3871100 prefixEnd_3871100 1987734961619909537147141 := by
  unfold tailWord_3871100
  simp only [CollatzResearch.WordTrace]
  refine ⟨70595308137836653044881377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94127077517115537393175169 70595308137836653044881377)
  ·
    refine ⟨52946481103377489783661033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70595308137836653044881377 52946481103377489783661033)
    ·
      refine ⟨39709860827533117337745775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52946481103377489783661033 39709860827533117337745775)
      ·
        refine ⟨59564791241299676006618663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39709860827533117337745775 59564791241299676006618663)
        ·
          refine ⟨89347186861949514009927995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59564791241299676006618663 89347186861949514009927995)
          ·
            refine ⟨134020780292924271014891993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89347186861949514009927995 134020780292924271014891993)
            ·
              refine ⟨100515585219693203261168995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134020780292924271014891993 100515585219693203261168995)
              ·
                refine ⟨150773377829539804891753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100515585219693203261168995 150773377829539804891753493)
                ·
                  refine ⟨7067502085759678354300945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150773377829539804891753493 7067502085759678354300945)
                  ·
                    refine ⟨5300626564319758765725709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067502085759678354300945 5300626564319758765725709)
                    ·
                      refine ⟨1987734961619909537147141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300626564319758765725709 1987734961619909537147141)
                      ·
                        rfl

theorem cell23_3871100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3871100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871100 prefixEnd_3871100 := by exact prefixLift 3871100
  have htrace : WordTrace (prefixWord ++ tailWord_3871100) baseStart_3871100 baseEnd_3871100 := by
    simpa [prefixWord, tailWord_3871100, baseEnd_3871100] using wordTrace_append hprefix tailTrace_3871100
  have hstable : (prefixWord ++ tailWord_3871100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871100).length < 2 ^ (prefixWord ++ tailWord_3871100).sum := by decide
  have hdescent : baseEnd_3871100 < baseStart_3871100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871134 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3871134 : Nat := 118140960795 + 3871134 * 2 ^ 59
def prefixEnd_3871134 : Nat := 4983230072969 + 3 ^ 40 * 3871134 * 2
def baseEnd_3871134 : Nat := 1987752419962162404121985

theorem tailTrace_3871134 : CollatzResearch.WordTrace tailWord_3871134 prefixEnd_3871134 1987752419962162404121985 := by
  unfold tailWord_3871134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648982044693766237062557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94127904238366753264333637 17648982044693766237062557)
  ·
    refine ⟨6618368266760162338898459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17648982044693766237062557 6618368266760162338898459)
    ·
      refine ⟨9927552400140243508347689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618368266760162338898459 9927552400140243508347689)
      ·
        refine ⟨7445664300105182631260767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927552400140243508347689 7445664300105182631260767)
        ·
          refine ⟨11168496450157773946891151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445664300105182631260767 11168496450157773946891151)
          ·
            refine ⟨16752744675236660920336727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168496450157773946891151 16752744675236660920336727)
            ·
              refine ⟨25129117012854991380505091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752744675236660920336727 25129117012854991380505091)
              ·
                refine ⟨37693675519282487070757637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25129117012854991380505091 37693675519282487070757637)
                ·
                  refine ⟨7067564159865466325767057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37693675519282487070757637 7067564159865466325767057)
                  ·
                    refine ⟨5300673119899099744325293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067564159865466325767057 5300673119899099744325293)
                    ·
                      refine ⟨1987752419962162404121985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300673119899099744325293 1987752419962162404121985)
                      ·
                        rfl

theorem cell23_3871134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3871134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871134 prefixEnd_3871134 := by exact prefixLift 3871134
  have htrace : WordTrace (prefixWord ++ tailWord_3871134) baseStart_3871134 baseEnd_3871134 := by
    simpa [prefixWord, tailWord_3871134, baseEnd_3871134] using wordTrace_append hprefix tailTrace_3871134
  have hstable : (prefixWord ++ tailWord_3871134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871134).length < 2 ^ (prefixWord ++ tailWord_3871134).sum := by decide
  have hdescent : baseEnd_3871134 < baseStart_3871134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871200 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3871200 : Nat := 118140960795 + 3871200 * 2 ^ 59
def prefixEnd_3871200 : Nat := 4983230072969 + 3 ^ 40 * 3871200 * 2
def baseEnd_3871200 : Nat := 1987786309685359145896681

theorem tailTrace_3871200 : CollatzResearch.WordTrace tailWord_3871200 prefixEnd_3871200 1987786309685359145896681 := by
  unfold tailWord_3871200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70597131787655511584201527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94129509050207348778935369 70597131787655511584201527)
  ·
    refine ⟨105895697681483267376302291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70597131787655511584201527 105895697681483267376302291)
    ·
      refine ⟨158843546522224901064453437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105895697681483267376302291 158843546522224901064453437)
      ·
        refine ⟨59566329945834337899170039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158843546522224901064453437 59566329945834337899170039)
        ·
          refine ⟨89349494918751506848755059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59566329945834337899170039 89349494918751506848755059)
          ·
            refine ⟨134024242378127260273132589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89349494918751506848755059 134024242378127260273132589)
            ·
              refine ⟨50259090891797722602424721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134024242378127260273132589 50259090891797722602424721)
              ·
                refine ⟨37694318168848291951818541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50259090891797722602424721 37694318168848291951818541)
                ·
                  refine ⟨14135369313318109481931953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37694318168848291951818541 14135369313318109481931953)
                  ·
                    refine ⟨10601526984988582111448965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14135369313318109481931953 10601526984988582111448965)
                    ·
                      refine ⟨1987786309685359145896681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10601526984988582111448965 1987786309685359145896681)
                      ·
                        rfl

theorem cell23_3871200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3871200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871200 prefixEnd_3871200 := by exact prefixLift 3871200
  have htrace : WordTrace (prefixWord ++ tailWord_3871200) baseStart_3871200 baseEnd_3871200 := by
    simpa [prefixWord, tailWord_3871200, baseEnd_3871200] using wordTrace_append hprefix tailTrace_3871200
  have hstable : (prefixWord ++ tailWord_3871200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871200).length < 2 ^ (prefixWord ++ tailWord_3871200).sum := by decide
  have hdescent : baseEnd_3871200 < baseStart_3871200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871207 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3871207 : Nat := 118140960795 + 3871207 * 2 ^ 59
def prefixEnd_3871207 : Nat := 4983230072969 + 3 ^ 40 * 3871207 * 2
def baseEnd_3871207 : Nat := 1987789904049940618509149

theorem tailTrace_3871207 : CollatzResearch.WordTrace tailWord_3871207 prefixEnd_3871207 1987789904049940618509149 := by
  unfold tailWord_3871207
  simp only [CollatzResearch.WordTrace]
  refine ⟨141194518886285663363907875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94129679257523775575938583 141194518886285663363907875)
  ·
    refine ⟨211791778329428495045861813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141194518886285663363907875 211791778329428495045861813)
    ·
      refine ⟨19855479218383921410549545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211791778329428495045861813 19855479218383921410549545)
      ·
        refine ⟨14891609413787941057912159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19855479218383921410549545 14891609413787941057912159)
        ·
          refine ⟨22337414120681911586868239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891609413787941057912159 22337414120681911586868239)
          ·
            refine ⟨33506121181022867380302359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337414120681911586868239 33506121181022867380302359)
            ·
              refine ⟨50259181771534301070453539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33506121181022867380302359 50259181771534301070453539)
              ·
                refine ⟨75388772657301451605680309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50259181771534301070453539 75388772657301451605680309)
                ·
                  refine ⟨7067697436622011088032529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75388772657301451605680309 7067697436622011088032529)
                  ·
                    refine ⟨5300773077466508316024397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7067697436622011088032529 5300773077466508316024397)
                    ·
                      refine ⟨1987789904049940618509149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300773077466508316024397 1987789904049940618509149)
                      ·
                        rfl

theorem cell23_3871207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3871207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871207 prefixEnd_3871207 := by exact prefixLift 3871207
  have htrace : WordTrace (prefixWord ++ tailWord_3871207) baseStart_3871207 baseEnd_3871207 := by
    simpa [prefixWord, tailWord_3871207, baseEnd_3871207] using wordTrace_append hprefix tailTrace_3871207
  have hstable : (prefixWord ++ tailWord_3871207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871207).length < 2 ^ (prefixWord ++ tailWord_3871207).sum := by decide
  have hdescent : baseEnd_3871207 < baseStart_3871207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871214 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3871214 : Nat := 118140960795 + 3871214 * 2 ^ 59
def prefixEnd_3871214 : Nat := 4983230072969 + 3 ^ 40 * 3871214 * 2
def baseEnd_3871214 : Nat := 662597832804840697040539

theorem tailTrace_3871214 : CollatzResearch.WordTrace tailWord_3871214 prefixEnd_3871214 662597832804840697040539 := by
  unfold tailWord_3871214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649346774657537944926587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94129849464840202372941797 17649346774657537944926587)
  ·
    refine ⟨26474020161986306917389881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649346774657537944926587 26474020161986306917389881)
    ·
      refine ⟨19855515121489730188042411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26474020161986306917389881 19855515121489730188042411)
      ·
        refine ⟨29783272682234595282063617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855515121489730188042411 29783272682234595282063617)
        ·
          refine ⟨22337454511675946461547713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29783272682234595282063617 22337454511675946461547713)
          ·
            refine ⟨16753090883756959846160785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22337454511675946461547713 16753090883756959846160785)
            ·
              refine ⟨12564818162817719884620589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16753090883756959846160785 12564818162817719884620589)
              ·
                refine ⟨4711806811056644956732721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12564818162817719884620589 4711806811056644956732721)
                ·
                  refine ⟨3533855108292483717549541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711806811056644956732721 3533855108292483717549541)
                  ·
                    refine ⟨662597832804840697040539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533855108292483717549541 662597832804840697040539)
                    ·
                      rfl

theorem cell23_3871214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3871214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871214 prefixEnd_3871214 := by exact prefixLift 3871214
  have htrace : WordTrace (prefixWord ++ tailWord_3871214) baseStart_3871214 baseEnd_3871214 := by
    simpa [prefixWord, tailWord_3871214, baseEnd_3871214] using wordTrace_append hprefix tailTrace_3871214
  have hstable : (prefixWord ++ tailWord_3871214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871214).length < 2 ^ (prefixWord ++ tailWord_3871214).sum := by decide
  have hdescent : baseEnd_3871214 < baseStart_3871214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871217 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_3871217 : Nat := 118140960795 + 3871217 * 2 ^ 59
def prefixEnd_3871217 : Nat := 4983230072969 + 3 ^ 40 * 3871217 * 2
def baseEnd_3871217 : Nat := 1987795038856485579384103

theorem tailTrace_3871217 : CollatzResearch.WordTrace tailWord_3871217 prefixEnd_3871217 1987795038856485579384103 := by
  unfold tailWord_3871217
  simp only [CollatzResearch.WordTrace]
  refine ⟨141194883616249435071771905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94129922410832956714514603 141194883616249435071771905)
  ·
    refine ⟨105896162712187076303828929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141194883616249435071771905 105896162712187076303828929)
    ·
      refine ⟨79422122034140307227871697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105896162712187076303828929 79422122034140307227871697)
      ·
        refine ⟨59566591525605230420903773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79422122034140307227871697 59566591525605230420903773)
        ·
          refine ⟨22337471822101961407838915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59566591525605230420903773 22337471822101961407838915)
          ·
            refine ⟨33506207733152942111758373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337471822101961407838915 33506207733152942111758373)
            ·
              refine ⟨6282413949966176645954695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33506207733152942111758373 6282413949966176645954695)
              ·
                refine ⟨9423620924949264968932043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282413949966176645954695 9423620924949264968932043)
                ·
                  refine ⟨14135431387423897453398065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423620924949264968932043 14135431387423897453398065)
                  ·
                    refine ⟨10601573540567923090048549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14135431387423897453398065 10601573540567923090048549)
                    ·
                      refine ⟨1987795038856485579384103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10601573540567923090048549 1987795038856485579384103)
                      ·
                        rfl

theorem cell23_3871217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_3871217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871217 prefixEnd_3871217 := by exact prefixLift 3871217
  have htrace : WordTrace (prefixWord ++ tailWord_3871217) baseStart_3871217 baseEnd_3871217 := by
    simpa [prefixWord, tailWord_3871217, baseEnd_3871217] using wordTrace_append hprefix tailTrace_3871217
  have hstable : (prefixWord ++ tailWord_3871217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871217).length < 2 ^ (prefixWord ++ tailWord_3871217).sum := by decide
  have hdescent : baseEnd_3871217 < baseStart_3871217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871237 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_3871237 : Nat := 118140960795 + 3871237 * 2 ^ 59
def prefixEnd_3871237 : Nat := 4983230072969 + 3 ^ 40 * 3871237 * 2
def baseEnd_3871237 : Nat := 1987805308469575501134011

theorem tailTrace_3871237 : CollatzResearch.WordTrace tailWord_3871237 prefixEnd_3871237 1987805308469575501134011 := by
  unfold tailWord_3871237
  simp only [CollatzResearch.WordTrace]
  refine ⟨141195613076176978487499965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94130408717451318991666643 141195613076176978487499965)
  ·
    refine ⟨52948354903566366932812487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141195613076176978487499965 52948354903566366932812487)
    ·
      refine ⟨79422532355349550399218731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52948354903566366932812487 79422532355349550399218731)
      ·
        refine ⟨119133798533024325598828097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79422532355349550399218731 119133798533024325598828097)
        ·
          refine ⟨89350348899768244199121073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119133798533024325598828097 89350348899768244199121073)
          ·
            refine ⟨67012761674826183149340805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89350348899768244199121073 67012761674826183149340805)
            ·
              refine ⟨12564892814029909340501401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67012761674826183149340805 12564892814029909340501401)
              ·
                refine ⟨9423669610522432005376051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12564892814029909340501401 9423669610522432005376051)
                ·
                  refine ⟨14135504415783648008064077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423669610522432005376051 14135504415783648008064077)
                  ·
                    refine ⟨5300814155918868003024029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14135504415783648008064077 5300814155918868003024029)
                    ·
                      refine ⟨1987805308469575501134011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300814155918868003024029 1987805308469575501134011)
                      ·
                        rfl

theorem cell23_3871237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_3871237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871237 prefixEnd_3871237 := by exact prefixLift 3871237
  have htrace : WordTrace (prefixWord ++ tailWord_3871237) baseStart_3871237 baseEnd_3871237 := by
    simpa [prefixWord, tailWord_3871237, baseEnd_3871237] using wordTrace_append hprefix tailTrace_3871237
  have hstable : (prefixWord ++ tailWord_3871237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871237).length < 2 ^ (prefixWord ++ tailWord_3871237).sum := by decide
  have hdescent : baseEnd_3871237 < baseStart_3871237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871268 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3871268 : Nat := 118140960795 + 3871268 * 2 ^ 59
def prefixEnd_3871268 : Nat := 4983230072969 + 3 ^ 40 * 3871268 * 2
def baseEnd_3871268 : Nat := 1987821226369864879846369

theorem tailTrace_3871268 : CollatzResearch.WordTrace tailWord_3871268 prefixEnd_3871268 1987821226369864879846369 := by
  unfold tailWord_3871268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70598371869532335390939229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94131162492709780521252305 70598371869532335390939229)
  ·
    refine ⟨26474389451074625771602211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70598371869532335390939229 26474389451074625771602211)
    ·
      refine ⟨39711584176611938657403317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26474389451074625771602211 39711584176611938657403317)
      ·
        refine ⟨3722961016557369249131561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39711584176611938657403317 3722961016557369249131561)
        ·
          refine ⟨2792220762418026936848671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722961016557369249131561 2792220762418026936848671)
          ·
            refine ⟨4188331143627040405273007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792220762418026936848671 4188331143627040405273007)
            ·
              refine ⟨6282496715440560607909511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188331143627040405273007 6282496715440560607909511)
              ·
                refine ⟨9423745073160840911864267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282496715440560607909511 9423745073160840911864267)
                ·
                  refine ⟨14135617609741261367796401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9423745073160840911864267 14135617609741261367796401)
                  ·
                    refine ⟨10601713207305946025847301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14135617609741261367796401 10601713207305946025847301)
                    ·
                      refine ⟨1987821226369864879846369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10601713207305946025847301 1987821226369864879846369)
                      ·
                        rfl

theorem cell23_3871268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3871268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871268 prefixEnd_3871268 := by exact prefixLift 3871268
  have htrace : WordTrace (prefixWord ++ tailWord_3871268) baseStart_3871268 baseEnd_3871268 := by
    simpa [prefixWord, tailWord_3871268, baseEnd_3871268] using wordTrace_append hprefix tailTrace_3871268
  have hstable : (prefixWord ++ tailWord_3871268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871268).length < 2 ^ (prefixWord ++ tailWord_3871268).sum := by decide
  have hdescent : baseEnd_3871268 < baseStart_3871268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871297 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3871297 : Nat := 118140960795 + 3871297 * 2 ^ 59
def prefixEnd_3871297 : Nat := 4983230072969 + 3 ^ 40 * 3871297 * 2
def baseEnd_3871297 : Nat := 1987836117308845266383735

theorem tailTrace_3871297 : CollatzResearch.WordTrace tailWord_3871297 prefixEnd_3871297 1987836117308845266383735 := by
  unfold tailWord_3871297
  simp only [CollatzResearch.WordTrace]
  refine ⟨141197801455959608734684145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94131867637306405823122763 141197801455959608734684145)
  ·
    refine ⟨105898351091969706551013109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141197801455959608734684145 105898351091969706551013109)
    ·
      refine ⟨9927970414872159989157479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105898351091969706551013109 9927970414872159989157479)
      ·
        refine ⟨14891955622308239983736219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927970414872159989157479 14891955622308239983736219)
        ·
          refine ⟨22337933433462359975604329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891955622308239983736219 22337933433462359975604329)
          ·
            refine ⟨16753450075096769981703247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22337933433462359975604329 16753450075096769981703247)
            ·
              refine ⟨25130175112645154972554871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753450075096769981703247 25130175112645154972554871)
              ·
                refine ⟨37695262668967732458832307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25130175112645154972554871 37695262668967732458832307)
                ·
                  refine ⟨56542894003451598688248461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37695262668967732458832307 56542894003451598688248461)
                  ·
                    refine ⟨21203585251294349508093173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56542894003451598688248461 21203585251294349508093173)
                    ·
                      refine ⟨1987836117308845266383735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21203585251294349508093173 1987836117308845266383735)
                      ·
                        rfl

theorem cell23_3871297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3871297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871297 prefixEnd_3871297 := by exact prefixLift 3871297
  have htrace : WordTrace (prefixWord ++ tailWord_3871297) baseStart_3871297 baseEnd_3871297 := by
    simpa [prefixWord, tailWord_3871297, baseEnd_3871297] using wordTrace_append hprefix tailTrace_3871297
  have hstable : (prefixWord ++ tailWord_3871297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871297).length < 2 ^ (prefixWord ++ tailWord_3871297).sum := by decide
  have hdescent : baseEnd_3871297 < baseStart_3871297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871317 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 7]
def baseStart_3871317 : Nat := 118140960795 + 3871317 * 2 ^ 59
def prefixEnd_3871317 : Nat := 4983230072969 + 3 ^ 40 * 3871317 * 2
def baseEnd_3871317 : Nat := 220871820769103909792627

theorem tailTrace_3871317 : CollatzResearch.WordTrace tailWord_3871317 prefixEnd_3871317 220871820769103909792627 := by
  unfold tailWord_3871317
  simp only [CollatzResearch.WordTrace]
  refine ⟨141198530915887152150412205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94132353943924768100274803 141198530915887152150412205)
  ·
    refine ⟨52949449093457682056404577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141198530915887152150412205 52949449093457682056404577)
    ·
      refine ⟨39712086820093261542303433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52949449093457682056404577 39712086820093261542303433)
      ·
        refine ⟨29784065115069946156727575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39712086820093261542303433 29784065115069946156727575)
        ·
          refine ⟨44676097672604919235091363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29784065115069946156727575 44676097672604919235091363)
          ·
            refine ⟨67014146508907378852637045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44676097672604919235091363 67014146508907378852637045)
            ·
              refine ⟨6282576235210066767434723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67014146508907378852637045 6282576235210066767434723)
              ·
                refine ⟨9423864352815100151152085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282576235210066767434723 9423864352815100151152085)
                ·
                  refine ⟨220871820769103909792627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9423864352815100151152085 220871820769103909792627)
                  ·
                    rfl

theorem cell23_3871317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_3871317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871317 prefixEnd_3871317 := by exact prefixLift 3871317
  have htrace : WordTrace (prefixWord ++ tailWord_3871317) baseStart_3871317 baseEnd_3871317 := by
    simpa [prefixWord, tailWord_3871317, baseEnd_3871317] using wordTrace_append hprefix tailTrace_3871317
  have hstable : (prefixWord ++ tailWord_3871317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871317).length < 2 ^ (prefixWord ++ tailWord_3871317).sum := by decide
  have hdescent : baseEnd_3871317 < baseStart_3871317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871327 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_3871327 : Nat := 118140960795 + 3871327 * 2 ^ 59
def prefixEnd_3871327 : Nat := 4983230072969 + 3 ^ 40 * 3871327 * 2
def baseEnd_3871327 : Nat := 1987851521728480149008597

theorem tailTrace_3871327 : CollatzResearch.WordTrace tailWord_3871327 prefixEnd_3871327 1987851521728480149008597 := by
  unfold tailWord_3871327
  simp only [CollatzResearch.WordTrace]
  refine ⟨141198895645850923858276235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94132597097233949238850823 141198895645850923858276235)
  ·
    refine ⟨211798343468776385787414353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141198895645850923858276235 211798343468776385787414353)
    ·
      refine ⟨158848757601582289340560765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211798343468776385787414353 158848757601582289340560765)
      ·
        refine ⟨59568284100593358502710287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158848757601582289340560765 59568284100593358502710287)
        ·
          refine ⟨89352426150890037754065431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59568284100593358502710287 89352426150890037754065431)
          ·
            refine ⟨134028639226335056631098147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89352426150890037754065431 134028639226335056631098147)
            ·
              refine ⟨201042958839502584946647221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134028639226335056631098147 201042958839502584946647221)
              ·
                refine ⟨18847777391203367338748177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201042958839502584946647221 18847777391203367338748177)
                ·
                  refine ⟨14135833043402525504061133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18847777391203367338748177 14135833043402525504061133)
                  ·
                    refine ⟨5300937391275947064022925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14135833043402525504061133 5300937391275947064022925)
                    ·
                      refine ⟨1987851521728480149008597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5300937391275947064022925 1987851521728480149008597)
                      ·
                        rfl

theorem cell23_3871327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_3871327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871327 prefixEnd_3871327 := by exact prefixLift 3871327
  have htrace : WordTrace (prefixWord ++ tailWord_3871327) baseStart_3871327 baseEnd_3871327 := by
    simpa [prefixWord, tailWord_3871327, baseEnd_3871327] using wordTrace_append hprefix tailTrace_3871327
  have hstable : (prefixWord ++ tailWord_3871327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871327).length < 2 ^ (prefixWord ++ tailWord_3871327).sum := by decide
  have hdescent : baseEnd_3871327 < baseStart_3871327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871328 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2]
def baseStart_3871328 : Nat := 118140960795 + 3871328 * 2 ^ 59
def prefixEnd_3871328 : Nat := 4983230072969 + 3 ^ 40 * 3871328 * 2
def baseEnd_3871328 : Nat := 1987852035209134645096093

theorem tailTrace_3871328 : CollatzResearch.WordTrace tailWord_3871328 prefixEnd_3871328 1987852035209134645096093 := by
  unfold tailWord_3871328
  simp only [CollatzResearch.WordTrace]
  refine ⟨70599466059423650514531319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94132621412564867352708425 70599466059423650514531319)
  ·
    refine ⟨105899199089135475771796979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70599466059423650514531319 105899199089135475771796979)
    ·
      refine ⟨158848798633703213657695469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105899199089135475771796979 158848798633703213657695469)
      ·
        refine ⟨59568299487638705121635801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158848798633703213657695469 59568299487638705121635801)
        ·
          refine ⟨44676224615729028841226851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59568299487638705121635801 44676224615729028841226851)
          ·
            refine ⟨67014336923593543261840277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44676224615729028841226851 67014336923593543261840277)
            ·
              refine ⟨3141297043293447340398763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67014336923593543261840277 3141297043293447340398763)
              ·
                refine ⟨4711945564940171010598145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141297043293447340398763 4711945564940171010598145)
                ·
                  refine ⟨3533959173705128257948609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711945564940171010598145 3533959173705128257948609)
                  ·
                    refine ⟨2650469380278846193461457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533959173705128257948609 2650469380278846193461457)
                    ·
                      refine ⟨1987852035209134645096093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650469380278846193461457 1987852035209134645096093)
                      ·
                        rfl

theorem cell23_3871328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_3871328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871328 prefixEnd_3871328 := by exact prefixLift 3871328
  have htrace : WordTrace (prefixWord ++ tailWord_3871328) baseStart_3871328 baseEnd_3871328 := by
    simpa [prefixWord, tailWord_3871328, baseEnd_3871328] using wordTrace_append hprefix tailTrace_3871328
  have hstable : (prefixWord ++ tailWord_3871328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871328).length < 2 ^ (prefixWord ++ tailWord_3871328).sum := by decide
  have hdescent : baseEnd_3871328 < baseStart_3871328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871364 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3871364 : Nat := 118140960795 + 3871364 * 2 ^ 59
def prefixEnd_3871364 : Nat := 4983230072969 + 3 ^ 40 * 3871364 * 2
def baseEnd_3871364 : Nat := 662623506837565501415309

theorem tailTrace_3871364 : CollatzResearch.WordTrace tailWord_3871364 prefixEnd_3871364 662623506837565501415309 := by
  unfold tailWord_3871364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70600122573358439588686573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94133496764477919451582097 70600122573358439588686573)
  ·
    refine ⟨26475045965009414845757465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70600122573358439588686573 26475045965009414845757465)
    ·
      refine ⟨19856284473757061134318099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26475045965009414845757465 19856284473757061134318099)
      ·
        refine ⟨29784426710635591701477149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19856284473757061134318099 29784426710635591701477149)
        ·
          refine ⟨11169160016488346888053931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29784426710635591701477149 11169160016488346888053931)
          ·
            refine ⟨16753740024732520332080897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11169160016488346888053931 16753740024732520332080897)
            ·
              refine ⟨12565305018549390249060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16753740024732520332080897 12565305018549390249060673)
              ·
                refine ⟨9423978763912042686795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12565305018549390249060673 9423978763912042686795505)
                ·
                  refine ⟨7067984072934032015096629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9423978763912042686795505 7067984072934032015096629)
                  ·
                    refine ⟨662623506837565501415309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7067984072934032015096629 662623506837565501415309)
                    ·
                      rfl

theorem cell23_3871364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3871364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871364 prefixEnd_3871364 := by exact prefixLift 3871364
  have htrace : WordTrace (prefixWord ++ tailWord_3871364) baseStart_3871364 baseEnd_3871364 := by
    simpa [prefixWord, tailWord_3871364, baseEnd_3871364] using wordTrace_append hprefix tailTrace_3871364
  have hstable : (prefixWord ++ tailWord_3871364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871364).length < 2 ^ (prefixWord ++ tailWord_3871364).sum := by decide
  have hdescent : baseEnd_3871364 < baseStart_3871364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871411 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 1, 4]
def baseStart_3871411 : Nat := 118140960795 + 3871411 * 2 ^ 59
def prefixEnd_3871411 : Nat := 4983230072969 + 3 ^ 40 * 3871411 * 2
def baseEnd_3871411 : Nat := 662631551367819273452737

theorem tailTrace_3871411 : CollatzResearch.WordTrace tailWord_3871411 prefixEnd_3871411 662631551367819273452737 := by
  unfold tailWord_3871411
  simp only [CollatzResearch.WordTrace]
  refine ⟨141201959377546606204334087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94134639585031070802889391 141201959377546606204334087)
  ·
    refine ⟨211802939066319909306501131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141201959377546606204334087 211802939066319909306501131)
    ·
      refine ⟨317704408599479863959751697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211802939066319909306501131 317704408599479863959751697)
      ·
        refine ⟨238278306449609897969813773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317704408599479863959751697 238278306449609897969813773)
        ·
          refine ⟨89354364918603711738680165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238278306449609897969813773 89354364918603711738680165)
          ·
            refine ⟨16753943422238195951002531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89354364918603711738680165 16753943422238195951002531)
            ·
              refine ⟨25130915133357293926503797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753943422238195951002531 25130915133357293926503797)
              ·
                refine ⟨2356023293752246305609731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25130915133357293926503797 2356023293752246305609731)
                ·
                  refine ⟨3534034940628369458414597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356023293752246305609731 3534034940628369458414597)
                  ·
                    refine ⟨662631551367819273452737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534034940628369458414597 662631551367819273452737)
                    ·
                      rfl

theorem cell23_3871411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 4].length) (baseStart_3871411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871411 prefixEnd_3871411 := by exact prefixLift 3871411
  have htrace : WordTrace (prefixWord ++ tailWord_3871411) baseStart_3871411 baseEnd_3871411 := by
    simpa [prefixWord, tailWord_3871411, baseEnd_3871411] using wordTrace_append hprefix tailTrace_3871411
  have hstable : (prefixWord ++ tailWord_3871411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871411).length < 2 ^ (prefixWord ++ tailWord_3871411).sum := by decide
  have hdescent : baseEnd_3871411 < baseStart_3871411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871424 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 6]
def baseStart_3871424 : Nat := 118140960795 + 3871424 * 2 ^ 59
def prefixEnd_3871424 : Nat := 4983230072969 + 3 ^ 40 * 3871424 * 2
def baseEnd_3871424 : Nat := 220877925483551807721739

theorem tailTrace_3871424 : CollatzResearch.WordTrace tailWord_3871424 prefixEnd_3871424 220877925483551807721739 := by
  unfold tailWord_3871424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70601216763249754712278663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94134955684333006283038217 70601216763249754712278663)
  ·
    refine ⟨105901825144874632068417995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70601216763249754712278663 105901825144874632068417995)
    ·
      refine ⟨158852737717311948102626993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105901825144874632068417995 158852737717311948102626993)
      ·
        refine ⟨119139553287983961076970245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158852737717311948102626993 119139553287983961076970245)
        ·
          refine ⟨22338666241496992701931921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119139553287983961076970245 22338666241496992701931921)
          ·
            refine ⟨16753999681122744526448941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22338666241496992701931921 16753999681122744526448941)
            ·
              refine ⟨6282749880421029197418353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16753999681122744526448941 6282749880421029197418353)
              ·
                refine ⟨4712062410315771898063765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6282749880421029197418353 4712062410315771898063765)
                ·
                  refine ⟨220877925483551807721739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4712062410315771898063765 220877925483551807721739)
                  ·
                    rfl

theorem cell23_3871424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_3871424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871424 prefixEnd_3871424 := by exact prefixLift 3871424
  have htrace : WordTrace (prefixWord ++ tailWord_3871424) baseStart_3871424 baseEnd_3871424 := by
    simpa [prefixWord, tailWord_3871424, baseEnd_3871424] using wordTrace_append hprefix tailTrace_3871424
  have hstable : (prefixWord ++ tailWord_3871424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871424).length < 2 ^ (prefixWord ++ tailWord_3871424).sum := by decide
  have hdescent : baseEnd_3871424 < baseStart_3871424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871428 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3871428 : Nat := 118140960795 + 3871428 * 2 ^ 59
def prefixEnd_3871428 : Nat := 4983230072969 + 3 ^ 40 * 3871428 * 2
def baseEnd_3871428 : Nat := 662634461091528084615211

theorem tailTrace_3871428 : CollatzResearch.WordTrace tailWord_3871428 prefixEnd_3871428 662634461091528084615211 := by
  unfold tailWord_3871428
  simp only [CollatzResearch.WordTrace]
  refine ⟨70601289709242509053851469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94135052945656678738468625 70601289709242509053851469)
  ·
    refine ⟨26475483640965940895194301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70601289709242509053851469 26475483640965940895194301)
    ·
      refine ⟨9928306365362227835697863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26475483640965940895194301 9928306365362227835697863)
      ·
        refine ⟨14892459548043341753546795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928306365362227835697863 14892459548043341753546795)
        ·
          refine ⟨22338689322065012630320193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14892459548043341753546795 22338689322065012630320193)
          ·
            refine ⟨16754016991548759472740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22338689322065012630320193 16754016991548759472740145)
            ·
              refine ⟨12565512743661569604555109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16754016991548759472740145 12565512743661569604555109)
              ·
                refine ⟨2356033639436544300854083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12565512743661569604555109 2356033639436544300854083)
                ·
                  refine ⟨3534050459154816451281125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356033639436544300854083 3534050459154816451281125)
                  ·
                    refine ⟨662634461091528084615211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534050459154816451281125 662634461091528084615211)
                    ·
                      rfl

theorem cell23_3871428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3871428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871428 prefixEnd_3871428 := by exact prefixLift 3871428
  have htrace : WordTrace (prefixWord ++ tailWord_3871428) baseStart_3871428 baseEnd_3871428 := by
    simpa [prefixWord, tailWord_3871428, baseEnd_3871428] using wordTrace_append hprefix tailTrace_3871428
  have hstable : (prefixWord ++ tailWord_3871428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871428).length < 2 ^ (prefixWord ++ tailWord_3871428).sum := by decide
  have hdescent : baseEnd_3871428 < baseStart_3871428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871461 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3871461 : Nat := 118140960795 + 3871461 * 2 ^ 59
def prefixEnd_3871461 : Nat := 4983230072969 + 3 ^ 40 * 3871461 * 2
def baseEnd_3871461 : Nat := 1987920328136182624732981

theorem tailTrace_3871461 : CollatzResearch.WordTrace tailWord_3871461 prefixEnd_3871461 1987920328136182624732981 := by
  unfold tailWord_3871461
  simp only [CollatzResearch.WordTrace]
  refine ⟨141203783027365464743654237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94135855351576976495769491 141203783027365464743654237)
  ·
    refine ⟨52951418635262049278870339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141203783027365464743654237 52951418635262049278870339)
    ·
      refine ⟨79427127952893073918305509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52951418635262049278870339 79427127952893073918305509)
      ·
        refine ⟨14892586491167451359682283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79427127952893073918305509 14892586491167451359682283)
        ·
          refine ⟨22338879736751177039523425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14892586491167451359682283 22338879736751177039523425)
          ·
            refine ⟨16754159802563382779642569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22338879736751177039523425 16754159802563382779642569)
            ·
              refine ⟨12565619851922537084731927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16754159802563382779642569 12565619851922537084731927)
              ·
                refine ⟨18848429777883805627097891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565619851922537084731927 18848429777883805627097891)
                ·
                  refine ⟨28272644666825708440646837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18848429777883805627097891 28272644666825708440646837)
                  ·
                    refine ⟨2650560437514910166310641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28272644666825708440646837 2650560437514910166310641)
                    ·
                      refine ⟨1987920328136182624732981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650560437514910166310641 1987920328136182624732981)
                      ·
                        rfl

theorem cell23_3871461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3871461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871461 prefixEnd_3871461 := by exact prefixLift 3871461
  have htrace : WordTrace (prefixWord ++ tailWord_3871461) baseStart_3871461 baseEnd_3871461 := by
    simpa [prefixWord, tailWord_3871461, baseEnd_3871461] using wordTrace_append hprefix tailTrace_3871461
  have hstable : (prefixWord ++ tailWord_3871461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871461).length < 2 ^ (prefixWord ++ tailWord_3871461).sum := by decide
  have hdescent : baseEnd_3871461 < baseStart_3871461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871467 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 6]
def baseStart_3871467 : Nat := 118140960795 + 3871467 * 2 ^ 59
def prefixEnd_3871467 : Nat := 4983230072969 + 3 ^ 40 * 3871467 * 2
def baseEnd_3871467 : Nat := 662641136340036533752651

theorem tailTrace_3871467 : CollatzResearch.WordTrace tailWord_3871467 prefixEnd_3871467 662641136340036533752651 := by
  unfold tailWord_3871467
  simp only [CollatzResearch.WordTrace]
  refine ⟨141204001865343727768372655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94136001243562485178915103 141204001865343727768372655)
  ·
    refine ⟨211806002798015591652558983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141204001865343727768372655 211806002798015591652558983)
    ·
      refine ⟨317709004197023387478838475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211806002798015591652558983 317709004197023387478838475)
      ·
        refine ⟨476563506295535081218257713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317709004197023387478838475 476563506295535081218257713)
        ·
          refine ⟨357422629721651310913693285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476563506295535081218257713 357422629721651310913693285)
          ·
            refine ⟨67016743072809620796317491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357422629721651310913693285 67016743072809620796317491)
            ·
              refine ⟨100525114609214431194476237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67016743072809620796317491 100525114609214431194476237)
              ·
                refine ⟨37696917978455411697928589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100525114609214431194476237 37696917978455411697928589)
                ·
                  refine ⟨14136344241920779386723221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37696917978455411697928589 14136344241920779386723221)
                  ·
                    refine ⟨662641136340036533752651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14136344241920779386723221 662641136340036533752651)
                    ·
                      rfl

theorem cell23_3871467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_3871467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871467 prefixEnd_3871467 := by exact prefixLift 3871467
  have htrace : WordTrace (prefixWord ++ tailWord_3871467) baseStart_3871467 baseEnd_3871467 := by
    simpa [prefixWord, tailWord_3871467, baseEnd_3871467] using wordTrace_append hprefix tailTrace_3871467
  have hstable : (prefixWord ++ tailWord_3871467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871467).length < 2 ^ (prefixWord ++ tailWord_3871467).sum := by decide
  have hdescent : baseEnd_3871467 < baseStart_3871467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871478 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3871478 : Nat := 118140960795 + 3871478 * 2 ^ 59
def prefixEnd_3871478 : Nat := 4983230072969 + 3 ^ 40 * 3871478 * 2
def baseEnd_3871478 : Nat := 1987929057307309058220403

theorem tailTrace_3871478 : CollatzResearch.WordTrace tailWord_3871478 prefixEnd_3871478 1987929057307309058220403 := by
  unfold tailWord_3871478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825275191768992290438943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94136268712202584431348725 8825275191768992290438943)
  ·
    refine ⟨13237912787653488435658415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8825275191768992290438943 13237912787653488435658415)
    ·
      refine ⟨19856869181480232653487623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237912787653488435658415 19856869181480232653487623)
      ·
        refine ⟨29785303772220348980231435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19856869181480232653487623 29785303772220348980231435)
        ·
          refine ⟨44677955658330523470347153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29785303772220348980231435 44677955658330523470347153)
          ·
            refine ⟨33508466743747892602760365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44677955658330523470347153 33508466743747892602760365)
            ·
              refine ⟨12565675028905459726035137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33508466743747892602760365 12565675028905459726035137)
              ·
                refine ⟨9424256271679094794526353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12565675028905459726035137 9424256271679094794526353)
                ·
                  refine ⟨7068192203759321095894765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9424256271679094794526353 7068192203759321095894765)
                  ·
                    refine ⟨2650572076409745410960537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7068192203759321095894765 2650572076409745410960537)
                    ·
                      refine ⟨1987929057307309058220403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650572076409745410960537 1987929057307309058220403)
                      ·
                        rfl

theorem cell23_3871478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3871478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871478 prefixEnd_3871478 := by exact prefixLift 3871478
  have htrace : WordTrace (prefixWord ++ tailWord_3871478) baseStart_3871478 baseEnd_3871478 := by
    simpa [prefixWord, tailWord_3871478, baseEnd_3871478] using wordTrace_append hprefix tailTrace_3871478
  have hstable : (prefixWord ++ tailWord_3871478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871478).length < 2 ^ (prefixWord ++ tailWord_3871478).sum := by decide
  have hdescent : baseEnd_3871478 < baseStart_3871478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871485 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_3871485 : Nat := 118140960795 + 3871485 * 2 ^ 59
def prefixEnd_3871485 : Nat := 4983230072969 + 3 ^ 40 * 3871485 * 2
def baseEnd_3871485 : Nat := 1987932651671890530832871

theorem tailTrace_3871485 : CollatzResearch.WordTrace tailWord_3871485 prefixEnd_3871485 1987932651671890530832871 := by
  unfold tailWord_3871485
  simp only [CollatzResearch.WordTrace]
  refine ⟨141204658379278516842527909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94136438919519011228351939 141204658379278516842527909)
  ·
    refine ⟨26475873446114721907973983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141204658379278516842527909 26475873446114721907973983)
    ·
      refine ⟨39713810169172082861960975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26475873446114721907973983 39713810169172082861960975)
      ·
        refine ⟨59570715253758124292941463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39713810169172082861960975 59570715253758124292941463)
        ·
          refine ⟨89356072880637186439412195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59570715253758124292941463 89356072880637186439412195)
          ·
            refine ⟨134034109320955779659118293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89356072880637186439412195 134034109320955779659118293)
            ·
              refine ⟨3141424437209901085760585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134034109320955779659118293 3141424437209901085760585)
              ·
                refine ⟨2356068327907425814320439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141424437209901085760585 2356068327907425814320439)
                ·
                  refine ⟨3534102491861138721480659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356068327907425814320439 3534102491861138721480659)
                  ·
                    refine ⟨5301153737791708082220989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534102491861138721480659 5301153737791708082220989)
                    ·
                      refine ⟨1987932651671890530832871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5301153737791708082220989 1987932651671890530832871)
                      ·
                        rfl

theorem cell23_3871485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_3871485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871485 prefixEnd_3871485 := by exact prefixLift 3871485
  have htrace : WordTrace (prefixWord ++ tailWord_3871485) baseStart_3871485 baseEnd_3871485 := by
    simpa [prefixWord, tailWord_3871485, baseEnd_3871485] using wordTrace_append hprefix tailTrace_3871485
  have hstable : (prefixWord ++ tailWord_3871485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871485).length < 2 ^ (prefixWord ++ tailWord_3871485).sum := by decide
  have hdescent : baseEnd_3871485 < baseStart_3871485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871497 : List Nat := [1, 2, 1, 1, 3, 2, 3, 10]
def baseStart_3871497 : Nat := 118140960795 + 3871497 * 2 ^ 59
def prefixEnd_3871497 : Nat := 4983230072969 + 3 ^ 40 * 3871497 * 2
def baseEnd_3871497 : Nat := 73627363460731277180845

theorem tailTrace_3871497 : CollatzResearch.WordTrace tailWord_3871497 prefixEnd_3871497 73627363460731277180845 := by
  unfold tailWord_3871497
  simp only [CollatzResearch.WordTrace]
  refine ⟨141205096055235042891964745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94136730703490028594643163 141205096055235042891964745)
  ·
    refine ⟨105903822041426282168973559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141205096055235042891964745 105903822041426282168973559)
    ·
      refine ⟨158855733062139423253460339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105903822041426282168973559 158855733062139423253460339)
      ·
        refine ⟨238283599593209134880190509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158855733062139423253460339 238283599593209134880190509)
        ·
          refine ⟨89356349847453425580071441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238283599593209134880190509 89356349847453425580071441)
          ·
            refine ⟨67017262385590069185053581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89356349847453425580071441 67017262385590069185053581)
            ·
              refine ⟨25131473394596275944395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67017262385590069185053581 25131473394596275944395093)
              ·
                refine ⟨73627363460731277180845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25131473394596275944395093 73627363460731277180845)
                ·
                  rfl

theorem cell23_3871497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 10].length) (baseStart_3871497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871497 prefixEnd_3871497 := by exact prefixLift 3871497
  have htrace : WordTrace (prefixWord ++ tailWord_3871497) baseStart_3871497 baseEnd_3871497 := by
    simpa [prefixWord, tailWord_3871497, baseEnd_3871497] using wordTrace_append hprefix tailTrace_3871497
  have hstable : (prefixWord ++ tailWord_3871497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871497).length < 2 ^ (prefixWord ++ tailWord_3871497).sum := by decide
  have hdescent : baseEnd_3871497 < baseStart_3871497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871525 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_3871525 : Nat := 118140960795 + 3871525 * 2 ^ 59
def prefixEnd_3871525 : Nat := 4983230072969 + 3 ^ 40 * 3871525 * 2
def baseEnd_3871525 : Nat := 1987953190898070374332687

theorem tailTrace_3871525 : CollatzResearch.WordTrace tailWord_3871525 prefixEnd_3871525 1987953190898070374332687 := by
  unfold tailWord_3871525
  simp only [CollatzResearch.WordTrace]
  refine ⟨141206117299133603673984029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94137411532755735782656019 141206117299133603673984029)
  ·
    refine ⟨52952293987175101377744011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141206117299133603673984029 52952293987175101377744011)
    ·
      refine ⟨79428440980762652066616017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52952293987175101377744011 79428440980762652066616017)
      ·
        refine ⟨59571330735571989049962013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79428440980762652066616017 59571330735571989049962013)
        ·
          refine ⟨22339249025839495893735755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59571330735571989049962013 22339249025839495893735755)
          ·
            refine ⟨33508873538759243840603633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22339249025839495893735755 33508873538759243840603633)
            ·
              refine ⟨25131655154069432880452725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33508873538759243840603633 25131655154069432880452725)
              ·
                refine ⟨2356092670694009332542443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25131655154069432880452725 2356092670694009332542443)
                ·
                  refine ⟨3534139006041013998813665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356092670694009332542443 3534139006041013998813665)
                  ·
                    refine ⟨2650604254530760499110249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534139006041013998813665 2650604254530760499110249)
                    ·
                      refine ⟨1987953190898070374332687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650604254530760499110249 1987953190898070374332687)
                      ·
                        rfl

theorem cell23_3871525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_3871525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871525 prefixEnd_3871525 := by exact prefixLift 3871525
  have htrace : WordTrace (prefixWord ++ tailWord_3871525) baseStart_3871525 baseEnd_3871525 := by
    simpa [prefixWord, tailWord_3871525, baseEnd_3871525] using wordTrace_append hprefix tailTrace_3871525
  have hstable : (prefixWord ++ tailWord_3871525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871525).length < 2 ^ (prefixWord ++ tailWord_3871525).sum := by decide
  have hdescent : baseEnd_3871525 < baseStart_3871525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871584 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3871584 : Nat := 118140960795 + 3871584 * 2 ^ 59
def prefixEnd_3871584 : Nat := 4983230072969 + 3 ^ 40 * 3871584 * 2
def baseEnd_3871584 : Nat := 1987983486256685643494915

theorem tailTrace_3871584 : CollatzResearch.WordTrace tailWord_3871584 prefixEnd_3871584 1987983486256685643494915 := by
  unfold tailWord_3871584
  simp only [CollatzResearch.WordTrace]
  refine ⟨70604134602959928375190903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94138846137279904500254537 70604134602959928375190903)
  ·
    refine ⟨105906201904439892562786355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70604134602959928375190903 105906201904439892562786355)
    ·
      refine ⟨158859302856659838844179533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105906201904439892562786355 158859302856659838844179533)
      ·
        refine ⟨59572238571247439566567325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158859302856659838844179533 59572238571247439566567325)
        ·
          refine ⟨22339589464217789837462747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59572238571247439566567325 22339589464217789837462747)
          ·
            refine ⟨33509384196326684756194121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22339589464217789837462747 33509384196326684756194121)
            ·
              refine ⟨25132038147245013567145591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33509384196326684756194121 25132038147245013567145591)
              ·
                refine ⟨37698057220867520350718387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25132038147245013567145591 37698057220867520350718387)
                ·
                  refine ⟨56547085831301280526077581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37698057220867520350718387 56547085831301280526077581)
                  ·
                    refine ⟨21205157186737980197279093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56547085831301280526077581 21205157186737980197279093)
                    ·
                      refine ⟨1987983486256685643494915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21205157186737980197279093 1987983486256685643494915)
                      ·
                        rfl

theorem cell23_3871584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3871584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871584 prefixEnd_3871584 := by exact prefixLift 3871584
  have htrace : WordTrace (prefixWord ++ tailWord_3871584) baseStart_3871584 baseEnd_3871584 := by
    simpa [prefixWord, tailWord_3871584, baseEnd_3871584] using wordTrace_append hprefix tailTrace_3871584
  have hstable : (prefixWord ++ tailWord_3871584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871584).length < 2 ^ (prefixWord ++ tailWord_3871584).sum := by decide
  have hdescent : baseEnd_3871584 < baseStart_3871584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871641 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 7, 2]
def baseStart_3871641 : Nat := 118140960795 + 3871641 * 2 ^ 59
def prefixEnd_3871641 : Nat := 4983230072969 + 3 ^ 40 * 3871641 * 2
def baseEnd_3871641 : Nat := 1988012754653991920482153

theorem tailTrace_3871641 : CollatzResearch.WordTrace tailWord_3871641 prefixEnd_3871641 1988012754653991920482153 := by
  unfold tailWord_3871641
  simp only [CollatzResearch.WordTrace]
  refine ⟨141210348166713355485206777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94140232111142236990137851 141210348166713355485206777)
  ·
    refine ⟨105907761125035016613905083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141210348166713355485206777 105907761125035016613905083)
    ·
      refine ⟨158861641687552524920857625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105907761125035016613905083 158861641687552524920857625)
      ·
        refine ⟨119146231265664393690643219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158861641687552524920857625 119146231265664393690643219)
        ·
          refine ⟨178719346898496590535964829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119146231265664393690643219 178719346898496590535964829)
          ·
            refine ⟨67019755086936221450986811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178719346898496590535964829 67019755086936221450986811)
            ·
              refine ⟨100529632630404332176480217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67019755086936221450986811 100529632630404332176480217)
              ·
                refine ⟨75397224472803249132360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100529632630404332176480217 75397224472803249132360163)
                ·
                  refine ⟨113095836709204873698540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75397224472803249132360163 113095836709204873698540245)
                  ·
                    refine ⟨2650683672871989227309537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 113095836709204873698540245 2650683672871989227309537)
                    ·
                      refine ⟨1988012754653991920482153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650683672871989227309537 1988012754653991920482153)
                      ·
                        rfl

theorem cell23_3871641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_3871641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871641 prefixEnd_3871641 := by exact prefixLift 3871641
  have htrace : WordTrace (prefixWord ++ tailWord_3871641) baseStart_3871641 baseEnd_3871641 := by
    simpa [prefixWord, tailWord_3871641, baseEnd_3871641] using wordTrace_append hprefix tailTrace_3871641
  have hstable : (prefixWord ++ tailWord_3871641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871641).length < 2 ^ (prefixWord ++ tailWord_3871641).sum := by decide
  have hdescent : baseEnd_3871641 < baseStart_3871641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871655 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 7]
def baseStart_3871655 : Nat := 118140960795 + 3871655 * 2 ^ 59
def prefixEnd_3871655 : Nat := 4983230072969 + 3 ^ 40 * 3871655 * 2
def baseEnd_3871655 : Nat := 220891104820350540634121

theorem tailTrace_3871655 : CollatzResearch.WordTrace tailWord_3871655 prefixEnd_3871655 220891104820350540634121 := by
  unfold tailWord_3871655
  simp only [CollatzResearch.WordTrace]
  refine ⟨141210858788662635876216419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94140572525775090584144279 141210858788662635876216419)
  ·
    refine ⟨211816288182993953814324629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141210858788662635876216419 211816288182993953814324629)
    ·
      refine ⟨9928888508577841585046467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211816288182993953814324629 9928888508577841585046467)
      ·
        refine ⟨14893332762866762377569701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928888508577841585046467 14893332762866762377569701)
        ·
          refine ⟨2792499893037517945794319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14893332762866762377569701 2792499893037517945794319)
          ·
            refine ⟨4188749839556276918691479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792499893037517945794319 4188749839556276918691479)
            ·
              refine ⟨6283124759334415378037219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188749839556276918691479 6283124759334415378037219)
              ·
                refine ⟨9424687139001623067055829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283124759334415378037219 9424687139001623067055829)
                ·
                  refine ⟨220891104820350540634121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9424687139001623067055829 220891104820350540634121)
                  ·
                    rfl

theorem cell23_3871655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 7].length) (baseStart_3871655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871655 prefixEnd_3871655 := by exact prefixLift 3871655
  have htrace : WordTrace (prefixWord ++ tailWord_3871655) baseStart_3871655 baseEnd_3871655 := by
    simpa [prefixWord, tailWord_3871655, baseEnd_3871655] using wordTrace_append hprefix tailTrace_3871655
  have hstable : (prefixWord ++ tailWord_3871655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871655).length < 2 ^ (prefixWord ++ tailWord_3871655).sum := by decide
  have hdescent : baseEnd_3871655 < baseStart_3871655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871715 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 1, 4]
def baseStart_3871715 : Nat := 118140960795 + 3871715 * 2 ^ 59
def prefixEnd_3871715 : Nat := 4983230072969 + 3 ^ 40 * 3871715 * 2
def baseEnd_3871715 : Nat := 662683584074141543652271

theorem tailTrace_3871715 : CollatzResearch.WordTrace tailWord_3871715 prefixEnd_3871715 662683584074141543652271 := by
  unfold tailWord_3871715
  simp only [CollatzResearch.WordTrace]
  refine ⟨141213047168445266123400599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94142031445630177415600399 141213047168445266123400599)
  ·
    refine ⟨211819570752667899185100899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141213047168445266123400599 211819570752667899185100899)
    ·
      refine ⟨317729356129001848777651349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211819570752667899185100899 317729356129001848777651349)
      ·
        refine ⟨14893563568546961661452407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317729356129001848777651349 14893563568546961661452407)
        ·
          refine ⟨22340345352820442492178611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14893563568546961661452407 22340345352820442492178611)
          ·
            refine ⟨33510518029230663738267917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22340345352820442492178611 33510518029230663738267917)
            ·
              refine ⟨12566444260961498901850469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33510518029230663738267917 12566444260961498901850469)
              ·
                refine ⟨2356208298930281044096963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12566444260961498901850469 2356208298930281044096963)
                ·
                  refine ⟨3534312448395421566145445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356208298930281044096963 3534312448395421566145445)
                  ·
                    refine ⟨662683584074141543652271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534312448395421566145445 662683584074141543652271)
                    ·
                      rfl

theorem cell23_3871715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 4].length) (baseStart_3871715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871715 prefixEnd_3871715 := by exact prefixLift 3871715
  have htrace : WordTrace (prefixWord ++ tailWord_3871715) baseStart_3871715 baseEnd_3871715 := by
    simpa [prefixWord, tailWord_3871715, baseEnd_3871715] using wordTrace_append hprefix tailTrace_3871715
  have hstable : (prefixWord ++ tailWord_3871715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871715).length < 2 ^ (prefixWord ++ tailWord_3871715).sum := by decide
  have hdescent : baseEnd_3871715 < baseStart_3871715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871762 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_3871762 : Nat := 118140960795 + 3871762 * 2 ^ 59
def prefixEnd_3871762 : Nat := 4983230072969 + 3 ^ 40 * 3871762 * 2
def baseEnd_3871762 : Nat := 220897209534798438563233

theorem tailTrace_3871762 : CollatzResearch.WordTrace tailWord_3871762 prefixEnd_3871762 220897209534798438563233 := by
  unfold tailWord_3871762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35303690349818748287590385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94143174266183328766907693 35303690349818748287590385)
  ·
    refine ⟨26477767762364061215692789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35303690349818748287590385 26477767762364061215692789)
    ·
      refine ⟨2482290727721630738971199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26477767762364061215692789 2482290727721630738971199)
      ·
        refine ⟨3723436091582446108456799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482290727721630738971199 3723436091582446108456799)
        ·
          refine ⟨5585154137373669162685199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723436091582446108456799 5585154137373669162685199)
          ·
            refine ⟨8377731206060503744027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585154137373669162685199 8377731206060503744027799)
            ·
              refine ⟨12566596809090755616041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377731206060503744027799 12566596809090755616041699)
              ·
                refine ⟨18849895213636133424062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12566596809090755616041699 18849895213636133424062549)
                ·
                  refine ⟨220897209534798438563233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18849895213636133424062549 220897209534798438563233)
                  ·
                    rfl

theorem cell23_3871762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_3871762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871762 prefixEnd_3871762 := by exact prefixLift 3871762
  have htrace : WordTrace (prefixWord ++ tailWord_3871762) baseStart_3871762 baseEnd_3871762 := by
    simpa [prefixWord, tailWord_3871762, baseEnd_3871762] using wordTrace_append hprefix tailTrace_3871762
  have hstable : (prefixWord ++ tailWord_3871762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871762).length < 2 ^ (prefixWord ++ tailWord_3871762).sum := by decide
  have hdescent : baseEnd_3871762 < baseStart_3871762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871772 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3871772 : Nat := 118140960795 + 3871772 * 2 ^ 59
def prefixEnd_3871772 : Nat := 4983230072969 + 3 ^ 40 * 3871772 * 2
def baseEnd_3871772 : Nat := 1988080020619730907944051

theorem tailTrace_3871772 : CollatzResearch.WordTrace tailWord_3871772 prefixEnd_3871772 1988080020619730907944051 := by
  unfold tailWord_3871772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70607563064619382429112785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94143417419492509905483713 70607563064619382429112785)
  ·
    refine ⟨52955672298464536821834589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70607563064619382429112785 52955672298464536821834589)
    ·
      refine ⟨19858377111924201308187971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52955672298464536821834589 19858377111924201308187971)
      ·
        refine ⟨29787565667886301962281957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19858377111924201308187971 29787565667886301962281957)
        ·
          refine ⟨5585168562728681617927867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29787565667886301962281957 5585168562728681617927867)
          ·
            refine ⟨8377752844093022426891801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585168562728681617927867 8377752844093022426891801)
            ·
              refine ⟨6283314633069766820168851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8377752844093022426891801 6283314633069766820168851)
              ·
                refine ⟨9424971949604650230253277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283314633069766820168851 9424971949604650230253277)
                ·
                  refine ⟨3534364481101743836344979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9424971949604650230253277 3534364481101743836344979)
                  ·
                    refine ⟨5301546721652615754517469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534364481101743836344979 5301546721652615754517469)
                    ·
                      refine ⟨1988080020619730907944051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5301546721652615754517469 1988080020619730907944051)
                      ·
                        rfl

theorem cell23_3871772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3871772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871772 prefixEnd_3871772 := by exact prefixLift 3871772
  have htrace : WordTrace (prefixWord ++ tailWord_3871772) baseStart_3871772 baseEnd_3871772 := by
    simpa [prefixWord, tailWord_3871772, baseEnd_3871772] using wordTrace_append hprefix tailTrace_3871772
  have hstable : (prefixWord ++ tailWord_3871772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871772).length < 2 ^ (prefixWord ++ tailWord_3871772).sum := by decide
  have hdescent : baseEnd_3871772 < baseStart_3871772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871806 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3871806 : Nat := 118140960795 + 3871806 * 2 ^ 59
def prefixEnd_3871806 : Nat := 4983230072969 + 3 ^ 40 * 3871806 * 2
def baseEnd_3871806 : Nat := 1988097478961983774918895

theorem tailTrace_3871806 : CollatzResearch.WordTrace tailWord_3871806 prefixEnd_3871806 1988097478961983774918895 := by
  unfold tailWord_3871806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652045776389448583120409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94144244140743725776642181 17652045776389448583120409)
  ·
    refine ⟨13239034332292086437340307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17652045776389448583120409 13239034332292086437340307)
    ·
      refine ⟨19858551498438129656010461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13239034332292086437340307 19858551498438129656010461)
      ·
        refine ⟨7446956811914298621003923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19858551498438129656010461 7446956811914298621003923)
        ·
          refine ⟨11170435217871447931505885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446956811914298621003923 11170435217871447931505885)
          ·
            refine ⟨4188913206701792974314707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11170435217871447931505885 4188913206701792974314707)
            ·
              refine ⟨6283369810052689461472061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188913206701792974314707 6283369810052689461472061)
              ·
                refine ⟨2356263678769758548052023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6283369810052689461472061 2356263678769758548052023)
                ·
                  refine ⟨3534395518154637822078035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356263678769758548052023 3534395518154637822078035)
                  ·
                    refine ⟨5301593277231956733117053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534395518154637822078035 5301593277231956733117053)
                    ·
                      refine ⟨1988097478961983774918895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5301593277231956733117053 1988097478961983774918895)
                      ·
                        rfl

theorem cell23_3871806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3871806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871806 prefixEnd_3871806 := by exact prefixLift 3871806
  have htrace : WordTrace (prefixWord ++ tailWord_3871806) baseStart_3871806 baseEnd_3871806 := by
    simpa [prefixWord, tailWord_3871806, baseEnd_3871806] using wordTrace_append hprefix tailTrace_3871806
  have hstable : (prefixWord ++ tailWord_3871806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871806).length < 2 ^ (prefixWord ++ tailWord_3871806).sum := by decide
  have hdescent : baseEnd_3871806 < baseStart_3871806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871815 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_3871815 : Nat := 118140960795 + 3871815 * 2 ^ 59
def prefixEnd_3871815 : Nat := 4983230072969 + 3 ^ 40 * 3871815 * 2
def baseEnd_3871815 : Nat := 1988102100287874239706353

theorem tailTrace_3871815 : CollatzResearch.WordTrace tailWord_3871815 prefixEnd_3871815 1988102100287874239706353 := by
  unfold tailWord_3871815
  simp only [CollatzResearch.WordTrace]
  refine ⟨141216694468082983202040899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94144462978721988801360599 141216694468082983202040899)
  ·
    refine ⟨211825041702124474803061349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141216694468082983202040899 211825041702124474803061349)
    ·
      refine ⟨39717195319148339025574003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211825041702124474803061349 39717195319148339025574003)
      ·
        refine ⟨59575792978722508538361005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39717195319148339025574003 59575792978722508538361005)
        ·
          refine ⟨22340922367020940701885377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59575792978722508538361005 22340922367020940701885377)
          ·
            refine ⟨16755691775265705526414033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22340922367020940701885377 16755691775265705526414033)
            ·
              refine ⟨12566768831449279144810525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16755691775265705526414033 12566768831449279144810525)
              ·
                refine ⟨4712538311793479679303947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12566768831449279144810525 4712538311793479679303947)
                ·
                  refine ⟨7068807467690219518955921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712538311793479679303947 7068807467690219518955921)
                  ·
                    refine ⟨5301605600767664639216941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7068807467690219518955921 5301605600767664639216941)
                    ·
                      refine ⟨1988102100287874239706353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5301605600767664639216941 1988102100287874239706353)
                      ·
                        rfl

theorem cell23_3871815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_3871815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871815 prefixEnd_3871815 := by exact prefixLift 3871815
  have htrace : WordTrace (prefixWord ++ tailWord_3871815) baseStart_3871815 baseEnd_3871815 := by
    simpa [prefixWord, tailWord_3871815, baseEnd_3871815] using wordTrace_append hprefix tailTrace_3871815
  have hstable : (prefixWord ++ tailWord_3871815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871815).length < 2 ^ (prefixWord ++ tailWord_3871815).sum := by decide
  have hdescent : baseEnd_3871815 < baseStart_3871815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871831 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 7]
def baseStart_3871831 : Nat := 118140960795 + 3871831 * 2 ^ 59
def prefixEnd_3871831 : Nat := 4983230072969 + 3 ^ 40 * 3871831 * 2
def baseEnd_3871831 : Nat := 662703438659448725702093

theorem tailTrace_3871831 : CollatzResearch.WordTrace tailWord_3871831 prefixEnd_3871831 662703438659448725702093 := by
  unfold tailWord_3871831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141217278036025017934623347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94144852024016678623082231 141217278036025017934623347)
  ·
    refine ⟨211825917054037526901935021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141217278036025017934623347 211825917054037526901935021)
    ·
      refine ⟨79434718895264072588225633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211825917054037526901935021 79434718895264072588225633)
      ·
        refine ⟨59576039171448054441169225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79434718895264072588225633 59576039171448054441169225)
        ·
          refine ⟨44682029378586040830876919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59576039171448054441169225 44682029378586040830876919)
          ·
            refine ⟨67023044067879061246315379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44682029378586040830876919 67023044067879061246315379)
            ·
              refine ⟨100534566101818591869473069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67023044067879061246315379 100534566101818591869473069)
              ·
                refine ⟨37700462288181971951052401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100534566101818591869473069 37700462288181971951052401)
                ·
                  refine ⟨28275346716136478963289301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37700462288181971951052401 28275346716136478963289301)
                  ·
                    refine ⟨662703438659448725702093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28275346716136478963289301 662703438659448725702093)
                    ·
                      rfl

theorem cell23_3871831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_3871831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871831 prefixEnd_3871831 := by exact prefixLift 3871831
  have htrace : WordTrace (prefixWord ++ tailWord_3871831) baseStart_3871831 baseEnd_3871831 := by
    simpa [prefixWord, tailWord_3871831, baseEnd_3871831] using wordTrace_append hprefix tailTrace_3871831
  have hstable : (prefixWord ++ tailWord_3871831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871831).length < 2 ^ (prefixWord ++ tailWord_3871831).sum := by decide
  have hdescent : baseEnd_3871831 < baseStart_3871831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871855 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 3, 3, 2]
def baseStart_3871855 : Nat := 118140960795 + 3871855 * 2 ^ 59
def prefixEnd_3871855 : Nat := 4983230072969 + 3 ^ 40 * 3871855 * 2
def baseEnd_3871855 : Nat := 1988122639514054083206169

theorem tailTrace_3871855 : CollatzResearch.WordTrace tailWord_3871855 prefixEnd_3871855 1988122639514054083206169 := by
  unfold tailWord_3871855
  simp only [CollatzResearch.WordTrace]
  refine ⟨141218153387938070033497019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94145435591958713355664679 141218153387938070033497019)
  ·
    refine ⟨211827230081907105050245529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141218153387938070033497019 211827230081907105050245529)
    ·
      refine ⟨158870422561430328787684147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211827230081907105050245529 158870422561430328787684147)
      ·
        refine ⟨238305633842145493181526221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158870422561430328787684147 238305633842145493181526221)
        ·
          refine ⟨89364612690804559943072333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238305633842145493181526221 89364612690804559943072333)
          ·
            refine ⟨33511729759051709978652125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89364612690804559943072333 33511729759051709978652125)
            ·
              refine ⟨12566898659644391241994547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33511729759051709978652125 12566898659644391241994547)
              ·
                refine ⟨18850347989466586862991821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12566898659644391241994547 18850347989466586862991821)
                ·
                  refine ⟨7068880496049970073621933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18850347989466586862991821 7068880496049970073621933)
                  ·
                    refine ⟨2650830186018738777608225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7068880496049970073621933 2650830186018738777608225)
                    ·
                      refine ⟨1988122639514054083206169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650830186018738777608225 1988122639514054083206169)
                      ·
                        rfl

theorem cell23_3871855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3, 2].length) (baseStart_3871855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871855 prefixEnd_3871855 := by exact prefixLift 3871855
  have htrace : WordTrace (prefixWord ++ tailWord_3871855) baseStart_3871855 baseEnd_3871855 := by
    simpa [prefixWord, tailWord_3871855, baseEnd_3871855] using wordTrace_append hprefix tailTrace_3871855
  have hstable : (prefixWord ++ tailWord_3871855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871855).length < 2 ^ (prefixWord ++ tailWord_3871855).sum := by decide
  have hdescent : baseEnd_3871855 < baseStart_3871855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871880 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3871880 : Nat := 118140960795 + 3871880 * 2 ^ 59
def prefixEnd_3871880 : Nat := 4983230072969 + 3 ^ 40 * 3871880 * 2
def baseEnd_3871880 : Nat := 1988135476530416485393555

theorem tailTrace_3871880 : CollatzResearch.WordTrace tailWord_3871880 prefixEnd_3871880 1988135476530416485393555 := by
  unfold tailWord_3871880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70609532606423749651578547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94146043475231666202104729 70609532606423749651578547)
  ·
    refine ⟨105914298909635624477367821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70609532606423749651578547 105914298909635624477367821)
    ·
      refine ⟨39717862091113359179012933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105914298909635624477367821 39717862091113359179012933)
      ·
        refine ⟨7447099142083754846064925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39717862091113359179012933 7447099142083754846064925)
        ·
          refine ⟨2792662178281408067274347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7447099142083754846064925 2792662178281408067274347)
          ·
            refine ⟨4188993267422112100911521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792662178281408067274347 4188993267422112100911521)
            ·
              refine ⟨3141744950566584075683641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188993267422112100911521 3141744950566584075683641)
              ·
                refine ⟨2356308712924938056762731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141744950566584075683641 2356308712924938056762731)
                ·
                  refine ⟨3534463069387407085144097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356308712924938056762731 3534463069387407085144097)
                  ·
                    refine ⟨2650847302040555313858073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534463069387407085144097 2650847302040555313858073)
                    ·
                      refine ⟨1988135476530416485393555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650847302040555313858073 1988135476530416485393555)
                      ·
                        rfl

theorem cell23_3871880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3871880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871880 prefixEnd_3871880 := by exact prefixLift 3871880
  have htrace : WordTrace (prefixWord ++ tailWord_3871880) baseStart_3871880 baseEnd_3871880 := by
    simpa [prefixWord, tailWord_3871880, baseEnd_3871880] using wordTrace_append hprefix tailTrace_3871880
  have hstable : (prefixWord ++ tailWord_3871880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871880).length < 2 ^ (prefixWord ++ tailWord_3871880).sum := by decide
  have hdescent : baseEnd_3871880 < baseStart_3871880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871908 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3871908 : Nat := 118140960795 + 3871908 * 2 ^ 59
def prefixEnd_3871908 : Nat := 4983230072969 + 3 ^ 40 * 3871908 * 2
def baseEnd_3871908 : Nat := 220905539332082486204825

theorem tailTrace_3871908 : CollatzResearch.WordTrace tailWord_3871908 prefixEnd_3871908 220905539332082486204825 := by
  unfold tailWord_3871908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70610043228373030042588189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94146724304497373390117585 70610043228373030042588189)
  ·
    refine ⟨26478766210639886265970571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70610043228373030042588189 26478766210639886265970571)
    ·
      refine ⟨39718149315959829398955857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26478766210639886265970571 39718149315959829398955857)
      ·
        refine ⟨29788611986969872049216893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39718149315959829398955857 29788611986969872049216893)
        ·
          refine ⟨11170729495113702018456335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29788611986969872049216893 11170729495113702018456335)
          ·
            refine ⟨16756094242670553027684503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170729495113702018456335 16756094242670553027684503)
            ·
              refine ⟨25134141364005829541526755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756094242670553027684503 25134141364005829541526755)
              ·
                refine ⟨37701212046008744312290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25134141364005829541526755 37701212046008744312290133)
                ·
                  refine ⟨220905539332082486204825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37701212046008744312290133 220905539332082486204825)
                  ·
                    rfl

theorem cell23_3871908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3871908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871908 prefixEnd_3871908 := by exact prefixLift 3871908
  have htrace : WordTrace (prefixWord ++ tailWord_3871908) baseStart_3871908 baseEnd_3871908 := by
    simpa [prefixWord, tailWord_3871908, baseEnd_3871908] using wordTrace_append hprefix tailTrace_3871908
  have hstable : (prefixWord ++ tailWord_3871908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871908).length < 2 ^ (prefixWord ++ tailWord_3871908).sum := by decide
  have hdescent : baseEnd_3871908 < baseStart_3871908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871936 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2]
def baseStart_3871936 : Nat := 118140960795 + 3871936 * 2 ^ 59
def prefixEnd_3871936 : Nat := 4983230072969 + 3 ^ 40 * 3871936 * 2
def baseEnd_3871936 : Nat := 1988164231447068266293297

theorem tailTrace_3871936 : CollatzResearch.WordTrace tailWord_3871936 prefixEnd_3871936 1988164231447068266293297 := by
  unfold tailWord_3871936
  simp only [CollatzResearch.WordTrace]
  refine ⟨70610553850322310433597831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94147405133763080578130441 70610553850322310433597831)
  ·
    refine ⟨105915830775483465650396747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70610553850322310433597831 105915830775483465650396747)
    ·
      refine ⟨158873746163225198475595121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105915830775483465650396747 158873746163225198475595121)
      ·
        refine ⟨119155309622418898856696341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158873746163225198475595121 119155309622418898856696341)
        ·
          refine ⟨5585405138550885883907641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119155309622418898856696341 5585405138550885883907641)
          ·
            refine ⟨4189053853913164412930731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5585405138550885883907641 4189053853913164412930731)
            ·
              refine ⟨6283580780869746619396097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189053853913164412930731 6283580780869746619396097)
              ·
                refine ⟨4712685585652309964547073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283580780869746619396097 4712685585652309964547073)
                ·
                  refine ⟨3534514189239232473410305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712685585652309964547073 3534514189239232473410305)
                  ·
                    refine ⟨2650885641929424355057729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534514189239232473410305 2650885641929424355057729)
                    ·
                      refine ⟨1988164231447068266293297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2650885641929424355057729 1988164231447068266293297)
                      ·
                        rfl

theorem cell23_3871936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_3871936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3871936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3871936 prefixEnd_3871936 := by exact prefixLift 3871936
  have htrace : WordTrace (prefixWord ++ tailWord_3871936) baseStart_3871936 baseEnd_3871936 := by
    simpa [prefixWord, tailWord_3871936, baseEnd_3871936] using wordTrace_append hprefix tailTrace_3871936
  have hstable : (prefixWord ++ tailWord_3871936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871936).length < 2 ^ (prefixWord ++ tailWord_3871936).sum := by decide
  have hdescent : baseEnd_3871936 < baseStart_3871936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872029 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3872029 : Nat := 118140960795 + 3872029 * 2 ^ 59
def prefixEnd_3872029 : Nat := 4983230072969 + 3 ^ 40 * 3872029 * 2
def baseEnd_3872029 : Nat := 1988211985147936402430369

theorem tailTrace_3872029 : CollatzResearch.WordTrace tailWord_3872029 prefixEnd_3872029 1988211985147936402430369 := by
  unfold tailWord_3872029
  simp only [CollatzResearch.WordTrace]
  refine ⟨141224499689307697750331141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94149666459538465166887427 141224499689307697750331141)
  ·
    refine ⟨26479593691745193328187089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141224499689307697750331141 26479593691745193328187089)
    ·
      refine ⟨19859695268808894996140317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26479593691745193328187089 19859695268808894996140317)
      ·
        refine ⟨7447385725803335623552619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19859695268808894996140317 7447385725803335623552619)
        ·
          refine ⟨11171078588705003435328929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447385725803335623552619 11171078588705003435328929)
          ·
            refine ⟨8378308941528752576496697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171078588705003435328929 8378308941528752576496697)
            ·
              refine ⟨6283731706146564432372523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8378308941528752576496697 6283731706146564432372523)
              ·
                refine ⟨9425597559219846648558785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283731706146564432372523 9425597559219846648558785)
                ·
                  refine ⟨7069198169414884986419089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9425597559219846648558785 7069198169414884986419089)
                  ·
                    refine ⟨5301898627061163739814317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7069198169414884986419089 5301898627061163739814317)
                    ·
                      refine ⟨1988211985147936402430369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5301898627061163739814317 1988211985147936402430369)
                      ·
                        rfl

theorem cell23_3872029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3872029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872029 prefixEnd_3872029 := by exact prefixLift 3872029
  have htrace : WordTrace (prefixWord ++ tailWord_3872029) baseStart_3872029 baseEnd_3872029 := by
    simpa [prefixWord, tailWord_3872029, baseEnd_3872029] using wordTrace_append hprefix tailTrace_3872029
  have hstable : (prefixWord ++ tailWord_3872029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872029).length < 2 ^ (prefixWord ++ tailWord_3872029).sum := by decide
  have hdescent : baseEnd_3872029 < baseStart_3872029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872082 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3872082 : Nat := 118140960795 + 3872082 * 2 ^ 59
def prefixEnd_3872082 : Nat := 4983230072969 + 3 ^ 40 * 3872082 * 2
def baseEnd_3872082 : Nat := 1988239199622624695067625

theorem tailTrace_3872082 : CollatzResearch.WordTrace tailWord_3872082 prefixEnd_3872082 1988239199622624695067625 := by
  unfold tailWord_3872082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35306608189528921950502625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94150955172077125201340333 35306608189528921950502625)
  ·
    refine ⟨26479956142146691462876969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35306608189528921950502625 26479956142146691462876969)
    ·
      refine ⟨19859967106610018597157727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26479956142146691462876969 19859967106610018597157727)
      ·
        refine ⟨29789950659915027895736591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19859967106610018597157727 29789950659915027895736591)
        ·
          refine ⟨44684925989872541843604887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789950659915027895736591 44684925989872541843604887)
          ·
            refine ⟨67027388984808812765407331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44684925989872541843604887 67027388984808812765407331)
            ·
              refine ⟨100541083477213219148110997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67027388984808812765407331 100541083477213219148110997)
              ·
                refine ⟨4712863287994369647567703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100541083477213219148110997 4712863287994369647567703)
                ·
                  refine ⟨7069294931991554471351555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712863287994369647567703 7069294931991554471351555)
                  ·
                    refine ⟨10603942397987331707027333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069294931991554471351555 10603942397987331707027333)
                    ·
                      refine ⟨1988239199622624695067625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10603942397987331707027333 1988239199622624695067625)
                      ·
                        rfl

theorem cell23_3872082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3872082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872082 prefixEnd_3872082 := by exact prefixLift 3872082
  have htrace : WordTrace (prefixWord ++ tailWord_3872082) baseStart_3872082 baseEnd_3872082 := by
    simpa [prefixWord, tailWord_3872082, baseEnd_3872082] using wordTrace_append hprefix tailTrace_3872082
  have hstable : (prefixWord ++ tailWord_3872082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872082).length < 2 ^ (prefixWord ++ tailWord_3872082).sum := by decide
  have hdescent : baseEnd_3872082 < baseStart_3872082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872099 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3872099 : Nat := 118140960795 + 3872099 * 2 ^ 59
def prefixEnd_3872099 : Nat := 4983230072969 + 3 ^ 40 * 3872099 * 2
def baseEnd_3872099 : Nat := 1988247928793751128555047

theorem tailTrace_3872099 : CollatzResearch.WordTrace tailWord_3872099 prefixEnd_3872099 1988247928793751128555047 := by
  unfold tailWord_3872099
  simp only [CollatzResearch.WordTrace]
  refine ⟨141227052799054099705379351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94151368532702733136919567 141227052799054099705379351)
  ·
    refine ⟨211840579198581149558069027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141227052799054099705379351 211840579198581149558069027)
    ·
      refine ⟨317760868797871724337103541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211840579198581149558069027 317760868797871724337103541)
      ·
        refine ⟨29790081449800474156603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317760868797871724337103541 29790081449800474156603457)
        ·
          refine ⟨22342561087350355617452593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29790081449800474156603457 22342561087350355617452593)
          ·
            refine ⟨16756920815512766713089445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22342561087350355617452593 16756920815512766713089445)
            ·
              refine ⟨3141922652908643758704271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16756920815512766713089445 3141922652908643758704271)
              ·
                refine ⟨4712883979362965638056407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141922652908643758704271 4712883979362965638056407)
                ·
                  refine ⟨7069325969044448457084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712883979362965638056407 7069325969044448457084611)
                  ·
                    refine ⟨10603988953566672685626917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069325969044448457084611 10603988953566672685626917)
                    ·
                      refine ⟨1988247928793751128555047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10603988953566672685626917 1988247928793751128555047)
                      ·
                        rfl

theorem cell23_3872099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3872099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872099 prefixEnd_3872099 := by exact prefixLift 3872099
  have htrace : WordTrace (prefixWord ++ tailWord_3872099) baseStart_3872099 baseEnd_3872099 := by
    simpa [prefixWord, tailWord_3872099, baseEnd_3872099] using wordTrace_append hprefix tailTrace_3872099
  have hstable : (prefixWord ++ tailWord_3872099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872099).length < 2 ^ (prefixWord ++ tailWord_3872099).sum := by decide
  have hdescent : baseEnd_3872099 < baseStart_3872099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872109 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3872109 : Nat := 118140960795 + 3872109 * 2 ^ 59
def prefixEnd_3872109 : Nat := 4983230072969 + 3 ^ 40 * 3872109 * 2
def baseEnd_3872109 : Nat := 662751021200098696476667

theorem tailTrace_3872109 : CollatzResearch.WordTrace tailWord_3872109 prefixEnd_3872109 662751021200098696476667 := by
  unfold tailWord_3872109
  simp only [CollatzResearch.WordTrace]
  refine ⟨141227417529017871413243381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94151611686011914275495587 141227417529017871413243381)
  ·
    refine ⟨13240070393345425444991567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141227417529017871413243381 13240070393345425444991567)
    ·
      refine ⟨19860105590018138167487351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240070393345425444991567 19860105590018138167487351)
      ·
        refine ⟨29790158385027207251231027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19860105590018138167487351 29790158385027207251231027)
        ·
          refine ⟨44685237577540810876846541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29790158385027207251231027 44685237577540810876846541)
          ·
            refine ⟨16756964091577804078817453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44685237577540810876846541 16756964091577804078817453)
            ·
              refine ⟨6283861534341676529556545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16756964091577804078817453 6283861534341676529556545)
              ·
                refine ⟨4712896150756257397167409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283861534341676529556545 4712896150756257397167409)
                ·
                  refine ⟨3534672113067193047875557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712896150756257397167409 3534672113067193047875557)
                  ·
                    refine ⟨662751021200098696476667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534672113067193047875557 662751021200098696476667)
                    ·
                      rfl

theorem cell23_3872109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3872109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872109 prefixEnd_3872109 := by exact prefixLift 3872109
  have htrace : WordTrace (prefixWord ++ tailWord_3872109) baseStart_3872109 baseEnd_3872109 := by
    simpa [prefixWord, tailWord_3872109, baseEnd_3872109] using wordTrace_append hprefix tailTrace_3872109
  have hstable : (prefixWord ++ tailWord_3872109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872109).length < 2 ^ (prefixWord ++ tailWord_3872109).sum := by decide
  have hdescent : baseEnd_3872109 < baseStart_3872109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872165 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3872165 : Nat := 118140960795 + 3872165 * 2 ^ 59
def prefixEnd_3872165 : Nat := 4983230072969 + 3 ^ 40 * 3872165 * 2
def baseEnd_3872165 : Nat := 662760606172315956776581

theorem tailTrace_3872165 : CollatzResearch.WordTrace tailWord_3872165 prefixEnd_3872165 662760606172315956776581 := by
  unfold tailWord_3872165
  simp only [CollatzResearch.WordTrace]
  refine ⟨141229460016814992977281949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94152973344543328651521299 141229460016814992977281949)
  ·
    refine ⟨52961047506305622366480731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141229460016814992977281949 52961047506305622366480731)
    ·
      refine ⟨79441571259458433549721097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52961047506305622366480731 79441571259458433549721097)
      ·
        refine ⟨59581178444593825162290823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79441571259458433549721097 59581178444593825162290823)
        ·
          refine ⟨89371767666890737743436235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59581178444593825162290823 89371767666890737743436235)
          ·
            refine ⟨134057651500336106615154353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89371767666890737743436235 134057651500336106615154353)
            ·
              refine ⟨100543238625252079961365765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134057651500336106615154353 100543238625252079961365765)
              ·
                refine ⟨18851857242234764992756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100543238625252079961365765 18851857242234764992756081)
                ·
                  refine ⟨14138892931676073744567061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18851857242234764992756081 14138892931676073744567061)
                  ·
                    refine ⟨662760606172315956776581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14138892931676073744567061 662760606172315956776581)
                    ·
                      rfl

theorem cell23_3872165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3872165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872165 prefixEnd_3872165 := by exact prefixLift 3872165
  have htrace : WordTrace (prefixWord ++ tailWord_3872165) baseStart_3872165 baseEnd_3872165 := by
    simpa [prefixWord, tailWord_3872165, baseEnd_3872165] using wordTrace_append hprefix tailTrace_3872165
  have hstable : (prefixWord ++ tailWord_3872165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872165).length < 2 ^ (prefixWord ++ tailWord_3872165).sum := by decide
  have hdescent : baseEnd_3872165 < baseStart_3872165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872189 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3872189 : Nat := 118140960795 + 3872189 * 2 ^ 59
def prefixEnd_3872189 : Nat := 4983230072969 + 3 ^ 40 * 3872189 * 2
def baseEnd_3872189 : Nat := 1988294142052655776429633

theorem tailTrace_3872189 : CollatzResearch.WordTrace tailWord_3872189 prefixEnd_3872189 1988294142052655776429633 := by
  unfold tailWord_3872189
  simp only [CollatzResearch.WordTrace]
  refine ⟨141230335368728045076155621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94153556912485363384103747 141230335368728045076155621)
  ·
    refine ⟨26480687881636508451779179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141230335368728045076155621 26480687881636508451779179)
    ·
      refine ⟨39721031822454762677668769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26480687881636508451779179 39721031822454762677668769)
      ·
        refine ⟨29790773866841072008251577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39721031822454762677668769 29790773866841072008251577)
        ·
          refine ⟨22343080400130804006188683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29790773866841072008251577 22343080400130804006188683)
          ·
            refine ⟨33514620600196206009283025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22343080400130804006188683 33514620600196206009283025)
            ·
              refine ⟨25135965450147154506962269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33514620600196206009283025 25135965450147154506962269)
              ·
                refine ⟨9425987043805182940110851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25135965450147154506962269 9425987043805182940110851)
                ·
                  refine ⟨14138980565707774410166277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9425987043805182940110851 14138980565707774410166277)
                  ·
                    refine ⟨2651058856070207701906177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14138980565707774410166277 2651058856070207701906177)
                    ·
                      refine ⟨1988294142052655776429633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651058856070207701906177 1988294142052655776429633)
                      ·
                        rfl

theorem cell23_3872189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3872189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872189 prefixEnd_3872189 := by exact prefixLift 3872189
  have htrace : WordTrace (prefixWord ++ tailWord_3872189) baseStart_3872189 baseEnd_3872189 := by
    simpa [prefixWord, tailWord_3872189, baseEnd_3872189] using wordTrace_append hprefix tailTrace_3872189
  have hstable : (prefixWord ++ tailWord_3872189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872189).length < 2 ^ (prefixWord ++ tailWord_3872189).sum := by decide
  have hdescent : baseEnd_3872189 < baseStart_3872189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872195 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 7]
def baseStart_3872195 : Nat := 118140960795 + 3872195 * 2 ^ 59
def prefixEnd_3872195 : Nat := 4983230072969 + 3 ^ 40 * 3872195 * 2
def baseEnd_3872195 : Nat := 220921913659620305883845

theorem tailTrace_3872195 : CollatzResearch.WordTrace tailWord_3872195 prefixEnd_3872195 220921913659620305883845 := by
  unfold tailWord_3872195
  simp only [CollatzResearch.WordTrace]
  refine ⟨141230554206706308100874039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94153702804470872067249359 141230554206706308100874039)
  ·
    refine ⟨211845831310059462151311059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141230554206706308100874039 211845831310059462151311059)
    ·
      refine ⟨317768746965089193226966589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211845831310059462151311059 317768746965089193226966589)
      ·
        refine ⟨119163280111908447460112471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317768746965089193226966589 119163280111908447460112471)
        ·
          refine ⟨178744920167862671190168707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119163280111908447460112471 178744920167862671190168707)
          ·
            refine ⟨268117380251794006785253061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178744920167862671190168707 268117380251794006785253061)
            ·
              refine ⟨50272008797211376272234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268117380251794006785253061 50272008797211376272234949)
              ·
                refine ⟨9426001649477133051044053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50272008797211376272234949 9426001649477133051044053)
                ·
                  refine ⟨220921913659620305883845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9426001649477133051044053 220921913659620305883845)
                  ·
                    rfl

theorem cell23_3872195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 7].length) (baseStart_3872195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872195 prefixEnd_3872195 := by exact prefixLift 3872195
  have htrace : WordTrace (prefixWord ++ tailWord_3872195) baseStart_3872195 baseEnd_3872195 := by
    simpa [prefixWord, tailWord_3872195, baseEnd_3872195] using wordTrace_append hprefix tailTrace_3872195
  have hstable : (prefixWord ++ tailWord_3872195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872195).length < 2 ^ (prefixWord ++ tailWord_3872195).sum := by decide
  have hdescent : baseEnd_3872195 < baseStart_3872195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872235 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_3872235 : Nat := 118140960795 + 3872235 * 2 ^ 59
def prefixEnd_3872235 : Nat := 4983230072969 + 3 ^ 40 * 3872235 * 2
def baseEnd_3872235 : Nat := 1988317762162762596454421

theorem tailTrace_3872235 : CollatzResearch.WordTrace tailWord_3872235 prefixEnd_3872235 1988317762162762596454421 := by
  unfold tailWord_3872235
  simp only [CollatzResearch.WordTrace]
  refine ⟨141232013126561394932330159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94154675417707596621553439 141232013126561394932330159)
  ·
    refine ⟨211848019689842092398495239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141232013126561394932330159 211848019689842092398495239)
    ·
      refine ⟨317772029534763138597742859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211848019689842092398495239 317772029534763138597742859)
      ·
        refine ⟨476658044302144707896614289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317772029534763138597742859 476658044302144707896614289)
        ·
          refine ⟨357493533226608530922460717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476658044302144707896614289 357493533226608530922460717)
          ·
            refine ⟨134060074959978199095922769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357493533226608530922460717 134060074959978199095922769)
            ·
              refine ⟨100545056219983649321942077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134060074959978199095922769 100545056219983649321942077)
              ·
                refine ⟨37704396082493868495728279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100545056219983649321942077 37704396082493868495728279)
                ·
                  refine ⟨56556594123740802743592419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37704396082493868495728279 56556594123740802743592419)
                  ·
                    refine ⟨84834891185611204115388629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56556594123740802743592419 84834891185611204115388629)
                    ·
                      refine ⟨1988317762162762596454421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84834891185611204115388629 1988317762162762596454421)
                      ·
                        rfl

theorem cell23_3872235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_3872235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872235 prefixEnd_3872235 := by exact prefixLift 3872235
  have htrace : WordTrace (prefixWord ++ tailWord_3872235) baseStart_3872235 baseEnd_3872235 := by
    simpa [prefixWord, tailWord_3872235, baseEnd_3872235] using wordTrace_append hprefix tailTrace_3872235
  have hstable : (prefixWord ++ tailWord_3872235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872235).length < 2 ^ (prefixWord ++ tailWord_3872235).sum := by decide
  have hdescent : baseEnd_3872235 < baseStart_3872235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872255 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 10]
def baseStart_3872255 : Nat := 118140960795 + 3872255 * 2 ^ 59
def prefixEnd_3872255 : Nat := 4983230072969 + 3 ^ 40 * 3872255 * 2
def baseEnd_3872255 : Nat := 662776010591950839401443

theorem tailTrace_3872255 : CollatzResearch.WordTrace tailWord_3872255 prefixEnd_3872255 662776010591950839401443 := by
  unfold tailWord_3872255
  simp only [CollatzResearch.WordTrace]
  refine ⟨141232742586488938348058219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94155161724325958898705479 141232742586488938348058219)
  ·
    refine ⟨211849113879733407522087329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141232742586488938348058219 211849113879733407522087329)
    ·
      refine ⟨158886835409800055641565497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211849113879733407522087329 158886835409800055641565497)
      ·
        refine ⟨119165126557350041731174123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158886835409800055641565497 119165126557350041731174123)
        ·
          refine ⟨178747689836025062596761185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119165126557350041731174123 178747689836025062596761185)
          ·
            refine ⟨134060767377018796947570889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178747689836025062596761185 134060767377018796947570889)
            ·
              refine ⟨100545575532764097710678167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134060767377018796947570889 100545575532764097710678167)
              ·
                refine ⟨150818363299146146566017251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100545575532764097710678167 150818363299146146566017251)
                ·
                  refine ⟨226227544948719219849025877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150818363299146146566017251 226227544948719219849025877)
                  ·
                    refine ⟨662776010591950839401443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 226227544948719219849025877 662776010591950839401443)
                    ·
                      rfl

theorem cell23_3872255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_3872255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872255 prefixEnd_3872255 := by exact prefixLift 3872255
  have htrace : WordTrace (prefixWord ++ tailWord_3872255) baseStart_3872255 baseEnd_3872255 := by
    simpa [prefixWord, tailWord_3872255, baseEnd_3872255] using wordTrace_append hprefix tailTrace_3872255
  have hstable : (prefixWord ++ tailWord_3872255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872255).length < 2 ^ (prefixWord ++ tailWord_3872255).sum := by decide
  have hdescent : baseEnd_3872255 < baseStart_3872255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872289 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3872289 : Nat := 118140960795 + 3872289 * 2 ^ 59
def prefixEnd_3872289 : Nat := 4983230072969 + 3 ^ 40 * 3872289 * 2
def baseEnd_3872289 : Nat := 662781830039368461726391

theorem tailTrace_3872289 : CollatzResearch.WordTrace tailWord_3872289 prefixEnd_3872289 662781830039368461726391 := by
  unfold tailWord_3872289
  simp only [CollatzResearch.WordTrace]
  refine ⟨141233982668365762154795921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94155988445577174769863947 141233982668365762154795921)
  ·
    refine ⟨105925487001274321616096941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141233982668365762154795921 105925487001274321616096941)
    ·
      refine ⟨39722057625477870606036353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105925487001274321616096941 39722057625477870606036353)
      ·
        refine ⟨29791543219108402954527265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39722057625477870606036353 29791543219108402954527265)
        ·
          refine ⟨22343657414331302215895449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29791543219108402954527265 22343657414331302215895449)
          ·
            refine ⟨16757743060748476661921587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22343657414331302215895449 16757743060748476661921587)
            ·
              refine ⟨25136614591122714992882381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757743060748476661921587 25136614591122714992882381)
              ·
                refine ⟨9426230471671018122330893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25136614591122714992882381 9426230471671018122330893)
                ·
                  refine ⟨3534836426876631795874085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9426230471671018122330893 3534836426876631795874085)
                  ·
                    refine ⟨662781830039368461726391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534836426876631795874085 662781830039368461726391)
                    ·
                      rfl

theorem cell23_3872289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3872289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872289 prefixEnd_3872289 := by exact prefixLift 3872289
  have htrace : WordTrace (prefixWord ++ tailWord_3872289) baseStart_3872289 baseEnd_3872289 := by
    simpa [prefixWord, tailWord_3872289, baseEnd_3872289] using wordTrace_append hprefix tailTrace_3872289
  have hstable : (prefixWord ++ tailWord_3872289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872289).length < 2 ^ (prefixWord ++ tailWord_3872289).sum := by decide
  have hdescent : baseEnd_3872289 < baseStart_3872289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872329 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_3872329 : Nat := 118140960795 + 3872329 * 2 ^ 59
def prefixEnd_3872329 : Nat := 4983230072969 + 3 ^ 40 * 3872329 * 2
def baseEnd_3872329 : Nat := 1988366029344285228678989

theorem tailTrace_3872329 : CollatzResearch.WordTrace tailWord_3872329 prefixEnd_3872329 1988366029344285228678989 := by
  unfold tailWord_3872329
  simp only [CollatzResearch.WordTrace]
  refine ⟨141235441588220848986252041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94156961058813899324168027 141235441588220848986252041)
  ·
    refine ⟨105926581191165636739689031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141235441588220848986252041 105926581191165636739689031)
    ·
      refine ⟨158889871786748455109533547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105926581191165636739689031 158889871786748455109533547)
      ·
        refine ⟨238334807680122682664300321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158889871786748455109533547 238334807680122682664300321)
        ·
          refine ⟨178751105760092011998225241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238334807680122682664300321 178751105760092011998225241)
          ·
            refine ⟨134063329320069008998668931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178751105760092011998225241 134063329320069008998668931)
            ·
              refine ⟨201094993980103513498003397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134063329320069008998668931 201094993980103513498003397)
              ·
                refine ⟨37705311371269408780875637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201094993980103513498003397 37705311371269408780875637)
                ·
                  refine ⟨3534872941056507073207091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37705311371269408780875637 3534872941056507073207091)
                  ·
                    refine ⟨5302309411584760609810637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534872941056507073207091 5302309411584760609810637)
                    ·
                      refine ⟨1988366029344285228678989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5302309411584760609810637 1988366029344285228678989)
                      ·
                        rfl

theorem cell23_3872329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_3872329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872329 prefixEnd_3872329 := by exact prefixLift 3872329
  have htrace : WordTrace (prefixWord ++ tailWord_3872329) baseStart_3872329 baseEnd_3872329 := by
    simpa [prefixWord, tailWord_3872329, baseEnd_3872329] using wordTrace_append hprefix tailTrace_3872329
  have hstable : (prefixWord ++ tailWord_3872329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872329).length < 2 ^ (prefixWord ++ tailWord_3872329).sum := by decide
  have hdescent : baseEnd_3872329 < baseStart_3872329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872333 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3872333 : Nat := 118140960795 + 3872333 * 2 ^ 59
def prefixEnd_3872333 : Nat := 4983230072969 + 3 ^ 40 * 3872333 * 2
def baseEnd_3872333 : Nat := 1988368083266903213028971

theorem tailTrace_3872333 : CollatzResearch.WordTrace tailWord_3872333 prefixEnd_3872333 1988368083266903213028971 := by
  unfold tailWord_3872333
  simp only [CollatzResearch.WordTrace]
  refine ⟨141235587480206357669397653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94157058320137571779598435 141235587480206357669397653)
  ·
    refine ⟨6620418163134673015753015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141235587480206357669397653 6620418163134673015753015)
    ·
      refine ⟨9930627244702009523629523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620418163134673015753015 9930627244702009523629523)
      ·
        refine ⟨14895940867053014285444285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930627244702009523629523 14895940867053014285444285)
        ·
          refine ⟨5585977825144880357041607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14895940867053014285444285 5585977825144880357041607)
          ·
            refine ⟨8378966737717320535562411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585977825144880357041607 8378966737717320535562411)
            ·
              refine ⟨12568450106575980803343617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378966737717320535562411 12568450106575980803343617)
              ·
                refine ⟨9426337579931985602507713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12568450106575980803343617 9426337579931985602507713)
                ·
                  refine ⟨7069753184948989201880785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426337579931985602507713 7069753184948989201880785)
                  ·
                    refine ⟨5302314888711741901410589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7069753184948989201880785 5302314888711741901410589)
                    ·
                      refine ⟨1988368083266903213028971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5302314888711741901410589 1988368083266903213028971)
                      ·
                        rfl

theorem cell23_3872333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3872333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872333 prefixEnd_3872333 := by exact prefixLift 3872333
  have htrace : WordTrace (prefixWord ++ tailWord_3872333) baseStart_3872333 baseEnd_3872333 := by
    simpa [prefixWord, tailWord_3872333, baseEnd_3872333] using wordTrace_append hprefix tailTrace_3872333
  have hstable : (prefixWord ++ tailWord_3872333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872333).length < 2 ^ (prefixWord ++ tailWord_3872333).sum := by decide
  have hdescent : baseEnd_3872333 < baseStart_3872333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872352 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3872352 : Nat := 118140960795 + 3872352 * 2 ^ 59
def prefixEnd_3872352 : Nat := 4983230072969 + 3 ^ 40 * 3872352 * 2
def baseEnd_3872352 : Nat := 1988377839399338638691383

theorem tailTrace_3872352 : CollatzResearch.WordTrace tailWord_3872352 prefixEnd_3872352 1988377839399338638691383 := by
  unfold tailWord_3872352
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618140233568761957169655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94157520311425015942892873 70618140233568761957169655)
  ·
    refine ⟨105927210350353142935754483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70618140233568761957169655 105927210350353142935754483)
    ·
      refine ⟨158890815525529714403631725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105927210350353142935754483 158890815525529714403631725)
      ·
        refine ⟨59584055822073642901361897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158890815525529714403631725 59584055822073642901361897)
        ·
          refine ⟨44688041866555232176021423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59584055822073642901361897 44688041866555232176021423)
          ·
            refine ⟨67032062799832848264032135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44688041866555232176021423 67032062799832848264032135)
            ·
              refine ⟨100548094199749272396048203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67032062799832848264032135 100548094199749272396048203)
              ·
                refine ⟨150822141299623908594072305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100548094199749272396048203 150822141299623908594072305)
                ·
                  refine ⟨113116605974717931445554229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150822141299623908594072305 113116605974717931445554229)
                  ·
                    refine ⟨10604681810129806073020709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113116605974717931445554229 10604681810129806073020709)
                    ·
                      refine ⟨1988377839399338638691383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10604681810129806073020709 1988377839399338638691383)
                      ·
                        rfl

theorem cell23_3872352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3872352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872352 prefixEnd_3872352 := by exact prefixLift 3872352
  have htrace : WordTrace (prefixWord ++ tailWord_3872352) baseStart_3872352 baseEnd_3872352 := by
    simpa [prefixWord, tailWord_3872352, baseEnd_3872352] using wordTrace_append hprefix tailTrace_3872352
  have hstable : (prefixWord ++ tailWord_3872352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872352).length < 2 ^ (prefixWord ++ tailWord_3872352).sum := by decide
  have hdescent : baseEnd_3872352 < baseStart_3872352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872366 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3872366 : Nat := 118140960795 + 3872366 * 2 ^ 59
def prefixEnd_3872366 : Nat := 4983230072969 + 3 ^ 40 * 3872366 * 2
def baseEnd_3872366 : Nat := 662795009376167194638773

theorem tailTrace_3872366 : CollatzResearch.WordTrace tailWord_3872366 prefixEnd_3872366 662795009376167194638773 := by
  unfold tailWord_3872366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654598886135850538168619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94157860726057869536899301 17654598886135850538168619)
  ·
    refine ⟨26481898329203775807252929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17654598886135850538168619 26481898329203775807252929)
    ·
      refine ⟨19861423746902831855439697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26481898329203775807252929 19861423746902831855439697)
      ·
        refine ⟨14896067810177123891579773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19861423746902831855439697 14896067810177123891579773)
        ·
          refine ⟨5586025428816421459342415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14896067810177123891579773 5586025428816421459342415)
          ·
            refine ⟨8379038143224632189013623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586025428816421459342415 8379038143224632189013623)
            ·
              refine ⟨12568557214836948283520435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379038143224632189013623 12568557214836948283520435)
              ·
                refine ⟨18852835822255422425280653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568557214836948283520435 18852835822255422425280653)
                ·
                  refine ⟨7069813433345783409480245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18852835822255422425280653 7069813433345783409480245)
                  ·
                    refine ⟨662795009376167194638773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7069813433345783409480245 662795009376167194638773)
                    ·
                      rfl

theorem cell23_3872366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3872366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872366 prefixEnd_3872366 := by exact prefixLift 3872366
  have htrace : WordTrace (prefixWord ++ tailWord_3872366) baseStart_3872366 baseEnd_3872366 := by
    simpa [prefixWord, tailWord_3872366, baseEnd_3872366] using wordTrace_append hprefix tailTrace_3872366
  have hstable : (prefixWord ++ tailWord_3872366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872366).length < 2 ^ (prefixWord ++ tailWord_3872366).sum := by decide
  have hdescent : baseEnd_3872366 < baseStart_3872366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872369 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_3872369 : Nat := 118140960795 + 3872369 * 2 ^ 59
def prefixEnd_3872369 : Nat := 4983230072969 + 3 ^ 40 * 3872369 * 2
def baseEnd_3872369 : Nat := 1988386568570465072178805

theorem tailTrace_3872369 : CollatzResearch.WordTrace tailWord_3872369 prefixEnd_3872369 1988386568570465072178805 := by
  unfold tailWord_3872369
  simp only [CollatzResearch.WordTrace]
  refine ⟨141236900508075935817708161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94157933672050623878472107 141236900508075935817708161)
  ·
    refine ⟨105927675381056951863281121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141236900508075935817708161 105927675381056951863281121)
    ·
      refine ⟨79445756535792713897460841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105927675381056951863281121 79445756535792713897460841)
      ·
        refine ⟨59584317401844535423095631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79445756535792713897460841 59584317401844535423095631)
        ·
          refine ⟨89376476102766803134643447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59584317401844535423095631 89376476102766803134643447)
          ·
            refine ⟨134064714154150204701965171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89376476102766803134643447 134064714154150204701965171)
            ·
              refine ⟨201097071231225307052947757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134064714154150204701965171 201097071231225307052947757)
              ·
                refine ⟨75411401711709490144855409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201097071231225307052947757 75411401711709490144855409)
                ·
                  refine ⟨56558551283782117608641557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75411401711709490144855409 56558551283782117608641557)
                  ·
                    refine ⟨2651182091427286762905073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56558551283782117608641557 2651182091427286762905073)
                    ·
                      refine ⟨1988386568570465072178805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651182091427286762905073 1988386568570465072178805)
                      ·
                        rfl

theorem cell23_3872369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_3872369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872369 prefixEnd_3872369 := by exact prefixLift 3872369
  have htrace : WordTrace (prefixWord ++ tailWord_3872369) baseStart_3872369 baseEnd_3872369 := by
    simpa [prefixWord, tailWord_3872369, baseEnd_3872369] using wordTrace_append hprefix tailTrace_3872369
  have hstable : (prefixWord ++ tailWord_3872369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872369).length < 2 ^ (prefixWord ++ tailWord_3872369).sum := by decide
  have hdescent : baseEnd_3872369 < baseStart_3872369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872373 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3872373 : Nat := 118140960795 + 3872373 * 2 ^ 59
def prefixEnd_3872373 : Nat := 4983230072969 + 3 ^ 40 * 3872373 * 2
def baseEnd_3872373 : Nat := 1988388622493083056528787

theorem tailTrace_3872373 : CollatzResearch.WordTrace tailWord_3872373 prefixEnd_3872373 1988388622493083056528787 := by
  unfold tailWord_3872373
  simp only [CollatzResearch.WordTrace]
  refine ⟨141237046400061444500853773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94158030933374296333902515 141237046400061444500853773)
  ·
    refine ⟨52963892400023041687820165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141237046400061444500853773 52963892400023041687820165)
    ·
      refine ⟨9930729825004320316466281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52963892400023041687820165 9930729825004320316466281)
      ·
        refine ⟨7448047368753240237349711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9930729825004320316466281 7448047368753240237349711)
        ·
          refine ⟨11172071053129860356024567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448047368753240237349711 11172071053129860356024567)
          ·
            refine ⟨16758106579694790534036851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11172071053129860356024567 16758106579694790534036851)
            ·
              refine ⟨25137159869542185801055277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16758106579694790534036851 25137159869542185801055277)
              ·
                refine ⟨9426434951078319675395729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25137159869542185801055277 9426434951078319675395729)
                ·
                  refine ⟨7069826213308739756546797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426434951078319675395729 7069826213308739756546797)
                  ·
                    refine ⟨2651184829990777408705049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7069826213308739756546797 2651184829990777408705049)
                    ·
                      refine ⟨1988388622493083056528787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651184829990777408705049 1988388622493083056528787)
                      ·
                        rfl

theorem cell23_3872373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3872373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872373 prefixEnd_3872373 := by exact prefixLift 3872373
  have htrace : WordTrace (prefixWord ++ tailWord_3872373) baseStart_3872373 baseEnd_3872373 := by
    simpa [prefixWord, tailWord_3872373, baseEnd_3872373] using wordTrace_append hprefix tailTrace_3872373
  have hstable : (prefixWord ++ tailWord_3872373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872373).length < 2 ^ (prefixWord ++ tailWord_3872373).sum := by decide
  have hdescent : baseEnd_3872373 < baseStart_3872373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872396 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_3872396 : Nat := 118140960795 + 3872396 * 2 ^ 59
def prefixEnd_3872396 : Nat := 4983230072969 + 3 ^ 40 * 3872396 * 2
def baseEnd_3872396 : Nat := 662800144182712155513727

theorem tailTrace_3872396 : CollatzResearch.WordTrace tailWord_3872396 prefixEnd_3872396 662800144182712155513727 := by
  unfold tailWord_3872396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618942639489059714470521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94158590185985412952627361 70618942639489059714470521)
  ·
    refine ⟨52964206979616794785852891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70618942639489059714470521 52964206979616794785852891)
    ·
      refine ⟨79446310469425192178779337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52964206979616794785852891 79446310469425192178779337)
      ·
        refine ⟨59584732852068894134084503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79446310469425192178779337 59584732852068894134084503)
        ·
          refine ⟨89377099278103341201126755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59584732852068894134084503 89377099278103341201126755)
          ·
            refine ⟨134065648917155011801690133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89377099278103341201126755 134065648917155011801690133)
            ·
              refine ⟨6284327292991641178204225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134065648917155011801690133 6284327292991641178204225)
              ·
                refine ⟨4713245469743730883653169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284327292991641178204225 4713245469743730883653169)
                ·
                  refine ⟨3534934102307798162739877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713245469743730883653169 3534934102307798162739877)
                  ·
                    refine ⟨662800144182712155513727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3534934102307798162739877 662800144182712155513727)
                    ·
                      rfl

theorem cell23_3872396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_3872396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872396 prefixEnd_3872396 := by exact prefixLift 3872396
  have htrace : WordTrace (prefixWord ++ tailWord_3872396) baseStart_3872396 baseEnd_3872396 := by
    simpa [prefixWord, tailWord_3872396, baseEnd_3872396] using wordTrace_append hprefix tailTrace_3872396
  have hstable : (prefixWord ++ tailWord_3872396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872396).length < 2 ^ (prefixWord ++ tailWord_3872396).sum := by decide
  have hdescent : baseEnd_3872396 < baseStart_3872396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872416 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3872416 : Nat := 118140960795 + 3872416 * 2 ^ 59
def prefixEnd_3872416 : Nat := 4983230072969 + 3 ^ 40 * 3872416 * 2
def baseEnd_3872416 : Nat := 1988410702161226388291089

theorem tailTrace_3872416 : CollatzResearch.WordTrace tailWord_3872416 prefixEnd_3872416 1988410702161226388291089 := by
  unfold tailWord_3872416
  simp only [CollatzResearch.WordTrace]
  refine ⟨70619307369452831422334551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94159076492603775229779401 70619307369452831422334551)
  ·
    refine ⟨105928961054179247133501827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70619307369452831422334551 105928961054179247133501827)
    ·
      refine ⟨158893441581268870700252741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105928961054179247133501827 158893441581268870700252741)
      ·
        refine ⟨29792520296487913256297389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158893441581268870700252741 29792520296487913256297389)
        ·
          refine ⟨11172195111182967471111521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29792520296487913256297389 11172195111182967471111521)
          ·
            refine ⟨8379146333387225603333641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11172195111182967471111521 8379146333387225603333641)
            ·
              refine ⟨6284359750040419202500231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379146333387225603333641 6284359750040419202500231)
              ·
                refine ⟨9426539625060628803750347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284359750040419202500231 9426539625060628803750347)
                ·
                  refine ⟨14139809437590943205625521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9426539625060628803750347 14139809437590943205625521)
                  ·
                    refine ⟨10604857078193207404219141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14139809437590943205625521 10604857078193207404219141)
                    ·
                      refine ⟨1988410702161226388291089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10604857078193207404219141 1988410702161226388291089)
                      ·
                        rfl

theorem cell23_3872416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3872416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872416 prefixEnd_3872416 := by exact prefixLift 3872416
  have htrace : WordTrace (prefixWord ++ tailWord_3872416) baseStart_3872416 baseEnd_3872416 := by
    simpa [prefixWord, tailWord_3872416, baseEnd_3872416] using wordTrace_append hprefix tailTrace_3872416
  have hstable : (prefixWord ++ tailWord_3872416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872416).length < 2 ^ (prefixWord ++ tailWord_3872416).sum := by decide
  have hdescent : baseEnd_3872416 < baseStart_3872416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872424 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3872424 : Nat := 118140960795 + 3872424 * 2 ^ 59
def prefixEnd_3872424 : Nat := 4983230072969 + 3 ^ 40 * 3872424 * 2
def baseEnd_3872424 : Nat := 1988414810006462356991053

theorem tailTrace_3872424 : CollatzResearch.WordTrace tailWord_3872424 prefixEnd_3872424 1988414810006462356991053 := by
  unfold tailWord_3872424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70619453261438340105480163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94159271015251120140640217 70619453261438340105480163)
  ·
    refine ⟨105929179892157510158220245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70619453261438340105480163 105929179892157510158220245)
    ·
      refine ⟨2482715153722441644333287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105929179892157510158220245 2482715153722441644333287)
      ·
        refine ⟨3724072730583662466499931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482715153722441644333287 3724072730583662466499931)
        ·
          refine ⟨5586109095875493699749897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724072730583662466499931 5586109095875493699749897)
          ·
            refine ⟨4189581821906620274812423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586109095875493699749897 4189581821906620274812423)
            ·
              refine ⟨6284372732859930412218635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189581821906620274812423 6284372732859930412218635)
              ·
                refine ⟨9426559099289895618327953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284372732859930412218635 9426559099289895618327953)
                ·
                  refine ⟨7069919324467421713745965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426559099289895618327953 7069919324467421713745965)
                  ·
                    refine ⟨2651219746675283142654737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7069919324467421713745965 2651219746675283142654737)
                    ·
                      refine ⟨1988414810006462356991053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651219746675283142654737 1988414810006462356991053)
                      ·
                        rfl

theorem cell23_3872424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3872424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872424 prefixEnd_3872424 := by exact prefixLift 3872424
  have htrace : WordTrace (prefixWord ++ tailWord_3872424) baseStart_3872424 baseEnd_3872424 := by
    simpa [prefixWord, tailWord_3872424, baseEnd_3872424] using wordTrace_append hprefix tailTrace_3872424
  have hstable : (prefixWord ++ tailWord_3872424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872424).length < 2 ^ (prefixWord ++ tailWord_3872424).sum := by decide
  have hdescent : baseEnd_3872424 < baseStart_3872424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872437 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3872437 : Nat := 118140960795 + 3872437 * 2 ^ 59
def prefixEnd_3872437 : Nat := 4983230072969 + 3 ^ 40 * 3872437 * 2
def baseEnd_3872437 : Nat := 1988421485254970806128493

theorem tailTrace_3872437 : CollatzResearch.WordTrace tailWord_3872437 prefixEnd_3872437 1988421485254970806128493 := by
  unfold tailWord_3872437
  simp only [CollatzResearch.WordTrace]
  refine ⟨141239380671829583431183565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94159587114553055620789043 141239380671829583431183565)
  ·
    refine ⟨52964767751936093786693837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141239380671829583431183565 52964767751936093786693837)
    ·
      refine ⟨19861787906976035170010189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52964767751936093786693837 19861787906976035170010189)
      ·
        refine ⟨7448170465116013188753821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19861787906976035170010189 7448170465116013188753821)
        ·
          refine ⟨2793063924418504945782683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448170465116013188753821 2793063924418504945782683)
          ·
            refine ⟨4189595886627757418674025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793063924418504945782683 4189595886627757418674025)
            ·
              refine ⟨3142196914970818064005519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189595886627757418674025 3142196914970818064005519)
              ·
                refine ⟨4713295372456227096008279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142196914970818064005519 4713295372456227096008279)
                ·
                  refine ⟨7069943058684340644012419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713295372456227096008279 7069943058684340644012419)
                  ·
                    refine ⟨10604914588026510966018629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069943058684340644012419 10604914588026510966018629)
                    ·
                      refine ⟨1988421485254970806128493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10604914588026510966018629 1988421485254970806128493)
                      ·
                        rfl

theorem cell23_3872437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3872437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872437 prefixEnd_3872437 := by exact prefixLift 3872437
  have htrace : WordTrace (prefixWord ++ tailWord_3872437) baseStart_3872437 baseEnd_3872437 := by
    simpa [prefixWord, tailWord_3872437, baseEnd_3872437] using wordTrace_append hprefix tailTrace_3872437
  have hstable : (prefixWord ++ tailWord_3872437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872437).length < 2 ^ (prefixWord ++ tailWord_3872437).sum := by decide
  have hdescent : baseEnd_3872437 < baseStart_3872437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872454 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3872454 : Nat := 118140960795 + 3872454 * 2 ^ 59
def prefixEnd_3872454 : Nat := 4983230072969 + 3 ^ 40 * 3872454 * 2
def baseEnd_3872454 : Nat := 1988430214426097239615915

theorem tailTrace_3872454 : CollatzResearch.WordTrace tailWord_3872454 prefixEnd_3872454 1988430214426097239615915 := by
  unfold tailWord_3872454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413750022273999854204763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94160000475178663556368277 4413750022273999854204763)
  ·
    refine ⟨6620625033410999781307145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4413750022273999854204763 6620625033410999781307145)
    ·
      refine ⟨4965468775058249835980359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6620625033410999781307145 4965468775058249835980359)
      ·
        refine ⟨7448203162587374753970539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965468775058249835980359 7448203162587374753970539)
        ·
          refine ⟨11172304743881062130955809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448203162587374753970539 11172304743881062130955809)
          ·
            refine ⟨8379228557910796598216857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11172304743881062130955809 8379228557910796598216857)
            ·
              refine ⟨6284421418433097448662643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379228557910796598216857 6284421418433097448662643)
              ·
                refine ⟨9426632127649646172993965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284421418433097448662643 9426632127649646172993965)
                ·
                  refine ⟨3534987047868617314872737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9426632127649646172993965 3534987047868617314872737)
                  ·
                    refine ⟨2651240285901462986154553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534987047868617314872737 2651240285901462986154553)
                    ·
                      refine ⟨1988430214426097239615915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651240285901462986154553 1988430214426097239615915)
                      ·
                        rfl

theorem cell23_3872454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3872454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872454 prefixEnd_3872454 := by exact prefixLift 3872454
  have htrace : WordTrace (prefixWord ++ tailWord_3872454) baseStart_3872454 baseEnd_3872454 := by
    simpa [prefixWord, tailWord_3872454, baseEnd_3872454] using wordTrace_append hprefix tailTrace_3872454
  have hstable : (prefixWord ++ tailWord_3872454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872454).length < 2 ^ (prefixWord ++ tailWord_3872454).sum := by decide
  have hdescent : baseEnd_3872454 < baseStart_3872454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872479 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3872479 : Nat := 118140960795 + 3872479 * 2 ^ 59
def prefixEnd_3872479 : Nat := 4983230072969 + 3 ^ 40 * 3872479 * 2
def baseEnd_3872479 : Nat := 1988443051442459641803299

theorem tailTrace_3872479 : CollatzResearch.WordTrace tailWord_3872479 prefixEnd_3872479 1988443051442459641803299 := by
  unfold tailWord_3872479
  simp only [CollatzResearch.WordTrace]
  refine ⟨141240912537677424604212491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94160608358451616402808327 141240912537677424604212491)
  ·
    refine ⟨211861368806516136906318737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141240912537677424604212491 211861368806516136906318737)
    ·
      refine ⟨158896026604887102679739053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211861368806516136906318737 158896026604887102679739053)
      ·
        refine ⟨59586009976832663504902145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158896026604887102679739053 59586009976832663504902145)
        ·
          refine ⟨44689507482624497628676609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59586009976832663504902145 44689507482624497628676609)
          ·
            refine ⟨33517130611968373221507457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44689507482624497628676609 33517130611968373221507457)
            ·
              refine ⟨25137847958976279916130593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33517130611968373221507457 25137847958976279916130593)
              ·
                refine ⟨18853385969232209937097945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25137847958976279916130593 18853385969232209937097945)
                ·
                  refine ⟨14140039476924157452823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18853385969232209937097945 14140039476924157452823459)
                  ·
                    refine ⟨21210059215386236179235189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14140039476924157452823459 21210059215386236179235189)
                    ·
                      refine ⟨1988443051442459641803299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21210059215386236179235189 1988443051442459641803299)
                      ·
                        rfl

theorem cell23_3872479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3872479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872479 prefixEnd_3872479 := by exact prefixLift 3872479
  have htrace : WordTrace (prefixWord ++ tailWord_3872479) baseStart_3872479 baseEnd_3872479 := by
    simpa [prefixWord, tailWord_3872479, baseEnd_3872479] using wordTrace_append hprefix tailTrace_3872479
  have hstable : (prefixWord ++ tailWord_3872479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872479).length < 2 ^ (prefixWord ++ tailWord_3872479).sum := by decide
  have hdescent : baseEnd_3872479 < baseStart_3872479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872516 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 7]
def baseStart_3872516 : Nat := 118140960795 + 3872516 * 2 ^ 59
def prefixEnd_3872516 : Nat := 4983230072969 + 3 ^ 40 * 3872516 * 2
def baseEnd_3872516 : Nat := 220940227802963999671181

theorem tailTrace_3872516 : CollatzResearch.WordTrace tailWord_3872516 prefixEnd_3872516 220940227802963999671181 := by
  unfold tailWord_3872516
  simp only [CollatzResearch.WordTrace]
  refine ⟨70621131019271689961654701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94161508025695586615539601 70621131019271689961654701)
  ·
    refine ⟨26482924132226883735620513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70621131019271689961654701 26482924132226883735620513)
    ·
      refine ⟨19862193099170162801715385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26482924132226883735620513 19862193099170162801715385)
      ·
        refine ⟨14896644824377622101286539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19862193099170162801715385 14896644824377622101286539)
        ·
          refine ⟨22344967236566433151929809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14896644824377622101286539 22344967236566433151929809)
          ·
            refine ⟨16758725427424824863947357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22344967236566433151929809 16758725427424824863947357)
            ·
              refine ⟨6284522035284309323980259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16758725427424824863947357 6284522035284309323980259)
              ·
                refine ⟨9426783052926463985970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284522035284309323980259 9426783052926463985970389)
                ·
                  refine ⟨220940227802963999671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9426783052926463985970389 220940227802963999671181)
                  ·
                    rfl

theorem cell23_3872516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_3872516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872516 prefixEnd_3872516 := by exact prefixLift 3872516
  have htrace : WordTrace (prefixWord ++ tailWord_3872516) baseStart_3872516 baseEnd_3872516 := by
    simpa [prefixWord, tailWord_3872516, baseEnd_3872516] using wordTrace_append hprefix tailTrace_3872516
  have hstable : (prefixWord ++ tailWord_3872516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872516).length < 2 ^ (prefixWord ++ tailWord_3872516).sum := by decide
  have hdescent : baseEnd_3872516 < baseStart_3872516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872526 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3872526 : Nat := 118140960795 + 3872526 * 2 ^ 59
def prefixEnd_3872526 : Nat := 4983230072969 + 3 ^ 40 * 3872526 * 2
def baseEnd_3872526 : Nat := 1988467185033220957915583

theorem tailTrace_3872526 : CollatzResearch.WordTrace tailWord_3872526 prefixEnd_3872526 1988467185033220957915583 := by
  unfold tailWord_3872526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655328346063393953896679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94161751179004767754115621 17655328346063393953896679)
  ·
    refine ⟨26482992519095090930845019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17655328346063393953896679 26482992519095090930845019)
    ·
      refine ⟨39724488778642636396267529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26482992519095090930845019 39724488778642636396267529)
      ·
        refine ⟨29793366583981977297200647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39724488778642636396267529 29793366583981977297200647)
        ·
          refine ⟨44690049875972965945800971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29793366583981977297200647 44690049875972965945800971)
          ·
            refine ⟨67035074813959448918701457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44690049875972965945800971 67035074813959448918701457)
            ·
              refine ⟨50276306110469586689026093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67035074813959448918701457 50276306110469586689026093)
              ·
                refine ⟨18853614791426095008384785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50276306110469586689026093 18853614791426095008384785)
                ·
                  refine ⟨14140211093569571256288589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18853614791426095008384785 14140211093569571256288589)
                  ·
                    refine ⟨5302579160088589221108221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14140211093569571256288589 5302579160088589221108221)
                    ·
                      refine ⟨1988467185033220957915583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5302579160088589221108221 1988467185033220957915583)
                      ·
                        rfl

theorem cell23_3872526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3872526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872526 prefixEnd_3872526 := by exact prefixLift 3872526
  have htrace : WordTrace (prefixWord ++ tailWord_3872526) baseStart_3872526 baseEnd_3872526 := by
    simpa [prefixWord, tailWord_3872526, baseEnd_3872526] using wordTrace_append hprefix tailTrace_3872526
  have hstable : (prefixWord ++ tailWord_3872526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872526).length < 2 ^ (prefixWord ++ tailWord_3872526).sum := by decide
  have hdescent : baseEnd_3872526 < baseStart_3872526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872529 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_3872529 : Nat := 118140960795 + 3872529 * 2 ^ 59
def prefixEnd_3872529 : Nat := 4983230072969 + 3 ^ 40 * 3872529 * 2
def baseEnd_3872529 : Nat := 662822908491728148726023

theorem tailTrace_3872529 : CollatzResearch.WordTrace tailWord_3872529 prefixEnd_3872529 662822908491728148726023 := by
  unfold tailWord_3872529
  simp only [CollatzResearch.WordTrace]
  refine ⟨141242736187496283143532641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94161824124997522095688427 141242736187496283143532641)
  ·
    refine ⟨105932052140622212357649481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141242736187496283143532641 105932052140622212357649481)
    ·
      refine ⟨79449039105466659268237111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105932052140622212357649481 79449039105466659268237111)
      ·
        refine ⟨119173558658199988902355667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79449039105466659268237111 119173558658199988902355667)
        ·
          refine ⟨178760337987299983353533501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119173558658199988902355667 178760337987299983353533501)
          ·
            refine ⟨67035126745237493757575063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178760337987299983353533501 67035126745237493757575063)
            ·
              refine ⟨100552690117856240636362595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67035126745237493757575063 100552690117856240636362595)
              ·
                refine ⟨150829035176784360954543893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100552690117856240636362595 150829035176784360954543893)
                ·
                  refine ⟨7070111023911766919744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150829035176784360954543893 7070111023911766919744245)
                  ·
                    refine ⟨662822908491728148726023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7070111023911766919744245 662822908491728148726023)
                    ·
                      rfl

theorem cell23_3872529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_3872529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872529 prefixEnd_3872529 := by exact prefixLift 3872529
  have htrace : WordTrace (prefixWord ++ tailWord_3872529) baseStart_3872529 baseEnd_3872529 := by
    simpa [prefixWord, tailWord_3872529, baseEnd_3872529] using wordTrace_append hprefix tailTrace_3872529
  have hstable : (prefixWord ++ tailWord_3872529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872529).length < 2 ^ (prefixWord ++ tailWord_3872529).sum := by decide
  have hdescent : baseEnd_3872529 < baseStart_3872529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872586 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_3872586 : Nat := 118140960795 + 3872586 * 2 ^ 59
def prefixEnd_3872586 : Nat := 4983230072969 + 3 ^ 40 * 3872586 * 2
def baseEnd_3872586 : Nat := 1988497993872490723165307

theorem tailTrace_3872586 : CollatzResearch.WordTrace tailWord_3872586 prefixEnd_3872586 1988497993872490723165307 := by
  unfold tailWord_3872586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35311203787072445469589403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94163210098859854585571741 35311203787072445469589403)
  ·
    refine ⟨52966805680608668204384105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35311203787072445469589403 52966805680608668204384105)
    ·
      refine ⟨39725104260456501153288079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52966805680608668204384105 39725104260456501153288079)
      ·
        refine ⟨59587656390684751729932119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39725104260456501153288079 59587656390684751729932119)
        ·
          refine ⟨89381484586027127594898179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59587656390684751729932119 89381484586027127594898179)
          ·
            refine ⟨134072226879040691392347269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89381484586027127594898179 134072226879040691392347269)
            ·
              refine ⟨25138542539820129636065113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134072226879040691392347269 25138542539820129636065113)
              ·
                refine ⟨18853906904865097227048835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25138542539820129636065113 18853906904865097227048835)
                ·
                  refine ⟨28280860357297645840573253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18853906904865097227048835 28280860357297645840573253)
                  ·
                    refine ⟨5302661316993308595107485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28280860357297645840573253 5302661316993308595107485)
                    ·
                      refine ⟨1988497993872490723165307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5302661316993308595107485 1988497993872490723165307)
                      ·
                        rfl

theorem cell23_3872586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_3872586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872586 prefixEnd_3872586 := by exact prefixLift 3872586
  have htrace : WordTrace (prefixWord ++ tailWord_3872586) baseStart_3872586 baseEnd_3872586 := by
    simpa [prefixWord, tailWord_3872586, baseEnd_3872586] using wordTrace_append hprefix tailTrace_3872586
  have hstable : (prefixWord ++ tailWord_3872586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872586).length < 2 ^ (prefixWord ++ tailWord_3872586).sum := by decide
  have hdescent : baseEnd_3872586 < baseStart_3872586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872593 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_3872593 : Nat := 118140960795 + 3872593 * 2 ^ 59
def prefixEnd_3872593 : Nat := 4983230072969 + 3 ^ 40 * 3872593 * 2
def baseEnd_3872593 : Nat := 662833862745690731925925

theorem tailTrace_3872593 : CollatzResearch.WordTrace tailWord_3872593 prefixEnd_3872593 662833862745690731925925 := by
  unfold tailWord_3872593
  simp only [CollatzResearch.WordTrace]
  refine ⟨141245070459264422073862433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94163380306176281382574955 141245070459264422073862433)
  ·
    refine ⟨105933802844448316555396825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141245070459264422073862433 105933802844448316555396825)
    ·
      refine ⟨79450352133336237416547619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105933802844448316555396825 79450352133336237416547619)
      ·
        refine ⟨119175528200004356124821429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79450352133336237416547619 119175528200004356124821429)
        ·
          refine ⟨11172705768750408386702009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119175528200004356124821429 11172705768750408386702009)
          ·
            refine ⟨8379529326562806290026507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11172705768750408386702009 8379529326562806290026507)
            ·
              refine ⟨12569293989844209435039761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379529326562806290026507 12569293989844209435039761)
              ·
                refine ⟨9426970492383157076279821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12569293989844209435039761 9426970492383157076279821)
                ·
                  refine ⟨3535113934643683903604933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9426970492383157076279821 3535113934643683903604933)
                  ·
                    refine ⟨662833862745690731925925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535113934643683903604933 662833862745690731925925)
                    ·
                      rfl

theorem cell23_3872593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_3872593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872593 prefixEnd_3872593 := by exact prefixLift 3872593
  have htrace : WordTrace (prefixWord ++ tailWord_3872593) baseStart_3872593 baseEnd_3872593 := by
    simpa [prefixWord, tailWord_3872593, baseEnd_3872593] using wordTrace_append hprefix tailTrace_3872593
  have hstable : (prefixWord ++ tailWord_3872593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872593).length < 2 ^ (prefixWord ++ tailWord_3872593).sum := by decide
  have hdescent : baseEnd_3872593 < baseStart_3872593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872643 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 5, 2]
def baseStart_3872643 : Nat := 118140960795 + 3872643 * 2 ^ 59
def prefixEnd_3872643 : Nat := 4983230072969 + 3 ^ 40 * 3872643 * 2
def baseEnd_3872643 : Nat := 1988527262269797000152545

theorem tailTrace_3872643 : CollatzResearch.WordTrace tailWord_3872643 prefixEnd_3872643 1988527262269797000152545 := by
  unfold tailWord_3872643
  simp only [CollatzResearch.WordTrace]
  refine ⟨141246894109083280613182583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94164596072722187075455055 141246894109083280613182583)
  ·
    refine ⟨211870341163624920919773875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141246894109083280613182583 211870341163624920919773875)
    ·
      refine ⟨317805511745437381379660813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211870341163624920919773875 317805511745437381379660813)
      ·
        refine ⟨119177066904539018017372805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317805511745437381379660813 119177066904539018017372805)
        ·
          refine ⟨22345700044601065878257401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119177066904539018017372805 22345700044601065878257401)
          ·
            refine ⟨16759275033450799408693051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22345700044601065878257401 16759275033450799408693051)
            ·
              refine ⟨25138912550176199113039577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16759275033450799408693051 25138912550176199113039577)
              ·
                refine ⟨18854184412632149334779683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25138912550176199113039577 18854184412632149334779683)
                ·
                  refine ⟨28281276618948224002169525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18854184412632149334779683 28281276618948224002169525)
                  ·
                    refine ⟨2651369683026396000203393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28281276618948224002169525 2651369683026396000203393)
                    ·
                      refine ⟨1988527262269797000152545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651369683026396000203393 1988527262269797000152545)
                      ·
                        rfl

theorem cell23_3872643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_3872643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872643 prefixEnd_3872643 := by exact prefixLift 3872643
  have htrace : WordTrace (prefixWord ++ tailWord_3872643) baseStart_3872643 baseEnd_3872643 := by
    simpa [prefixWord, tailWord_3872643, baseEnd_3872643] using wordTrace_append hprefix tailTrace_3872643
  have hstable : (prefixWord ++ tailWord_3872643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872643).length < 2 ^ (prefixWord ++ tailWord_3872643).sum := by decide
  have hdescent : baseEnd_3872643 < baseStart_3872643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872660 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3872660 : Nat := 118140960795 + 3872660 * 2 ^ 59
def prefixEnd_3872660 : Nat := 4983230072969 + 3 ^ 40 * 3872660 * 2
def baseEnd_3872660 : Nat := 1988535991440923433639967

theorem tailTrace_3872660 : CollatzResearch.WordTrace tailWord_3872660 prefixEnd_3872660 1988535991440923433639967 := by
  unfold tailWord_3872660
  simp only [CollatzResearch.WordTrace]
  refine ⟨70623757075010846258275717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94165009433347795011034289 70623757075010846258275717)
  ·
    refine ⟨13241954451564533673426697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70623757075010846258275717 13241954451564533673426697)
    ·
      refine ⟨9931465838673400255070023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13241954451564533673426697 9931465838673400255070023)
      ·
        refine ⟨14897198758010100382605035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931465838673400255070023 14897198758010100382605035)
        ·
          refine ⟨22345798137015150573907553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897198758010100382605035 22345798137015150573907553)
          ·
            refine ⟨16759348602761362930430665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22345798137015150573907553 16759348602761362930430665)
            ·
              refine ⟨12569511452071022197822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759348602761362930430665 12569511452071022197822999)
              ·
                refine ⟨18854267178106533296734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569511452071022197822999 18854267178106533296734499)
                ·
                  refine ⟨28281400767159799945101749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18854267178106533296734499 28281400767159799945101749)
                  ·
                    refine ⟨2651381321921231244853289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28281400767159799945101749 2651381321921231244853289)
                    ·
                      refine ⟨1988535991440923433639967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651381321921231244853289 1988535991440923433639967)
                      ·
                        rfl

theorem cell23_3872660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3872660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872660 prefixEnd_3872660 := by exact prefixLift 3872660
  have htrace : WordTrace (prefixWord ++ tailWord_3872660) baseStart_3872660 baseEnd_3872660 := by
    simpa [prefixWord, tailWord_3872660, baseEnd_3872660] using wordTrace_append hprefix tailTrace_3872660
  have hstable : (prefixWord ++ tailWord_3872660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872660).length < 2 ^ (prefixWord ++ tailWord_3872660).sum := by decide
  have hdescent : baseEnd_3872660 < baseStart_3872660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872693 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3872693 : Nat := 118140960795 + 3872693 * 2 ^ 59
def prefixEnd_3872693 : Nat := 4983230072969 + 3 ^ 40 * 3872693 * 2
def baseEnd_3872693 : Nat := 1988552936302521804527315

theorem tailTrace_3872693 : CollatzResearch.WordTrace tailWord_3872693 prefixEnd_3872693 1988552936302521804527315 := by
  unfold tailWord_3872693
  simp only [CollatzResearch.WordTrace]
  refine ⟨141248717758902139152502733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94165811839268092768335155 141248717758902139152502733)
  ·
    refine ⟨52968269159588302182188525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141248717758902139152502733 52968269159588302182188525)
    ·
      refine ⟨19863100934845613318320697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52968269159588302182188525 19863100934845613318320697)
      ·
        refine ⟨14897325701134209988740523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19863100934845613318320697 14897325701134209988740523)
        ·
          refine ⟨22345988551701314983110785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897325701134209988740523 22345988551701314983110785)
          ·
            refine ⟨16759491413775986237333089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22345988551701314983110785 16759491413775986237333089)
            ·
              refine ⟨12569618560331989677999817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759491413775986237333089 12569618560331989677999817)
              ·
                refine ⟨9427213920248992258499863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12569618560331989677999817 9427213920248992258499863)
                ·
                  refine ⟨14140820880373488387749795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427213920248992258499863 14140820880373488387749795)
                  ·
                    refine ⟨21211231320560232581624693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14140820880373488387749795 21211231320560232581624693)
                    ·
                      refine ⟨1988552936302521804527315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21211231320560232581624693 1988552936302521804527315)
                      ·
                        rfl

theorem cell23_3872693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3872693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872693 prefixEnd_3872693 := by exact prefixLift 3872693
  have htrace : WordTrace (prefixWord ++ tailWord_3872693) baseStart_3872693 baseEnd_3872693 := by
    simpa [prefixWord, tailWord_3872693, baseEnd_3872693] using wordTrace_append hprefix tailTrace_3872693
  have hstable : (prefixWord ++ tailWord_3872693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872693).length < 2 ^ (prefixWord ++ tailWord_3872693).sum := by decide
  have hdescent : baseEnd_3872693 < baseStart_3872693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872696 : List Nat := [2, 1, 2, 1, 2, 3, 4, 8]
def baseStart_3872696 : Nat := 118140960795 + 3872696 * 2 ^ 59
def prefixEnd_3872696 : Nat := 4983230072969 + 3 ^ 40 * 3872696 * 2
def baseEnd_3872696 : Nat := 73650165805351307140363

theorem tailTrace_3872696 : CollatzResearch.WordTrace tailWord_3872696 prefixEnd_3872696 73650165805351307140363 := by
  unfold tailWord_3872696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624413588945635332430971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94165884785260847109907961 70624413588945635332430971)
  ·
    refine ⟨105936620383418452998646457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70624413588945635332430971 105936620383418452998646457)
    ·
      refine ⟨79452465287563839748984843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105936620383418452998646457 79452465287563839748984843)
      ·
        refine ⟨119178697931345759623477265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452465287563839748984843 119178697931345759623477265)
        ·
          refine ⟨89384023448509319717607949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119178697931345759623477265 89384023448509319717607949)
          ·
            refine ⟨33519008793190994894102981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89384023448509319717607949 33519008793190994894102981)
            ·
              refine ⟨6284814148723311542644309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33519008793190994894102981 6284814148723311542644309)
              ·
                refine ⟨73650165805351307140363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6284814148723311542644309 73650165805351307140363)
                ·
                  rfl

theorem cell23_3872696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 8].length) (baseStart_3872696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872696 prefixEnd_3872696 := by exact prefixLift 3872696
  have htrace : WordTrace (prefixWord ++ tailWord_3872696) baseStart_3872696 baseEnd_3872696 := by
    simpa [prefixWord, tailWord_3872696, baseEnd_3872696] using wordTrace_append hprefix tailTrace_3872696
  have hstable : (prefixWord ++ tailWord_3872696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872696).length < 2 ^ (prefixWord ++ tailWord_3872696).sum := by decide
  have hdescent : baseEnd_3872696 < baseStart_3872696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872724 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3872724 : Nat := 118140960795 + 3872724 * 2 ^ 59
def prefixEnd_3872724 : Nat := 4983230072969 + 3 ^ 40 * 3872724 * 2
def baseEnd_3872724 : Nat := 1988568854202811183239673

theorem tailTrace_3872724 : CollatzResearch.WordTrace tailWord_3872724 prefixEnd_3872724 1988568854202811183239673 := by
  unfold tailWord_3872724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624924210894915723440613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94166565614526554297920817 70624924210894915723440613)
  ·
    refine ⟨13242173289542796698145115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70624924210894915723440613 13242173289542796698145115)
    ·
      refine ⟨19863259934314195047217673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13242173289542796698145115 19863259934314195047217673)
      ·
        refine ⟨14897444950735646285413255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19863259934314195047217673 14897444950735646285413255)
        ·
          refine ⟨22346167426103469428119883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897444950735646285413255 22346167426103469428119883)
          ·
            refine ⟨33519251139155204142179825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22346167426103469428119883 33519251139155204142179825)
            ·
              refine ⟨25139438354366403106634869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33519251139155204142179825 25139438354366403106634869)
              ·
                refine ⟨2356822345721850291247019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25139438354366403106634869 2356822345721850291247019)
                ·
                  refine ⟨3535233518582775436870529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356822345721850291247019 3535233518582775436870529)
                  ·
                    refine ⟨2651425138937081577652897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3535233518582775436870529 2651425138937081577652897)
                    ·
                      refine ⟨1988568854202811183239673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651425138937081577652897 1988568854202811183239673)
                      ·
                        rfl

theorem cell23_3872724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3872724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872724 prefixEnd_3872724 := by exact prefixLift 3872724
  have htrace : WordTrace (prefixWord ++ tailWord_3872724) baseStart_3872724 baseEnd_3872724 := by
    simpa [prefixWord, tailWord_3872724, baseEnd_3872724] using wordTrace_append hprefix tailTrace_3872724
  have hstable : (prefixWord ++ tailWord_3872724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872724).length < 2 ^ (prefixWord ++ tailWord_3872724).sum := by decide
  have hdescent : baseEnd_3872724 < baseStart_3872724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872736 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3872736 : Nat := 118140960795 + 3872736 * 2 ^ 59
def prefixEnd_3872736 : Nat := 4983230072969 + 3 ^ 40 * 3872736 * 2
def baseEnd_3872736 : Nat := 1988575015970665136289617

theorem tailTrace_3872736 : CollatzResearch.WordTrace tailWord_3872736 prefixEnd_3872736 1988575015970665136289617 := by
  unfold tailWord_3872736
  simp only [CollatzResearch.WordTrace]
  refine ⟨70625143048873178748159031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94166857398497571664212041 70625143048873178748159031)
  ·
    refine ⟨105937714573309768122238547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70625143048873178748159031 105937714573309768122238547)
    ·
      refine ⟨158906571859964652183357821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105937714573309768122238547 158906571859964652183357821)
      ·
        refine ⟨59589964447486744568759183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158906571859964652183357821 59589964447486744568759183)
        ·
          refine ⟨89384946671230116853138775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59589964447486744568759183 89384946671230116853138775)
          ·
            refine ⟨134077420006845175279708163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89384946671230116853138775 134077420006845175279708163)
            ·
              refine ⟨201116130010267762919562245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134077420006845175279708163 201116130010267762919562245)
              ·
                refine ⟨37709274376925205547417921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201116130010267762919562245 37709274376925205547417921)
                ·
                  refine ⟨28281955782693904160563441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37709274376925205547417921 28281955782693904160563441)
                  ·
                    refine ⟨21211466837020428120422581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28281955782693904160563441 21211466837020428120422581)
                    ·
                      refine ⟨1988575015970665136289617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21211466837020428120422581 1988575015970665136289617)
                      ·
                        rfl

theorem cell23_3872736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3872736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872736 prefixEnd_3872736 := by exact prefixLift 3872736
  have htrace : WordTrace (prefixWord ++ tailWord_3872736) baseStart_3872736 baseEnd_3872736 := by
    simpa [prefixWord, tailWord_3872736, baseEnd_3872736] using wordTrace_append hprefix tailTrace_3872736
  have hstable : (prefixWord ++ tailWord_3872736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872736).length < 2 ^ (prefixWord ++ tailWord_3872736).sum := by decide
  have hdescent : baseEnd_3872736 < baseStart_3872736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872780 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_3872780 : Nat := 118140960795 + 3872780 * 2 ^ 59
def prefixEnd_3872780 : Nat := 4983230072969 + 3 ^ 40 * 3872780 * 2
def baseEnd_3872780 : Nat := 1988597609119462964139415

theorem tailTrace_3872780 : CollatzResearch.WordTrace tailWord_3872780 prefixEnd_3872780 1988597609119462964139415 := by
  unfold tailWord_3872780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70625945454793476505459897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94167927273057968673946529 70625945454793476505459897)
  ·
    refine ⟨52969459091095107379094923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70625945454793476505459897 52969459091095107379094923)
    ·
      refine ⟨79454188636642661068642385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52969459091095107379094923 79454188636642661068642385)
      ·
        refine ⟨59590641477481995801481789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79454188636642661068642385 59590641477481995801481789)
        ·
          refine ⟨22346490554055748425555671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59590641477481995801481789 22346490554055748425555671)
          ·
            refine ⟨33519735831083622638333507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22346490554055748425555671 33519735831083622638333507)
            ·
              refine ⟨50279603746625433957500261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33519735831083622638333507 50279603746625433957500261)
              ·
                refine ⟨9427425702492268867031299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50279603746625433957500261 9427425702492268867031299)
                ·
                  refine ⟨14141138553738403300546949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427425702492268867031299 14141138553738403300546949)
                  ·
                    refine ⟨2651463478825950618852553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14141138553738403300546949 2651463478825950618852553)
                    ·
                      refine ⟨1988597609119462964139415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651463478825950618852553 1988597609119462964139415)
                      ·
                        rfl

theorem cell23_3872780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_3872780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872780 prefixEnd_3872780 := by exact prefixLift 3872780
  have htrace : WordTrace (prefixWord ++ tailWord_3872780) baseStart_3872780 baseEnd_3872780 := by
    simpa [prefixWord, tailWord_3872780, baseEnd_3872780] using wordTrace_append hprefix tailTrace_3872780
  have hstable : (prefixWord ++ tailWord_3872780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872780).length < 2 ^ (prefixWord ++ tailWord_3872780).sum := by decide
  have hdescent : baseEnd_3872780 < baseStart_3872780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872791 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3872791 : Nat := 118140960795 + 3872791 * 2 ^ 59
def prefixEnd_3872791 : Nat := 4983230072969 + 3 ^ 40 * 3872791 * 2
def baseEnd_3872791 : Nat := 1988603257406662421101865

theorem tailTrace_3872791 : CollatzResearch.WordTrace tailWord_3872791 prefixEnd_3872791 1988603257406662421101865 := by
  unfold tailWord_3872791
  simp only [CollatzResearch.WordTrace]
  refine ⟨141252292112547101889570227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94168194741698067926380151 141252292112547101889570227)
  ·
    refine ⟨211878438168820652834355341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141252292112547101889570227 211878438168820652834355341)
    ·
      refine ⟨79454414313307744812883253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211878438168820652834355341 79454414313307744812883253)
      ·
        refine ⟨7448851341872601076207805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79454414313307744812883253 7448851341872601076207805)
        ·
          refine ⟨2793319253202225403577927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448851341872601076207805 2793319253202225403577927)
          ·
            refine ⟨4189978879803338105366891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793319253202225403577927 4189978879803338105366891)
            ·
              refine ⟨6284968319705007158050337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189978879803338105366891 6284968319705007158050337)
              ·
                refine ⟨4713726239778755368537753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284968319705007158050337 4713726239778755368537753)
                ·
                  refine ⟨3535294679834066526403315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713726239778755368537753 3535294679834066526403315)
                  ·
                    refine ⟨5302942019751099789604973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535294679834066526403315 5302942019751099789604973)
                    ·
                      refine ⟨1988603257406662421101865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5302942019751099789604973 1988603257406662421101865)
                      ·
                        rfl

theorem cell23_3872791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3872791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872791 prefixEnd_3872791 := by exact prefixLift 3872791
  have htrace : WordTrace (prefixWord ++ tailWord_3872791) baseStart_3872791 baseEnd_3872791 := by
    simpa [prefixWord, tailWord_3872791, baseEnd_3872791] using wordTrace_append hprefix tailTrace_3872791
  have hstable : (prefixWord ++ tailWord_3872791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872791).length < 2 ^ (prefixWord ++ tailWord_3872791).sum := by decide
  have hdescent : baseEnd_3872791 < baseStart_3872791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872803 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 7]
def baseStart_3872803 : Nat := 118140960795 + 3872803 * 2 ^ 59
def prefixEnd_3872803 : Nat := 4983230072969 + 3 ^ 40 * 3872803 * 2
def baseEnd_3872803 : Nat := 220956602130501819350201

theorem tailTrace_3872803 : CollatzResearch.WordTrace tailWord_3872803 prefixEnd_3872803 220956602130501819350201 := by
  unfold tailWord_3872803
  simp only [CollatzResearch.WordTrace]
  refine ⟨141252729788503627939007063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94168486525669085292671375 141252729788503627939007063)
  ·
    refine ⟨211879094682755441908510595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141252729788503627939007063 211879094682755441908510595)
    ·
      refine ⟨317818642024133162862765893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211879094682755441908510595 317818642024133162862765893)
      ·
        refine ⟨59590995379524968036768605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317818642024133162862765893 59590995379524968036768605)
        ·
          refine ⟨22346623267321863013788227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59590995379524968036768605 22346623267321863013788227)
          ·
            refine ⟨33519934900982794520682341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22346623267321863013788227 33519934900982794520682341)
            ·
              refine ⟨6284987793934273972627939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33519934900982794520682341 6284987793934273972627939)
              ·
                refine ⟨9427481690901410958941909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284987793934273972627939 9427481690901410958941909)
                ·
                  refine ⟨220956602130501819350201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9427481690901410958941909 220956602130501819350201)
                  ·
                    rfl

theorem cell23_3872803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 7].length) (baseStart_3872803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872803 prefixEnd_3872803 := by exact prefixLift 3872803
  have htrace : WordTrace (prefixWord ++ tailWord_3872803) baseStart_3872803 baseEnd_3872803 := by
    simpa [prefixWord, tailWord_3872803, baseEnd_3872803] using wordTrace_append hprefix tailTrace_3872803
  have hstable : (prefixWord ++ tailWord_3872803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872803).length < 2 ^ (prefixWord ++ tailWord_3872803).sum := by decide
  have hdescent : baseEnd_3872803 < baseStart_3872803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872810 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3872810 : Nat := 118140960795 + 3872810 * 2 ^ 59
def prefixEnd_3872810 : Nat := 4983230072969 + 3 ^ 40 * 3872810 * 2
def baseEnd_3872810 : Nat := 1988613013539097846764277

theorem tailTrace_3872810 : CollatzResearch.WordTrace tailWord_3872810 prefixEnd_3872810 1988613013539097846764277 := by
  unfold tailWord_3872810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35313246274869567033627971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94168656732985512089674589 35313246274869567033627971)
  ·
    refine ⟨52969869412304350550441957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35313246274869567033627971 52969869412304350550441957)
    ·
      refine ⟨9931850514807065728207867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52969869412304350550441957 9931850514807065728207867)
      ·
        refine ⟨14897775772210598592311801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931850514807065728207867 14897775772210598592311801)
        ·
          refine ⟨11173331829157948944233851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14897775772210598592311801 11173331829157948944233851)
          ·
            refine ⟨16759997743736923416350777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173331829157948944233851 16759997743736923416350777)
            ·
              refine ⟨12569998307802692562263083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759997743736923416350777 12569998307802692562263083)
              ·
                refine ⟨18854997461704038843394625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569998307802692562263083 18854997461704038843394625)
                ·
                  refine ⟨14141248096278029132545969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18854997461704038843394625 14141248096278029132545969)
                  ·
                    refine ⟨10605936072208521849409477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14141248096278029132545969 10605936072208521849409477)
                    ·
                      refine ⟨1988613013539097846764277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10605936072208521849409477 1988613013539097846764277)
                      ·
                        rfl

theorem cell23_3872810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3872810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872810 prefixEnd_3872810 := by exact prefixLift 3872810
  have htrace : WordTrace (prefixWord ++ tailWord_3872810) baseStart_3872810 baseEnd_3872810 := by
    simpa [prefixWord, tailWord_3872810, baseEnd_3872810] using wordTrace_append hprefix tailTrace_3872810
  have hstable : (prefixWord ++ tailWord_3872810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872810).length < 2 ^ (prefixWord ++ tailWord_3872810).sum := by decide
  have hdescent : baseEnd_3872810 < baseStart_3872810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872814 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_3872814 : Nat := 118140960795 + 3872814 * 2 ^ 59
def prefixEnd_3872814 : Nat := 4983230072969 + 3 ^ 40 * 3872814 * 2
def baseEnd_3872814 : Nat := 1988615067461715831114259

theorem tailTrace_3872814 : CollatzResearch.WordTrace tailWord_3872814 prefixEnd_3872814 1988615067461715831114259 := by
  unfold tailWord_3872814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656641373932972102207187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94168753994309184545104997 17656641373932972102207187)
  ·
    refine ⟨26484962060899458153310781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656641373932972102207187 26484962060899458153310781)
    ·
      refine ⟨9931860772837296807491543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26484962060899458153310781 9931860772837296807491543)
      ·
        refine ⟨14897791159255945211237315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931860772837296807491543 14897791159255945211237315)
        ·
          refine ⟨22346686738883917816855973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897791159255945211237315 22346686738883917816855973)
          ·
            refine ⟨4190003763540734590660495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22346686738883917816855973 4190003763540734590660495)
            ·
              refine ⟨6285005645311101885990743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190003763540734590660495 6285005645311101885990743)
              ·
                refine ⟨9427508467966652828986115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285005645311101885990743 9427508467966652828986115)
                ·
                  refine ⟨14141262701949979243479173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427508467966652828986115 14141262701949979243479173)
                  ·
                    refine ⟨2651486756615621108152345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14141262701949979243479173 2651486756615621108152345)
                    ·
                      refine ⟨1988615067461715831114259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651486756615621108152345 1988615067461715831114259)
                      ·
                        rfl

theorem cell23_3872814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_3872814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872814 prefixEnd_3872814 := by exact prefixLift 3872814
  have htrace : WordTrace (prefixWord ++ tailWord_3872814) baseStart_3872814 baseEnd_3872814 := by
    simpa [prefixWord, tailWord_3872814, baseEnd_3872814] using wordTrace_append hprefix tailTrace_3872814
  have hstable : (prefixWord ++ tailWord_3872814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872814).length < 2 ^ (prefixWord ++ tailWord_3872814).sum := by decide
  have hdescent : baseEnd_3872814 < baseStart_3872814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872854 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3872854 : Nat := 118140960795 + 3872854 * 2 ^ 59
def prefixEnd_3872854 : Nat := 4983230072969 + 3 ^ 40 * 3872854 * 2
def baseEnd_3872854 : Nat := 220959511854210630512675

theorem tailTrace_3872854 : CollatzResearch.WordTrace tailWord_3872854 prefixEnd_3872854 220959511854210630512675 := by
  unfold tailWord_3872854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828411869457428978069601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94169726607545909099409077 8828411869457428978069601)
  ·
    refine ⟨6621308902093071733552201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8828411869457428978069601 6621308902093071733552201)
    ·
      refine ⟨4965981676569803800164151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6621308902093071733552201 4965981676569803800164151)
      ·
        refine ⟨7448972514854705700246227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965981676569803800164151 7448972514854705700246227)
        ·
          refine ⟨11173458772282058550369341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448972514854705700246227 11173458772282058550369341)
          ·
            refine ⟨4190047039605771956388503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11173458772282058550369341 4190047039605771956388503)
            ·
              refine ⟨6285070559408657934582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190047039605771956388503 6285070559408657934582755)
              ·
                refine ⟨9427605839112986901874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285070559408657934582755 9427605839112986901874133)
                ·
                  refine ⟨220959511854210630512675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9427605839112986901874133 220959511854210630512675)
                  ·
                    rfl

theorem cell23_3872854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3872854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872854 prefixEnd_3872854 := by exact prefixLift 3872854
  have htrace : WordTrace (prefixWord ++ tailWord_3872854) baseStart_3872854 baseEnd_3872854 := by
    simpa [prefixWord, tailWord_3872854, baseEnd_3872854] using wordTrace_append hprefix tailTrace_3872854
  have hstable : (prefixWord ++ tailWord_3872854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872854).length < 2 ^ (prefixWord ++ tailWord_3872854).sum := by decide
  have hdescent : baseEnd_3872854 < baseStart_3872854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872860 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3872860 : Nat := 118140960795 + 3872860 * 2 ^ 59
def prefixEnd_3872860 : Nat := 4983230072969 + 3 ^ 40 * 3872860 * 2
def baseEnd_3872860 : Nat := 1988638687571822651139047

theorem tailTrace_3872860 : CollatzResearch.WordTrace tailWord_3872860 prefixEnd_3872860 1988638687571822651139047 := by
  unfold tailWord_3872860
  simp only [CollatzResearch.WordTrace]
  refine ⟨70627404374648563336916017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94169872499531417782554689 70627404374648563336916017)
  ·
    refine ⟨52970553280986422502687013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70627404374648563336916017 52970553280986422502687013)
    ·
      refine ⟨9931978740184954219253815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52970553280986422502687013 9931978740184954219253815)
      ·
        refine ⟨14897968110277431328880723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931978740184954219253815 14897968110277431328880723)
        ·
          refine ⟨22346952165416146993321085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897968110277431328880723 22346952165416146993321085)
          ·
            refine ⟨8380107062031055122495407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22346952165416146993321085 8380107062031055122495407)
            ·
              refine ⟨12570160593046582683743111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380107062031055122495407 12570160593046582683743111)
              ·
                refine ⟨18855240889569874025614667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12570160593046582683743111 18855240889569874025614667)
                ·
                  refine ⟨28282861334354811038422001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18855240889569874025614667 28282861334354811038422001)
                  ·
                    refine ⟨21212146000766108278816501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28282861334354811038422001 21212146000766108278816501)
                    ·
                      refine ⟨1988638687571822651139047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21212146000766108278816501 1988638687571822651139047)
                      ·
                        rfl

theorem cell23_3872860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3872860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872860 prefixEnd_3872860 := by exact prefixLift 3872860
  have htrace : WordTrace (prefixWord ++ tailWord_3872860) baseStart_3872860 baseEnd_3872860 := by
    simpa [prefixWord, tailWord_3872860, baseEnd_3872860] using wordTrace_append hprefix tailTrace_3872860
  have hstable : (prefixWord ++ tailWord_3872860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872860).length < 2 ^ (prefixWord ++ tailWord_3872860).sum := by decide
  have hdescent : baseEnd_3872860 < baseStart_3872860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872914 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3872914 : Nat := 118140960795 + 3872914 * 2 ^ 59
def prefixEnd_3872914 : Nat := 4983230072969 + 3 ^ 40 * 3872914 * 2
def baseEnd_3872914 : Nat := 662888805175721813287933

theorem tailTrace_3872914 : CollatzResearch.WordTrace tailWord_3872914 prefixEnd_3872914 662888805175721813287933 := by
  unfold tailWord_3872914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314194572775373474074449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94171185527400995930865197 35314194572775373474074449)
  ·
    refine ⟨26485645929581530105555837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35314194572775373474074449 26485645929581530105555837)
    ·
      refine ⟨9932117223593073789583439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26485645929581530105555837 9932117223593073789583439)
      ·
        refine ⟨14898175835389610684375159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932117223593073789583439 14898175835389610684375159)
        ·
          refine ⟨22347263753084416026562739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898175835389610684375159 22347263753084416026562739)
          ·
            refine ⟨33520895629626624039844109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22347263753084416026562739 33520895629626624039844109)
            ·
              refine ⟨12570335861109984014941541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33520895629626624039844109 12570335861109984014941541)
              ·
                refine ⟨2356937973958122002801539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12570335861109984014941541 2356937973958122002801539)
                ·
                  refine ⟨3535406960937183004202309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356937973958122002801539 3535406960937183004202309)
                  ·
                    refine ⟨662888805175721813287933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535406960937183004202309 662888805175721813287933)
                    ·
                      rfl

theorem cell23_3872914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3872914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872914 prefixEnd_3872914 := by exact prefixLift 3872914
  have htrace : WordTrace (prefixWord ++ tailWord_3872914) baseStart_3872914 baseEnd_3872914 := by
    simpa [prefixWord, tailWord_3872914, baseEnd_3872914] using wordTrace_append hprefix tailTrace_3872914
  have hstable : (prefixWord ++ tailWord_3872914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872914).length < 2 ^ (prefixWord ++ tailWord_3872914).sum := by decide
  have hdescent : baseEnd_3872914 < baseStart_3872914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872923 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 5, 5]
def baseStart_3872923 : Nat := 118140960795 + 3872923 * 2 ^ 59
def prefixEnd_3872923 : Nat := 4983230072969 + 3 ^ 40 * 3872923 * 2
def baseEnd_3872923 : Nat := 662890345617685301550419

theorem tailTrace_3872923 : CollatzResearch.WordTrace tailWord_3872923 prefixEnd_3872923 662890345617685301550419 := by
  unfold tailWord_3872923
  simp only [CollatzResearch.WordTrace]
  refine ⟨141257106548068888433375423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94171404365379258955583615 141257106548068888433375423)
  ·
    refine ⟨211885659822103332650063135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141257106548068888433375423 211885659822103332650063135)
    ·
      refine ⟨317828489733154998975094703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211885659822103332650063135 317828489733154998975094703)
      ·
        refine ⟨476742734599732498462642055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317828489733154998975094703 476742734599732498462642055)
        ·
          refine ⟨715114101899598747693963083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476742734599732498462642055 715114101899598747693963083)
          ·
            refine ⟨1072671152849398121540944625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715114101899598747693963083 1072671152849398121540944625)
            ·
              refine ⟨804503364637048591155708469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072671152849398121540944625 804503364637048591155708469)
              ·
                refine ⟨75422190434723305420847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804503364637048591155708469 75422190434723305420847669)
                ·
                  refine ⟨7070830353255309883204469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75422190434723305420847669 7070830353255309883204469)
                  ·
                    refine ⟨662890345617685301550419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7070830353255309883204469 662890345617685301550419)
                    ·
                      rfl

theorem cell23_3872923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].length) (baseStart_3872923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872923 prefixEnd_3872923 := by exact prefixLift 3872923
  have htrace : WordTrace (prefixWord ++ tailWord_3872923) baseStart_3872923 baseEnd_3872923 := by
    simpa [prefixWord, tailWord_3872923, baseEnd_3872923] using wordTrace_append hprefix tailTrace_3872923
  have hstable : (prefixWord ++ tailWord_3872923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872923).length < 2 ^ (prefixWord ++ tailWord_3872923).sum := by decide
  have hdescent : baseEnd_3872923 < baseStart_3872923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872933 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3872933 : Nat := 118140960795 + 3872933 * 2 ^ 59
def prefixEnd_3872933 : Nat := 4983230072969 + 3 ^ 40 * 3872933 * 2
def baseEnd_3872933 : Nat := 1988676171659600865526211

theorem tailTrace_3872933 : CollatzResearch.WordTrace tailWord_3872933 prefixEnd_3872933 1988676171659600865526211 := by
  unfold tailWord_3872933
  simp only [CollatzResearch.WordTrace]
  refine ⟨141257471278032660141239453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94171647518688440094159635 141257471278032660141239453)
  ·
    refine ⟨52971551729262247552964795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141257471278032660141239453 52971551729262247552964795)
    ·
      refine ⟨79457327593893371329447193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52971551729262247552964795 79457327593893371329447193)
      ·
        refine ⟨59592995695420028497085395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79457327593893371329447193 59592995695420028497085395)
        ·
          refine ⟨89389493543130042745628093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59592995695420028497085395 89389493543130042745628093)
          ·
            refine ⟨33521060078673766029610535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89389493543130042745628093 33521060078673766029610535)
            ·
              refine ⟨50281590118010649044415803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33521060078673766029610535 50281590118010649044415803)
              ·
                refine ⟨75422385177015973566623705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50281590118010649044415803 75422385177015973566623705)
                ·
                  refine ⟨56566788882761980174967779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75422385177015973566623705 56566788882761980174967779)
                  ·
                    refine ⟨84850183324142970262451669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56566788882761980174967779 84850183324142970262451669)
                    ·
                      refine ⟨1988676171659600865526211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84850183324142970262451669 1988676171659600865526211)
                      ·
                        rfl

theorem cell23_3872933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3872933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872933 prefixEnd_3872933 := by exact prefixLift 3872933
  have htrace : WordTrace (prefixWord ++ tailWord_3872933) baseStart_3872933 baseEnd_3872933 := by
    simpa [prefixWord, tailWord_3872933, baseEnd_3872933] using wordTrace_append hprefix tailTrace_3872933
  have hstable : (prefixWord ++ tailWord_3872933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872933).length < 2 ^ (prefixWord ++ tailWord_3872933).sum := by decide
  have hdescent : baseEnd_3872933 < baseStart_3872933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872954 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_3872954 : Nat := 118140960795 + 3872954 * 2 ^ 59
def prefixEnd_3872954 : Nat := 4983230072969 + 3 ^ 40 * 3872954 * 2
def baseEnd_3872954 : Nat := 1988686954753345283363615

theorem tailTrace_3872954 : CollatzResearch.WordTrace tailWord_3872954 prefixEnd_3872954 1988686954753345283363615 := by
  unfold tailWord_3872954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314559302739145181938479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94172158140637720485169277 35314559302739145181938479)
  ·
    refine ⟨52971838954108717772907719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35314559302739145181938479 52971838954108717772907719)
    ·
      refine ⟨79457758431163076659361579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52971838954108717772907719 79457758431163076659361579)
      ·
        refine ⟨119186637646744614989042369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79457758431163076659361579 119186637646744614989042369)
        ·
          refine ⟨89389978235058461241781777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119186637646744614989042369 89389978235058461241781777)
          ·
            refine ⟨67042483676293845931336333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89389978235058461241781777 67042483676293845931336333)
            ·
              refine ⟨25140931378610192224251125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67042483676293845931336333 25140931378610192224251125)
              ·
                refine ⟨2356962316744705521023543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25140931378610192224251125 2356962316744705521023543)
                ·
                  refine ⟨3535443475117058281535315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356962316744705521023543 3535443475117058281535315)
                  ·
                    refine ⟨5303165212675587422302973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535443475117058281535315 5303165212675587422302973)
                    ·
                      refine ⟨1988686954753345283363615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303165212675587422302973 1988686954753345283363615)
                      ·
                        rfl

theorem cell23_3872954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_3872954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872954 prefixEnd_3872954 := by exact prefixLift 3872954
  have htrace : WordTrace (prefixWord ++ tailWord_3872954) baseStart_3872954 baseEnd_3872954 := by
    simpa [prefixWord, tailWord_3872954, baseEnd_3872954] using wordTrace_append hprefix tailTrace_3872954
  have hstable : (prefixWord ++ tailWord_3872954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872954).length < 2 ^ (prefixWord ++ tailWord_3872954).sum := by decide
  have hdescent : baseEnd_3872954 < baseStart_3872954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872961 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 6]
def baseStart_3872961 : Nat := 118140960795 + 3872961 * 2 ^ 59
def prefixEnd_3872961 : Nat := 4983230072969 + 3 ^ 40 * 3872961 * 2
def baseEnd_3872961 : Nat := 220965616568658528441787

theorem tailTrace_3872961 : CollatzResearch.WordTrace tailWord_3872961 prefixEnd_3872961 220965616568658528441787 := by
  unfold tailWord_3872961
  simp only [CollatzResearch.WordTrace]
  refine ⟨141258492521931220923258737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94172328347954147282172491 141258492521931220923258737)
  ·
    refine ⟨105943869391448415692444053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141258492521931220923258737 105943869391448415692444053)
    ·
      refine ⟨4966118877724144485583315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105943869391448415692444053 4966118877724144485583315)
      ·
        refine ⟨7449178316586216728374973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966118877724144485583315 7449178316586216728374973)
        ·
          refine ⟨2793441868719831273140615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7449178316586216728374973 2793441868719831273140615)
          ·
            refine ⟨4190162803079746909710923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793441868719831273140615 4190162803079746909710923)
            ·
              refine ⟨6285244204619620364566385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190162803079746909710923 6285244204619620364566385)
              ·
                refine ⟨4713933153464715273424789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285244204619620364566385 4713933153464715273424789)
                ·
                  refine ⟨220965616568658528441787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4713933153464715273424789 220965616568658528441787)
                  ·
                    rfl

theorem cell23_3872961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_3872961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872961 prefixEnd_3872961 := by exact prefixLift 3872961
  have htrace : WordTrace (prefixWord ++ tailWord_3872961) baseStart_3872961 baseEnd_3872961 := by
    simpa [prefixWord, tailWord_3872961, baseEnd_3872961] using wordTrace_append hprefix tailTrace_3872961
  have hstable : (prefixWord ++ tailWord_3872961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872961).length < 2 ^ (prefixWord ++ tailWord_3872961).sum := by decide
  have hdescent : baseEnd_3872961 < baseStart_3872961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872983 : List Nat := [1, 1, 3, 2, 1, 2, 1, 12]
def baseStart_3872983 : Nat := 118140960795 + 3872983 * 2 ^ 59
def prefixEnd_3872983 : Nat := 4983230072969 + 3 ^ 40 * 3872983 * 2
def baseEnd_3872983 : Nat := 73655623914530580366703

theorem tailTrace_3872983 : CollatzResearch.WordTrace tailWord_3872983 prefixEnd_3872983 73655623914530580366703 := by
  unfold tailWord_3872983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141259294927851518680559603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94172863285234345787039735 141259294927851518680559603)
  ·
    refine ⟨211888942391777278020839405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141259294927851518680559603 211888942391777278020839405)
    ·
      refine ⟨79458353396916479257814777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211888942391777278020839405 79458353396916479257814777)
      ·
        refine ⟨59593765047687359443361083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79458353396916479257814777 59593765047687359443361083)
        ·
          refine ⟨89390647571531039165041625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59593765047687359443361083 89390647571531039165041625)
          ·
            refine ⟨67042985678648279373781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89390647571531039165041625 67042985678648279373781219)
            ·
              refine ⟨100564478517972419060671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67042985678648279373781219 100564478517972419060671829)
              ·
                refine ⟨73655623914530580366703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 100564478517972419060671829 73655623914530580366703)
                ·
                  rfl

theorem cell23_3872983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 12].length) (baseStart_3872983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3872983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3872983 prefixEnd_3872983 := by exact prefixLift 3872983
  have htrace : WordTrace (prefixWord ++ tailWord_3872983) baseStart_3872983 baseEnd_3872983 := by
    simpa [prefixWord, tailWord_3872983, baseEnd_3872983] using wordTrace_append hprefix tailTrace_3872983
  have hstable : (prefixWord ++ tailWord_3872983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872983).length < 2 ^ (prefixWord ++ tailWord_3872983).sum := by decide
  have hdescent : baseEnd_3872983 < baseStart_3872983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873000 : List Nat := [2, 1, 4, 1, 2, 3, 1, 9]
def baseStart_3873000 : Nat := 118140960795 + 3873000 * 2 ^ 59
def prefixEnd_3873000 : Nat := 4983230072969 + 3 ^ 40 * 3873000 * 2
def baseEnd_3873000 : Nat := 73655947217164892718089

theorem tailTrace_3873000 : CollatzResearch.WordTrace tailWord_3873000 prefixEnd_3873000 73655947217164892718089 := by
  unfold tailWord_3873000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70629957484394965291964227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94173276645859953722618969 70629957484394965291964227)
  ·
    refine ⟨105944936226592447937946341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70629957484394965291964227 105944936226592447937946341)
    ·
      refine ⟨19864675542486083988364939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105944936226592447937946341 19864675542486083988364939)
      ·
        refine ⟨29797013313729125982547409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19864675542486083988364939 29797013313729125982547409)
        ·
          refine ⟨22347759985296844486910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29797013313729125982547409 22347759985296844486910557)
          ·
            refine ⟨8380409994486316682591459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22347759985296844486910557 8380409994486316682591459)
            ·
              refine ⟨12570614991729475023887189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380409994486316682591459 12570614991729475023887189)
              ·
                refine ⟨73655947217164892718089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12570614991729475023887189 73655947217164892718089)
                ·
                  rfl

theorem cell23_3873000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 9].length) (baseStart_3873000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873000 prefixEnd_3873000 := by exact prefixLift 3873000
  have htrace : WordTrace (prefixWord ++ tailWord_3873000) baseStart_3873000 baseEnd_3873000 := by
    simpa [prefixWord, tailWord_3873000, baseEnd_3873000] using wordTrace_append hprefix tailTrace_3873000
  have hstable : (prefixWord ++ tailWord_3873000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873000).length < 2 ^ (prefixWord ++ tailWord_3873000).sum := by decide
  have hdescent : baseEnd_3873000 < baseStart_3873000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873005 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3873005 : Nat := 118140960795 + 3873005 * 2 ^ 59
def prefixEnd_3873005 : Nat := 4983230072969 + 3 ^ 40 * 3873005 * 2
def baseEnd_3873005 : Nat := 1988713142266724583825881

theorem tailTrace_3873005 : CollatzResearch.WordTrace tailWord_3873005 prefixEnd_3873005 1988713142266724583825881 := by
  unfold tailWord_3873005
  simp only [CollatzResearch.WordTrace]
  refine ⟨141260097333771816437860469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94173398222514544291906979 141260097333771816437860469)
  ·
    refine ⟨13243134125041107791049419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141260097333771816437860469 13243134125041107791049419)
    ·
      refine ⟨19864701187561661686574129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243134125041107791049419 19864701187561661686574129)
      ·
        refine ⟨14898525890671246264930597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19864701187561661686574129 14898525890671246264930597)
        ·
          refine ⟨2793473604500858674674487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14898525890671246264930597 2793473604500858674674487)
          ·
            refine ⟨4190210406751288012011731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793473604500858674674487 4190210406751288012011731)
            ·
              refine ⟨6285315610126932018017597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190210406751288012011731 6285315610126932018017597)
              ·
                refine ⟨2356993353797599506756599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6285315610126932018017597 2356993353797599506756599)
                ·
                  refine ⟨3535490030696399260134899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356993353797599506756599 3535490030696399260134899)
                  ·
                    refine ⟨5303235046044598890202349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535490030696399260134899 5303235046044598890202349)
                    ·
                      refine ⟨1988713142266724583825881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303235046044598890202349 1988713142266724583825881)
                      ·
                        rfl

theorem cell23_3873005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3873005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873005 prefixEnd_3873005 := by exact prefixLift 3873005
  have htrace : WordTrace (prefixWord ++ tailWord_3873005) baseStart_3873005 baseEnd_3873005 := by
    simpa [prefixWord, tailWord_3873005, baseEnd_3873005] using wordTrace_append hprefix tailTrace_3873005
  have hstable : (prefixWord ++ tailWord_3873005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873005).length < 2 ^ (prefixWord ++ tailWord_3873005).sum := by decide
  have hdescent : baseEnd_3873005 < baseStart_3873005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873014 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3873014 : Nat := 118140960795 + 3873014 * 2 ^ 59
def prefixEnd_3873014 : Nat := 4983230072969 + 3 ^ 40 * 3873014 * 2
def baseEnd_3873014 : Nat := 1988717763592615048613339

theorem tailTrace_3873014 : CollatzResearch.WordTrace tailWord_3873014 prefixEnd_3873014 1988717763592615048613339 := by
  unfold tailWord_3873014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828776599421200685933631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94173617060492807316625397 8828776599421200685933631)
  ·
    refine ⟨13243164899131801028900447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8828776599421200685933631 13243164899131801028900447)
    ·
      refine ⟨19864747348697701543350671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243164899131801028900447 19864747348697701543350671)
      ·
        refine ⟨29797121023046552315026007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19864747348697701543350671 29797121023046552315026007)
        ·
          refine ⟨44695681534569828472539011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29797121023046552315026007 44695681534569828472539011)
          ·
            refine ⟨67043522301854742708808517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44695681534569828472539011 67043522301854742708808517)
            ·
              refine ⟨12570660431597764257901597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67043522301854742708808517 12570660431597764257901597)
              ·
                refine ⟨4713997661849161596713099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12570660431597764257901597 4713997661849161596713099)
                ·
                  refine ⟨7070996492773742395069649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713997661849161596713099 7070996492773742395069649)
                  ·
                    refine ⟨5303247369580306796302237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7070996492773742395069649 5303247369580306796302237)
                    ·
                      refine ⟨1988717763592615048613339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303247369580306796302237 1988717763592615048613339)
                      ·
                        rfl

theorem cell23_3873014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3873014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873014 prefixEnd_3873014 := by exact prefixLift 3873014
  have htrace : WordTrace (prefixWord ++ tailWord_3873014) baseStart_3873014 baseEnd_3873014 := by
    simpa [prefixWord, tailWord_3873014, baseEnd_3873014] using wordTrace_append hprefix tailTrace_3873014
  have hstable : (prefixWord ++ tailWord_3873014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873014).length < 2 ^ (prefixWord ++ tailWord_3873014).sum := by decide
  have hdescent : baseEnd_3873014 < baseStart_3873014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
