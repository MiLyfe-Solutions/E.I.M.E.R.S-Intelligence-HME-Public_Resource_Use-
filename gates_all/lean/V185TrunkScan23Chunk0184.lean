import V185TrunkScan23Chunk0183

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1089690 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1089690 : Nat := 118140960795 + 1089690 * 2 ^ 59
def prefixEnd_1089690 : Nat := 4983230072969 + 3 ^ 40 * 1089690 * 2
def baseEnd_1089690 : Nat := 559534734397946816563613

theorem tailTrace_1089690 : CollatzResearch.WordTrace tailWord_1089690 prefixEnd_1089690 559534734397946816563613 := by
  unfold tailWord_1089690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936064855561677270148631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26496172948164472720396349 9936064855561677270148631)
  ·
    refine ⟨14904097283342515905222947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9936064855561677270148631 14904097283342515905222947)
    ·
      refine ⟨22356145925013773857834421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14904097283342515905222947 22356145925013773857834421)
      ·
        refine ⟨2095888680470041299171977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22356145925013773857834421 2095888680470041299171977)
        ·
          refine ⟨1571916510352530974378983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095888680470041299171977 1571916510352530974378983)
          ·
            refine ⟨2357874765528796461568475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571916510352530974378983 2357874765528796461568475)
            ·
              refine ⟨3536812148293194692352713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357874765528796461568475 3536812148293194692352713)
              ·
                refine ⟨2652609111219896019264535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536812148293194692352713 2652609111219896019264535)
                ·
                  refine ⟨3978913666829844028896803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652609111219896019264535 3978913666829844028896803)
                  ·
                    refine ⟨5968370500244766043345205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3978913666829844028896803 5968370500244766043345205)
                    ·
                      refine ⟨559534734397946816563613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5968370500244766043345205 559534734397946816563613)
                      ·
                        rfl

theorem cell23_1089690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1089690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089690 prefixEnd_1089690 := by exact prefixLift 1089690
  have htrace : WordTrace (prefixWord ++ tailWord_1089690) baseStart_1089690 baseEnd_1089690 := by
    simpa [prefixWord, tailWord_1089690, baseEnd_1089690] using wordTrace_append hprefix tailTrace_1089690
  have hstable : (prefixWord ++ tailWord_1089690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089690).length < 2 ^ (prefixWord ++ tailWord_1089690).sum := by decide
  have hdescent : baseEnd_1089690 < baseStart_1089690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089697 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1089697 : Nat := 118140960795 + 1089697 * 2 ^ 59
def prefixEnd_1089697 : Nat := 4983230072969 + 3 ^ 40 * 1089697 * 2
def baseEnd_1089697 : Nat := 186512776254176096392027

theorem tailTrace_1089697 : CollatzResearch.WordTrace tailWord_1089697 prefixEnd_1089697 186512776254176096392027 := by
  unfold tailWord_1089697
  simp only [CollatzResearch.WordTrace]
  refine ⟨39744514733221349276099345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26496343155480899517399563 39744514733221349276099345)
  ·
    refine ⟨29808386049916011957074509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39744514733221349276099345 29808386049916011957074509)
    ·
      refine ⟨11178144768718504483902941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29808386049916011957074509 11178144768718504483902941)
      ·
        refine ⟨4191804288269439181463603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11178144768718504483902941 4191804288269439181463603)
        ·
          refine ⟨6287706432404158772195405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191804288269439181463603 6287706432404158772195405)
          ·
            refine ⟨2357889912151559539573277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6287706432404158772195405 2357889912151559539573277)
            ·
              refine ⟨884208717056834827339979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357889912151559539573277 884208717056834827339979)
              ·
                refine ⟨1326313075585252241009969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884208717056834827339979 1326313075585252241009969)
                ·
                  refine ⟨994734806688939180757477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326313075585252241009969 994734806688939180757477)
                  ·
                    refine ⟨186512776254176096392027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 994734806688939180757477 186512776254176096392027)
                    ·
                      rfl

theorem cell23_1089697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1089697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089697 prefixEnd_1089697 := by exact prefixLift 1089697
  have htrace : WordTrace (prefixWord ++ tailWord_1089697) baseStart_1089697 baseEnd_1089697 := by
    simpa [prefixWord, tailWord_1089697, baseEnd_1089697] using wordTrace_append hprefix tailTrace_1089697
  have hstable : (prefixWord ++ tailWord_1089697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089697).length < 2 ^ (prefixWord ++ tailWord_1089697).sum := by decide
  have hdescent : baseEnd_1089697 < baseStart_1089697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089760 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2]
def baseStart_1089760 : Nat := 118140960795 + 1089760 * 2 ^ 59
def prefixEnd_1089760 : Nat := 4983230072969 + 3 ^ 40 * 1089760 * 2
def baseEnd_1089760 : Nat := 559570678043761542688291

theorem tailTrace_1089760 : CollatzResearch.WordTrace tailWord_1089760 prefixEnd_1089760 559570678043761542688291 := by
  unfold tailWord_1089760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19873406265996555517821367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26497875021328740690428489 19873406265996555517821367)
  ·
    refine ⟨29810109398994833276732051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19873406265996555517821367 29810109398994833276732051)
    ·
      refine ⟨44715164098492249915098077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29810109398994833276732051 44715164098492249915098077)
      ·
        refine ⟨16768186536934593718161779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44715164098492249915098077 16768186536934593718161779)
        ·
          refine ⟨25152279805401890577242669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16768186536934593718161779 25152279805401890577242669)
          ·
            refine ⟨9432104927025708966466001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25152279805401890577242669 9432104927025708966466001)
            ·
              refine ⟨7074078695269281724849501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9432104927025708966466001 7074078695269281724849501)
              ·
                refine ⟨2652779510725980646818563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7074078695269281724849501 2652779510725980646818563)
                ·
                  refine ⟨3979169266088970970227845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652779510725980646818563 3979169266088970970227845)
                  ·
                    refine ⟨746094237391682056917721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979169266088970970227845 746094237391682056917721)
                    ·
                      refine ⟨559570678043761542688291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746094237391682056917721 559570678043761542688291)
                      ·
                        rfl

theorem cell23_1089760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_1089760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089760 prefixEnd_1089760 := by exact prefixLift 1089760
  have htrace : WordTrace (prefixWord ++ tailWord_1089760) baseStart_1089760 baseEnd_1089760 := by
    simpa [prefixWord, tailWord_1089760, baseEnd_1089760] using wordTrace_append hprefix tailTrace_1089760
  have hstable : (prefixWord ++ tailWord_1089760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089760).length < 2 ^ (prefixWord ++ tailWord_1089760).sum := by decide
  have hdescent : baseEnd_1089760 < baseStart_1089760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089790 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1089790 : Nat := 118140960795 + 1089790 * 2 ^ 59
def prefixEnd_1089790 : Nat := 4983230072969 + 3 ^ 40 * 1089790 * 2
def baseEnd_1089790 : Nat := 559586082463396425313153

theorem tailTrace_1089790 : CollatzResearch.WordTrace tailWord_1089790 prefixEnd_1089790 559586082463396425313153 := by
  unfold tailWord_1089790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968488340235553269904353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26498604481256284106156549 4968488340235553269904353)
  ·
    refine ⟨3726366255176664952428265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4968488340235553269904353 3726366255176664952428265)
    ·
      refine ⟨2794774691382498714321199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3726366255176664952428265 2794774691382498714321199)
      ·
        refine ⟨4192162037073748071481799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794774691382498714321199 4192162037073748071481799)
        ·
          refine ⟨6288243055610622107222699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192162037073748071481799 6288243055610622107222699)
          ·
            refine ⟨9432364583415933160834049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288243055610622107222699 9432364583415933160834049)
            ·
              refine ⟨7074273437561949870625537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9432364583415933160834049 7074273437561949870625537)
              ·
                refine ⟨5305705078171462402969153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7074273437561949870625537 5305705078171462402969153)
                ·
                  refine ⟨3979278808628596802226865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5305705078171462402969153 3979278808628596802226865)
                  ·
                    refine ⟨2984459106471447601670149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3979278808628596802226865 2984459106471447601670149)
                    ·
                      refine ⟨559586082463396425313153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2984459106471447601670149 559586082463396425313153)
                      ·
                        rfl

theorem cell23_1089790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1089790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089790 prefixEnd_1089790 := by exact prefixLift 1089790
  have htrace : WordTrace (prefixWord ++ tailWord_1089790) baseStart_1089790 baseEnd_1089790 := by
    simpa [prefixWord, tailWord_1089790, baseEnd_1089790] using wordTrace_append hprefix tailTrace_1089790
  have hstable : (prefixWord ++ tailWord_1089790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089790).length < 2 ^ (prefixWord ++ tailWord_1089790).sum := by decide
  have hdescent : baseEnd_1089790 < baseStart_1089790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089813 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1089813 : Nat := 118140960795 + 1089813 * 2 ^ 59
def prefixEnd_1089813 : Nat := 4983230072969 + 3 ^ 40 * 1089813 * 2
def baseEnd_1089813 : Nat := 186532630839483278441849

theorem tailTrace_1089813 : CollatzResearch.WordTrace tailWord_1089813 prefixEnd_1089813 186532630839483278441849 := by
  unfold tailWord_1089813
  simp only [CollatzResearch.WordTrace]
  refine ⟨39748745600801101087322093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26499163733867400724881395 39748745600801101087322093)
  ·
    refine ⟨14905779600300412907745785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39748745600801101087322093 14905779600300412907745785)
    ·
      refine ⟨11179334700225309680809339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14905779600300412907745785 11179334700225309680809339)
      ·
        refine ⟨16769002050337964521214009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179334700225309680809339 16769002050337964521214009)
        ·
          refine ⟨12576751537753473390910507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16769002050337964521214009 12576751537753473390910507)
          ·
            refine ⟨18865127306630210086365761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576751537753473390910507 18865127306630210086365761)
            ·
              refine ⟨14148845479972657564774321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18865127306630210086365761 14148845479972657564774321)
              ·
                refine ⟨10611634109979493173580741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14148845479972657564774321 10611634109979493173580741)
                ·
                  refine ⟨1989681395621154970046389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10611634109979493173580741 1989681395621154970046389)
                  ·
                    refine ⟨186532630839483278441849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1989681395621154970046389 186532630839483278441849)
                    ·
                      rfl

theorem cell23_1089813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1089813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089813 prefixEnd_1089813 := by exact prefixLift 1089813
  have htrace : WordTrace (prefixWord ++ tailWord_1089813) baseStart_1089813 baseEnd_1089813 := by
    simpa [prefixWord, tailWord_1089813, baseEnd_1089813] using wordTrace_append hprefix tailTrace_1089813
  have hstable : (prefixWord ++ tailWord_1089813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089813).length < 2 ^ (prefixWord ++ tailWord_1089813).sum := by decide
  have hdescent : baseEnd_1089813 < baseStart_1089813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089820 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1089820 : Nat := 118140960795 + 1089820 * 2 ^ 59
def prefixEnd_1089820 : Nat := 4983230072969 + 3 ^ 40 * 1089820 * 2
def baseEnd_1089820 : Nat := 559601486883031307938015

theorem tailTrace_1089820 : CollatzResearch.WordTrace tailWord_1089820 prefixEnd_1089820 559601486883031307938015 := by
  unfold tailWord_1089820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19874500455887870641413457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26499333941183827521884609 19874500455887870641413457)
  ·
    refine ⟨14905875341915902981060093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19874500455887870641413457 14905875341915902981060093)
    ·
      refine ⟨5589703253218463617897535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14905875341915902981060093 5589703253218463617897535)
      ·
        refine ⟨8384554879827695426846303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589703253218463617897535 8384554879827695426846303)
        ·
          refine ⟨12576832319741543140269455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384554879827695426846303 12576832319741543140269455)
          ·
            refine ⟨18865248479612314710404183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576832319741543140269455 18865248479612314710404183)
            ·
              refine ⟨28297872719418472065606275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18865248479612314710404183 28297872719418472065606275)
              ·
                refine ⟨42446809079127708098409413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28297872719418472065606275 42446809079127708098409413)
                ·
                  refine ⟨7958776702336445268451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42446809079127708098409413 7958776702336445268451765)
                  ·
                    refine ⟨746135315844041743917353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7958776702336445268451765 746135315844041743917353)
                    ·
                      refine ⟨559601486883031307938015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746135315844041743917353 559601486883031307938015)
                      ·
                        rfl

theorem cell23_1089820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1089820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089820 prefixEnd_1089820 := by exact prefixLift 1089820
  have htrace : WordTrace (prefixWord ++ tailWord_1089820) baseStart_1089820 baseEnd_1089820 := by
    simpa [prefixWord, tailWord_1089820, baseEnd_1089820] using wordTrace_append hprefix tailTrace_1089820
  have hstable : (prefixWord ++ tailWord_1089820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089820).length < 2 ^ (prefixWord ++ tailWord_1089820).sum := by decide
  have hdescent : baseEnd_1089820 < baseStart_1089820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089834 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_1089834 : Nat := 118140960795 + 1089834 * 2 ^ 59
def prefixEnd_1089834 : Nat := 4983230072969 + 3 ^ 40 * 1089834 * 2
def baseEnd_1089834 : Nat := 62178741734688250351439

theorem tailTrace_1089834 : CollatzResearch.WordTrace tailWord_1089834 prefixEnd_1089834 62178741734688250351439 := by
  unfold tailWord_1089834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937377883431255418459139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26499674355816681115891037 9937377883431255418459139)
  ·
    refine ⟨14906066825146883127688709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9937377883431255418459139 14906066825146883127688709)
    ·
      refine ⟨2794887529715040586441633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14906066825146883127688709 2794887529715040586441633)
      ·
        refine ⟨2096165647286280439831225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2794887529715040586441633 2096165647286280439831225)
        ·
          refine ⟨1572124235464710329873419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2096165647286280439831225 1572124235464710329873419)
          ·
            refine ⟨2358186353197065494810129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572124235464710329873419 2358186353197065494810129)
            ·
              refine ⟨1768639764897799121107597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2358186353197065494810129 1768639764897799121107597)
              ·
                refine ⟨663239911836674670415349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1768639764897799121107597 663239911836674670415349)
                ·
                  refine ⟨62178741734688250351439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663239911836674670415349 62178741734688250351439)
                  ·
                    rfl

theorem cell23_1089834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_1089834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089834 prefixEnd_1089834 := by exact prefixLift 1089834
  have htrace : WordTrace (prefixWord ++ tailWord_1089834) baseStart_1089834 baseEnd_1089834 := by
    simpa [prefixWord, tailWord_1089834, baseEnd_1089834] using wordTrace_append hprefix tailTrace_1089834
  have hstable : (prefixWord ++ tailWord_1089834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089834).length < 2 ^ (prefixWord ++ tailWord_1089834).sum := by decide
  have hdescent : baseEnd_1089834 < baseStart_1089834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089863 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1089863 : Nat := 118140960795 + 1089863 * 2 ^ 59
def prefixEnd_1089863 : Nat := 4983230072969 + 3 ^ 40 * 1089863 * 2
def baseEnd_1089863 : Nat := 559623566551174639700317

theorem tailTrace_1089863 : CollatzResearch.WordTrace tailWord_1089863 prefixEnd_1089863 559623566551174639700317 := by
  unfold tailWord_1089863
  simp only [CollatzResearch.WordTrace]
  refine ⟨39750569250619959626642243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26500379500413306417761495 39750569250619959626642243)
  ·
    refine ⟨59625853875929939439963365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39750569250619959626642243 59625853875929939439963365)
    ·
      refine ⟨11179847601736863644993131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59625853875929939439963365 11179847601736863644993131)
      ·
        refine ⟨16769771402605295467489697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179847601736863644993131 16769771402605295467489697)
        ·
          refine ⟨12577328551953971600617273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16769771402605295467489697 12577328551953971600617273)
          ·
            refine ⟨9432996413965478700462955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12577328551953971600617273 9432996413965478700462955)
            ·
              refine ⟨14149494620948218050694433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432996413965478700462955 14149494620948218050694433)
              ·
                refine ⟨10612120965711163538020825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14149494620948218050694433 10612120965711163538020825)
                ·
                  refine ⟨7959090724283372653515619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10612120965711163538020825 7959090724283372653515619)
                  ·
                    refine ⟨11938636086425058980273429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7959090724283372653515619 11938636086425058980273429)
                    ·
                      refine ⟨559623566551174639700317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11938636086425058980273429 559623566551174639700317)
                      ·
                        rfl

theorem cell23_1089863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1089863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089863 prefixEnd_1089863 := by exact prefixLift 1089863
  have htrace : WordTrace (prefixWord ++ tailWord_1089863) baseStart_1089863 baseEnd_1089863 := by
    simpa [prefixWord, tailWord_1089863, baseEnd_1089863] using wordTrace_append hprefix tailTrace_1089863
  have hstable : (prefixWord ++ tailWord_1089863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089863).length < 2 ^ (prefixWord ++ tailWord_1089863).sum := by decide
  have hdescent : baseEnd_1089863 < baseStart_1089863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089870 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_1089870 : Nat := 118140960795 + 1089870 * 2 ^ 59
def prefixEnd_1089870 : Nat := 4983230072969 + 3 ^ 40 * 1089870 * 2
def baseEnd_1089870 : Nat := 559627160915756112312785

theorem tailTrace_1089870 : CollatzResearch.WordTrace tailWord_1089870 prefixEnd_1089870 559627160915756112312785 := by
  unfold tailWord_1089870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968853070199324977768383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26500549707729733214764709 4968853070199324977768383)
  ·
    refine ⟨7453279605298987466652575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4968853070199324977768383 7453279605298987466652575)
    ·
      refine ⟨11179919407948481199978863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453279605298987466652575 11179919407948481199978863)
      ·
        refine ⟨16769879111922721799968295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179919407948481199978863 16769879111922721799968295)
        ·
          refine ⟨25154818667884082699952443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16769879111922721799968295 25154818667884082699952443)
          ·
            refine ⟨37732228001826124049928665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25154818667884082699952443 37732228001826124049928665)
            ·
              refine ⟨28299171001369593037446499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37732228001826124049928665 28299171001369593037446499)
              ·
                refine ⟨42448756502054389556169749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28299171001369593037446499 42448756502054389556169749)
                ·
                  refine ⟨1989785461033799510445457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42448756502054389556169749 1989785461033799510445457)
                  ·
                    refine ⟨1492339095775349632834093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1989785461033799510445457 1492339095775349632834093)
                    ·
                      refine ⟨559627160915756112312785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492339095775349632834093 559627160915756112312785)
                      ·
                        rfl

theorem cell23_1089870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_1089870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089870 prefixEnd_1089870 := by exact prefixLift 1089870
  have htrace : WordTrace (prefixWord ++ tailWord_1089870) baseStart_1089870 baseEnd_1089870 := by
    simpa [prefixWord, tailWord_1089870, baseEnd_1089870] using wordTrace_append hprefix tailTrace_1089870
  have hstable : (prefixWord ++ tailWord_1089870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089870).length < 2 ^ (prefixWord ++ tailWord_1089870).sum := by decide
  have hdescent : baseEnd_1089870 < baseStart_1089870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089890 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1089890 : Nat := 118140960795 + 1089890 * 2 ^ 59
def prefixEnd_1089890 : Nat := 4983230072969 + 3 ^ 40 * 1089890 * 2
def baseEnd_1089890 : Nat := 62181936725427337118077

theorem tailTrace_1089890 : CollatzResearch.WordTrace tailWord_1089890 prefixEnd_1089890 62181936725427337118077 := by
  unfold tailWord_1089890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937888505380535809468781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26501036014348095491916749 9937888505380535809468781)
  ·
    refine ⟨3726708189517700928550793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9937888505380535809468781 3726708189517700928550793)
    ·
      refine ⟨2795031142138275696413095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3726708189517700928550793 2795031142138275696413095)
      ·
        refine ⟨4192546713207413544619643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795031142138275696413095 4192546713207413544619643)
        ·
          refine ⟨6288820069811120316929465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192546713207413544619643 6288820069811120316929465)
          ·
            refine ⟨4716615052358340237697099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288820069811120316929465 4716615052358340237697099)
            ·
              refine ⟨7074922578537510356545649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716615052358340237697099 7074922578537510356545649)
              ·
                refine ⟨5306191933903132767409237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7074922578537510356545649 5306191933903132767409237)
                ·
                  refine ⟨62181936725427337118077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5306191933903132767409237 62181936725427337118077)
                  ·
                    rfl

theorem cell23_1089890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1089890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089890 prefixEnd_1089890 := by exact prefixLift 1089890
  have htrace : WordTrace (prefixWord ++ tailWord_1089890) baseStart_1089890 baseEnd_1089890 := by
    simpa [prefixWord, tailWord_1089890, baseEnd_1089890] using wordTrace_append hprefix tailTrace_1089890
  have hstable : (prefixWord ++ tailWord_1089890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089890).length < 2 ^ (prefixWord ++ tailWord_1089890).sum := by decide
  have hdescent : baseEnd_1089890 < baseStart_1089890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089913 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1089913 : Nat := 118140960795 + 1089913 * 2 ^ 59
def prefixEnd_1089913 : Nat := 4983230072969 + 3 ^ 40 * 1089913 * 2
def baseEnd_1089913 : Nat := 559649240583899444075087

theorem tailTrace_1089913 : CollatzResearch.WordTrace tailWord_1089913 prefixEnd_1089913 559649240583899444075087 := by
  unfold tailWord_1089913
  simp only [CollatzResearch.WordTrace]
  refine ⟨39752392900438818165962393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26501595266959212110641595 39752392900438818165962393)
  ·
    refine ⟨29814294675329113624471795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39752392900438818165962393 29814294675329113624471795)
    ·
      refine ⟨44721442012993670436707693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29814294675329113624471795 44721442012993670436707693)
      ·
        refine ⟨16770540754872626413765385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44721442012993670436707693 16770540754872626413765385)
        ·
          refine ⟨12577905566154469810324039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16770540754872626413765385 12577905566154469810324039)
          ·
            refine ⟨18866858349231704715486059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577905566154469810324039 18866858349231704715486059)
            ·
              refine ⟨28300287523847557073229089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18866858349231704715486059 28300287523847557073229089)
              ·
                refine ⟨21225215642885667804921817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28300287523847557073229089 21225215642885667804921817)
                ·
                  refine ⟨15918911732164250853691363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21225215642885667804921817 15918911732164250853691363)
                  ·
                    refine ⟨23878367598246376280537045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15918911732164250853691363 23878367598246376280537045)
                    ·
                      refine ⟨559649240583899444075087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23878367598246376280537045 559649240583899444075087)
                      ·
                        rfl

theorem cell23_1089913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1089913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089913 prefixEnd_1089913 := by exact prefixLift 1089913
  have htrace : WordTrace (prefixWord ++ tailWord_1089913) baseStart_1089913 baseEnd_1089913 := by
    simpa [prefixWord, tailWord_1089913, baseEnd_1089913] using wordTrace_append hprefix tailTrace_1089913
  have hstable : (prefixWord ++ tailWord_1089913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089913).length < 2 ^ (prefixWord ++ tailWord_1089913).sum := by decide
  have hdescent : baseEnd_1089913 < baseStart_1089913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089927 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_1089927 : Nat := 118140960795 + 1089927 * 2 ^ 59
def prefixEnd_1089927 : Nat := 4983230072969 + 3 ^ 40 * 1089927 * 2
def baseEnd_1089927 : Nat := 559656429313062389300023

theorem tailTrace_1089927 : CollatzResearch.WordTrace tailWord_1089927 prefixEnd_1089927 559656429313062389300023 := by
  unfold tailWord_1089927
  simp only [CollatzResearch.WordTrace]
  refine ⟨39752903522388098556972035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26501935681592065704648023 39752903522388098556972035)
  ·
    refine ⟨59629355283582147835458053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39752903522388098556972035 59629355283582147835458053)
    ·
      refine ⟨11180504115671652719148385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59629355283582147835458053 11180504115671652719148385)
      ·
        refine ⟨8385378086753739539361289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11180504115671652719148385 8385378086753739539361289)
        ·
          refine ⟨6289033565065304654520967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8385378086753739539361289 6289033565065304654520967)
          ·
            refine ⟨9433550347597956981781451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289033565065304654520967 9433550347597956981781451)
            ·
              refine ⟨14150325521396935472672177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9433550347597956981781451 14150325521396935472672177)
              ·
                refine ⟨10612744141047701604504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14150325521396935472672177 10612744141047701604504133)
                ·
                  refine ⟨1989889526446444050844525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10612744141047701604504133 1989889526446444050844525)
                  ·
                    refine ⟨746208572417416519066697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989889526446444050844525 746208572417416519066697)
                    ·
                      refine ⟨559656429313062389300023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746208572417416519066697 559656429313062389300023)
                      ·
                        rfl

theorem cell23_1089927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_1089927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089927 prefixEnd_1089927 := by exact prefixLift 1089927
  have htrace : WordTrace (prefixWord ++ tailWord_1089927) baseStart_1089927 baseEnd_1089927 := by
    simpa [prefixWord, tailWord_1089927, baseEnd_1089927] using wordTrace_append hprefix tailTrace_1089927
  have hstable : (prefixWord ++ tailWord_1089927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089927).length < 2 ^ (prefixWord ++ tailWord_1089927).sum := by decide
  have hdescent : baseEnd_1089927 < baseStart_1089927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089944 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1089944 : Nat := 118140960795 + 1089944 * 2 ^ 59
def prefixEnd_1089944 : Nat := 4983230072969 + 3 ^ 40 * 1089944 * 2
def baseEnd_1089944 : Nat := 559665158484188822787445

theorem tailTrace_1089944 : CollatzResearch.WordTrace tailWord_1089944 prefixEnd_1089944 559665158484188822787445 := by
  unfold tailWord_1089944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19876761781663255230170443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26502349042217673640227257 19876761781663255230170443)
  ·
    refine ⟨29815142672494882845255665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19876761781663255230170443 29815142672494882845255665)
    ·
      refine ⟨22361357004371162133941749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29815142672494882845255665 22361357004371162133941749)
      ·
        refine ⟨2096377219159796450057039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22361357004371162133941749 2096377219159796450057039)
        ·
          refine ⟨3144565828739694675085559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096377219159796450057039 3144565828739694675085559)
          ·
            refine ⟨4716848743109542012628339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144565828739694675085559 4716848743109542012628339)
            ·
              refine ⟨7075273114664313018942509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716848743109542012628339 7075273114664313018942509)
              ·
                refine ⟨2653227417999117382103441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7075273114664313018942509 2653227417999117382103441)
                ·
                  refine ⟨1989920563499338036577581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653227417999117382103441 1989920563499338036577581)
                  ·
                    refine ⟨746220211312251763716593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989920563499338036577581 746220211312251763716593)
                    ·
                      refine ⟨559665158484188822787445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746220211312251763716593 559665158484188822787445)
                      ·
                        rfl

theorem cell23_1089944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1089944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089944 prefixEnd_1089944 := by exact prefixLift 1089944
  have htrace : WordTrace (prefixWord ++ tailWord_1089944) baseStart_1089944 baseEnd_1089944 := by
    simpa [prefixWord, tailWord_1089944, baseEnd_1089944] using wordTrace_append hprefix tailTrace_1089944
  have hstable : (prefixWord ++ tailWord_1089944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089944).length < 2 ^ (prefixWord ++ tailWord_1089944).sum := by decide
  have hdescent : baseEnd_1089944 < baseStart_1089944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089954 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1089954 : Nat := 118140960795 + 1089954 * 2 ^ 59
def prefixEnd_1089954 : Nat := 4983230072969 + 3 ^ 40 * 1089954 * 2
def baseEnd_1089954 : Nat := 186556764430244594554133

theorem tailTrace_1089954 : CollatzResearch.WordTrace tailWord_1089954 prefixEnd_1089954 186556764430244594554133 := by
  unfold tailWord_1089954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938472073322570542051229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26502592195526854778803277 9938472073322570542051229)
  ·
    refine ⟨3726927027495963953269211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9938472073322570542051229 3726927027495963953269211)
    ·
      refine ⟨5590390541243945929903817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726927027495963953269211 5590390541243945929903817)
      ·
        refine ⟨4192792905932959447427863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5590390541243945929903817 4192792905932959447427863)
        ·
          refine ⟨6289189358899439171141795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192792905932959447427863 6289189358899439171141795)
          ·
            refine ⟨9433784038349158756712693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289189358899439171141795 9433784038349158756712693)
            ·
              refine ⟨884417253595233633441815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9433784038349158756712693 884417253595233633441815)
              ·
                refine ⟨1326625880392850450162723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884417253595233633441815 1326625880392850450162723)
                ·
                  refine ⟨1989938820589275675244085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326625880392850450162723 1989938820589275675244085)
                  ·
                    refine ⟨186556764430244594554133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1989938820589275675244085 186556764430244594554133)
                    ·
                      rfl

theorem cell23_1089954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1089954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089954 prefixEnd_1089954 := by exact prefixLift 1089954
  have htrace : WordTrace (prefixWord ++ tailWord_1089954) baseStart_1089954 baseEnd_1089954 := by
    simpa [prefixWord, tailWord_1089954, baseEnd_1089954] using wordTrace_append hprefix tailTrace_1089954
  have hstable : (prefixWord ++ tailWord_1089954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089954).length < 2 ^ (prefixWord ++ tailWord_1089954).sum := by decide
  have hdescent : baseEnd_1089954 < baseStart_1089954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089962 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1089962 : Nat := 118140960795 + 1089962 * 2 ^ 59
def prefixEnd_1089962 : Nat := 4983230072969 + 3 ^ 40 * 1089962 * 2
def baseEnd_1089962 : Nat := 186558133711989917454121

theorem tailTrace_1089962 : CollatzResearch.WordTrace tailWord_1089962 prefixEnd_1089962 186558133711989917454121 := by
  unfold tailWord_1089962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938545019315324883624035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26502786718174199689664093 9938545019315324883624035)
  ·
    refine ⟨14907817528972987325436053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9938545019315324883624035 14907817528972987325436053)
    ·
      refine ⟨698803946670608780879815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14907817528972987325436053 698803946670608780879815)
      ·
        refine ⟨1048205920005913171319723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698803946670608780879815 1048205920005913171319723)
        ·
          refine ⟨1572308880008869756979585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048205920005913171319723 1572308880008869756979585)
          ·
            refine ⟨1179231660006652317734689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572308880008869756979585 1179231660006652317734689)
            ·
              refine ⟨884423745004989238301017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179231660006652317734689 884423745004989238301017)
              ·
                refine ⟨663317808753741928725763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884423745004989238301017 663317808753741928725763)
                ·
                  refine ⟨994976713130612893088645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663317808753741928725763 994976713130612893088645)
                  ·
                    refine ⟨186558133711989917454121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 994976713130612893088645 186558133711989917454121)
                    ·
                      rfl

theorem cell23_1089962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1089962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089962 prefixEnd_1089962 := by exact prefixLift 1089962
  have htrace : WordTrace (prefixWord ++ tailWord_1089962) baseStart_1089962 baseEnd_1089962 := by
    simpa [prefixWord, tailWord_1089962, baseEnd_1089962] using wordTrace_append hprefix tailTrace_1089962
  have hstable : (prefixWord ++ tailWord_1089962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089962).length < 2 ^ (prefixWord ++ tailWord_1089962).sum := by decide
  have hdescent : baseEnd_1089962 < baseStart_1089962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089970 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1089970 : Nat := 118140960795 + 1089970 * 2 ^ 59
def prefixEnd_1089970 : Nat := 4983230072969 + 3 ^ 40 * 1089970 * 2
def baseEnd_1089970 : Nat := 559678508981205721062325

theorem tailTrace_1089970 : CollatzResearch.WordTrace tailWord_1089970 prefixEnd_1089970 559678508981205721062325 := by
  unfold tailWord_1089970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938617965308079225196841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26502981240821544600524909 9938617965308079225196841)
  ·
    refine ⟨7453963473981059418897631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9938617965308079225196841 7453963473981059418897631)
    ·
      refine ⟨11180945210971589128346447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453963473981059418897631 11180945210971589128346447)
      ·
        refine ⟨16771417816457383692519671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11180945210971589128346447 16771417816457383692519671)
        ·
          refine ⟨25157126724686075538779507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16771417816457383692519671 25157126724686075538779507)
          ·
            refine ⟨37735690087029113308169261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25157126724686075538779507 37735690087029113308169261)
            ·
              refine ⟨14150883782635917490563473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37735690087029113308169261 14150883782635917490563473)
              ·
                refine ⟨10613162836976938117922605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14150883782635917490563473 10613162836976938117922605)
                ·
                  refine ⟨3979936063866351794220977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10613162836976938117922605 3979936063866351794220977)
                  ·
                    refine ⟨2984952047899763845665733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3979936063866351794220977 2984952047899763845665733)
                    ·
                      refine ⟨559678508981205721062325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2984952047899763845665733 559678508981205721062325)
                      ·
                        rfl

theorem cell23_1089970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1089970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089970 prefixEnd_1089970 := by exact prefixLift 1089970
  have htrace : WordTrace (prefixWord ++ tailWord_1089970) baseStart_1089970 baseEnd_1089970 := by
    simpa [prefixWord, tailWord_1089970, baseEnd_1089970] using wordTrace_append hprefix tailTrace_1089970
  have hstable : (prefixWord ++ tailWord_1089970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089970).length < 2 ^ (prefixWord ++ tailWord_1089970).sum := by decide
  have hdescent : baseEnd_1089970 < baseStart_1089970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089977 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1089977 : Nat := 118140960795 + 1089977 * 2 ^ 59
def prefixEnd_1089977 : Nat := 4983230072969 + 3 ^ 40 * 1089977 * 2
def baseEnd_1089977 : Nat := 559682103345787193674793

theorem tailTrace_1089977 : CollatzResearch.WordTrace tailWord_1089977 prefixEnd_1089977 559682103345787193674793 := by
  unfold tailWord_1089977
  simp only [CollatzResearch.WordTrace]
  refine ⟨39754727172206957096292185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26503151448137971397528123 39754727172206957096292185)
  ·
    refine ⟨29816045379155217822219139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39754727172206957096292185 29816045379155217822219139)
    ·
      refine ⟨44724068068732826733328709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29816045379155217822219139 44724068068732826733328709)
      ·
        refine ⟨8385762762887405012499133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44724068068732826733328709 8385762762887405012499133)
        ·
          refine ⟨3144661036082776879687175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8385762762887405012499133 3144661036082776879687175)
          ·
            refine ⟨4716991554124165319530763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144661036082776879687175 4716991554124165319530763)
            ·
              refine ⟨7075487331186247979296145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716991554124165319530763 7075487331186247979296145)
              ·
                refine ⟨5306615498389685984472109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7075487331186247979296145 5306615498389685984472109)
                ·
                  refine ⟨1989980811896132244177041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5306615498389685984472109 1989980811896132244177041)
                  ·
                    refine ⟨1492485608922099183132781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1989980811896132244177041 1492485608922099183132781)
                    ·
                      refine ⟨559682103345787193674793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492485608922099183132781 559682103345787193674793)
                      ·
                        rfl

theorem cell23_1089977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1089977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089977 prefixEnd_1089977 := by exact prefixLift 1089977
  have htrace : WordTrace (prefixWord ++ tailWord_1089977) baseStart_1089977 baseEnd_1089977 := by
    simpa [prefixWord, tailWord_1089977, baseEnd_1089977] using wordTrace_append hprefix tailTrace_1089977
  have hstable : (prefixWord ++ tailWord_1089977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089977).length < 2 ^ (prefixWord ++ tailWord_1089977).sum := by decide
  have hdescent : baseEnd_1089977 < baseStart_1089977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090024 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1090024 : Nat := 118140960795 + 1090024 * 2 ^ 59
def prefixEnd_1090024 : Nat := 4983230072969 + 3 ^ 40 * 1090024 * 2
def baseEnd_1090024 : Nat := 559706236936548509787077

theorem tailTrace_1090024 : CollatzResearch.WordTrace tailWord_1090024 prefixEnd_1090024 559706236936548509787077 := by
  unfold tailWord_1090024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878220701518342061626563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26504294268691122748835417 19878220701518342061626563)
  ·
    refine ⟨29817331052277513092439845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19878220701518342061626563 29817331052277513092439845)
    ·
      refine ⟨5590749572302033704832471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29817331052277513092439845 5590749572302033704832471)
      ·
        refine ⟨8386124358453050557248707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590749572302033704832471 8386124358453050557248707)
        ·
          refine ⟨12579186537679575835873061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8386124358453050557248707 12579186537679575835873061)
          ·
            refine ⟨2358597475814920469226199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12579186537679575835873061 2358597475814920469226199)
            ·
              refine ⟨3537896213722380703839299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358597475814920469226199 3537896213722380703839299)
              ·
                refine ⟨5306844320583571055758949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537896213722380703839299 5306844320583571055758949)
                ·
                  refine ⟨995033310109419572954803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5306844320583571055758949 995033310109419572954803)
                  ·
                    refine ⟨1492549965164129359432205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995033310109419572954803 1492549965164129359432205)
                    ·
                      refine ⟨559706236936548509787077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492549965164129359432205 559706236936548509787077)
                      ·
                        rfl

theorem cell23_1090024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1090024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090024 prefixEnd_1090024 := by exact prefixLift 1090024
  have htrace : WordTrace (prefixWord ++ tailWord_1090024) baseStart_1090024 baseEnd_1090024 := by
    simpa [prefixWord, tailWord_1090024, baseEnd_1090024] using wordTrace_append hprefix tailTrace_1090024
  have hstable : (prefixWord ++ tailWord_1090024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090024).length < 2 ^ (prefixWord ++ tailWord_1090024).sum := by decide
  have hdescent : baseEnd_1090024 < baseStart_1090024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090040 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1090040 : Nat := 118140960795 + 1090040 * 2 ^ 59
def prefixEnd_1090040 : Nat := 4983230072969 + 3 ^ 40 * 1090040 * 2
def baseEnd_1090040 : Nat := 186571484209006815729001

theorem tailTrace_1090040 : CollatzResearch.WordTrace tailWord_1090040 prefixEnd_1090040 186571484209006815729001 := by
  unfold tailWord_1090040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878512485489359427917787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26504683313985812570557049 19878512485489359427917787)
  ·
    refine ⟨29817768728234039141876681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19878512485489359427917787 29817768728234039141876681)
    ·
      refine ⟨22363326546175529356407511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29817768728234039141876681 22363326546175529356407511)
      ·
        refine ⟨33544989819263294034611267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22363326546175529356407511 33544989819263294034611267)
        ·
          refine ⟨50317484728894941051916901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33544989819263294034611267 50317484728894941051916901)
          ·
            refine ⟨9434528386667801447234419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50317484728894941051916901 9434528386667801447234419)
            ·
              refine ⟨14151792580001702170851629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9434528386667801447234419 14151792580001702170851629)
              ·
                refine ⟨5306922217500638314069361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14151792580001702170851629 5306922217500638314069361)
                ·
                  refine ⟨3980191663125478735552021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306922217500638314069361 3980191663125478735552021)
                  ·
                    refine ⟨186571484209006815729001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3980191663125478735552021 186571484209006815729001)
                    ·
                      rfl

theorem cell23_1090040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1090040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090040 prefixEnd_1090040 := by exact prefixLift 1090040
  have htrace : WordTrace (prefixWord ++ tailWord_1090040) baseStart_1090040 baseEnd_1090040 := by
    simpa [prefixWord, tailWord_1090040, baseEnd_1090040] using wordTrace_append hprefix tailTrace_1090040
  have hstable : (prefixWord ++ tailWord_1090040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090040).length < 2 ^ (prefixWord ++ tailWord_1090040).sum := by decide
  have hdescent : baseEnd_1090040 < baseStart_1090040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090068 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1090068 : Nat := 118140960795 + 1090068 * 2 ^ 59
def prefixEnd_1090068 : Nat := 4983230072969 + 3 ^ 40 * 1090068 * 2
def baseEnd_1090068 : Nat := 559728830085346337636875

theorem tailTrace_1090068 : CollatzResearch.WordTrace tailWord_1090068 prefixEnd_1090068 559728830085346337636875 := by
  unfold tailWord_1090068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19879023107438639818927429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26505364143251519758569905 19879023107438639818927429)
  ·
    refine ⟨3727316832644744966048893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19879023107438639818927429 3727316832644744966048893)
    ·
      refine ⟨1397743812241779362268335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3727316832644744966048893 1397743812241779362268335)
      ·
        refine ⟨2096615718362669043402503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397743812241779362268335 2096615718362669043402503)
        ·
          refine ⟨3144923577544003565103755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096615718362669043402503 3144923577544003565103755)
          ·
            refine ⟨4717385366316005347655633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144923577544003565103755 4717385366316005347655633)
            ·
              refine ⟨3538039024737004010741725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717385366316005347655633 3538039024737004010741725)
              ·
                refine ⟨1326764634276376504028147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3538039024737004010741725 1326764634276376504028147)
                ·
                  refine ⟨1990146951414564756042221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326764634276376504028147 1990146951414564756042221)
                  ·
                    refine ⟨746305106780461783515833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990146951414564756042221 746305106780461783515833)
                    ·
                      refine ⟨559728830085346337636875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746305106780461783515833 559728830085346337636875)
                      ·
                        rfl

theorem cell23_1090068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1090068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090068 prefixEnd_1090068 := by exact prefixLift 1090068
  have htrace : WordTrace (prefixWord ++ tailWord_1090068) baseStart_1090068 baseEnd_1090068 := by
    simpa [prefixWord, tailWord_1090068, baseEnd_1090068] using wordTrace_append hprefix tailTrace_1090068
  have hstable : (prefixWord ++ tailWord_1090068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090068).length < 2 ^ (prefixWord ++ tailWord_1090068).sum := by decide
  have hdescent : baseEnd_1090068 < baseStart_1090068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090081 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1090081 : Nat := 118140960795 + 1090081 * 2 ^ 59
def prefixEnd_1090081 : Nat := 4983230072969 + 3 ^ 40 * 1090081 * 2
def baseEnd_1090081 : Nat := 559735505333854786774315

theorem tailTrace_1090081 : CollatzResearch.WordTrace tailWord_1090081 prefixEnd_1090081 559735505333854786774315 := by
  unfold tailWord_1090081
  simp only [CollatzResearch.WordTrace]
  refine ⟨39758520363830182858078097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26505680242553455238718731 39758520363830182858078097)
  ·
    refine ⟨29818890272872637143558573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39758520363830182858078097 29818890272872637143558573)
    ·
      refine ⟨11182083852327238928834465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29818890272872637143558573 11182083852327238928834465)
      ·
        refine ⟨8386562889245429196625849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11182083852327238928834465 8386562889245429196625849)
        ·
          refine ⟨6289922166934071897469387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8386562889245429196625849 6289922166934071897469387)
          ·
            refine ⟨9434883250401107846204081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289922166934071897469387 9434883250401107846204081)
            ·
              refine ⟨7076162437800830884653061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9434883250401107846204081 7076162437800830884653061)
              ·
                refine ⟨1326780457087655790872449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7076162437800830884653061 1326780457087655790872449)
                ·
                  refine ⟨995085342815741843154337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326780457087655790872449 995085342815741843154337)
                  ·
                    refine ⟨746314007111806382365753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995085342815741843154337 746314007111806382365753)
                    ·
                      refine ⟨559735505333854786774315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746314007111806382365753 559735505333854786774315)
                      ·
                        rfl

theorem cell23_1090081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1090081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090081 prefixEnd_1090081 := by exact prefixLift 1090081
  have htrace : WordTrace (prefixWord ++ tailWord_1090081) baseStart_1090081 baseEnd_1090081 := by
    simpa [prefixWord, tailWord_1090081, baseEnd_1090081] using wordTrace_append hprefix tailTrace_1090081
  have hstable : (prefixWord ++ tailWord_1090081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090081).length < 2 ^ (prefixWord ++ tailWord_1090081).sum := by decide
  have hdescent : baseEnd_1090081 < baseStart_1090081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090097 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1090097 : Nat := 118140960795 + 1090097 * 2 ^ 59
def prefixEnd_1090097 : Nat := 4983230072969 + 3 ^ 40 * 1090097 * 2
def baseEnd_1090097 : Nat := 559743721024326724174241

theorem tailTrace_1090097 : CollatzResearch.WordTrace tailWord_1090097 prefixEnd_1090097 559743721024326724174241 := by
  unfold tailWord_1090097
  simp only [CollatzResearch.WordTrace]
  refine ⟨39759103931772217590660545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26506069287848145060440363 39759103931772217590660545)
  ·
    refine ⟨29819327948829163192995409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39759103931772217590660545 29819327948829163192995409)
    ·
      refine ⟨22364495961621872394746557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29819327948829163192995409 22364495961621872394746557)
      ·
        refine ⟨8386685985608202148029959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22364495961621872394746557 8386685985608202148029959)
        ·
          refine ⟨12580028978412303222044939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8386685985608202148029959 12580028978412303222044939)
          ·
            refine ⟨18870043467618454833067409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12580028978412303222044939 18870043467618454833067409)
            ·
              refine ⟨14152532600713841124800557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18870043467618454833067409 14152532600713841124800557)
              ·
                refine ⟨5307199725267690421800209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14152532600713841124800557 5307199725267690421800209)
                ·
                  refine ⟨3980399793950767816350157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5307199725267690421800209 3980399793950767816350157)
                  ·
                    refine ⟨1492649922731537931131309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3980399793950767816350157 1492649922731537931131309)
                    ·
                      refine ⟨559743721024326724174241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492649922731537931131309 559743721024326724174241)
                      ·
                        rfl

theorem cell23_1090097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1090097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090097 prefixEnd_1090097 := by exact prefixLift 1090097
  have htrace : WordTrace (prefixWord ++ tailWord_1090097) baseStart_1090097 baseEnd_1090097 := by
    simpa [prefixWord, tailWord_1090097, baseEnd_1090097] using wordTrace_append hprefix tailTrace_1090097
  have hstable : (prefixWord ++ tailWord_1090097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090097).length < 2 ^ (prefixWord ++ tailWord_1090097).sum := by decide
  have hdescent : baseEnd_1090097 < baseStart_1090097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090098 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_1090098 : Nat := 118140960795 + 1090098 * 2 ^ 59
def prefixEnd_1090098 : Nat := 4983230072969 + 3 ^ 40 * 1090098 * 2
def baseEnd_1090098 : Nat := 559744234504981220261737

theorem tailTrace_1090098 : CollatzResearch.WordTrace tailWord_1090098 prefixEnd_1090098 559744234504981220261737 := by
  unfold tailWord_1090098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939785101192148690361737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26506093603179063174297965 9939785101192148690361737)
  ·
    refine ⟨7454838825894111517771303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9939785101192148690361737 7454838825894111517771303)
    ·
      refine ⟨11182258238841167276656955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7454838825894111517771303 11182258238841167276656955)
      ·
        refine ⟨16773387358261750914985433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11182258238841167276656955 16773387358261750914985433)
        ·
          refine ⟨12580040518696313186239075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16773387358261750914985433 12580040518696313186239075)
          ·
            refine ⟨18870060778044469779358613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12580040518696313186239075 18870060778044469779358613)
            ·
              refine ⟨884534098970834520907435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18870060778044469779358613 884534098970834520907435)
              ·
                refine ⟨1326801148456251781361153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884534098970834520907435 1326801148456251781361153)
                ·
                  refine ⟨995100861342188836020865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326801148456251781361153 995100861342188836020865)
                  ·
                    refine ⟨746325646006641627015649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995100861342188836020865 746325646006641627015649)
                    ·
                      refine ⟨559744234504981220261737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746325646006641627015649 559744234504981220261737)
                      ·
                        rfl

theorem cell23_1090098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_1090098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090098 prefixEnd_1090098 := by exact prefixLift 1090098
  have htrace : WordTrace (prefixWord ++ tailWord_1090098) baseStart_1090098 baseEnd_1090098 := by
    simpa [prefixWord, tailWord_1090098, baseEnd_1090098] using wordTrace_append hprefix tailTrace_1090098
  have hstable : (prefixWord ++ tailWord_1090098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090098).length < 2 ^ (prefixWord ++ tailWord_1090098).sum := by decide
  have hdescent : baseEnd_1090098 < baseStart_1090098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090117 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1090117 : Nat := 118140960795 + 1090117 * 2 ^ 59
def prefixEnd_1090117 : Nat := 4983230072969 + 3 ^ 40 * 1090117 * 2
def baseEnd_1090117 : Nat := 186584663545805548641383

theorem tailTrace_1090117 : CollatzResearch.WordTrace tailWord_1090117 prefixEnd_1090117 186584663545805548641383 := by
  unfold tailWord_1090117
  simp only [CollatzResearch.WordTrace]
  refine ⟨39759833391699761006388605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26506555594466507337592403 39759833391699761006388605)
  ·
    refine ⟨14909937521887410377395727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39759833391699761006388605 14909937521887410377395727)
    ·
      refine ⟨22364906282831115566093591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14909937521887410377395727 22364906282831115566093591)
      ·
        refine ⟨33547359424246673349140387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22364906282831115566093591 33547359424246673349140387)
        ·
          refine ⟨50321039136370010023710581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33547359424246673349140387 50321039136370010023710581)
          ·
            refine ⟨4717597419034688439722867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50321039136370010023710581 4717597419034688439722867)
            ·
              refine ⟨7076396128552032659584301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717597419034688439722867 7076396128552032659584301)
              ·
                refine ⟨2653648548207012247344113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7076396128552032659584301 2653648548207012247344113)
                ·
                  refine ⟨1990236411155259185508085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653648548207012247344113 1990236411155259185508085)
                  ·
                    refine ⟨186584663545805548641383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1990236411155259185508085 186584663545805548641383)
                    ·
                      rfl

theorem cell23_1090117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1090117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090117 prefixEnd_1090117 := by exact prefixLift 1090117
  have htrace : WordTrace (prefixWord ++ tailWord_1090117) baseStart_1090117 baseEnd_1090117 := by
    simpa [prefixWord, tailWord_1090117, baseEnd_1090117] using wordTrace_append hprefix tailTrace_1090117
  have hstable : (prefixWord ++ tailWord_1090117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090117).length < 2 ^ (prefixWord ++ tailWord_1090117).sum := by decide
  have hdescent : baseEnd_1090117 < baseStart_1090117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090177 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 8]
def baseStart_1090177 : Nat := 118140960795 + 1090177 * 2 ^ 59
def prefixEnd_1090177 : Nat := 4983230072969 + 3 ^ 40 * 1090177 * 2
def baseEnd_1090177 : Nat := 62198311052965156797097

theorem tailTrace_1090177 : CollatzResearch.WordTrace tailWord_1090177 prefixEnd_1090177 62198311052965156797097 := by
  unfold tailWord_1090177
  simp only [CollatzResearch.WordTrace]
  refine ⟨39762021771482391253572785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26508014514321594169048523 39762021771482391253572785)
  ·
    refine ⟨29821516328611793440179589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39762021771482391253572785 29821516328611793440179589)
    ·
      refine ⟨5591534311614711270033673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29821516328611793440179589 5591534311614711270033673)
      ·
        refine ⟨4193650733711033452525255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5591534311614711270033673 4193650733711033452525255)
        ·
          refine ⟨6290476100566550178787883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193650733711033452525255 6290476100566550178787883)
          ·
            refine ⟨9435714150849825268181825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290476100566550178787883 9435714150849825268181825)
            ·
              refine ⟨7076785613137368951136369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9435714150849825268181825 7076785613137368951136369)
              ·
                refine ⟨5307589209853026713352277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7076785613137368951136369 5307589209853026713352277)
                ·
                  refine ⟨62198311052965156797097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5307589209853026713352277 62198311052965156797097)
                  ·
                    rfl

theorem cell23_1090177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_1090177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090177 prefixEnd_1090177 := by exact prefixLift 1090177
  have htrace : WordTrace (prefixWord ++ tailWord_1090177) baseStart_1090177 baseEnd_1090177 := by
    simpa [prefixWord, tailWord_1090177, baseEnd_1090177] using wordTrace_append hprefix tailTrace_1090177
  have hstable : (prefixWord ++ tailWord_1090177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090177).length < 2 ^ (prefixWord ++ tailWord_1090177).sum := by decide
  have hdescent : baseEnd_1090177 < baseStart_1090177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090181 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1090181 : Nat := 118140960795 + 1090181 * 2 ^ 59
def prefixEnd_1090181 : Nat := 4983230072969 + 3 ^ 40 * 1090181 * 2
def baseEnd_1090181 : Nat := 186595617799768131841285

theorem tailTrace_1090181 : CollatzResearch.WordTrace tailWord_1090181 prefixEnd_1090181 186595617799768131841285 := by
  unfold tailWord_1090181
  simp only [CollatzResearch.WordTrace]
  refine ⟨39762167663467899936718397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26508111775645266624478931 39762167663467899936718397)
  ·
    refine ⟨14910812873800462476269399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39762167663467899936718397 14910812873800462476269399)
    ·
      refine ⟨22366219310700693714404099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14910812873800462476269399 22366219310700693714404099)
      ·
        refine ⟨33549328966051040571606149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22366219310700693714404099 33549328966051040571606149)
        ·
          refine ⟨6290499181134570107176153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33549328966051040571606149 6290499181134570107176153)
          ·
            refine ⟨4717874385850927580382115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6290499181134570107176153 4717874385850927580382115)
            ·
              refine ⟨7076811578776391370573173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717874385850927580382115 7076811578776391370573173)
              ·
                refine ⟨663451085510286690991235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7076811578776391370573173 663451085510286690991235)
                ·
                  refine ⟨995176628265430036486853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663451085510286690991235 995176628265430036486853)
                  ·
                    refine ⟨186595617799768131841285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995176628265430036486853 186595617799768131841285)
                    ·
                      rfl

theorem cell23_1090181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1090181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090181 prefixEnd_1090181 := by exact prefixLift 1090181
  have htrace : WordTrace (prefixWord ++ tailWord_1090181) baseStart_1090181 baseEnd_1090181 := by
    simpa [prefixWord, tailWord_1090181, baseEnd_1090181] using wordTrace_append hprefix tailTrace_1090181
  have hstable : (prefixWord ++ tailWord_1090181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090181).length < 2 ^ (prefixWord ++ tailWord_1090181).sum := by decide
  have hdescent : baseEnd_1090181 < baseStart_1090181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090194 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_1090194 : Nat := 118140960795 + 1090194 * 2 ^ 59
def prefixEnd_1090194 : Nat := 4983230072969 + 3 ^ 40 * 1090194 * 2
def baseEnd_1090194 : Nat := 62199280960868093851255

theorem tailTrace_1090194 : CollatzResearch.WordTrace tailWord_1090194 prefixEnd_1090194 62199280960868093851255 := by
  unfold tailWord_1090194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940660453105200789235409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26508427874947202104627757 9940660453105200789235409)
  ·
    refine ⟨7455495339828900591926557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9940660453105200789235409 7455495339828900591926557)
    ·
      refine ⟨2795810752435837721972459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7455495339828900591926557 2795810752435837721972459)
      ·
        refine ⟨4193716128653756582958689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795810752435837721972459 4193716128653756582958689)
        ·
          refine ⟨3145287096490317437219017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4193716128653756582958689 3145287096490317437219017)
          ·
            refine ⟨2358965322367738077914263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3145287096490317437219017 2358965322367738077914263)
            ·
              refine ⟨3538447983551607116871395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358965322367738077914263 3538447983551607116871395)
              ·
                refine ⟨5307671975327410675307093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538447983551607116871395 5307671975327410675307093)
                ·
                  refine ⟨62199280960868093851255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5307671975327410675307093 62199280960868093851255)
                  ·
                    rfl

theorem cell23_1090194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_1090194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090194 prefixEnd_1090194 := by exact prefixLift 1090194
  have htrace : WordTrace (prefixWord ++ tailWord_1090194) baseStart_1090194 baseEnd_1090194 := by
    simpa [prefixWord, tailWord_1090194, baseEnd_1090194] using wordTrace_append hprefix tailTrace_1090194
  have hstable : (prefixWord ++ tailWord_1090194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090194).length < 2 ^ (prefixWord ++ tailWord_1090194).sum := by decide
  have hdescent : baseEnd_1090194 < baseStart_1090194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090257 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_1090257 : Nat := 118140960795 + 1090257 * 2 ^ 59
def prefixEnd_1090257 : Nat := 4983230072969 + 3 ^ 40 * 1090257 * 2
def baseEnd_1090257 : Nat := 559825877929046098173505

theorem tailTrace_1090257 : CollatzResearch.WordTrace tailWord_1090257 prefixEnd_1090257 559825877929046098173505 := by
  unfold tailWord_1090257
  simp only [CollatzResearch.WordTrace]
  refine ⟨39764939611192564916485025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26509959740795043277656683 39764939611192564916485025)
  ·
    refine ⟨29823704708394423687363769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39764939611192564916485025 29823704708394423687363769)
    ·
      refine ⟨22367778531295817765522827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29823704708394423687363769 22367778531295817765522827)
      ·
        refine ⟨33551667796943726648284241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22367778531295817765522827 33551667796943726648284241)
        ·
          refine ⟨25163750847707794986213181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33551667796943726648284241 25163750847707794986213181)
          ·
            refine ⟨9436406567890423119829943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25163750847707794986213181 9436406567890423119829943)
            ·
              refine ⟨14154609851835634679744915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9436406567890423119829943 14154609851835634679744915)
              ·
                refine ⟨21231914777753452019617373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154609851835634679744915 21231914777753452019617373)
                ·
                  refine ⟨7961968041657544507356515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21231914777753452019617373 7961968041657544507356515)
                  ·
                    refine ⟨11942952062486316761034773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7961968041657544507356515 11942952062486316761034773)
                    ·
                      refine ⟨559825877929046098173505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11942952062486316761034773 559825877929046098173505)
                      ·
                        rfl

theorem cell23_1090257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_1090257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090257 prefixEnd_1090257 := by exact prefixLift 1090257
  have htrace : WordTrace (prefixWord ++ tailWord_1090257) baseStart_1090257 baseEnd_1090257 := by
    simpa [prefixWord, tailWord_1090257, baseEnd_1090257] using wordTrace_append hprefix tailTrace_1090257
  have hstable : (prefixWord ++ tailWord_1090257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090257).length < 2 ^ (prefixWord ++ tailWord_1090257).sum := by decide
  have hdescent : baseEnd_1090257 < baseStart_1090257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090264 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1090264 : Nat := 118140960795 + 1090264 * 2 ^ 59
def prefixEnd_1090264 : Nat := 4983230072969 + 3 ^ 40 * 1090264 * 2
def baseEnd_1090264 : Nat := 559829472293627570785973

theorem tailTrace_1090264 : CollatzResearch.WordTrace tailWord_1090264 prefixEnd_1090264 559829472293627570785973 := by
  unfold tailWord_1090264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19882597461083602555994923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26510129948111470074659897 19882597461083602555994923)
  ·
    refine ⟨29823896191625403833992385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19882597461083602555994923 29823896191625403833992385)
    ·
      refine ⟨22367922143719052875494289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29823896191625403833992385 22367922143719052875494289)
      ·
        refine ⟨16775941607789289656620717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22367922143719052875494289 16775941607789289656620717)
        ·
          refine ⟨6290978102920983621232769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16775941607789289656620717 6290978102920983621232769)
          ·
            refine ⟨4718233577190737715924577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6290978102920983621232769 4718233577190737715924577)
            ·
              refine ⟨3538675182893053286943433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718233577190737715924577 3538675182893053286943433)
              ·
                refine ⟨2654006387169789965207575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538675182893053286943433 2654006387169789965207575)
                ·
                  refine ⟨3981009580754684947811363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654006387169789965207575 3981009580754684947811363)
                  ·
                    refine ⟨5971514371132027421717045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981009580754684947811363 5971514371132027421717045)
                    ·
                      refine ⟨559829472293627570785973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5971514371132027421717045 559829472293627570785973)
                      ·
                        rfl

theorem cell23_1090264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1090264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090264 prefixEnd_1090264 := by exact prefixLift 1090264
  have htrace : WordTrace (prefixWord ++ tailWord_1090264) baseStart_1090264 baseEnd_1090264 := by
    simpa [prefixWord, tailWord_1090264, baseEnd_1090264] using wordTrace_append hprefix tailTrace_1090264
  have hstable : (prefixWord ++ tailWord_1090264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090264).length < 2 ^ (prefixWord ++ tailWord_1090264).sum := by decide
  have hdescent : baseEnd_1090264 < baseStart_1090264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090271 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 2, 4]
def baseStart_1090271 : Nat := 118140960795 + 1090271 * 2 ^ 59
def prefixEnd_1090271 : Nat := 4983230072969 + 3 ^ 40 * 1090271 * 2
def baseEnd_1090271 : Nat := 186611022219403014466147

theorem tailTrace_1090271 : CollatzResearch.WordTrace tailWord_1090271 prefixEnd_1090271 186611022219403014466147 := by
  unfold tailWord_1090271
  simp only [CollatzResearch.WordTrace]
  refine ⟨39765450233141845307494667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26510300155427896871663111 39765450233141845307494667)
  ·
    refine ⟨59648175349712767961242001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39765450233141845307494667 59648175349712767961242001)
    ·
      refine ⟨44736131512284575970931501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59648175349712767961242001 44736131512284575970931501)
      ·
        refine ⟨16776049317106715989099313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44736131512284575970931501 16776049317106715989099313)
        ·
          refine ⟨12582036987830036991824485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16776049317106715989099313 12582036987830036991824485)
          ·
            refine ⟨2359131935218131935967091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12582036987830036991824485 2359131935218131935967091)
            ·
              refine ⟨3538697902827197903950637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359131935218131935967091 3538697902827197903950637)
              ·
                refine ⟨1327011713560199213981489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3538697902827197903950637 1327011713560199213981489)
                ·
                  refine ⟨995258785170149410486117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327011713560199213981489 995258785170149410486117)
                  ·
                    refine ⟨186611022219403014466147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995258785170149410486117 186611022219403014466147)
                    ·
                      rfl

theorem cell23_1090271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_1090271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090271 prefixEnd_1090271 := by exact prefixLift 1090271
  have htrace : WordTrace (prefixWord ++ tailWord_1090271) baseStart_1090271 baseEnd_1090271 := by
    simpa [prefixWord, tailWord_1090271, baseEnd_1090271] using wordTrace_append hprefix tailTrace_1090271
  have hstable : (prefixWord ++ tailWord_1090271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090271).length < 2 ^ (prefixWord ++ tailWord_1090271).sum := by decide
  have hdescent : baseEnd_1090271 < baseStart_1090271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090281 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_1090281 : Nat := 118140960795 + 1090281 * 2 ^ 59
def prefixEnd_1090281 : Nat := 4983230072969 + 3 ^ 40 * 1090281 * 2
def baseEnd_1090281 : Nat := 559838201464754004273395

theorem tailTrace_1090281 : CollatzResearch.WordTrace tailWord_1090281 prefixEnd_1090281 559838201464754004273395 := by
  unfold tailWord_1090281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39765814963105617015358697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26510543308737078010239131 39765814963105617015358697)
  ·
    refine ⟨29824361222329212761519023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39765814963105617015358697 29824361222329212761519023)
    ·
      refine ⟨44736541833493819142278535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29824361222329212761519023 44736541833493819142278535)
      ·
        refine ⟨67104812750240728713417803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44736541833493819142278535 67104812750240728713417803)
        ·
          refine ⟨100657219125361093070126705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67104812750240728713417803 100657219125361093070126705)
          ·
            refine ⟨75492914344020819802595029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100657219125361093070126705 75492914344020819802595029)
            ·
              refine ⟨1769365179937987964123321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75492914344020819802595029 1769365179937987964123321)
              ·
                refine ⟨1327023884953490973092491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769365179937987964123321 1327023884953490973092491)
                ·
                  refine ⟨1990535827430236459638737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327023884953490973092491 1990535827430236459638737)
                  ·
                    refine ⟨1492901870572677344729053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990535827430236459638737 1492901870572677344729053)
                    ·
                      refine ⟨559838201464754004273395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492901870572677344729053 559838201464754004273395)
                      ·
                        rfl

theorem cell23_1090281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_1090281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090281 prefixEnd_1090281 := by exact prefixLift 1090281
  have htrace : WordTrace (prefixWord ++ tailWord_1090281) baseStart_1090281 baseEnd_1090281 := by
    simpa [prefixWord, tailWord_1090281, baseEnd_1090281] using wordTrace_append hprefix tailTrace_1090281
  have hstable : (prefixWord ++ tailWord_1090281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090281).length < 2 ^ (prefixWord ++ tailWord_1090281).sum := by decide
  have hdescent : baseEnd_1090281 < baseStart_1090281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090292 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1090292 : Nat := 118140960795 + 1090292 * 2 ^ 59
def prefixEnd_1090292 : Nat := 4983230072969 + 3 ^ 40 * 1090292 * 2
def baseEnd_1090292 : Nat := 186614616583984487078615

theorem tailTrace_1090292 : CollatzResearch.WordTrace tailWord_1090292 prefixEnd_1090292 186614616583984487078615 := by
  unfold tailWord_1090292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883108083032882947004565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26510810777377177262672753 19883108083032882947004565)
  ·
    refine ⟨932020691392166388140839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19883108083032882947004565 932020691392166388140839)
    ·
      refine ⟨1398031037088249582211259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932020691392166388140839 1398031037088249582211259)
      ·
        refine ⟨2097046555632374373316889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398031037088249582211259 2097046555632374373316889)
        ·
          refine ⟨1572784916724280779987667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097046555632374373316889 1572784916724280779987667)
          ·
            refine ⟨2359177375086421169981501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572784916724280779987667 2359177375086421169981501)
            ·
              refine ⟨884691515657407938743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2359177375086421169981501 884691515657407938743063)
              ·
                refine ⟨1327037273486111908114595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884691515657407938743063 1327037273486111908114595)
                ·
                  refine ⟨1990555910229167862171893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327037273486111908114595 1990555910229167862171893)
                  ·
                    refine ⟨186614616583984487078615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1990555910229167862171893 186614616583984487078615)
                    ·
                      rfl

theorem cell23_1090292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1090292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090292 prefixEnd_1090292 := by exact prefixLift 1090292
  have htrace : WordTrace (prefixWord ++ tailWord_1090292) baseStart_1090292 baseEnd_1090292 := by
    simpa [prefixWord, tailWord_1090292, baseEnd_1090292] using wordTrace_append hprefix tailTrace_1090292
  have hstable : (prefixWord ++ tailWord_1090292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090292).length < 2 ^ (prefixWord ++ tailWord_1090292).sum := by decide
  have hdescent : baseEnd_1090292 < baseStart_1090292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090297 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_1090297 : Nat := 118140960795 + 1090297 * 2 ^ 59
def prefixEnd_1090297 : Nat := 4983230072969 + 3 ^ 40 * 1090297 * 2
def baseEnd_1090297 : Nat := 186615472385075313891107

theorem tailTrace_1090297 : CollatzResearch.WordTrace tailWord_1090297 prefixEnd_1090297 186615472385075313891107 := by
  unfold tailWord_1090297
  simp only [CollatzResearch.WordTrace]
  refine ⟨39766398531047651747941145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26510932354031767831960763 39766398531047651747941145)
  ·
    refine ⟨29824798898285738810955859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39766398531047651747941145 29824798898285738810955859)
    ·
      refine ⟨44737198347428608216433789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29824798898285738810955859 44737198347428608216433789)
      ·
        refine ⟨16776449380285728081162671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44737198347428608216433789 16776449380285728081162671)
        ·
          refine ⟨25164674070428592121744007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16776449380285728081162671 25164674070428592121744007)
          ·
            refine ⟨37747011105642888182616011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25164674070428592121744007 37747011105642888182616011)
            ·
              refine ⟨56620516658464332273924017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37747011105642888182616011 56620516658464332273924017)
              ·
                refine ⟨42465387493848249205443013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56620516658464332273924017 42465387493848249205443013)
                ·
                  refine ⟨7962260155096546726020565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42465387493848249205443013 7962260155096546726020565)
                  ·
                    refine ⟨186615472385075313891107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7962260155096546726020565 186615472385075313891107)
                    ·
                      rfl

theorem cell23_1090297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_1090297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090297 prefixEnd_1090297 := by exact prefixLift 1090297
  have htrace : WordTrace (prefixWord ++ tailWord_1090297) baseStart_1090297 baseEnd_1090297 := by
    simpa [prefixWord, tailWord_1090297, baseEnd_1090297] using wordTrace_append hprefix tailTrace_1090297
  have hstable : (prefixWord ++ tailWord_1090297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090297).length < 2 ^ (prefixWord ++ tailWord_1090297).sum := by decide
  have hdescent : baseEnd_1090297 < baseStart_1090297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090312 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_1090312 : Nat := 118140960795 + 1090312 * 2 ^ 59
def prefixEnd_1090312 : Nat := 4983230072969 + 3 ^ 40 * 1090312 * 2
def baseEnd_1090312 : Nat := 559854119365043382985753

theorem tailTrace_1090312 : CollatzResearch.WordTrace tailWord_1090312 prefixEnd_1090312 559854119365043382985753 := by
  unfold tailWord_1090312
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883472812996654654868595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26511297083995539539824793 19883472812996654654868595)
  ·
    refine ⟨29825209219494981982302893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883472812996654654868595 29825209219494981982302893)
    ·
      refine ⟨11184453457310618243363585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29825209219494981982302893 11184453457310618243363585)
      ·
        refine ⟨8388340092982963682522689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11184453457310618243363585 8388340092982963682522689)
        ·
          refine ⟨6291255069737222761892017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8388340092982963682522689 6291255069737222761892017)
          ·
            refine ⟨4718441302302917071419013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6291255069737222761892017 4718441302302917071419013)
            ·
              refine ⟨884707744181796950891065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4718441302302917071419013 884707744181796950891065)
              ·
                refine ⟨663530808136347713168299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884707744181796950891065 663530808136347713168299)
                ·
                  refine ⟨995296212204521569752449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663530808136347713168299 995296212204521569752449)
                  ·
                    refine ⟨746472159153391177314337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995296212204521569752449 746472159153391177314337)
                    ·
                      refine ⟨559854119365043382985753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746472159153391177314337 559854119365043382985753)
                      ·
                        rfl

theorem cell23_1090312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_1090312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090312 prefixEnd_1090312 := by exact prefixLift 1090312
  have htrace : WordTrace (prefixWord ++ tailWord_1090312) baseStart_1090312 baseEnd_1090312 := by
    simpa [prefixWord, tailWord_1090312, baseEnd_1090312] using wordTrace_append hprefix tailTrace_1090312
  have hstable : (prefixWord ++ tailWord_1090312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090312).length < 2 ^ (prefixWord ++ tailWord_1090312).sum := by decide
  have hdescent : baseEnd_1090312 < baseStart_1090312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090321 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_1090321 : Nat := 118140960795 + 1090321 * 2 ^ 59
def prefixEnd_1090321 : Nat := 4983230072969 + 3 ^ 40 * 1090321 * 2
def baseEnd_1090321 : Nat := 559858740690933847773211

theorem tailTrace_1090321 : CollatzResearch.WordTrace tailWord_1090321 prefixEnd_1090321 559858740690933847773211 := by
  unfold tailWord_1090321
  simp only [CollatzResearch.WordTrace]
  refine ⟨39767273882960703846814817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26511515921973802564543211 39767273882960703846814817)
  ·
    refine ⟨29825455412220527885111113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39767273882960703846814817 29825455412220527885111113)
    ·
      refine ⟨22369091559165395913833335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29825455412220527885111113 22369091559165395913833335)
      ·
        refine ⟨33553637338748093870750003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22369091559165395913833335 33553637338748093870750003)
        ·
          refine ⟨50330456008122140806125005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33553637338748093870750003 50330456008122140806125005)
          ·
            refine ⟨18873921003045802802296877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50330456008122140806125005 18873921003045802802296877)
            ·
              refine ⟨7077720376142176050861329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18873921003045802802296877 7077720376142176050861329)
              ·
                refine ⟨5308290282106632038145997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7077720376142176050861329 5308290282106632038145997)
                ·
                  refine ⟨1990608855789987014304749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308290282106632038145997 1990608855789987014304749)
                  ·
                    refine ⟨746478320921245130364281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990608855789987014304749 746478320921245130364281)
                    ·
                      refine ⟨559858740690933847773211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746478320921245130364281 559858740690933847773211)
                      ·
                        rfl

theorem cell23_1090321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_1090321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090321 prefixEnd_1090321 := by exact prefixLift 1090321
  have htrace : WordTrace (prefixWord ++ tailWord_1090321) baseStart_1090321 baseEnd_1090321 := by
    simpa [prefixWord, tailWord_1090321, baseEnd_1090321] using wordTrace_append hprefix tailTrace_1090321
  have hstable : (prefixWord ++ tailWord_1090321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090321).length < 2 ^ (prefixWord ++ tailWord_1090321).sum := by decide
  have hdescent : baseEnd_1090321 < baseStart_1090321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090338 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_1090338 : Nat := 118140960795 + 1090338 * 2 ^ 59
def prefixEnd_1090338 : Nat := 4983230072969 + 3 ^ 40 * 1090338 * 2
def baseEnd_1090338 : Nat := 559867469862060281260633

theorem tailTrace_1090338 : CollatzResearch.WordTrace tailWord_1090338 prefixEnd_1090338 559867469862060281260633 := by
  unfold tailWord_1090338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9941973480974778937545917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26511929282599410500122445 9941973480974778937545917)
  ·
    refine ⟨3728240055365542101579719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9941973480974778937545917 3728240055365542101579719)
    ·
      refine ⟨5592360083048313152369579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728240055365542101579719 5592360083048313152369579)
      ·
        refine ⟨8388540124572469728554369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592360083048313152369579 8388540124572469728554369)
        ·
          refine ⟨6291405093429352296415777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8388540124572469728554369 6291405093429352296415777)
          ·
            refine ⟨4718553820072014222311833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6291405093429352296415777 4718553820072014222311833)
            ·
              refine ⟨3538915365054010666733875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718553820072014222311833 3538915365054010666733875)
              ·
                refine ⟨5308373047581016000100813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538915365054010666733875 5308373047581016000100813)
                ·
                  refine ⟨1990639892842881000037805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308373047581016000100813 1990639892842881000037805)
                  ·
                    refine ⟨746489959816080375014177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990639892842881000037805 746489959816080375014177)
                    ·
                      refine ⟨559867469862060281260633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746489959816080375014177 559867469862060281260633)
                      ·
                        rfl

theorem cell23_1090338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_1090338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090338 prefixEnd_1090338 := by exact prefixLift 1090338
  have htrace : WordTrace (prefixWord ++ tailWord_1090338) baseStart_1090338 baseEnd_1090338 := by
    simpa [prefixWord, tailWord_1090338, baseEnd_1090338] using wordTrace_append hprefix tailTrace_1090338
  have hstable : (prefixWord ++ tailWord_1090338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090338).length < 2 ^ (prefixWord ++ tailWord_1090338).sum := by decide
  have hdescent : baseEnd_1090338 < baseStart_1090338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090344 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1090344 : Nat := 118140960795 + 1090344 * 2 ^ 59
def prefixEnd_1090344 : Nat := 4983230072969 + 3 ^ 40 * 1090344 * 2
def baseEnd_1090344 : Nat := 186623516915329085928535

theorem tailTrace_1090344 : CollatzResearch.WordTrace tailWord_1090344 prefixEnd_1090344 186623516915329085928535 := by
  unfold tailWord_1090344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19884056380938689387451043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26512075174584919183268057 19884056380938689387451043)
  ·
    refine ⟨29826084571408034081176565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19884056380938689387451043 29826084571408034081176565)
    ·
      refine ⟨2796195428569503195110303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29826084571408034081176565 2796195428569503195110303)
      ·
        refine ⟨4194293142854254792665455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796195428569503195110303 4194293142854254792665455)
        ·
          refine ⟨6291439714281382188998183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194293142854254792665455 6291439714281382188998183)
          ·
            refine ⟨9437159571422073283497275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291439714281382188998183 9437159571422073283497275)
            ·
              refine ⟨14155739357133109925245913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9437159571422073283497275 14155739357133109925245913)
              ·
                refine ⟨10616804517849832443934435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14155739357133109925245913 10616804517849832443934435)
                ·
                  refine ⟨15925206776774748665901653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10616804517849832443934435 15925206776774748665901653)
                  ·
                    refine ⟨186623516915329085928535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15925206776774748665901653 186623516915329085928535)
                    ·
                      rfl

theorem cell23_1090344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1090344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090344 prefixEnd_1090344 := by exact prefixLift 1090344
  have htrace : WordTrace (prefixWord ++ tailWord_1090344) baseStart_1090344 baseEnd_1090344 := by
    simpa [prefixWord, tailWord_1090344, baseEnd_1090344] using wordTrace_append hprefix tailTrace_1090344
  have hstable : (prefixWord ++ tailWord_1090344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090344).length < 2 ^ (prefixWord ++ tailWord_1090344).sum := by decide
  have hdescent : baseEnd_1090344 < baseStart_1090344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090349 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1090349 : Nat := 118140960795 + 1090349 * 2 ^ 59
def prefixEnd_1090349 : Nat := 4983230072969 + 3 ^ 40 * 1090349 * 2
def baseEnd_1090349 : Nat := 559873118149259738223083

theorem tailTrace_1090349 : CollatzResearch.WordTrace tailWord_1090349 prefixEnd_1090349 559873118149259738223083 := by
  unfold tailWord_1090349
  simp only [CollatzResearch.WordTrace]
  refine ⟨39768295126859264628834101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26512196751239509752556067 39768295126859264628834101)
  ·
    refine ⟨3728277668143056058953197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39768295126859264628834101 3728277668143056058953197)
    ·
      refine ⟨1398104125553646022107449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3728277668143056058953197 1398104125553646022107449)
      ·
        refine ⟨1048578094165234516580587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1398104125553646022107449 1048578094165234516580587)
        ·
          refine ⟨1572867141247851774870881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048578094165234516580587 1572867141247851774870881)
          ·
            refine ⟨1179650355935888831153161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572867141247851774870881 1179650355935888831153161)
            ·
              refine ⟨884737766951916623364871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179650355935888831153161 884737766951916623364871)
              ·
                refine ⟨1327106650427874935047307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884737766951916623364871 1327106650427874935047307)
                ·
                  refine ⟨1990659975641812402570961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327106650427874935047307 1990659975641812402570961)
                  ·
                    refine ⟨1492994981731359301928221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1990659975641812402570961 1492994981731359301928221)
                    ·
                      refine ⟨559873118149259738223083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1492994981731359301928221 559873118149259738223083)
                      ·
                        rfl

theorem cell23_1090349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1090349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090349 prefixEnd_1090349 := by exact prefixLift 1090349
  have htrace : WordTrace (prefixWord ++ tailWord_1090349) baseStart_1090349 baseEnd_1090349 := by
    simpa [prefixWord, tailWord_1090349, baseEnd_1090349] using wordTrace_append hprefix tailTrace_1090349
  have hstable : (prefixWord ++ tailWord_1090349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090349).length < 2 ^ (prefixWord ++ tailWord_1090349).sum := by decide
  have hdescent : baseEnd_1090349 < baseStart_1090349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090354 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1090354 : Nat := 118140960795 + 1090354 * 2 ^ 59
def prefixEnd_1090354 : Nat := 4983230072969 + 3 ^ 40 * 1090354 * 2
def baseEnd_1090354 : Nat := 559875685552532218660559

theorem tailTrace_1090354 : CollatzResearch.WordTrace tailWord_1090354 prefixEnd_1090354 559875685552532218660559 := by
  unfold tailWord_1090354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9942119372960287620691529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26512318327894100321844077 9942119372960287620691529)
  ·
    refine ⟨7456589529720215715518647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9942119372960287620691529 7456589529720215715518647)
    ·
      refine ⟨11184884294580323573277971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7456589529720215715518647 11184884294580323573277971)
      ·
        refine ⟨16777326441870485359916957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11184884294580323573277971 16777326441870485359916957)
        ·
          refine ⟨6291497415701432009968859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16777326441870485359916957 6291497415701432009968859)
          ·
            refine ⟨9437246123552148014953289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291497415701432009968859 9437246123552148014953289)
            ·
              refine ⟨7077934592664111011214967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9437246123552148014953289 7077934592664111011214967)
              ·
                refine ⟨10616901888996166516822451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077934592664111011214967 10616901888996166516822451)
                ·
                  refine ⟨15925352833494249775233677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10616901888996166516822451 15925352833494249775233677)
                  ·
                    refine ⟨5972007312560343665712629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15925352833494249775233677 5972007312560343665712629)
                    ·
                      refine ⟨559875685552532218660559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5972007312560343665712629 559875685552532218660559)
                      ·
                        rfl

theorem cell23_1090354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1090354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090354 prefixEnd_1090354 := by exact prefixLift 1090354
  have htrace : WordTrace (prefixWord ++ tailWord_1090354) baseStart_1090354 baseEnd_1090354 := by
    simpa [prefixWord, tailWord_1090354, baseEnd_1090354] using wordTrace_append hprefix tailTrace_1090354
  have hstable : (prefixWord ++ tailWord_1090354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090354).length < 2 ^ (prefixWord ++ tailWord_1090354).sum := by decide
  have hdescent : baseEnd_1090354 < baseStart_1090354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090355 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 1, 3, 2]
def baseStart_1090355 : Nat := 118140960795 + 1090355 * 2 ^ 59
def prefixEnd_1090355 : Nat := 4983230072969 + 3 ^ 40 * 1090355 * 2
def baseEnd_1090355 : Nat := 559876199033186714748055

theorem tailTrace_1090355 : CollatzResearch.WordTrace tailWord_1090355 prefixEnd_1090355 559876199033186714748055 := by
  unfold tailWord_1090355
  simp only [CollatzResearch.WordTrace]
  refine ⟨39768513964837527653552519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26512342643225018435701679 39768513964837527653552519)
  ·
    refine ⟨59652770947256291480328779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39768513964837527653552519 59652770947256291480328779)
    ·
      refine ⟨89479156420884437220493169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59652770947256291480328779 89479156420884437220493169)
      ·
        refine ⟨67109367315663327915369877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89479156420884437220493169 67109367315663327915369877)
        ·
          refine ⟨3145751592921718496032963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67109367315663327915369877 3145751592921718496032963)
          ·
            refine ⟨4718627389382577744049445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145751592921718496032963 4718627389382577744049445)
            ·
              refine ⟨884742635509233327009271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4718627389382577744049445 884742635509233327009271)
              ·
                refine ⟨1327113953263849990513907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884742635509233327009271 1327113953263849990513907)
                ·
                  refine ⟨1990670929895774985770861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327113953263849990513907 1990670929895774985770861)
                  ·
                    refine ⟨746501598710915619664073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990670929895774985770861 746501598710915619664073)
                    ·
                      refine ⟨559876199033186714748055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746501598710915619664073 559876199033186714748055)
                      ·
                        rfl

theorem cell23_1090355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 3, 2].length) (baseStart_1090355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090355 prefixEnd_1090355 := by exact prefixLift 1090355
  have htrace : WordTrace (prefixWord ++ tailWord_1090355) baseStart_1090355 baseEnd_1090355 := by
    simpa [prefixWord, tailWord_1090355, baseEnd_1090355] using wordTrace_append hprefix tailTrace_1090355
  have hstable : (prefixWord ++ tailWord_1090355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090355).length < 2 ^ (prefixWord ++ tailWord_1090355).sum := by decide
  have hdescent : baseEnd_1090355 < baseStart_1090355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090362 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_1090362 : Nat := 118140960795 + 1090362 * 2 ^ 59
def prefixEnd_1090362 : Nat := 4983230072969 + 3 ^ 40 * 1090362 * 2
def baseEnd_1090362 : Nat := 559879793397768187360523

theorem tailTrace_1090362 : CollatzResearch.WordTrace tailWord_1090362 prefixEnd_1090362 559879793397768187360523 := by
  unfold tailWord_1090362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9942192318953041962264335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26512512850541445232704893 9942192318953041962264335)
  ·
    refine ⟨14913288478429562943396503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9942192318953041962264335 14913288478429562943396503)
    ·
      refine ⟨22369932717644344415094755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14913288478429562943396503 22369932717644344415094755)
      ·
        refine ⟨33554899076466516622642133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22369932717644344415094755 33554899076466516622642133)
        ·
          refine ⟨786442947104683983343175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33554899076466516622642133 786442947104683983343175)
          ·
            refine ⟨1179664420657025975014763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786442947104683983343175 1179664420657025975014763)
            ·
              refine ⟨1769496630985538962522145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179664420657025975014763 1769496630985538962522145)
              ·
                refine ⟨1327122473239154221891609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769496630985538962522145 1327122473239154221891609)
                ·
                  refine ⟨995341854929365666418707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327122473239154221891609 995341854929365666418707)
                  ·
                    refine ⟨1493012782394048499628061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995341854929365666418707 1493012782394048499628061)
                    ·
                      refine ⟨559879793397768187360523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1493012782394048499628061 559879793397768187360523)
                      ·
                        rfl

theorem cell23_1090362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_1090362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090362 prefixEnd_1090362 := by exact prefixLift 1090362
  have htrace : WordTrace (prefixWord ++ tailWord_1090362) baseStart_1090362 baseEnd_1090362 := by
    simpa [prefixWord, tailWord_1090362, baseEnd_1090362] using wordTrace_append hprefix tailTrace_1090362
  have hstable : (prefixWord ++ tailWord_1090362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090362).length < 2 ^ (prefixWord ++ tailWord_1090362).sum := by decide
  have hdescent : baseEnd_1090362 < baseStart_1090362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090385 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_1090385 : Nat := 118140960795 + 1090385 * 2 ^ 59
def prefixEnd_1090385 : Nat := 4983230072969 + 3 ^ 40 * 1090385 * 2
def baseEnd_1090385 : Nat := 559891603452821597372917

theorem tailTrace_1090385 : CollatzResearch.WordTrace tailWord_1090385 prefixEnd_1090385 559891603452821597372917 := by
  unfold tailWord_1090385
  simp only [CollatzResearch.WordTrace]
  refine ⟨39769608154728842777144609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26513072103152561851429739 39769608154728842777144609)
  ·
    refine ⟨29827206116046632082858457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39769608154728842777144609 29827206116046632082858457)
    ·
      refine ⟨22370404587034974062143843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29827206116046632082858457 22370404587034974062143843)
      ·
        refine ⟨33555606880552461093215765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22370404587034974062143843 33555606880552461093215765)
        ·
          refine ⟨1572919072525896613744489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33555606880552461093215765 1572919072525896613744489)
          ·
            refine ⟨1179689304394422460308367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572919072525896613744489 1179689304394422460308367)
            ·
              refine ⟨1769533956591633690462551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179689304394422460308367 1769533956591633690462551)
              ·
                refine ⟨2654300934887450535693827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769533956591633690462551 2654300934887450535693827)
                ·
                  refine ⟨3981451402331175803540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654300934887450535693827 3981451402331175803540741)
                  ·
                    refine ⟨746522137937095463163889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3981451402331175803540741 746522137937095463163889)
                    ·
                      refine ⟨559891603452821597372917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746522137937095463163889 559891603452821597372917)
                      ·
                        rfl

theorem cell23_1090385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_1090385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090385 prefixEnd_1090385 := by exact prefixLift 1090385
  have htrace : WordTrace (prefixWord ++ tailWord_1090385) baseStart_1090385 baseEnd_1090385 := by
    simpa [prefixWord, tailWord_1090385, baseEnd_1090385] using wordTrace_append hprefix tailTrace_1090385
  have hstable : (prefixWord ++ tailWord_1090385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090385).length < 2 ^ (prefixWord ++ tailWord_1090385).sum := by decide
  have hdescent : baseEnd_1090385 < baseStart_1090385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090408 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 5]
def baseStart_1090408 : Nat := 118140960795 + 1090408 * 2 ^ 59
def prefixEnd_1090408 : Nat := 4983230072969 + 3 ^ 40 * 1090408 * 2
def baseEnd_1090408 : Nat := 62211490389763889709479

theorem tailTrace_1090408 : CollatzResearch.WordTrace tailWord_1090408 prefixEnd_1090408 62211490389763889709479 := by
  unfold tailWord_1090408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885223516822758852615939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26513631355763678470154585 19885223516822758852615939)
  ·
    refine ⟨29827835275234138278923909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19885223516822758852615939 29827835275234138278923909)
    ·
      refine ⟨5592719114106400927298233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29827835275234138278923909 5592719114106400927298233)
      ·
        refine ⟨4194539335579800695473675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592719114106400927298233 4194539335579800695473675)
        ·
          refine ⟨6291809003369701043210513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194539335579800695473675 6291809003369701043210513)
          ·
            refine ⟨4718856752527275782407885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6291809003369701043210513 4718856752527275782407885)
            ·
              refine ⟨1769571282197728418402957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4718856752527275782407885 1769571282197728418402957)
              ·
                refine ⟨663589230824148156901109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769571282197728418402957 663589230824148156901109)
                ·
                  refine ⟨62211490389763889709479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663589230824148156901109 62211490389763889709479)
                  ·
                    rfl

theorem cell23_1090408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 5].length) (baseStart_1090408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090408 prefixEnd_1090408 := by exact prefixLift 1090408
  have htrace : WordTrace (prefixWord ++ tailWord_1090408) baseStart_1090408 baseEnd_1090408 := by
    simpa [prefixWord, tailWord_1090408, baseEnd_1090408] using wordTrace_append hprefix tailTrace_1090408
  have hstable : (prefixWord ++ tailWord_1090408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090408).length < 2 ^ (prefixWord ++ tailWord_1090408).sum := by decide
  have hdescent : baseEnd_1090408 < baseStart_1090408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090421 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1090421 : Nat := 118140960795 + 1090421 * 2 ^ 59
def prefixEnd_1090421 : Nat := 4983230072969 + 3 ^ 40 * 1090421 * 2
def baseEnd_1090421 : Nat := 186636696252127818840917

theorem tailTrace_1090421 : CollatzResearch.WordTrace tailWord_1090421 prefixEnd_1090421 186636696252127818840917 := by
  unfold tailWord_1090421
  simp only [CollatzResearch.WordTrace]
  refine ⟨39770921182598420925455117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26513947455065613950303411 39770921182598420925455117)
  ·
    refine ⟨14914095443474407847045669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39770921182598420925455117 14914095443474407847045669)
    ·
      refine ⟨2796392895651451471321063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14914095443474407847045669 2796392895651451471321063)
      ·
        refine ⟨4194589343477177206981595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796392895651451471321063 4194589343477177206981595)
        ·
          refine ⟨6291884015215765810472393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194589343477177206981595 6291884015215765810472393)
          ·
            refine ⟨4718913011411824357854295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6291884015215765810472393 4718913011411824357854295)
            ·
              refine ⟨7078369517117736536781443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718913011411824357854295 7078369517117736536781443)
              ·
                refine ⟨10617554275676604805172165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7078369517117736536781443 10617554275676604805172165)
                ·
                  refine ⟨1990791426689363400969781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10617554275676604805172165 1990791426689363400969781)
                  ·
                    refine ⟨186636696252127818840917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1990791426689363400969781 186636696252127818840917)
                    ·
                      rfl

theorem cell23_1090421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1090421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090421 prefixEnd_1090421 := by exact prefixLift 1090421
  have htrace : WordTrace (prefixWord ++ tailWord_1090421) baseStart_1090421 baseEnd_1090421 := by
    simpa [prefixWord, tailWord_1090421, baseEnd_1090421] using wordTrace_append hprefix tailTrace_1090421
  have hstable : (prefixWord ++ tailWord_1090421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090421).length < 2 ^ (prefixWord ++ tailWord_1090421).sum := by decide
  have hdescent : baseEnd_1090421 < baseStart_1090421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090424 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1090424 : Nat := 118140960795 + 1090424 * 2 ^ 59
def prefixEnd_1090424 : Nat := 4983230072969 + 3 ^ 40 * 1090424 * 2
def baseEnd_1090424 : Nat := 559911629198346944785237

theorem tailTrace_1090424 : CollatzResearch.WordTrace tailWord_1090424 prefixEnd_1090424 559911629198346944785237 := by
  unfold tailWord_1090424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885515300793776218907163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26514020401058368291876217 19885515300793776218907163)
  ·
    refine ⟨29828272951190664328360745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19885515300793776218907163 29828272951190664328360745)
    ·
      refine ⟨22371204713392998246270559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29828272951190664328360745 22371204713392998246270559)
      ·
        refine ⟨33556807070089497369405839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22371204713392998246270559 33556807070089497369405839)
        ·
          refine ⟨50335210605134246054108759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33556807070089497369405839 50335210605134246054108759)
          ·
            refine ⟨75502815907701369081163139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50335210605134246054108759 75502815907701369081163139)
            ·
              refine ⟨113254223861552053621744709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75502815907701369081163139 113254223861552053621744709)
              ·
                refine ⟨21235166974041010054077133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113254223861552053621744709 21235166974041010054077133)
                ·
                  refine ⟨7963187615265378770278925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21235166974041010054077133 7963187615265378770278925)
                  ·
                    refine ⟨2986195355724517038854597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7963187615265378770278925 2986195355724517038854597)
                    ·
                      refine ⟨559911629198346944785237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2986195355724517038854597 559911629198346944785237)
                      ·
                        rfl

theorem cell23_1090424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1090424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090424 prefixEnd_1090424 := by exact prefixLift 1090424
  have htrace : WordTrace (prefixWord ++ tailWord_1090424) baseStart_1090424 baseEnd_1090424 := by
    simpa [prefixWord, tailWord_1090424, baseEnd_1090424] using wordTrace_append hprefix tailTrace_1090424
  have hstable : (prefixWord ++ tailWord_1090424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090424).length < 2 ^ (prefixWord ++ tailWord_1090424).sum := by decide
  have hdescent : baseEnd_1090424 < baseStart_1090424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090464 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 10]
def baseStart_1090464 : Nat := 118140960795 + 1090464 * 2 ^ 59
def prefixEnd_1090464 : Nat := 4983230072969 + 3 ^ 40 * 1090464 * 2
def baseEnd_1090464 : Nat := 62214685380502976476117

theorem tailTrace_1090464 : CollatzResearch.WordTrace tailWord_1090464 prefixEnd_1090464 62214685380502976476117 := by
  unfold tailWord_1090464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19886244760721319634635223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26514993014295092846180297 19886244760721319634635223)
  ·
    refine ⟨29829367141081979451952835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19886244760721319634635223 29829367141081979451952835)
    ·
      refine ⟨44744050711622969177929253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29829367141081979451952835 44744050711622969177929253)
      ·
        refine ⟨8389509508429306720861735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44744050711622969177929253 8389509508429306720861735)
        ·
          refine ⟨12584264262643960081292603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8389509508429306720861735 12584264262643960081292603)
          ·
            refine ⟨18876396393965940121938905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12584264262643960081292603 18876396393965940121938905)
            ·
              refine ⟨14157297295474455091454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18876396393965940121938905 14157297295474455091454179)
              ·
                refine ⟨21235945943211682637181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14157297295474455091454179 21235945943211682637181269)
                ·
                  refine ⟨62214685380502976476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21235945943211682637181269 62214685380502976476117)
                  ·
                    rfl

theorem cell23_1090464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_1090464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090464 prefixEnd_1090464 := by exact prefixLift 1090464
  have htrace : WordTrace (prefixWord ++ tailWord_1090464) baseStart_1090464 baseEnd_1090464 := by
    simpa [prefixWord, tailWord_1090464, baseEnd_1090464] using wordTrace_append hprefix tailTrace_1090464
  have hstable : (prefixWord ++ tailWord_1090464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090464).length < 2 ^ (prefixWord ++ tailWord_1090464).sum := by decide
  have hdescent : baseEnd_1090464 < baseStart_1090464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090485 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1090485 : Nat := 118140960795 + 1090485 * 2 ^ 59
def prefixEnd_1090485 : Nat := 4983230072969 + 3 ^ 40 * 1090485 * 2
def baseEnd_1090485 : Nat := 186647650506090402040819

theorem tailTrace_1090485 : CollatzResearch.WordTrace tailWord_1090485 prefixEnd_1090485 186647650506090402040819 := by
  unfold tailWord_1090485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39773255454366559855784909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26515503636244373237189939 39773255454366559855784909)
  ·
    refine ⟨14914970795387459945919341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39773255454366559855784909 14914970795387459945919341)
    ·
      refine ⟨5593114048270297479719753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14914970795387459945919341 5593114048270297479719753)
      ·
        refine ⟨4194835536202723109789815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5593114048270297479719753 4194835536202723109789815)
        ·
          refine ⟨6292253304304084664684723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194835536202723109789815 6292253304304084664684723)
          ·
            refine ⟨9438379956456126997027085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292253304304084664684723 9438379956456126997027085)
            ·
              refine ⟨3539392483671047623885157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9438379956456126997027085 3539392483671047623885157)
              ·
                refine ⟨663636090688321429478467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3539392483671047623885157 663636090688321429478467)
                ·
                  refine ⟨995454136032482144217701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663636090688321429478467 995454136032482144217701)
                  ·
                    refine ⟨186647650506090402040819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995454136032482144217701 186647650506090402040819)
                    ·
                      rfl

theorem cell23_1090485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1090485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090485 prefixEnd_1090485 := by exact prefixLift 1090485
  have htrace : WordTrace (prefixWord ++ tailWord_1090485) baseStart_1090485 baseEnd_1090485 := by
    simpa [prefixWord, tailWord_1090485, baseEnd_1090485] using wordTrace_append hprefix tailTrace_1090485
  have hstable : (prefixWord ++ tailWord_1090485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090485).length < 2 ^ (prefixWord ++ tailWord_1090485).sum := by decide
  have hdescent : baseEnd_1090485 < baseStart_1090485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090511 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 3, 5]
def baseStart_1090511 : Nat := 118140960795 + 1090511 * 2 ^ 59
def prefixEnd_1090511 : Nat := 4983230072969 + 3 ^ 40 * 1090511 * 2
def baseEnd_1090511 : Nat := 186652100671762701465779

theorem tailTrace_1090511 : CollatzResearch.WordTrace tailWord_1090511 prefixEnd_1090511 186652100671762701465779 := by
  unfold tailWord_1090511
  simp only [CollatzResearch.WordTrace]
  refine ⟨39774203752272366296231387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26516135834848244197487591 39774203752272366296231387)
  ·
    refine ⟨59661305628408549444347081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39774203752272366296231387 59661305628408549444347081)
    ·
      refine ⟨44745979221306412083260311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59661305628408549444347081 44745979221306412083260311)
      ·
        refine ⟨67118968831959618124890467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44745979221306412083260311 67118968831959618124890467)
        ·
          refine ⟨100678453247939427187335701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67118968831959618124890467 100678453247939427187335701)
          ·
            refine ⟨4719302495997160649406361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100678453247939427187335701 4719302495997160649406361)
            ·
              refine ⟨3539476871997870487054771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4719302495997160649406361 3539476871997870487054771)
              ·
                refine ⟨5309215307996805730582157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539476871997870487054771 5309215307996805730582157)
                ·
                  refine ⟨1990955740498802148968309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5309215307996805730582157 1990955740498802148968309)
                  ·
                    refine ⟨186652100671762701465779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1990955740498802148968309 186652100671762701465779)
                    ·
                      rfl

theorem cell23_1090511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_1090511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090511 prefixEnd_1090511 := by exact prefixLift 1090511
  have htrace : WordTrace (prefixWord ++ tailWord_1090511) baseStart_1090511 baseEnd_1090511 := by
    simpa [prefixWord, tailWord_1090511, baseEnd_1090511] using wordTrace_append hprefix tailTrace_1090511
  have hstable : (prefixWord ++ tailWord_1090511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090511).length < 2 ^ (prefixWord ++ tailWord_1090511).sum := by decide
  have hdescent : baseEnd_1090511 < baseStart_1090511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090542 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1090542 : Nat := 118140960795 + 1090542 * 2 ^ 59
def prefixEnd_1090542 : Nat := 4983230072969 + 3 ^ 40 * 1090542 * 2
def baseEnd_1090542 : Nat := 559972219915577483109695

theorem tailTrace_1090542 : CollatzResearch.WordTrace tailWord_1090542 prefixEnd_1090542 559972219915577483109695 := by
  unfold tailWord_1090542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971916801895007323826235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26516889610106705727073253 4971916801895007323826235)
  ·
    refine ⟨7457875202842510985739353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971916801895007323826235 7457875202842510985739353)
    ·
      refine ⟨5593406402131883239304515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457875202842510985739353 5593406402131883239304515)
      ·
        refine ⟨8390109603197824858956773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593406402131883239304515 8390109603197824858956773)
        ·
          refine ⟨1573145550599592161054395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8390109603197824858956773 1573145550599592161054395)
          ·
            refine ⟨2359718325899388241581593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573145550599592161054395 2359718325899388241581593)
            ·
              refine ⟨1769788744424541181186195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359718325899388241581593 1769788744424541181186195)
              ·
                refine ⟨2654683116636811771779293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769788744424541181186195 2654683116636811771779293)
                ·
                  refine ⟨995506168738804414417235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2654683116636811771779293 995506168738804414417235)
                  ·
                    refine ⟨1493259253108206621625853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995506168738804414417235 1493259253108206621625853)
                    ·
                      refine ⟨559972219915577483109695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1493259253108206621625853 559972219915577483109695)
                      ·
                        rfl

theorem cell23_1090542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1090542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090542 prefixEnd_1090542 := by exact prefixLift 1090542
  have htrace : WordTrace (prefixWord ++ tailWord_1090542) baseStart_1090542 baseEnd_1090542 := by
    simpa [prefixWord, tailWord_1090542, baseEnd_1090542] using wordTrace_append hprefix tailTrace_1090542
  have hstable : (prefixWord ++ tailWord_1090542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090542).length < 2 ^ (prefixWord ++ tailWord_1090542).sum := by decide
  have hdescent : baseEnd_1090542 < baseStart_1090542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090565 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_1090565 : Nat := 118140960795 + 1090565 * 2 ^ 59
def prefixEnd_1090565 : Nat := 4983230072969 + 3 ^ 40 * 1090565 * 2
def baseEnd_1090565 : Nat := 559984029970630893122089

theorem tailTrace_1090565 : CollatzResearch.WordTrace tailWord_1090565 prefixEnd_1090565 559984029970630893122089 := by
  unfold tailWord_1090565
  simp only [CollatzResearch.WordTrace]
  refine ⟨39776173294076733518697149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26517448862717822345798099 39776173294076733518697149)
  ·
    refine ⟨14916064985278775069511431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39776173294076733518697149 14916064985278775069511431)
    ·
      refine ⟨22374097477918162604267147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14916064985278775069511431 22374097477918162604267147)
      ·
        refine ⟨33561146216877243906400721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22374097477918162604267147 33561146216877243906400721)
        ·
          refine ⟨25170859662657932929800541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33561146216877243906400721 25170859662657932929800541)
          ·
            refine ⟨9439072373496724848675203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25170859662657932929800541 9439072373496724848675203)
            ·
              refine ⟨14158608560245087273012805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9439072373496724848675203 14158608560245087273012805)
              ·
                refine ⟨2654739105045953863689901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14158608560245087273012805 2654739105045953863689901)
                ·
                  refine ⟨995527164392232698883713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2654739105045953863689901 995527164392232698883713)
                  ·
                    refine ⟨746645373294174524162785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995527164392232698883713 746645373294174524162785)
                    ·
                      refine ⟨559984029970630893122089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746645373294174524162785 559984029970630893122089)
                      ·
                        rfl

theorem cell23_1090565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_1090565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090565 prefixEnd_1090565 := by exact prefixLift 1090565
  have htrace : WordTrace (prefixWord ++ tailWord_1090565) baseStart_1090565 baseEnd_1090565 := by
    simpa [prefixWord, tailWord_1090565, baseEnd_1090565] using wordTrace_append hprefix tailTrace_1090565
  have hstable : (prefixWord ++ tailWord_1090565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090565).length < 2 ^ (prefixWord ++ tailWord_1090565).sum := by decide
  have hdescent : baseEnd_1090565 < baseStart_1090565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090571 : List Nat := [1, 1, 1, 1, 6, 3, 1, 9]
def baseStart_1090571 : Nat := 118140960795 + 1090571 * 2 ^ 59
def prefixEnd_1090571 : Nat := 4983230072969 + 3 ^ 40 * 1090571 * 2
def baseEnd_1090571 : Nat := 20740263364983624801743

theorem tailTrace_1090571 : CollatzResearch.WordTrace tailWord_1090571 prefixEnd_1090571 20740263364983624801743 := by
  unfold tailWord_1090571
  simp only [CollatzResearch.WordTrace]
  refine ⟨39776392132054996543415567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26517594754703331028943711 39776392132054996543415567)
  ·
    refine ⟨59664588198082494815123351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39776392132054996543415567 59664588198082494815123351)
    ·
      refine ⟨89496882297123742222685027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59664588198082494815123351 89496882297123742222685027)
      ·
        refine ⟨134245323445685613334027541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89496882297123742222685027 134245323445685613334027541)
        ·
          refine ⟨6292749536516513125032541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134245323445685613334027541 6292749536516513125032541)
          ·
            refine ⟨2359781076193692421887203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6292749536516513125032541 2359781076193692421887203)
            ·
              refine ⟨3539671614290538632830805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359781076193692421887203 3539671614290538632830805)
              ·
                refine ⟨20740263364983624801743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3539671614290538632830805 20740263364983624801743)
                ·
                  rfl

theorem cell23_1090571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 9].length) (baseStart_1090571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090571 prefixEnd_1090571 := by exact prefixLift 1090571
  have htrace : WordTrace (prefixWord ++ tailWord_1090571) baseStart_1090571 baseEnd_1090571 := by
    simpa [prefixWord, tailWord_1090571, baseEnd_1090571] using wordTrace_append hprefix tailTrace_1090571
  have hstable : (prefixWord ++ tailWord_1090571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090571).length < 2 ^ (prefixWord ++ tailWord_1090571).sum := by decide
  have hdescent : baseEnd_1090571 < baseStart_1090571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090588 : List Nat := [2, 2, 3, 1, 4, 2, 9]
def baseStart_1090588 : Nat := 118140960795 + 1090588 * 2 ^ 59
def prefixEnd_1090588 : Nat := 4983230072969 + 3 ^ 40 * 1090588 * 2
def baseEnd_1090588 : Nat := 6913528889205979051043

theorem tailTrace_1090588 : CollatzResearch.WordTrace tailWord_1090588 prefixEnd_1090588 6913528889205979051043 := by
  unfold tailWord_1090588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19888506086496704223392209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26518008115328938964522945 19888506086496704223392209)
  ·
    refine ⟨14916379564872528167544157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19888506086496704223392209 14916379564872528167544157)
    ·
      refine ⟨5593642336827198062829059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14916379564872528167544157 5593642336827198062829059)
      ·
        refine ⟨8390463505240797094243589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593642336827198062829059 8390463505240797094243589)
        ·
          refine ⟨1573211907232649455170673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8390463505240797094243589 1573211907232649455170673)
          ·
            refine ⟨1179908930424487091378005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573211907232649455170673 1179908930424487091378005)
            ·
              refine ⟨6913528889205979051043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1179908930424487091378005 6913528889205979051043)
              ·
                rfl

theorem cell23_1090588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 9].length) (baseStart_1090588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090588 prefixEnd_1090588 := by exact prefixLift 1090588
  have htrace : WordTrace (prefixWord ++ tailWord_1090588) baseStart_1090588 baseEnd_1090588 := by
    simpa [prefixWord, tailWord_1090588, baseEnd_1090588] using wordTrace_append hprefix tailTrace_1090588
  have hstable : (prefixWord ++ tailWord_1090588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090588).length < 2 ^ (prefixWord ++ tailWord_1090588).sum := by decide
  have hdescent : baseEnd_1090588 < baseStart_1090588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090599 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1090599 : Nat := 118140960795 + 1090599 * 2 ^ 59
def prefixEnd_1090599 : Nat := 4983230072969 + 3 ^ 40 * 1090599 * 2
def baseEnd_1090599 : Nat := 560001488312883760096933

theorem tailTrace_1090599 : CollatzResearch.WordTrace tailWord_1090599 prefixEnd_1090599 560001488312883760096933 := by
  unfold tailWord_1090599
  simp only [CollatzResearch.WordTrace]
  refine ⟨39777413375953557325434851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26518275583969038216956567 39777413375953557325434851)
  ·
    refine ⟨59666120063930335988152277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39777413375953557325434851 59666120063930335988152277)
    ·
      refine ⟨1398424688998367249722319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59666120063930335988152277 1398424688998367249722319)
      ·
        refine ⟨2097637033497550874583479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398424688998367249722319 2097637033497550874583479)
        ·
          refine ⟨3146455550246326311875219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097637033497550874583479 3146455550246326311875219)
          ·
            refine ⟨4719683325369489467812829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146455550246326311875219 4719683325369489467812829)
            ·
              refine ⟨1769881247013558550429811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719683325369489467812829 1769881247013558550429811)
              ·
                refine ⟨2654821870520337825644717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769881247013558550429811 2654821870520337825644717)
                ·
                  refine ⟨995558201445126684616769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2654821870520337825644717 995558201445126684616769)
                  ·
                    refine ⟨746668651083845013462577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995558201445126684616769 746668651083845013462577)
                    ·
                      refine ⟨560001488312883760096933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746668651083845013462577 560001488312883760096933)
                      ·
                        rfl

theorem cell23_1090599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1090599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090599 prefixEnd_1090599 := by exact prefixLift 1090599
  have htrace : WordTrace (prefixWord ++ tailWord_1090599) baseStart_1090599 baseEnd_1090599 := by
    simpa [prefixWord, tailWord_1090599, baseEnd_1090599] using wordTrace_append hprefix tailTrace_1090599
  have hstable : (prefixWord ++ tailWord_1090599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090599).length < 2 ^ (prefixWord ++ tailWord_1090599).sum := by decide
  have hdescent : baseEnd_1090599 < baseStart_1090599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090668 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1090668 : Nat := 118140960795 + 1090668 * 2 ^ 59
def prefixEnd_1090668 : Nat := 4983230072969 + 3 ^ 40 * 1090668 * 2
def baseEnd_1090668 : Nat := 560036918478043990134115

theorem tailTrace_1090668 : CollatzResearch.WordTrace tailWord_1090668 prefixEnd_1090668 560036918478043990134115 := by
  unfold tailWord_1090668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19889965006351791054848329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26519953341802388073131105 19889965006351791054848329)
  ·
    refine ⟨14917473754763843291136247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19889965006351791054848329 14917473754763843291136247)
    ·
      refine ⟨22376210632145764936704371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14917473754763843291136247 22376210632145764936704371)
      ·
        refine ⟨33564315948218647405056557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22376210632145764936704371 33564315948218647405056557)
        ·
          refine ⟨12586618480581992776896209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33564315948218647405056557 12586618480581992776896209)
          ·
            refine ⟨9439963860436494582672157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12586618480581992776896209 9439963860436494582672157)
            ·
              refine ⟨3539986447663685468502059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9439963860436494582672157 3539986447663685468502059)
              ·
                refine ⟨5309979671495528202753089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539986447663685468502059 5309979671495528202753089)
                ·
                  refine ⟨3982484753621646152064817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5309979671495528202753089 3982484753621646152064817)
                  ·
                    refine ⟨2986863565216234614048613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982484753621646152064817 2986863565216234614048613)
                    ·
                      refine ⟨560036918478043990134115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2986863565216234614048613 560036918478043990134115)
                      ·
                        rfl

theorem cell23_1090668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1090668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090668 prefixEnd_1090668 := by exact prefixLift 1090668
  have htrace : WordTrace (prefixWord ++ tailWord_1090668) baseStart_1090668 baseEnd_1090668 := by
    simpa [prefixWord, tailWord_1090668, baseEnd_1090668] using wordTrace_append hprefix tailTrace_1090668
  have hstable : (prefixWord ++ tailWord_1090668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090668).length < 2 ^ (prefixWord ++ tailWord_1090668).sum := by decide
  have hdescent : baseEnd_1090668 < baseStart_1090668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090672 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2]
def baseStart_1090672 : Nat := 118140960795 + 1090672 * 2 ^ 59
def prefixEnd_1090672 : Nat := 4983230072969 + 3 ^ 40 * 1090672 * 2
def baseEnd_1090672 : Nat := 560038972400661974484097

theorem tailTrace_1090672 : CollatzResearch.WordTrace tailWord_1090672 prefixEnd_1090672 560038972400661974484097 := by
  unfold tailWord_1090672
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890037952344545396421135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26520050603126060528561513 19890037952344545396421135)
  ·
    refine ⟨29835056928516818094631703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19890037952344545396421135 29835056928516818094631703)
    ·
      refine ⟨44752585392775227141947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29835056928516818094631703 44752585392775227141947555)
      ·
        refine ⟨67128878089162840712921333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44752585392775227141947555 67128878089162840712921333)
        ·
          refine ⟨6293332320859016316836375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67128878089162840712921333 6293332320859016316836375)
          ·
            refine ⟨9439998481288524475254563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293332320859016316836375 9439998481288524475254563)
            ·
              refine ⟨14159997721932786712881845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9439998481288524475254563 14159997721932786712881845)
              ·
                refine ⟨1327499786431198754332673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14159997721932786712881845 1327499786431198754332673)
                ·
                  refine ⟨995624839823399065749505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327499786431198754332673 995624839823399065749505)
                  ·
                    refine ⟨746718629867549299312129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995624839823399065749505 746718629867549299312129)
                    ·
                      refine ⟨560038972400661974484097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746718629867549299312129 560038972400661974484097)
                      ·
                        rfl

theorem cell23_1090672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2].length) (baseStart_1090672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090672 prefixEnd_1090672 := by exact prefixLift 1090672
  have htrace : WordTrace (prefixWord ++ tailWord_1090672) baseStart_1090672 baseEnd_1090672 := by
    simpa [prefixWord, tailWord_1090672, baseEnd_1090672] using wordTrace_append hprefix tailTrace_1090672
  have hstable : (prefixWord ++ tailWord_1090672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090672).length < 2 ^ (prefixWord ++ tailWord_1090672).sum := by decide
  have hdescent : baseEnd_1090672 < baseStart_1090672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090706 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1090706 : Nat := 118140960795 + 1090706 * 2 ^ 59
def prefixEnd_1090706 : Nat := 4983230072969 + 3 ^ 40 * 1090706 * 2
def baseEnd_1090706 : Nat := 560056430742914841458941

theorem tailTrace_1090706 : CollatzResearch.WordTrace tailWord_1090706 prefixEnd_1090706 560056430742914841458941 := by
  unfold tailWord_1090706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945328996641478649894993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26520877324377276399719981 9945328996641478649894993)
  ·
    refine ⟨7458996747481108987421245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9945328996641478649894993 7458996747481108987421245)
    ·
      refine ⟨2797123780305415870282967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7458996747481108987421245 2797123780305415870282967)
      ·
        refine ⟨4195685670458123805424451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797123780305415870282967 4195685670458123805424451)
        ·
          refine ⟨6293528505687185708136677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195685670458123805424451 6293528505687185708136677)
          ·
            refine ⟨1180036594816347320275627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6293528505687185708136677 1180036594816347320275627)
            ·
              refine ⟨1770054892224520980413441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180036594816347320275627 1770054892224520980413441)
              ·
                refine ⟨1327541169168390735310081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770054892224520980413441 1327541169168390735310081)
                ·
                  refine ⟨995655876876293051482561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327541169168390735310081 995655876876293051482561)
                  ·
                    refine ⟨746741907657219788611921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995655876876293051482561 746741907657219788611921)
                    ·
                      refine ⟨560056430742914841458941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746741907657219788611921 560056430742914841458941)
                      ·
                        rfl

theorem cell23_1090706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1090706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090706 prefixEnd_1090706 := by exact prefixLift 1090706
  have htrace : WordTrace (prefixWord ++ tailWord_1090706) baseStart_1090706 baseEnd_1090706 := by
    simpa [prefixWord, tailWord_1090706, baseEnd_1090706] using wordTrace_append hprefix tailTrace_1090706
  have hstable : (prefixWord ++ tailWord_1090706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090706).length < 2 ^ (prefixWord ++ tailWord_1090706).sum := by decide
  have hdescent : baseEnd_1090706 < baseStart_1090706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090785 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 6]
def baseStart_1090785 : Nat := 118140960795 + 1090785 * 2 ^ 59
def prefixEnd_1090785 : Nat := 4983230072969 + 3 ^ 40 * 1090785 * 2
def baseEnd_1090785 : Nat := 62232999523846670263453

theorem tailTrace_1090785 : CollatzResearch.WordTrace tailWord_1090785 prefixEnd_1090785 62232999523846670263453 := by
  unfold tailWord_1090785
  simp only [CollatzResearch.WordTrace]
  refine ⟨39784197353279711091705809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26522798235519807394470539 39784197353279711091705809)
  ·
    refine ⟨29838148014959783318779357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39784197353279711091705809 29838148014959783318779357)
    ·
      refine ⟨11189305505609918744542259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29838148014959783318779357 11189305505609918744542259)
      ·
        refine ⟨16783958258414878116813389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11189305505609918744542259 16783958258414878116813389)
        ·
          refine ⟨6293984346905579293805021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16783958258414878116813389 6293984346905579293805021)
          ·
            refine ⟨2360244130089592235176883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6293984346905579293805021 2360244130089592235176883)
            ·
              refine ⟨3540366195134388352765325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360244130089592235176883 3540366195134388352765325)
              ·
                refine ⟨1327637323175395632286997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540366195134388352765325 1327637323175395632286997)
                ·
                  refine ⟨62232999523846670263453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1327637323175395632286997 62232999523846670263453)
                  ·
                    rfl

theorem cell23_1090785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_1090785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090785 prefixEnd_1090785 := by exact prefixLift 1090785
  have htrace : WordTrace (prefixWord ++ tailWord_1090785) baseStart_1090785 baseEnd_1090785 := by
    simpa [prefixWord, tailWord_1090785, baseEnd_1090785] using wordTrace_append hprefix tailTrace_1090785
  have hstable : (prefixWord ++ tailWord_1090785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090785).length < 2 ^ (prefixWord ++ tailWord_1090785).sum := by decide
  have hdescent : baseEnd_1090785 < baseStart_1090785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090788 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1090788 : Nat := 118140960795 + 1090788 * 2 ^ 59
def prefixEnd_1090788 : Nat := 4983230072969 + 3 ^ 40 * 1090788 * 2
def baseEnd_1090788 : Nat := 560098536156583520633563

theorem tailTrace_1090788 : CollatzResearch.WordTrace tailWord_1090788 prefixEnd_1090788 560098536156583520633563 := by
  unfold tailWord_1090788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19892153386134421302032509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26522871181512561736043345 19892153386134421302032509)
  ·
    refine ⟨7459557519800407988262191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19892153386134421302032509 7459557519800407988262191)
    ·
      refine ⟨11189336279700611982393287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7459557519800407988262191 11189336279700611982393287)
      ·
        refine ⟨16784004419550917973589931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11189336279700611982393287 16784004419550917973589931)
        ·
          refine ⟨25176006629326376960384897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16784004419550917973589931 25176006629326376960384897)
          ·
            refine ⟨18882004971994782720288673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25176006629326376960384897 18882004971994782720288673)
            ·
              refine ⟨14161503728996087040216505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18882004971994782720288673 14161503728996087040216505)
              ·
                refine ⟨10621127796747065280162379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14161503728996087040216505 10621127796747065280162379)
                ·
                  refine ⟨15931691695120597920243569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10621127796747065280162379 15931691695120597920243569)
                  ·
                    refine ⟨11948768771340448440182677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15931691695120597920243569 11948768771340448440182677)
                    ·
                      refine ⟨560098536156583520633563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11948768771340448440182677 560098536156583520633563)
                      ·
                        rfl

theorem cell23_1090788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1090788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090788 prefixEnd_1090788 := by exact prefixLift 1090788
  have htrace : WordTrace (prefixWord ++ tailWord_1090788) baseStart_1090788 baseEnd_1090788 := by
    simpa [prefixWord, tailWord_1090788, baseEnd_1090788] using wordTrace_append hprefix tailTrace_1090788
  have hstable : (prefixWord ++ tailWord_1090788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090788).length < 2 ^ (prefixWord ++ tailWord_1090788).sum := by decide
  have hdescent : baseEnd_1090788 < baseStart_1090788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090835 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 6, 2]
def baseStart_1090835 : Nat := 118140960795 + 1090835 * 2 ^ 59
def prefixEnd_1090835 : Nat := 4983230072969 + 3 ^ 40 * 1090835 * 2
def baseEnd_1090835 : Nat := 560122669747344836745847

theorem tailTrace_1090835 : CollatzResearch.WordTrace tailWord_1090835 prefixEnd_1090835 560122669747344836745847 := by
  unfold tailWord_1090835
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786021003098569631025959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26524014002065713087350639 39786021003098569631025959)
  ·
    refine ⟨59679031504647854446538939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39786021003098569631025959 59679031504647854446538939)
    ·
      refine ⟨89518547256971781669808409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59679031504647854446538939 89518547256971781669808409)
      ·
        refine ⟨67138910442728836252356307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89518547256971781669808409 67138910442728836252356307)
        ·
          refine ⟨100708365664093254378534461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67138910442728836252356307 100708365664093254378534461)
          ·
            refine ⟨37765637124034970391950423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100708365664093254378534461 37765637124034970391950423)
            ·
              refine ⟨56648455686052455587925635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37765637124034970391950423 56648455686052455587925635)
              ·
                refine ⟨84972683529078683381888453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56648455686052455587925635 84972683529078683381888453)
                ·
                  refine ⟨15932378161702253134104085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84972683529078683381888453 15932378161702253134104085)
                  ·
                    refine ⟨746830226329793115661129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15932378161702253134104085 746830226329793115661129)
                    ·
                      refine ⟨560122669747344836745847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746830226329793115661129 560122669747344836745847)
                      ·
                        rfl

theorem cell23_1090835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 6, 2].length) (baseStart_1090835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090835 prefixEnd_1090835 := by exact prefixLift 1090835
  have htrace : WordTrace (prefixWord ++ tailWord_1090835) baseStart_1090835 baseEnd_1090835 := by
    simpa [prefixWord, tailWord_1090835, baseEnd_1090835] using wordTrace_append hprefix tailTrace_1090835
  have hstable : (prefixWord ++ tailWord_1090835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090835).length < 2 ^ (prefixWord ++ tailWord_1090835).sum := by decide
  have hdescent : baseEnd_1090835 < baseStart_1090835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090852 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1090852 : Nat := 118140960795 + 1090852 * 2 ^ 59
def prefixEnd_1090852 : Nat := 4983230072969 + 3 ^ 40 * 1090852 * 2
def baseEnd_1090852 : Nat := 560131398918471270233269

theorem tailTrace_1090852 : CollatzResearch.WordTrace tailWord_1090852 prefixEnd_1090852 560131398918471270233269 := by
  unfold tailWord_1090852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893320522018490767197405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26524427362691321022929873 19893320522018490767197405)
  ·
    refine ⟨7459995195756934037699027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19893320522018490767197405 7459995195756934037699027)
    ·
      refine ⟨11189992793635401056548541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7459995195756934037699027 11189992793635401056548541)
      ·
        refine ⟨4196247297613275396205703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11189992793635401056548541 4196247297613275396205703)
        ·
          refine ⟨6294370946419913094308555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196247297613275396205703 6294370946419913094308555)
          ·
            refine ⟨9441556419629869641462833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294370946419913094308555 9441556419629869641462833)
            ·
              refine ⟨7081167314722402231097125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9441556419629869641462833 7081167314722402231097125)
              ·
                refine ⟨1327718871510450418330711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7081167314722402231097125 1327718871510450418330711)
                ·
                  refine ⟨1991578307265675627496067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327718871510450418330711 1991578307265675627496067)
                  ·
                    refine ⟨2987367460898513441244101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1991578307265675627496067 2987367460898513441244101)
                    ·
                      refine ⟨560131398918471270233269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2987367460898513441244101 560131398918471270233269)
                      ·
                        rfl

theorem cell23_1090852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1090852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090852 prefixEnd_1090852 := by exact prefixLift 1090852
  have htrace : WordTrace (prefixWord ++ tailWord_1090852) baseStart_1090852 baseEnd_1090852 := by
    simpa [prefixWord, tailWord_1090852, baseEnd_1090852] using wordTrace_append hprefix tailTrace_1090852
  have hstable : (prefixWord ++ tailWord_1090852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090852).length < 2 ^ (prefixWord ++ tailWord_1090852).sum := by decide
  have hdescent : baseEnd_1090852 < baseStart_1090852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090856 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1090856 : Nat := 118140960795 + 1090856 * 2 ^ 59
def prefixEnd_1090856 : Nat := 4983230072969 + 3 ^ 40 * 1090856 * 2
def baseEnd_1090856 : Nat := 560133452841089254583251

theorem tailTrace_1090856 : CollatzResearch.WordTrace tailWord_1090856 prefixEnd_1090856 560133452841089254583251 := by
  unfold tailWord_1090856
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893393468011245108770211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26524524624014993478360281 19893393468011245108770211)
  ·
    refine ⟨29840090202016867663155317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19893393468011245108770211 29840090202016867663155317)
    ·
      refine ⟨2797508456439081343420811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29840090202016867663155317 2797508456439081343420811)
      ·
        refine ⟨4196262684658622015131217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797508456439081343420811 4196262684658622015131217)
        ·
          refine ⟨3147197013493966511348413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4196262684658622015131217 3147197013493966511348413)
          ·
            refine ⟨1180198880060237441755655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3147197013493966511348413 1180198880060237441755655)
            ·
              refine ⟨1770298320090356162633483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180198880060237441755655 1770298320090356162633483)
              ·
                refine ⟨2655447480135534243950225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770298320090356162633483 2655447480135534243950225)
                ·
                  refine ⟨1991585610101650682962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2655447480135534243950225 1991585610101650682962669)
                  ·
                    refine ⟨746844603788119006111001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991585610101650682962669 746844603788119006111001)
                    ·
                      refine ⟨560133452841089254583251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746844603788119006111001 560133452841089254583251)
                      ·
                        rfl

theorem cell23_1090856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1090856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090856 prefixEnd_1090856 := by exact prefixLift 1090856
  have htrace : WordTrace (prefixWord ++ tailWord_1090856) baseStart_1090856 baseEnd_1090856 := by
    simpa [prefixWord, tailWord_1090856, baseEnd_1090856] using wordTrace_append hprefix tailTrace_1090856
  have hstable : (prefixWord ++ tailWord_1090856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090856).length < 2 ^ (prefixWord ++ tailWord_1090856).sum := by decide
  have hdescent : baseEnd_1090856 < baseStart_1090856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090869 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_1090869 : Nat := 118140960795 + 1090869 * 2 ^ 59
def prefixEnd_1090869 : Nat := 4983230072969 + 3 ^ 40 * 1090869 * 2
def baseEnd_1090869 : Nat := 560140128089597703720691

theorem tailTrace_1090869 : CollatzResearch.WordTrace tailWord_1090869 prefixEnd_1090869 560140128089597703720691 := by
  unfold tailWord_1090869
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787261084975393437763661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26524840723316928958509107 39787261084975393437763661)
  ·
    refine ⟨14920222906865772539161373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39787261084975393437763661 14920222906865772539161373)
    ·
      refine ⟨5595083590074664702185515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14920222906865772539161373 5595083590074664702185515)
      ·
        refine ⟨8392625385111997053278273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595083590074664702185515 8392625385111997053278273)
        ·
          refine ⟨6294469038833997789958705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8392625385111997053278273 6294469038833997789958705)
          ·
            refine ⟨4720851779125498342469029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6294469038833997789958705 4720851779125498342469029)
            ·
              refine ⟨885159708586030939212943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4720851779125498342469029 885159708586030939212943)
              ·
                refine ⟨1327739562879046408819415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885159708586030939212943 1327739562879046408819415)
                ·
                  refine ⟨1991609344318569613229123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327739562879046408819415 1991609344318569613229123)
                  ·
                    refine ⟨2987414016477854419843685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1991609344318569613229123 2987414016477854419843685)
                    ·
                      refine ⟨560140128089597703720691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2987414016477854419843685 560140128089597703720691)
                      ·
                        rfl

theorem cell23_1090869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_1090869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090869 prefixEnd_1090869 := by exact prefixLift 1090869
  have htrace : WordTrace (prefixWord ++ tailWord_1090869) baseStart_1090869 baseEnd_1090869 := by
    simpa [prefixWord, tailWord_1090869, baseEnd_1090869] using wordTrace_append hprefix tailTrace_1090869
  have hstable : (prefixWord ++ tailWord_1090869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090869).length < 2 ^ (prefixWord ++ tailWord_1090869).sum := by decide
  have hdescent : baseEnd_1090869 < baseStart_1090869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090879 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 2, 4]
def baseStart_1090879 : Nat := 118140960795 + 1090879 * 2 ^ 59
def prefixEnd_1090879 : Nat := 4983230072969 + 3 ^ 40 * 1090879 * 2
def baseEnd_1090879 : Nat := 186715087632047554865215

theorem tailTrace_1090879 : CollatzResearch.WordTrace tailWord_1090879 prefixEnd_1090879 186715087632047554865215 := by
  unfold tailWord_1090879
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787625814939165145627691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26525083876626110097085127 39787625814939165145627691)
  ·
    refine ⟨59681438722408747718441537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39787625814939165145627691 59681438722408747718441537)
    ·
      refine ⟨44761079041806560788831153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59681438722408747718441537 44761079041806560788831153)
      ·
        refine ⟨33570809281354920591623365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44761079041806560788831153 33570809281354920591623365)
        ·
          refine ⟨6294526740254047610929381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33570809281354920591623365 6294526740254047610929381)
          ·
            refine ⟨1180223763797633927049259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6294526740254047610929381 1180223763797633927049259)
            ·
              refine ⟨1770335645696450890573889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180223763797633927049259 1770335645696450890573889)
              ·
                refine ⟨1327751734272338167930417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770335645696450890573889 1327751734272338167930417)
                ·
                  refine ⟨995813800704253625947813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327751734272338167930417 995813800704253625947813)
                  ·
                    refine ⟨186715087632047554865215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 995813800704253625947813 186715087632047554865215)
                    ·
                      rfl

theorem cell23_1090879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_1090879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090879 prefixEnd_1090879 := by exact prefixLift 1090879
  have htrace : WordTrace (prefixWord ++ tailWord_1090879) baseStart_1090879 baseEnd_1090879 := by
    simpa [prefixWord, tailWord_1090879, baseEnd_1090879] using wordTrace_append hprefix tailTrace_1090879
  have hstable : (prefixWord ++ tailWord_1090879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090879).length < 2 ^ (prefixWord ++ tailWord_1090879).sum := by decide
  have hdescent : baseEnd_1090879 < baseStart_1090879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_1090885 : Nat := 118140960795 + 1090885 * 2 ^ 59
def prefixEnd_1090885 : Nat := 4983230072969 + 3 ^ 40 * 1090885 * 2
def baseEnd_1090885 : Nat := 560148343780069641120617

theorem tailTrace_1090885 : CollatzResearch.WordTrace tailWord_1090885 prefixEnd_1090885 560148343780069641120617 := by
  unfold tailWord_1090885
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787844652917428170346109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26525229768611618780230739 39787844652917428170346109)
  ·
    refine ⟨14920441744844035563879791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39787844652917428170346109 14920441744844035563879791)
    ·
      refine ⟨22380662617266053345819687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14920441744844035563879791 22380662617266053345819687)
      ·
        refine ⟨33570993925899080018729531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22380662617266053345819687 33570993925899080018729531)
        ·
          refine ⟨50356490888848620028094297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33570993925899080018729531 50356490888848620028094297)
          ·
            refine ⟨37767368166636465021070723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50356490888848620028094297 37767368166636465021070723)
            ·
              refine ⟨56651052249954697531606085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37767368166636465021070723 56651052249954697531606085)
              ·
                refine ⟨10622072296866505787176141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56651052249954697531606085 10622072296866505787176141)
                ·
                  refine ⟨3983277111324939670191053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10622072296866505787176141 3983277111324939670191053)
                  ·
                    refine ⟨1493728916746852376321645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3983277111324939670191053 1493728916746852376321645)
                    ·
                      refine ⟨560148343780069641120617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1493728916746852376321645 560148343780069641120617)
                      ·
                        rfl

theorem cell23_1090885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_1090885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090885 prefixEnd_1090885 := by exact prefixLift 1090885
  have htrace : WordTrace (prefixWord ++ tailWord_1090885) baseStart_1090885 baseEnd_1090885 := by
    simpa [prefixWord, tailWord_1090885, baseEnd_1090885] using wordTrace_append hprefix tailTrace_1090885
  have hstable : (prefixWord ++ tailWord_1090885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090885).length < 2 ^ (prefixWord ++ tailWord_1090885).sum := by decide
  have hdescent : baseEnd_1090885 < baseStart_1090885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090915 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1090915 : Nat := 118140960795 + 1090915 * 2 ^ 59
def prefixEnd_1090915 : Nat := 4983230072969 + 3 ^ 40 * 1090915 * 2
def baseEnd_1090915 : Nat := 560163748199704523745479

theorem tailTrace_1090915 : CollatzResearch.WordTrace tailWord_1090915 prefixEnd_1090915 560163748199704523745479 := by
  unfold tailWord_1090915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39788938842808743293938199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26525959228539162195958799 39788938842808743293938199)
  ·
    refine ⟨59683408264213114940907299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39788938842808743293938199 59683408264213114940907299)
    ·
      refine ⟨89525112396319672411360949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59683408264213114940907299 89525112396319672411360949)
      ·
        refine ⟨8392979287154969288565089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89525112396319672411360949 8392979287154969288565089)
        ·
          refine ⟨6294734465366226966423817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8392979287154969288565089 6294734465366226966423817)
          ·
            refine ⟨4721050849024670224817863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6294734465366226966423817 4721050849024670224817863)
            ·
              refine ⟨7081576273537005337226795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721050849024670224817863 7081576273537005337226795)
              ·
                refine ⟨10622364410305508005840193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081576273537005337226795 10622364410305508005840193)
                ·
                  refine ⟨7966773307729131004380145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622364410305508005840193 7966773307729131004380145)
                  ·
                    refine ⟨5975079980796848253285109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7966773307729131004380145 5975079980796848253285109)
                    ·
                      refine ⟨560163748199704523745479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5975079980796848253285109 560163748199704523745479)
                      ·
                        rfl

theorem cell23_1090915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1090915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090915 prefixEnd_1090915 := by exact prefixLift 1090915
  have htrace : WordTrace (prefixWord ++ tailWord_1090915) baseStart_1090915 baseEnd_1090915 := by
    simpa [prefixWord, tailWord_1090915, baseEnd_1090915] using wordTrace_append hprefix tailTrace_1090915
  have hstable : (prefixWord ++ tailWord_1090915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090915).length < 2 ^ (prefixWord ++ tailWord_1090915).sum := by decide
  have hdescent : baseEnd_1090915 < baseStart_1090915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090920 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1090920 : Nat := 118140960795 + 1090920 * 2 ^ 59
def prefixEnd_1090920 : Nat := 4983230072969 + 3 ^ 40 * 1090920 * 2
def baseEnd_1090920 : Nat := 560166315602977004182957

theorem tailTrace_1090920 : CollatzResearch.WordTrace tailWord_1090920 prefixEnd_1090920 560166315602977004182957 := by
  unfold tailWord_1090920
  simp only [CollatzResearch.WordTrace]
  refine ⟨19894560603895314573935107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26526080805193752765246809 19894560603895314573935107)
  ·
    refine ⟨29841840905842971860902661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19894560603895314573935107 29841840905842971860902661)
    ·
      refine ⟨5595345169845557223919249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29841840905842971860902661 5595345169845557223919249)
      ·
        refine ⟨4196508877384167917939437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595345169845557223919249 4196508877384167917939437)
        ·
          refine ⟨1573690829019062969227289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4196508877384167917939437 1573690829019062969227289)
          ·
            refine ⟨1180268121764297226920467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573690829019062969227289 1180268121764297226920467)
            ·
              refine ⟨1770402182646445840380701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180268121764297226920467 1770402182646445840380701)
              ·
                refine ⟨663900818492417190142763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770402182646445840380701 663900818492417190142763)
                ·
                  refine ⟨995851227738625785214145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663900818492417190142763 995851227738625785214145)
                  ·
                    refine ⟨746888420803969338910609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995851227738625785214145 746888420803969338910609)
                    ·
                      refine ⟨560166315602977004182957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746888420803969338910609 560166315602977004182957)
                      ·
                        rfl

theorem cell23_1090920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1090920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090920 prefixEnd_1090920 := by exact prefixLift 1090920
  have htrace : WordTrace (prefixWord ++ tailWord_1090920) baseStart_1090920 baseEnd_1090920 := by
    simpa [prefixWord, tailWord_1090920, baseEnd_1090920] using wordTrace_append hprefix tailTrace_1090920
  have hstable : (prefixWord ++ tailWord_1090920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090920).length < 2 ^ (prefixWord ++ tailWord_1090920).sum := by decide
  have hdescent : baseEnd_1090920 < baseStart_1090920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090929 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_1090929 : Nat := 118140960795 + 1090929 * 2 ^ 59
def prefixEnd_1090929 : Nat := 4983230072969 + 3 ^ 40 * 1090929 * 2
def baseEnd_1090929 : Nat := 560170936928867468970415

theorem tailTrace_1090929 : CollatzResearch.WordTrace tailWord_1090929 prefixEnd_1090929 560170936928867468970415 := by
  unfold tailWord_1090929
  simp only [CollatzResearch.WordTrace]
  refine ⟨39789449464758023684947841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26526299643172015789965227 39789449464758023684947841)
  ·
    refine ⟨29842087098568517763710881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39789449464758023684947841 29842087098568517763710881)
    ·
      refine ⟨22381565323926388322783161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29842087098568517763710881 22381565323926388322783161)
      ·
        refine ⟨16786173992944791242087371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22381565323926388322783161 16786173992944791242087371)
        ·
          refine ⟨25179260989417186863131057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16786173992944791242087371 25179260989417186863131057)
          ·
            refine ⟨18884445742062890147348293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25179260989417186863131057 18884445742062890147348293)
            ·
              refine ⟨3540833576636791902627805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18884445742062890147348293 3540833576636791902627805)
              ·
                refine ⟨1327812591238796963485427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540833576636791902627805 1327812591238796963485427)
                ·
                  refine ⟨1991718886858195445228141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327812591238796963485427 1991718886858195445228141)
                  ·
                    refine ⟨746894582571823291960553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991718886858195445228141 746894582571823291960553)
                    ·
                      refine ⟨560170936928867468970415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746894582571823291960553 560170936928867468970415)
                      ·
                        rfl

theorem cell23_1090929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_1090929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090929 prefixEnd_1090929 := by exact prefixLift 1090929
  have htrace : WordTrace (prefixWord ++ tailWord_1090929) baseStart_1090929 baseEnd_1090929 := by
    simpa [prefixWord, tailWord_1090929, baseEnd_1090929] using wordTrace_append hprefix tailTrace_1090929
  have hstable : (prefixWord ++ tailWord_1090929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090929).length < 2 ^ (prefixWord ++ tailWord_1090929).sum := by decide
  have hdescent : baseEnd_1090929 < baseStart_1090929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090953 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 2, 1, 3]
def baseStart_1090953 : Nat := 118140960795 + 1090953 * 2 ^ 59
def prefixEnd_1090953 : Nat := 4983230072969 + 3 ^ 40 * 1090953 * 2
def baseEnd_1090953 : Nat := 560183260464575375070305

theorem tailTrace_1090953 : CollatzResearch.WordTrace tailWord_1090953 prefixEnd_1090953 560183260464575375070305 := by
  unfold tailWord_1090953
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790324816671075783821513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26526883211114050522547675 39790324816671075783821513)
  ·
    refine ⟨29842743612503306837866135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39790324816671075783821513 29842743612503306837866135)
    ·
      refine ⟨44764115418754960256799203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29842743612503306837866135 44764115418754960256799203)
      ·
        refine ⟨67146173128132440385198805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44764115418754960256799203 67146173128132440385198805)
        ·
          refine ⟨1573738432690604071528097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67146173128132440385198805 1573738432690604071528097)
          ·
            refine ⟨1180303824517953053646073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573738432690604071528097 1180303824517953053646073)
            ·
              refine ⟨885227868388464790234555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180303824517953053646073 885227868388464790234555)
              ·
                refine ⟨1327841802582697185351833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885227868388464790234555 1327841802582697185351833)
                ·
                  refine ⟨995881351937022889013875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1327841802582697185351833 995881351937022889013875)
                  ·
                    refine ⟨1493822027905534333520813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 995881351937022889013875 1493822027905534333520813)
                    ·
                      refine ⟨560183260464575375070305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1493822027905534333520813 560183260464575375070305)
                      ·
                        rfl

theorem cell23_1090953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 1, 3].length) (baseStart_1090953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090953 prefixEnd_1090953 := by exact prefixLift 1090953
  have htrace : WordTrace (prefixWord ++ tailWord_1090953) baseStart_1090953 baseEnd_1090953 := by
    simpa [prefixWord, tailWord_1090953, baseEnd_1090953] using wordTrace_append hprefix tailTrace_1090953
  have hstable : (prefixWord ++ tailWord_1090953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090953).length < 2 ^ (prefixWord ++ tailWord_1090953).sum := by decide
  have hdescent : baseEnd_1090953 < baseStart_1090953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090955 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_1090955 : Nat := 118140960795 + 1090955 * 2 ^ 59
def prefixEnd_1090955 : Nat := 4983230072969 + 3 ^ 40 * 1090955 * 2
def baseEnd_1090955 : Nat := 560184287425884367245295

theorem tailTrace_1090955 : CollatzResearch.WordTrace tailWord_1090955 prefixEnd_1090955 560184287425884367245295 := by
  unfold tailWord_1090955
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790397762663830125394319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26526931841775886750262879 39790397762663830125394319)
  ·
    refine ⟨59685596643995745188091479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39790397762663830125394319 59685596643995745188091479)
    ·
      refine ⟨89528394965993617782137219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59685596643995745188091479 89528394965993617782137219)
      ·
        refine ⟨134292592448990426673205829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89528394965993617782137219 134292592448990426673205829)
        ·
          refine ⟨25179861084185705001226093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134292592448990426673205829 25179861084185705001226093)
          ·
            refine ⟨9442447906569639375459785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25179861084185705001226093 9442447906569639375459785)
            ·
              refine ⟨7081835929927229531594839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442447906569639375459785 7081835929927229531594839)
              ·
                refine ⟨10622753894890844297392259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081835929927229531594839 10622753894890844297392259)
                ·
                  refine ⟨15934130842336266446088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10622753894890844297392259 15934130842336266446088389)
                  ·
                    refine ⟨2987649532938049958641573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15934130842336266446088389 2987649532938049958641573)
                    ·
                      refine ⟨560184287425884367245295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2987649532938049958641573 560184287425884367245295)
                      ·
                        rfl

theorem cell23_1090955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_1090955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090955 prefixEnd_1090955 := by exact prefixLift 1090955
  have htrace : WordTrace (prefixWord ++ tailWord_1090955) baseStart_1090955 baseEnd_1090955 := by
    simpa [prefixWord, tailWord_1090955, baseEnd_1090955] using wordTrace_append hprefix tailTrace_1090955
  have hstable : (prefixWord ++ tailWord_1090955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090955).length < 2 ^ (prefixWord ++ tailWord_1090955).sum := by decide
  have hdescent : baseEnd_1090955 < baseStart_1090955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090965 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 7]
def baseStart_1090965 : Nat := 118140960795 + 1090965 * 2 ^ 59
def prefixEnd_1090965 : Nat := 4983230072969 + 3 ^ 40 * 1090965 * 2
def baseEnd_1090965 : Nat := 62243269136936592013361

theorem tailTrace_1090965 : CollatzResearch.WordTrace tailWord_1090965 prefixEnd_1090965 62243269136936592013361 := by
  unfold tailWord_1090965
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790762492627601833258349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26527174995085067888838899 39790762492627601833258349)
  ·
    refine ⟨14921535934735350687471881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39790762492627601833258349 14921535934735350687471881)
    ·
      refine ⟨11191151951051513015603911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14921535934735350687471881 11191151951051513015603911)
      ·
        refine ⟨16786727926577269523405867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191151951051513015603911 16786727926577269523405867)
        ·
          refine ⟨25180091889865904285108801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16786727926577269523405867 25180091889865904285108801)
          ·
            refine ⟨18885068917399428213831601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25180091889865904285108801 18885068917399428213831601)
            ·
              refine ⟨14163801688049571160373701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18885068917399428213831601 14163801688049571160373701)
              ·
                refine ⟨2655712816509294592570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14163801688049571160373701 2655712816509294592570069)
                ·
                  refine ⟨62243269136936592013361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2655712816509294592570069 62243269136936592013361)
                  ·
                    rfl

theorem cell23_1090965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_1090965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1090965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1090965 prefixEnd_1090965 := by exact prefixLift 1090965
  have htrace : WordTrace (prefixWord ++ tailWord_1090965) baseStart_1090965 baseEnd_1090965 := by
    simpa [prefixWord, tailWord_1090965, baseEnd_1090965] using wordTrace_append hprefix tailTrace_1090965
  have hstable : (prefixWord ++ tailWord_1090965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090965).length < 2 ^ (prefixWord ++ tailWord_1090965).sum := by decide
  have hdescent : baseEnd_1090965 < baseStart_1090965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091093 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1091093 : Nat := 118140960795 + 1091093 * 2 ^ 59
def prefixEnd_1091093 : Nat := 4983230072969 + 3 ^ 40 * 1091093 * 2
def baseEnd_1091093 : Nat := 186751715918734942439887

theorem tailTrace_1091093 : CollatzResearch.WordTrace tailWord_1091093 prefixEnd_1091093 186751715918734942439887 := by
  unfold tailWord_1091093
  simp only [CollatzResearch.WordTrace]
  refine ⟨39795431036163879693917933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26530287357442586462611955 39795431036163879693917933)
  ·
    refine ⟨14923286638561454885219225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39795431036163879693917933 14923286638561454885219225)
    ·
      refine ⟨11192464978921091163914419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14923286638561454885219225 11192464978921091163914419)
      ·
        refine ⟨16788697468381636745871629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11192464978921091163914419 16788697468381636745871629)
        ·
          refine ⟨6295761550643113779701861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16788697468381636745871629 6295761550643113779701861)
          ·
            refine ⟨1180455290745583833694099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6295761550643113779701861 1180455290745583833694099)
            ·
              refine ⟨1770682936118375750541149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180455290745583833694099 1770682936118375750541149)
              ·
                refine ⟨664006101044390906452931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770682936118375750541149 664006101044390906452931)
                ·
                  refine ⟨996009151566586359679397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664006101044390906452931 996009151566586359679397)
                  ·
                    refine ⟨186751715918734942439887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996009151566586359679397 186751715918734942439887)
                    ·
                      rfl

theorem cell23_1091093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1091093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091093 prefixEnd_1091093 := by exact prefixLift 1091093
  have htrace : WordTrace (prefixWord ++ tailWord_1091093) baseStart_1091093 baseEnd_1091093 := by
    simpa [prefixWord, tailWord_1091093, baseEnd_1091093] using wordTrace_append hprefix tailTrace_1091093
  have hstable : (prefixWord ++ tailWord_1091093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091093).length < 2 ^ (prefixWord ++ tailWord_1091093).sum := by decide
  have hdescent : baseEnd_1091093 < baseStart_1091093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091122 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1091122 : Nat := 118140960795 + 1091122 * 2 ^ 59
def prefixEnd_1091122 : Nat := 4983230072969 + 3 ^ 40 * 1091122 * 2
def baseEnd_1091122 : Nat := 560270038695185213857027

theorem tailTrace_1091122 : CollatzResearch.WordTrace tailWord_1091122 prefixEnd_1091122 560270038695185213857027 := by
  unfold tailWord_1091122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949122188264704411680905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26530992502039211764482413 9949122188264704411680905)
  ·
    refine ⟨7461841641198528308760679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9949122188264704411680905 7461841641198528308760679)
    ·
      refine ⟨11192762461797792463141019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461841641198528308760679 11192762461797792463141019)
      ·
        refine ⟨16789143692696688694711529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11192762461797792463141019 16789143692696688694711529)
        ·
          refine ⟨12591857769522516521033647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16789143692696688694711529 12591857769522516521033647)
          ·
            refine ⟨18887786654283774781550471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12591857769522516521033647 18887786654283774781550471)
            ·
              refine ⟨28331679981425662172325707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18887786654283774781550471 28331679981425662172325707)
              ·
                refine ⟨42497519972138493258488561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28331679981425662172325707 42497519972138493258488561)
                ·
                  refine ⟨31873139979103869943866421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42497519972138493258488561 31873139979103869943866421)
                  ·
                    refine ⟨2988106873040987807237477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31873139979103869943866421 2988106873040987807237477)
                    ·
                      refine ⟨560270038695185213857027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2988106873040987807237477 560270038695185213857027)
                      ·
                        rfl

theorem cell23_1091122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1091122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091122 prefixEnd_1091122 := by exact prefixLift 1091122
  have htrace : WordTrace (prefixWord ++ tailWord_1091122) baseStart_1091122 baseEnd_1091122 := by
    simpa [prefixWord, tailWord_1091122, baseEnd_1091122] using wordTrace_append hprefix tailTrace_1091122
  have hstable : (prefixWord ++ tailWord_1091122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091122).length < 2 ^ (prefixWord ++ tailWord_1091122).sum := by decide
  have hdescent : baseEnd_1091122 < baseStart_1091122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091143 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_1091143 : Nat := 118140960795 + 1091143 * 2 ^ 59
def prefixEnd_1091143 : Nat := 4983230072969 + 3 ^ 40 * 1091143 * 2
def baseEnd_1091143 : Nat := 560280821788929631694431

theorem tailTrace_1091143 : CollatzResearch.WordTrace tailWord_1091143 prefixEnd_1091143 560280821788929631694431 := by
  unfold tailWord_1091143
  simp only [CollatzResearch.WordTrace]
  refine ⟨39797254685982738233238083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26531503123988492155492055 39797254685982738233238083)
  ·
    refine ⟨59695882028974107349857125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39797254685982738233238083 59695882028974107349857125)
    ·
      refine ⟨11192977880432645128098211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59695882028974107349857125 11192977880432645128098211)
      ·
        refine ⟨16789466820648967692147317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11192977880432645128098211 16789466820648967692147317)
        ·
          refine ⟨1574012514435840721138811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16789466820648967692147317 1574012514435840721138811)
          ·
            refine ⟨2361018771653761081708217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574012514435840721138811 2361018771653761081708217)
            ·
              refine ⟨1770764078740320811281163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361018771653761081708217 1770764078740320811281163)
              ·
                refine ⟨2656146118110481216921745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770764078740320811281163 2656146118110481216921745)
                ·
                  refine ⟨1992109588582860912691309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656146118110481216921745 1992109588582860912691309)
                  ·
                    refine ⟨747041095718572842259241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992109588582860912691309 747041095718572842259241)
                    ·
                      refine ⟨560280821788929631694431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747041095718572842259241 560280821788929631694431)
                      ·
                        rfl

theorem cell23_1091143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_1091143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091143 prefixEnd_1091143 := by exact prefixLift 1091143
  have htrace : WordTrace (prefixWord ++ tailWord_1091143) baseStart_1091143 baseEnd_1091143 := by
    simpa [prefixWord, tailWord_1091143, baseEnd_1091143] using wordTrace_append hprefix tailTrace_1091143
  have hstable : (prefixWord ++ tailWord_1091143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091143).length < 2 ^ (prefixWord ++ tailWord_1091143).sum := by decide
  have hdescent : baseEnd_1091143 < baseStart_1091143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091159 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1091159 : Nat := 118140960795 + 1091159 * 2 ^ 59
def prefixEnd_1091159 : Nat := 4983230072969 + 3 ^ 40 * 1091159 * 2
def baseEnd_1091159 : Nat := 560289037479401569094357

theorem tailTrace_1091159 : CollatzResearch.WordTrace tailWord_1091159 prefixEnd_1091159 560289037479401569094357 := by
  unfold tailWord_1091159
  simp only [CollatzResearch.WordTrace]
  refine ⟨39797838253924772965820531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26531892169283181977213687 39797838253924772965820531)
  ·
    refine ⟨59696757380887159448730797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39797838253924772965820531 59696757380887159448730797)
    ·
      refine ⟨22386284017832684793274049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59696757380887159448730797 22386284017832684793274049)
      ·
        refine ⟨16789713013374513594955537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22386284017832684793274049 16789713013374513594955537)
        ·
          refine ⟨12592284760030885196216653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16789713013374513594955537 12592284760030885196216653)
          ·
            refine ⟨4722106785011581948581245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12592284760030885196216653 4722106785011581948581245)
            ·
              refine ⟨1770790044379343230717967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722106785011581948581245 1770790044379343230717967)
              ·
                refine ⟨2656185066569014846076951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770790044379343230717967 2656185066569014846076951)
                ·
                  refine ⟨3984277599853522269115427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656185066569014846076951 3984277599853522269115427)
                  ·
                    refine ⟨5976416399780283403673141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3984277599853522269115427 5976416399780283403673141)
                    ·
                      refine ⟨560289037479401569094357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5976416399780283403673141 560289037479401569094357)
                      ·
                        rfl

theorem cell23_1091159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1091159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091159 prefixEnd_1091159 := by exact prefixLift 1091159
  have htrace : WordTrace (prefixWord ++ tailWord_1091159) baseStart_1091159 baseEnd_1091159 := by
    simpa [prefixWord, tailWord_1091159, baseEnd_1091159] using wordTrace_append hprefix tailTrace_1091159
  have hstable : (prefixWord ++ tailWord_1091159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091159).length < 2 ^ (prefixWord ++ tailWord_1091159).sum := by decide
  have hdescent : baseEnd_1091159 < baseStart_1091159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091176 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1091176 : Nat := 118140960795 + 1091176 * 2 ^ 59
def prefixEnd_1091176 : Nat := 4983230072969 + 3 ^ 40 * 1091176 * 2
def baseEnd_1091176 : Nat := 560297766650528002581779

theorem tailTrace_1091176 : CollatzResearch.WordTrace tailWord_1091176 prefixEnd_1091176 560297766650528002581779 := by
  unfold tailWord_1091176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19899229147431592434594691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26532305529908789912792921 19899229147431592434594691)
  ·
    refine ⟨29848843721147388651892037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19899229147431592434594691 29848843721147388651892037)
    ·
      refine ⟨5596658197715135372229757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29848843721147388651892037 5596658197715135372229757)
      ·
        refine ⟨2098746824143175764586159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5596658197715135372229757 2098746824143175764586159)
        ·
          refine ⟨3148120236214763646879239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098746824143175764586159 3148120236214763646879239)
          ·
            refine ⟨4722180354322145470318859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148120236214763646879239 4722180354322145470318859)
            ·
              refine ⟨7083270531483218205478289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722180354322145470318859 7083270531483218205478289)
              ·
                refine ⟨5312452898612413654108717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083270531483218205478289 5312452898612413654108717)
                ·
                  refine ⟨1992169836979655120290769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5312452898612413654108717 1992169836979655120290769)
                  ·
                    refine ⟨1494127377734741340218077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992169836979655120290769 1494127377734741340218077)
                    ·
                      refine ⟨560297766650528002581779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494127377734741340218077 560297766650528002581779)
                      ·
                        rfl

theorem cell23_1091176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1091176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091176 prefixEnd_1091176 := by exact prefixLift 1091176
  have htrace : WordTrace (prefixWord ++ tailWord_1091176) baseStart_1091176 baseEnd_1091176 := by
    simpa [prefixWord, tailWord_1091176, baseEnd_1091176] using wordTrace_append hprefix tailTrace_1091176
  have hstable : (prefixWord ++ tailWord_1091176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091176).length < 2 ^ (prefixWord ++ tailWord_1091176).sum := by decide
  have hdescent : baseEnd_1091176 < baseStart_1091176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091186 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1091186 : Nat := 118140960795 + 1091186 * 2 ^ 59
def prefixEnd_1091186 : Nat := 4983230072969 + 3 ^ 40 * 1091186 * 2
def baseEnd_1091186 : Nat := 560302901457072963456733

theorem tailTrace_1091186 : CollatzResearch.WordTrace tailWord_1091186 prefixEnd_1091186 560302901457072963456733 := by
  unfold tailWord_1091186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949705756206739144263353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26532548683217971051368941 9949705756206739144263353)
  ·
    refine ⟨7462279317155054358197515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9949705756206739144263353 7462279317155054358197515)
    ·
      refine ⟨11193418975732581537296273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462279317155054358197515 11193418975732581537296273)
      ·
        refine ⟨8395064231799436152972205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11193418975732581537296273 8395064231799436152972205)
        ·
          refine ⟨3148149086924788557364577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8395064231799436152972205 3148149086924788557364577)
          ·
            refine ⟨2361111815193591418023433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148149086924788557364577 2361111815193591418023433)
            ·
              refine ⟨1770833861395193563517575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361111815193591418023433 1770833861395193563517575)
              ·
                refine ⟨2656250792092790345276363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770833861395193563517575 2656250792092790345276363)
                ·
                  refine ⟨3984376188139185517914545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656250792092790345276363 3984376188139185517914545)
                  ·
                    refine ⟨2988282141104389138435909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984376188139185517914545 2988282141104389138435909)
                    ·
                      refine ⟨560302901457072963456733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2988282141104389138435909 560302901457072963456733)
                      ·
                        rfl

theorem cell23_1091186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1091186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091186 prefixEnd_1091186 := by exact prefixLift 1091186
  have htrace : WordTrace (prefixWord ++ tailWord_1091186) baseStart_1091186 baseEnd_1091186 := by
    simpa [prefixWord, tailWord_1091186, baseEnd_1091186] using wordTrace_append hprefix tailTrace_1091186
  have hstable : (prefixWord ++ tailWord_1091186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091186).length < 2 ^ (prefixWord ++ tailWord_1091186).sum := by decide
  have hdescent : baseEnd_1091186 < baseStart_1091186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091190 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1091190 : Nat := 118140960795 + 1091190 * 2 ^ 59
def prefixEnd_1091190 : Nat := 4983230072969 + 3 ^ 40 * 1091190 * 2
def baseEnd_1091190 : Nat := 560304955379690947806715

theorem tailTrace_1091190 : CollatzResearch.WordTrace tailWord_1091190 prefixEnd_1091190 560304955379690947806715 := by
  unfold tailWord_1091190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487435557300779078762439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26532645944541643506799349 2487435557300779078762439)
  ·
    refine ⟨3731153335951168618143659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487435557300779078762439 3731153335951168618143659)
    ·
      refine ⟨5596730003926752927215489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3731153335951168618143659 5596730003926752927215489)
      ·
        refine ⟨4197547502945064695411617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5596730003926752927215489 4197547502945064695411617)
        ·
          refine ⟨3148160627208798521558713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197547502945064695411617 3148160627208798521558713)
          ·
            refine ⟨2361120470406598891169035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148160627208798521558713 2361120470406598891169035)
            ·
              refine ⟨3541680705609898336753553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361120470406598891169035 3541680705609898336753553)
              ·
                refine ⟨2656260529207423752565165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541680705609898336753553 2656260529207423752565165)
                ·
                  refine ⟨996097698452783907211937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2656260529207423752565165 996097698452783907211937)
                  ·
                    refine ⟨747073273839587930408953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996097698452783907211937 747073273839587930408953)
                    ·
                      refine ⟨560304955379690947806715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747073273839587930408953 560304955379690947806715)
                      ·
                        rfl

theorem cell23_1091190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1091190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091190 prefixEnd_1091190 := by exact prefixLift 1091190
  have htrace : WordTrace (prefixWord ++ tailWord_1091190) baseStart_1091190 baseEnd_1091190 := by
    simpa [prefixWord, tailWord_1091190, baseEnd_1091190] using wordTrace_append hprefix tailTrace_1091190
  have hstable : (prefixWord ++ tailWord_1091190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091190).length < 2 ^ (prefixWord ++ tailWord_1091190).sum := by decide
  have hdescent : baseEnd_1091190 < baseStart_1091190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091210 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1091210 : Nat := 118140960795 + 1091210 * 2 ^ 59
def prefixEnd_1091210 : Nat := 4983230072969 + 3 ^ 40 * 1091210 * 2
def baseEnd_1091210 : Nat := 560315224992780869556623

theorem tailTrace_1091210 : CollatzResearch.WordTrace tailWord_1091210 prefixEnd_1091210 560315224992780869556623 := by
  unfold tailWord_1091210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949924594185002168981771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26533132251160005783951389 9949924594185002168981771)
  ·
    refine ⟨14924886891277503253472657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949924594185002168981771 14924886891277503253472657)
    ·
      refine ⟨11193665168458127440104493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14924886891277503253472657 11193665168458127440104493)
      ·
        refine ⟨4197624438171797790039185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11193665168458127440104493 4197624438171797790039185)
        ·
          refine ⟨3148218328628848342529389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197624438171797790039185 3148218328628848342529389)
          ·
            refine ⟨1180581873235818128448521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3148218328628848342529389 1180581873235818128448521)
            ·
              refine ⟨885436404926863596336391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180581873235818128448521 885436404926863596336391)
              ·
                refine ⟨1328154607390295394504587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885436404926863596336391 1328154607390295394504587)
                ·
                  refine ⟨1992231911085443091756881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328154607390295394504587 1992231911085443091756881)
                  ·
                    refine ⟨1494173933314082318817661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992231911085443091756881 1494173933314082318817661)
                    ·
                      refine ⟨560315224992780869556623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494173933314082318817661 560315224992780869556623)
                      ·
                        rfl

theorem cell23_1091210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1091210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091210 prefixEnd_1091210 := by exact prefixLift 1091210
  have htrace : WordTrace (prefixWord ++ tailWord_1091210) baseStart_1091210 baseEnd_1091210 := by
    simpa [prefixWord, tailWord_1091210, baseEnd_1091210] using wordTrace_append hprefix tailTrace_1091210
  have hstable : (prefixWord ++ tailWord_1091210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091210).length < 2 ^ (prefixWord ++ tailWord_1091210).sum := by decide
  have hdescent : baseEnd_1091210 < baseStart_1091210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091223 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1091223 : Nat := 118140960795 + 1091223 * 2 ^ 59
def prefixEnd_1091223 : Nat := 4983230072969 + 3 ^ 40 * 1091223 * 2
def baseEnd_1091223 : Nat := 560321900241289318694063

theorem tailTrace_1091223 : CollatzResearch.WordTrace tailWord_1091223 prefixEnd_1091223 560321900241289318694063 := by
  unfold tailWord_1091223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39800172525692911896150323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26533448350461941264100215 39800172525692911896150323)
  ·
    refine ⟨59700258788539367844225485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39800172525692911896150323 59700258788539367844225485)
    ·
      refine ⟨22387597045702262941584557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59700258788539367844225485 22387597045702262941584557)
      ·
        refine ⟨8395348892138348603094209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22387597045702262941584557 8395348892138348603094209)
        ·
          refine ⟨6296511669103761452320657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395348892138348603094209 6296511669103761452320657)
          ·
            refine ⟨4722383751827821089240493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296511669103761452320657 4722383751827821089240493)
            ·
              refine ⟨1770893906935432908465185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722383751827821089240493 1770893906935432908465185)
              ·
                refine ⟨1328170430201574681348889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770893906935432908465185 1328170430201574681348889)
                ·
                  refine ⟨996127822651181011011667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328170430201574681348889 996127822651181011011667)
                  ·
                    refine ⟨1494191733976771516517501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996127822651181011011667 1494191733976771516517501)
                    ·
                      refine ⟨560321900241289318694063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494191733976771516517501 560321900241289318694063)
                      ·
                        rfl

theorem cell23_1091223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1091223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091223 prefixEnd_1091223 := by exact prefixLift 1091223
  have htrace : WordTrace (prefixWord ++ tailWord_1091223) baseStart_1091223 baseEnd_1091223 := by
    simpa [prefixWord, tailWord_1091223, baseEnd_1091223] using wordTrace_append hprefix tailTrace_1091223
  have hstable : (prefixWord ++ tailWord_1091223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091223).length < 2 ^ (prefixWord ++ tailWord_1091223).sum := by decide
  have hdescent : baseEnd_1091223 < baseStart_1091223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091279 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_1091279 : Nat := 118140960795 + 1091279 * 2 ^ 59
def prefixEnd_1091279 : Nat := 4983230072969 + 3 ^ 40 * 1091279 * 2
def baseEnd_1091279 : Nat := 560350655157941099593805

theorem tailTrace_1091279 : CollatzResearch.WordTrace tailWord_1091279 prefixEnd_1091279 560350655157941099593805 := by
  unfold tailWord_1091279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39802215013490033460188891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26534810008993355640125927 39802215013490033460188891)
  ·
    refine ⟨59703322520235050190283337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39802215013490033460188891 59703322520235050190283337)
    ·
      refine ⟨44777491890176287642712503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59703322520235050190283337 44777491890176287642712503)
      ·
        refine ⟨67166237835264431464068755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44777491890176287642712503 67166237835264431464068755)
        ·
          refine ⟨100749356752896647196103133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67166237835264431464068755 100749356752896647196103133)
          ·
            refine ⟨37781008782336242698538675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100749356752896647196103133 37781008782336242698538675)
            ·
              refine ⟨56671513173504364047808013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37781008782336242698538675 56671513173504364047808013)
              ·
                refine ⟨21251817440064136517928005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56671513173504364047808013 21251817440064136517928005)
                ·
                  refine ⟨3984715770012025597111501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21251817440064136517928005 3984715770012025597111501)
                  ·
                    refine ⟨1494268413754509598916813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3984715770012025597111501 1494268413754509598916813)
                    ·
                      refine ⟨560350655157941099593805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494268413754509598916813 560350655157941099593805)
                      ·
                        rfl

theorem cell23_1091279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_1091279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091279 prefixEnd_1091279 := by exact prefixLift 1091279
  have htrace : WordTrace (prefixWord ++ tailWord_1091279) baseStart_1091279 baseEnd_1091279 := by
    simpa [prefixWord, tailWord_1091279, baseEnd_1091279] using wordTrace_append hprefix tailTrace_1091279
  have hstable : (prefixWord ++ tailWord_1091279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091279).length < 2 ^ (prefixWord ++ tailWord_1091279).sum := by decide
  have hdescent : baseEnd_1091279 < baseStart_1091279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091319 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1091319 : Nat := 118140960795 + 1091319 * 2 ^ 59
def prefixEnd_1091319 : Nat := 4983230072969 + 3 ^ 40 * 1091319 * 2
def baseEnd_1091319 : Nat := 560371194384120943093621

theorem tailTrace_1091319 : CollatzResearch.WordTrace tailWord_1091319 prefixEnd_1091319 560371194384120943093621 := by
  unfold tailWord_1091319
  simp only [CollatzResearch.WordTrace]
  refine ⟨39803673933345120291645011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26535782622230080194430007 39803673933345120291645011)
  ·
    refine ⟨59705510900017680437467517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39803673933345120291645011 59705510900017680437467517)
    ·
      refine ⟨22389566587506630164050319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59705510900017680437467517 22389566587506630164050319)
      ·
        refine ⟨33584349881259945246075479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22389566587506630164050319 33584349881259945246075479)
        ·
          refine ⟨50376524821889917869113219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33584349881259945246075479 50376524821889917869113219)
          ·
            refine ⟨75564787232834876803669829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50376524821889917869113219 75564787232834876803669829)
            ·
              refine ⟨14168397606156539400688093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75564787232834876803669829 14168397606156539400688093)
              ·
                refine ⟨5313149102308702275258035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14168397606156539400688093 5313149102308702275258035)
                ·
                  refine ⟨7969723653463053412887053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313149102308702275258035 7969723653463053412887053)
                  ·
                    refine ⟨2988646370048645029832645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7969723653463053412887053 2988646370048645029832645)
                    ·
                      refine ⟨560371194384120943093621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2988646370048645029832645 560371194384120943093621)
                      ·
                        rfl

theorem cell23_1091319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1091319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091319 prefixEnd_1091319 := by exact prefixLift 1091319
  have htrace : WordTrace (prefixWord ++ tailWord_1091319) baseStart_1091319 baseEnd_1091319 := by
    simpa [prefixWord, tailWord_1091319, baseEnd_1091319] using wordTrace_append hprefix tailTrace_1091319
  have hstable : (prefixWord ++ tailWord_1091319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091319).length < 2 ^ (prefixWord ++ tailWord_1091319).sum := by decide
  have hdescent : baseEnd_1091319 < baseStart_1091319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091336 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1091336 : Nat := 118140960795 + 1091336 * 2 ^ 59
def prefixEnd_1091336 : Nat := 4983230072969 + 3 ^ 40 * 1091336 * 2
def baseEnd_1091336 : Nat := 560379923555247376581043

theorem tailTrace_1091336 : CollatzResearch.WordTrace tailWord_1091336 prefixEnd_1091336 560379923555247376581043 := by
  unfold tailWord_1091336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902146987141766097506931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26536195982855688130009241 19902146987141766097506931)
  ·
    refine ⟨29853220480712649146260397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19902146987141766097506931 29853220480712649146260397)
    ·
      refine ⟨11194957680267243429847649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29853220480712649146260397 11194957680267243429847649)
      ·
        refine ⟨8396218260200432572385737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194957680267243429847649 8396218260200432572385737)
        ·
          refine ⟨6297163695150324429289303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8396218260200432572385737 6297163695150324429289303)
          ·
            refine ⟨9445745542725486643933955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297163695150324429289303 9445745542725486643933955)
            ·
              refine ⟨14168618314088229965900933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445745542725486643933955 14168618314088229965900933)
              ·
                refine ⟨2656615933891543118606425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14168618314088229965900933 2656615933891543118606425)
                ·
                  refine ⟨1992461950418657338954819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656615933891543118606425 1992461950418657338954819)
                  ·
                    refine ⟨2988692925627986008432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1992461950418657338954819 2988692925627986008432229)
                    ·
                      refine ⟨560379923555247376581043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2988692925627986008432229 560379923555247376581043)
                      ·
                        rfl

theorem cell23_1091336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1091336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091336 prefixEnd_1091336 := by exact prefixLift 1091336
  have htrace : WordTrace (prefixWord ++ tailWord_1091336) baseStart_1091336 baseEnd_1091336 := by
    simpa [prefixWord, tailWord_1091336, baseEnd_1091336] using wordTrace_append hprefix tailTrace_1091336
  have hstable : (prefixWord ++ tailWord_1091336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091336).length < 2 ^ (prefixWord ++ tailWord_1091336).sum := by decide
  have hdescent : baseEnd_1091336 < baseStart_1091336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091356 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1091356 : Nat := 118140960795 + 1091356 * 2 ^ 59
def prefixEnd_1091356 : Nat := 4983230072969 + 3 ^ 40 * 1091356 * 2
def baseEnd_1091356 : Nat := 560390193168337298330951

theorem tailTrace_1091356 : CollatzResearch.WordTrace tailWord_1091356 prefixEnd_1091356 560390193168337298330951 := by
  unfold tailWord_1091356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902511717105537805370961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26536682289474050407161281 19902511717105537805370961)
  ·
    refine ⟨14926883787829153354028221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19902511717105537805370961 14926883787829153354028221)
    ·
      refine ⟨5597581420435932507760583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14926883787829153354028221 5597581420435932507760583)
      ·
        refine ⟨8396372130653898761640875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597581420435932507760583 8396372130653898761640875)
        ·
          refine ⟨12594558195980848142461313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396372130653898761640875 12594558195980848142461313)
          ·
            refine ⟨9445918646985636106845985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594558195980848142461313 9445918646985636106845985)
            ·
              refine ⟨7084438985239227080134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9445918646985636106845985 7084438985239227080134489)
              ·
                refine ⟨5313329238929420310100867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084438985239227080134489 5313329238929420310100867)
                ·
                  refine ⟨7969993858394130465151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313329238929420310100867 7969993858394130465151301)
                  ·
                    refine ⟨1494373848448899462215869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7969993858394130465151301 1494373848448899462215869)
                    ·
                      refine ⟨560390193168337298330951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494373848448899462215869 560390193168337298330951)
                      ·
                        rfl

theorem cell23_1091356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1091356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091356 prefixEnd_1091356 := by exact prefixLift 1091356
  have htrace : WordTrace (prefixWord ++ tailWord_1091356) baseStart_1091356 baseEnd_1091356 := by
    simpa [prefixWord, tailWord_1091356, baseEnd_1091356] using wordTrace_append hprefix tailTrace_1091356
  have hstable : (prefixWord ++ tailWord_1091356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091356).length < 2 ^ (prefixWord ++ tailWord_1091356).sum := by decide
  have hdescent : baseEnd_1091356 < baseStart_1091356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091413 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1091413 : Nat := 118140960795 + 1091413 * 2 ^ 59
def prefixEnd_1091413 : Nat := 4983230072969 + 3 ^ 40 * 1091413 * 2
def baseEnd_1091413 : Nat := 560419461565643575318189

theorem tailTrace_1091413 : CollatzResearch.WordTrace tailWord_1091413 prefixEnd_1091413 560419461565643575318189 := by
  unfold tailWord_1091413
  simp only [CollatzResearch.WordTrace]
  refine ⟨39807102395004574345566893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26538068263336382897044595 39807102395004574345566893)
  ·
    refine ⟨14927663398126715379587585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39807102395004574345566893 14927663398126715379587585)
    ·
      refine ⟨11195747548595036534690689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14927663398126715379587585 11195747548595036534690689)
      ·
        refine ⟨8396810661446277401018017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11195747548595036534690689 8396810661446277401018017)
        ·
          refine ⟨6297607996084708050763513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8396810661446277401018017 6297607996084708050763513)
          ·
            refine ⟨4723205997063531038072635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297607996084708050763513 4723205997063531038072635)
            ·
              refine ⟨7084808995595296557108953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723205997063531038072635 7084808995595296557108953)
              ·
                refine ⟨5313606746696472417831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084808995595296557108953 5313606746696472417831715)
                ·
                  refine ⟨7970410120044708626747573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313606746696472417831715 7970410120044708626747573)
                  ·
                    refine ⟨747225948754191433757585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7970410120044708626747573 747225948754191433757585)
                    ·
                      refine ⟨560419461565643575318189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747225948754191433757585 560419461565643575318189)
                      ·
                        rfl

theorem cell23_1091413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1091413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091413 prefixEnd_1091413 := by exact prefixLift 1091413
  have htrace : WordTrace (prefixWord ++ tailWord_1091413) baseStart_1091413 baseEnd_1091413 := by
    simpa [prefixWord, tailWord_1091413, baseEnd_1091413] using wordTrace_append hprefix tailTrace_1091413
  have hstable : (prefixWord ++ tailWord_1091413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091413).length < 2 ^ (prefixWord ++ tailWord_1091413).sum := by decide
  have hdescent : baseEnd_1091413 < baseStart_1091413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091423 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 1, 5]
def baseStart_1091423 : Nat := 118140960795 + 1091423 * 2 ^ 59
def prefixEnd_1091423 : Nat := 4983230072969 + 3 ^ 40 * 1091423 * 2
def baseEnd_1091423 : Nat := 186808198790729512064381

theorem tailTrace_1091423 : CollatzResearch.WordTrace tailWord_1091423 prefixEnd_1091423 186808198790729512064381 := by
  unfold tailWord_1091423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39807467124968346053430923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26538311416645564035620615 39807467124968346053430923)
  ·
    refine ⟨59711200687452519080146385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39807467124968346053430923 59711200687452519080146385)
    ·
      refine ⟨44783400515589389310109789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59711200687452519080146385 44783400515589389310109789)
      ·
        refine ⟨16793775193346020991291171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44783400515589389310109789 16793775193346020991291171)
        ·
          refine ⟨25190662790019031486936757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16793775193346020991291171 25190662790019031486936757)
          ·
            refine ⟨2361624636564284201900321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25190662790019031486936757 2361624636564284201900321)
            ·
              refine ⟨1771218477423213151425241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361624636564284201900321 1771218477423213151425241)
              ·
                refine ⟨1328413858067409863568931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771218477423213151425241 1328413858067409863568931)
                ·
                  refine ⟨1992620787101114795353397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328413858067409863568931 1992620787101114795353397)
                  ·
                    refine ⟨186808198790729512064381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1992620787101114795353397 186808198790729512064381)
                    ·
                      rfl

theorem cell23_1091423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_1091423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091423 prefixEnd_1091423 := by exact prefixLift 1091423
  have htrace : WordTrace (prefixWord ++ tailWord_1091423) baseStart_1091423 baseEnd_1091423 := by
    simpa [prefixWord, tailWord_1091423, baseEnd_1091423] using wordTrace_append hprefix tailTrace_1091423
  have hstable : (prefixWord ++ tailWord_1091423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091423).length < 2 ^ (prefixWord ++ tailWord_1091423).sum := by decide
  have hdescent : baseEnd_1091423 < baseStart_1091423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091437 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1091437 : Nat := 118140960795 + 1091437 * 2 ^ 59
def prefixEnd_1091437 : Nat := 4983230072969 + 3 ^ 40 * 1091437 * 2
def baseEnd_1091437 : Nat := 560431785101351481418079

theorem tailTrace_1091437 : CollatzResearch.WordTrace tailWord_1091437 prefixEnd_1091437 560431785101351481418079 := by
  unfold tailWord_1091437
  simp only [CollatzResearch.WordTrace]
  refine ⟨39807977746917626444440565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26538651831278417629627043 39807977746917626444440565)
  ·
    refine ⟨3731997913773527479166303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39807977746917626444440565 3731997913773527479166303)
    ·
      refine ⟨5597996870660291218749455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3731997913773527479166303 5597996870660291218749455)
      ·
        refine ⟨8396995305990436828124183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597996870660291218749455 8396995305990436828124183)
        ·
          refine ⟨12595492958985655242186275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396995305990436828124183 12595492958985655242186275)
          ·
            refine ⟨18893239438478482863279413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12595492958985655242186275 18893239438478482863279413)
            ·
              refine ⟨1771241197357357768432445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18893239438478482863279413 1771241197357357768432445)
              ·
                refine ⟨664215449009009163162167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1771241197357357768432445 664215449009009163162167)
                ·
                  refine ⟨996323173513513744743251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664215449009009163162167 996323173513513744743251)
                  ·
                    refine ⟨1494484760270270617114877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996323173513513744743251 1494484760270270617114877)
                    ·
                      refine ⟨560431785101351481418079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494484760270270617114877 560431785101351481418079)
                      ·
                        rfl

theorem cell23_1091437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1091437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091437 prefixEnd_1091437 := by exact prefixLift 1091437
  have htrace : WordTrace (prefixWord ++ tailWord_1091437) baseStart_1091437 baseEnd_1091437 := by
    simpa [prefixWord, tailWord_1091437, baseEnd_1091437] using wordTrace_append hprefix tailTrace_1091437
  have hstable : (prefixWord ++ tailWord_1091437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091437).length < 2 ^ (prefixWord ++ tailWord_1091437).sum := by decide
  have hdescent : baseEnd_1091437 < baseStart_1091437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091453 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1091453 : Nat := 118140960795 + 1091453 * 2 ^ 59
def prefixEnd_1091453 : Nat := 4983230072969 + 3 ^ 40 * 1091453 * 2
def baseEnd_1091453 : Nat := 186813333597274472939335

theorem tailTrace_1091453 : CollatzResearch.WordTrace tailWord_1091453 prefixEnd_1091453 186813333597274472939335 := by
  unfold tailWord_1091453
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808561314859661177023013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26539040876573107451348675 39808561314859661177023013)
  ·
    refine ⟨7464105246536186470691815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39808561314859661177023013 7464105246536186470691815)
    ·
      refine ⟨11196157869804279706037723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464105246536186470691815 11196157869804279706037723)
      ·
        refine ⟨16794236804706419559056585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11196157869804279706037723 16794236804706419559056585)
        ·
          refine ⟨12595677603529814669292439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16794236804706419559056585 12595677603529814669292439)
          ·
            refine ⟨18893516405294722003938659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12595677603529814669292439 18893516405294722003938659)
            ·
              refine ⟨28340274607942083005907989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893516405294722003938659 28340274607942083005907989)
              ·
                refine ⟨1328450372247285140901937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28340274607942083005907989 1328450372247285140901937)
                ·
                  refine ⟨996337779185463855676453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328450372247285140901937 996337779185463855676453)
                  ·
                    refine ⟨186813333597274472939335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996337779185463855676453 186813333597274472939335)
                    ·
                      rfl

theorem cell23_1091453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1091453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091453 prefixEnd_1091453 := by exact prefixLift 1091453
  have htrace : WordTrace (prefixWord ++ tailWord_1091453) baseStart_1091453 baseEnd_1091453 := by
    simpa [prefixWord, tailWord_1091453, baseEnd_1091453] using wordTrace_append hprefix tailTrace_1091453
  have hstable : (prefixWord ++ tailWord_1091453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091453).length < 2 ^ (prefixWord ++ tailWord_1091453).sum := by decide
  have hdescent : baseEnd_1091453 < baseStart_1091453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091454 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1091454 : Nat := 118140960795 + 1091454 * 2 ^ 59
def prefixEnd_1091454 : Nat := 4983230072969 + 3 ^ 40 * 1091454 * 2
def baseEnd_1091454 : Nat := 560440514272477914905501

theorem tailTrace_1091454 : CollatzResearch.WordTrace tailWord_1091454 prefixEnd_1091454 560440514272477914905501 := by
  unfold tailWord_1091454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976074723482004793476177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26539065191904025565206277 4976074723482004793476177)
  ·
    refine ⟨3732056042611503595107133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976074723482004793476177 3732056042611503595107133)
    ·
      refine ⟨1399521015979313848165175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3732056042611503595107133 1399521015979313848165175)
      ·
        refine ⟨2099281523968970772247763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399521015979313848165175 2099281523968970772247763)
        ·
          refine ⟨3148922285953456158371645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099281523968970772247763 3148922285953456158371645)
          ·
            refine ⟨1180845857232546059389367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3148922285953456158371645 1180845857232546059389367)
            ·
              refine ⟨1771268785848819089084051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180845857232546059389367 1771268785848819089084051)
              ·
                refine ⟨2656903178773228633626077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771268785848819089084051 2656903178773228633626077)
                ·
                  refine ⟨996338692039960737609779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2656903178773228633626077 996338692039960737609779)
                  ·
                    refine ⟨1494508038059941106414669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996338692039960737609779 1494508038059941106414669)
                    ·
                      refine ⟨560440514272477914905501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494508038059941106414669 560440514272477914905501)
                      ·
                        rfl

theorem cell23_1091454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1091454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091454 prefixEnd_1091454 := by exact prefixLift 1091454
  have htrace : WordTrace (prefixWord ++ tailWord_1091454) baseStart_1091454 baseEnd_1091454 := by
    simpa [prefixWord, tailWord_1091454, baseEnd_1091454] using wordTrace_append hprefix tailTrace_1091454
  have hstable : (prefixWord ++ tailWord_1091454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091454).length < 2 ^ (prefixWord ++ tailWord_1091454).sum := by decide
  have hdescent : baseEnd_1091454 < baseStart_1091454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091490 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1091490 : Nat := 118140960795 + 1091490 * 2 ^ 59
def prefixEnd_1091490 : Nat := 4983230072969 + 3 ^ 40 * 1091490 * 2
def baseEnd_1091490 : Nat := 560458999576039774055335

theorem tailTrace_1091490 : CollatzResearch.WordTrace tailWord_1091490 prefixEnd_1091490 560458999576039774055335 := by
  unfold tailWord_1091490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952477703931404124029981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26539940543817077664079949 9952477703931404124029981)
  ·
    refine ⟨3732179138974276546511243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9952477703931404124029981 3732179138974276546511243)
    ·
      refine ⟨5598268708461414819766865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732179138974276546511243 5598268708461414819766865)
      ·
        refine ⟨4198701531346061114825149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5598268708461414819766865 4198701531346061114825149)
        ·
          refine ⟨1574513074254772918059431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4198701531346061114825149 1574513074254772918059431)
          ·
            refine ⟨2361769611382159377089147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574513074254772918059431 2361769611382159377089147)
            ·
              refine ⟨3542654417073239065633721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361769611382159377089147 3542654417073239065633721)
              ·
                refine ⟨2656990812804929299225291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542654417073239065633721 2656990812804929299225291)
                ·
                  refine ⟨3985486219207393948837937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656990812804929299225291 3985486219207393948837937)
                  ·
                    refine ⟨2989114664405545461628453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985486219207393948837937 2989114664405545461628453)
                    ·
                      refine ⟨560458999576039774055335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2989114664405545461628453 560458999576039774055335)
                      ·
                        rfl

theorem cell23_1091490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1091490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091490 prefixEnd_1091490 := by exact prefixLift 1091490
  have htrace : WordTrace (prefixWord ++ tailWord_1091490) baseStart_1091490 baseEnd_1091490 := by
    simpa [prefixWord, tailWord_1091490, baseEnd_1091490] using wordTrace_append hprefix tailTrace_1091490
  have hstable : (prefixWord ++ tailWord_1091490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091490).length < 2 ^ (prefixWord ++ tailWord_1091490).sum := by decide
  have hdescent : baseEnd_1091490 < baseStart_1091490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091493 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_1091493 : Nat := 118140960795 + 1091493 * 2 ^ 59
def prefixEnd_1091493 : Nat := 4983230072969 + 3 ^ 40 * 1091493 * 2
def baseEnd_1091493 : Nat := 560460540018003262317821

theorem tailTrace_1091493 : CollatzResearch.WordTrace tailWord_1091493 prefixEnd_1091493 560460540018003262317821 := by
  unfold tailWord_1091493
  simp only [CollatzResearch.WordTrace]
  refine ⟨39810020234714748008479133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26540013489809832005652755 39810020234714748008479133)
  ·
    refine ⟨14928757588018030503179675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39810020234714748008479133 14928757588018030503179675)
    ·
      refine ⟨22393136382027045754769513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14928757588018030503179675 22393136382027045754769513)
      ·
        refine ⟨16794852286520284316077135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22393136382027045754769513 16794852286520284316077135)
        ·
          refine ⟨25192278429780426474115703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16794852286520284316077135 25192278429780426474115703)
          ·
            refine ⟨37788417644670639711173555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25192278429780426474115703 37788417644670639711173555)
            ·
              refine ⟨56682626467005959566760333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37788417644670639711173555 56682626467005959566760333)
              ·
                refine ⟨21255984925127234837535125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56682626467005959566760333 21255984925127234837535125)
                ·
                  refine ⟨996374293365339133009459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21255984925127234837535125 996374293365339133009459)
                  ·
                    refine ⟨1494561440048008699514189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996374293365339133009459 1494561440048008699514189)
                    ·
                      refine ⟨560460540018003262317821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494561440048008699514189 560460540018003262317821)
                      ·
                        rfl

theorem cell23_1091493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_1091493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091493 prefixEnd_1091493 := by exact prefixLift 1091493
  have htrace : WordTrace (prefixWord ++ tailWord_1091493) baseStart_1091493 baseEnd_1091493 := by
    simpa [prefixWord, tailWord_1091493, baseEnd_1091493] using wordTrace_append hprefix tailTrace_1091493
  have hstable : (prefixWord ++ tailWord_1091493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091493).length < 2 ^ (prefixWord ++ tailWord_1091493).sum := by decide
  have hdescent : baseEnd_1091493 < baseStart_1091493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091506 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1091506 : Nat := 118140960795 + 1091506 * 2 ^ 59
def prefixEnd_1091506 : Nat := 4983230072969 + 3 ^ 40 * 1091506 * 2
def baseEnd_1091506 : Nat := 560467215266511711455261

theorem tailTrace_1091506 : CollatzResearch.WordTrace tailWord_1091506 prefixEnd_1091506 560467215266511711455261 := by
  unfold tailWord_1091506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952623595916912807175593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26540329589111767485801581 9952623595916912807175593)
  ·
    refine ⟨7464467696937684605381695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9952623595916912807175593 7464467696937684605381695)
    ·
      refine ⟨11196701545406526908072543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464467696937684605381695 11196701545406526908072543)
      ·
        refine ⟨16795052318109790362108815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11196701545406526908072543 16795052318109790362108815)
        ·
          refine ⟨25192578477164685543163223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16795052318109790362108815 25192578477164685543163223)
          ·
            refine ⟨37788867715747028314744835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25192578477164685543163223 37788867715747028314744835)
            ·
              refine ⟨56683301573620542472117253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37788867715747028314744835 56683301573620542472117253)
              ·
                refine ⟨10628119045053851713521985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56683301573620542472117253 10628119045053851713521985)
                ·
                  refine ⟨7971089283790388785141489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10628119045053851713521985 7971089283790388785141489)
                  ·
                    refine ⟨5978316962842791588856117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7971089283790388785141489 5978316962842791588856117)
                    ·
                      refine ⟨560467215266511711455261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5978316962842791588856117 560467215266511711455261)
                      ·
                        rfl

theorem cell23_1091506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1091506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091506 prefixEnd_1091506 := by exact prefixLift 1091506
  have htrace : WordTrace (prefixWord ++ tailWord_1091506) baseStart_1091506 baseEnd_1091506 := by
    simpa [prefixWord, tailWord_1091506, baseEnd_1091506] using wordTrace_append hprefix tailTrace_1091506
  have hstable : (prefixWord ++ tailWord_1091506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091506).length < 2 ^ (prefixWord ++ tailWord_1091506).sum := by decide
  have hdescent : baseEnd_1091506 < baseStart_1091506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091536 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_1091536 : Nat := 118140960795 + 1091536 * 2 ^ 59
def prefixEnd_1091536 : Nat := 4983230072969 + 3 ^ 40 * 1091536 * 2
def baseEnd_1091536 : Nat := 560482619686146594080123

theorem tailTrace_1091536 : CollatzResearch.WordTrace tailWord_1091536 prefixEnd_1091536 560482619686146594080123 := by
  unfold tailWord_1091536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19905794286779483176147231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26541059049039310901529641 19905794286779483176147231)
  ·
    refine ⟨29858691430169224764220847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19905794286779483176147231 29858691430169224764220847)
    ·
      refine ⟨44788037145253837146331271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29858691430169224764220847 44788037145253837146331271)
      ·
        refine ⟨67182055717880755719496907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44788037145253837146331271 67182055717880755719496907)
        ·
          refine ⟨100773083576821133579245361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67182055717880755719496907 100773083576821133579245361)
          ·
            refine ⟨75579812682615850184434021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100773083576821133579245361 75579812682615850184434021)
            ·
              refine ⟨14171214877990471909581379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75579812682615850184434021 14171214877990471909581379)
              ·
                refine ⟨21256822316985707864372069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14171214877990471909581379 21256822316985707864372069)
                ·
                  refine ⟨3985654184434820224569763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21256822316985707864372069 3985654184434820224569763)
                  ·
                    refine ⟨5978481276652230336854645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985654184434820224569763 5978481276652230336854645)
                    ·
                      refine ⟨560482619686146594080123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5978481276652230336854645 560482619686146594080123)
                      ·
                        rfl

theorem cell23_1091536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_1091536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091536 prefixEnd_1091536 := by exact prefixLift 1091536
  have htrace : WordTrace (prefixWord ++ tailWord_1091536) baseStart_1091536 baseEnd_1091536 := by
    simpa [prefixWord, tailWord_1091536, baseEnd_1091536] using wordTrace_append hprefix tailTrace_1091536
  have hstable : (prefixWord ++ tailWord_1091536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091536).length < 2 ^ (prefixWord ++ tailWord_1091536).sum := by decide
  have hdescent : baseEnd_1091536 < baseStart_1091536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091548 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1091548 : Nat := 118140960795 + 1091548 * 2 ^ 59
def prefixEnd_1091548 : Nat := 4983230072969 + 3 ^ 40 * 1091548 * 2
def baseEnd_1091548 : Nat := 560488781454000547130069

theorem tailTrace_1091548 : CollatzResearch.WordTrace tailWord_1091548 prefixEnd_1091548 560488781454000547130069 := by
  unfold tailWord_1091548
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906013124757746200865649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26541350833010328267820865 19906013124757746200865649)
  ·
    refine ⟨14929509843568309650649237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19906013124757746200865649 14929509843568309650649237)
    ·
      refine ⟨699820773917264514874183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14929509843568309650649237 699820773917264514874183)
      ·
        refine ⟨1049731160875896772311275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699820773917264514874183 1049731160875896772311275)
        ·
          refine ⟨1574596741313845158466913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049731160875896772311275 1574596741313845158466913)
          ·
            refine ⟨1180947555985383868850185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574596741313845158466913 1180947555985383868850185)
            ·
              refine ⟨885710666989037901637639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180947555985383868850185 885710666989037901637639)
              ·
                refine ⟨1328566000483556852456459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885710666989037901637639 1328566000483556852456459)
                ·
                  refine ⟨1992849000725335278684689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328566000483556852456459 1992849000725335278684689)
                  ·
                    refine ⟨1494636750544001459013517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992849000725335278684689 1494636750544001459013517)
                    ·
                      refine ⟨560488781454000547130069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494636750544001459013517 560488781454000547130069)
                      ·
                        rfl

theorem cell23_1091548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1091548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091548 prefixEnd_1091548 := by exact prefixLift 1091548
  have htrace : WordTrace (prefixWord ++ tailWord_1091548) baseStart_1091548 baseEnd_1091548 := by
    simpa [prefixWord, tailWord_1091548, baseEnd_1091548] using wordTrace_append hprefix tailTrace_1091548
  have hstable : (prefixWord ++ tailWord_1091548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091548).length < 2 ^ (prefixWord ++ tailWord_1091548).sum := by decide
  have hdescent : baseEnd_1091548 < baseStart_1091548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091556 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1091556 : Nat := 118140960795 + 1091556 * 2 ^ 59
def prefixEnd_1091556 : Nat := 4983230072969 + 3 ^ 40 * 1091556 * 2
def baseEnd_1091556 : Nat := 62276987699915168425559

theorem tailTrace_1091556 : CollatzResearch.WordTrace tailWord_1091556 prefixEnd_1091556 62276987699915168425559 := by
  unfold tailWord_1091556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906159016743254884011261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26541545355657673178681681 19906159016743254884011261)
  ·
    refine ⟨7464809631278720581504223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19906159016743254884011261 7464809631278720581504223)
    ·
      refine ⟨11197214446918080872256335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464809631278720581504223 11197214446918080872256335)
      ·
        refine ⟨16795821670377121308384503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197214446918080872256335 16795821670377121308384503)
        ·
          refine ⟨25193732505565681962576755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16795821670377121308384503 25193732505565681962576755)
          ·
            refine ⟨37790598758348522943865133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25193732505565681962576755 37790598758348522943865133)
            ·
              refine ⟨14171474534380696103949425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37790598758348522943865133 14171474534380696103949425)
              ·
                refine ⟨10628605900785522077962069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14171474534380696103949425 10628605900785522077962069)
                ·
                  refine ⟨62276987699915168425559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10628605900785522077962069 62276987699915168425559)
                  ·
                    rfl

theorem cell23_1091556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1091556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091556 prefixEnd_1091556 := by exact prefixLift 1091556
  have htrace : WordTrace (prefixWord ++ tailWord_1091556) baseStart_1091556 baseEnd_1091556 := by
    simpa [prefixWord, tailWord_1091556, baseEnd_1091556] using wordTrace_append hprefix tailTrace_1091556
  have hstable : (prefixWord ++ tailWord_1091556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091556).length < 2 ^ (prefixWord ++ tailWord_1091556).sum := by decide
  have hdescent : baseEnd_1091556 < baseStart_1091556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091624 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 7]
def baseStart_1091624 : Nat := 118140960795 + 1091624 * 2 ^ 59
def prefixEnd_1091624 : Nat := 4983230072969 + 3 ^ 40 * 1091624 * 2
def baseEnd_1091624 : Nat := 62280867331526916642191

theorem tailTrace_1091624 : CollatzResearch.WordTrace tailWord_1091624 prefixEnd_1091624 62280867331526916642191 := by
  unfold tailWord_1091624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19907399098620078690748963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26543198798160104920998617 19907399098620078690748963)
  ·
    refine ⟨29861098647930118036123445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19907399098620078690748963 29861098647930118036123445)
    ·
      refine ⟨2799477998243448565886573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29861098647930118036123445 2799477998243448565886573)
      ·
        refine ⟨1049804249341293212207465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2799477998243448565886573 1049804249341293212207465)
        ·
          refine ⟨787353187005969909155599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1049804249341293212207465 787353187005969909155599)
          ·
            refine ⟨1181029780508954863733399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787353187005969909155599 1181029780508954863733399)
            ·
              refine ⟨1771544670763432295600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181029780508954863733399 1771544670763432295600099)
              ·
                refine ⟨2657317006145148443400149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771544670763432295600099 2657317006145148443400149)
                ·
                  refine ⟨62280867331526916642191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2657317006145148443400149 62280867331526916642191)
                  ·
                    rfl

theorem cell23_1091624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_1091624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091624 prefixEnd_1091624 := by exact prefixLift 1091624
  have htrace : WordTrace (prefixWord ++ tailWord_1091624) baseStart_1091624 baseEnd_1091624 := by
    simpa [prefixWord, tailWord_1091624, baseEnd_1091624] using wordTrace_append hprefix tailTrace_1091624
  have hstable : (prefixWord ++ tailWord_1091624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091624).length < 2 ^ (prefixWord ++ tailWord_1091624).sum := by decide
  have hdescent : baseEnd_1091624 < baseStart_1091624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091630 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1091630 : Nat := 118140960795 + 1091630 * 2 ^ 59
def prefixEnd_1091630 : Nat := 4983230072969 + 3 ^ 40 * 1091630 * 2
def baseEnd_1091630 : Nat := 560530886867669226304691

theorem tailTrace_1091630 : CollatzResearch.WordTrace tailWord_1091630 prefixEnd_1091630 560530886867669226304691 := by
  unfold tailWord_1091630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976877129402302550777043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26543344690145613604144229 4976877129402302550777043)
  ·
    refine ⟨7465315694103453826165565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976877129402302550777043 7465315694103453826165565)
    ·
      refine ⟨2799493385288795184812087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7465315694103453826165565 2799493385288795184812087)
      ·
        refine ⟨4199240077933192777218131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799493385288795184812087 4199240077933192777218131)
        ·
          refine ⟨6298860116899789165827197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4199240077933192777218131 6298860116899789165827197)
          ·
            refine ⟨2362072543837420937185199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6298860116899789165827197 2362072543837420937185199)
            ·
              refine ⟨3543108815756131405777799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362072543837420937185199 3543108815756131405777799)
              ·
                refine ⟨5314663223634197108666699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543108815756131405777799 5314663223634197108666699)
                ·
                  refine ⟨7971994835451295663000049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314663223634197108666699 7971994835451295663000049)
                  ·
                    refine ⟨5978996126588471747250037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7971994835451295663000049 5978996126588471747250037)
                    ·
                      refine ⟨560530886867669226304691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5978996126588471747250037 560530886867669226304691)
                      ·
                        rfl

theorem cell23_1091630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1091630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091630 prefixEnd_1091630 := by exact prefixLift 1091630
  have htrace : WordTrace (prefixWord ++ tailWord_1091630) baseStart_1091630 baseEnd_1091630 := by
    simpa [prefixWord, tailWord_1091630, baseEnd_1091630] using wordTrace_append hprefix tailTrace_1091630
  have hstable : (prefixWord ++ tailWord_1091630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091630).length < 2 ^ (prefixWord ++ tailWord_1091630).sum := by decide
  have hdescent : baseEnd_1091630 < baseStart_1091630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091660 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1091660 : Nat := 118140960795 + 1091660 * 2 ^ 59
def prefixEnd_1091660 : Nat := 4983230072969 + 3 ^ 40 * 1091660 * 2
def baseEnd_1091660 : Nat := 560546291287304108929553

theorem tailTrace_1091660 : CollatzResearch.WordTrace tailWord_1091660 prefixEnd_1091660 560546291287304108929553 := by
  unfold tailWord_1091660
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908055612554867764904217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26544074150073157019872289 19908055612554867764904217)
  ·
    refine ⟨14931041709416150823678163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19908055612554867764904217 14931041709416150823678163)
    ·
      refine ⟨22396562564124226235517245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14931041709416150823678163 22396562564124226235517245)
      ·
        refine ⟨8398710961546584838318967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22396562564124226235517245 8398710961546584838318967)
        ·
          refine ⟨12598066442319877257478451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398710961546584838318967 12598066442319877257478451)
          ·
            refine ⟨18897099663479815886217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598066442319877257478451 18897099663479815886217677)
            ·
              refine ⟨7086412373804930957331629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18897099663479815886217677 7086412373804930957331629)
              ·
                refine ⟨2657404640176849108999361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7086412373804930957331629 2657404640176849108999361)
                ·
                  refine ⟨1993053480132636831749521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657404640176849108999361 1993053480132636831749521)
                  ·
                    refine ⟨1494790110099477623812141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993053480132636831749521 1494790110099477623812141)
                    ·
                      refine ⟨560546291287304108929553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494790110099477623812141 560546291287304108929553)
                      ·
                        rfl

theorem cell23_1091660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1091660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091660 prefixEnd_1091660 := by exact prefixLift 1091660
  have htrace : WordTrace (prefixWord ++ tailWord_1091660) baseStart_1091660 baseEnd_1091660 := by
    simpa [prefixWord, tailWord_1091660, baseEnd_1091660] using wordTrace_append hprefix tailTrace_1091660
  have hstable : (prefixWord ++ tailWord_1091660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091660).length < 2 ^ (prefixWord ++ tailWord_1091660).sum := by decide
  have hdescent : baseEnd_1091660 < baseStart_1091660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091680 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 6]
def baseStart_1091680 : Nat := 118140960795 + 1091680 * 2 ^ 59
def prefixEnd_1091680 : Nat := 4983230072969 + 3 ^ 40 * 1091680 * 2
def baseEnd_1091680 : Nat := 62284062322266003408829

theorem tailTrace_1091680 : CollatzResearch.WordTrace tailWord_1091680 prefixEnd_1091680 62284062322266003408829 := by
  unfold tailWord_1091680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908420342518639472768247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26544560456691519297024329 19908420342518639472768247)
  ·
    refine ⟨29862630513777959209152371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19908420342518639472768247 29862630513777959209152371)
    ·
      refine ⟨44793945770666938813728557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29862630513777959209152371 44793945770666938813728557)
      ·
        refine ⟨16797729664000102055148209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44793945770666938813728557 16797729664000102055148209)
        ·
          refine ⟨12598297248000076541361157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16797729664000102055148209 12598297248000076541361157)
          ·
            refine ⟨2362180734000014351505217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12598297248000076541361157 2362180734000014351505217)
            ·
              refine ⟨1771635550500010763628913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362180734000014351505217 1771635550500010763628913)
              ·
                refine ⟨1328726662875008072721685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771635550500010763628913 1328726662875008072721685)
                ·
                  refine ⟨62284062322266003408829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1328726662875008072721685 62284062322266003408829)
                  ·
                    rfl

theorem cell23_1091680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_1091680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091680 prefixEnd_1091680 := by exact prefixLift 1091680
  have htrace : WordTrace (prefixWord ++ tailWord_1091680) baseStart_1091680 baseEnd_1091680 := by
    simpa [prefixWord, tailWord_1091680, baseEnd_1091680] using wordTrace_append hprefix tailTrace_1091680
  have hstable : (prefixWord ++ tailWord_1091680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091680).length < 2 ^ (prefixWord ++ tailWord_1091680).sum := by decide
  have hdescent : baseEnd_1091680 < baseStart_1091680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091684 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1091684 : Nat := 118140960795 + 1091684 * 2 ^ 59
def prefixEnd_1091684 : Nat := 4983230072969 + 3 ^ 40 * 1091684 * 2
def baseEnd_1091684 : Nat := 186852871607670671676481

theorem tailTrace_1091684 : CollatzResearch.WordTrace tailWord_1091684 prefixEnd_1091684 186852871607670671676481 := by
  unfold tailWord_1091684
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908493288511393814341053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26544657718015191752454737 19908493288511393814341053)
  ·
    refine ⟨7465684983191772680377895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19908493288511393814341053 7465684983191772680377895)
    ·
      refine ⟨11198527474787659020566843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465684983191772680377895 11198527474787659020566843)
      ·
        refine ⟨16797791212181488530850265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11198527474787659020566843 16797791212181488530850265)
        ·
          refine ⟨12598343409136116398137699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16797791212181488530850265 12598343409136116398137699)
          ·
            refine ⟨18897515113704174597206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598343409136116398137699 18897515113704174597206549)
            ·
              refine ⟨885821020954883184244057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18897515113704174597206549 885821020954883184244057)
              ·
                refine ⟨664365765716162388183043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885821020954883184244057 664365765716162388183043)
                ·
                  refine ⟨996548648574243582274565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664365765716162388183043 996548648574243582274565)
                  ·
                    refine ⟨186852871607670671676481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996548648574243582274565 186852871607670671676481)
                    ·
                      rfl

theorem cell23_1091684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1091684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091684 prefixEnd_1091684 := by exact prefixLift 1091684
  have htrace : WordTrace (prefixWord ++ tailWord_1091684) baseStart_1091684 baseEnd_1091684 := by
    simpa [prefixWord, tailWord_1091684, baseEnd_1091684] using wordTrace_append hprefix tailTrace_1091684
  have hstable : (prefixWord ++ tailWord_1091684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091684).length < 2 ^ (prefixWord ++ tailWord_1091684).sum := by decide
  have hdescent : baseEnd_1091684 < baseStart_1091684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091717 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_1091717 : Nat := 118140960795 + 1091717 * 2 ^ 59
def prefixEnd_1091717 : Nat := 4983230072969 + 3 ^ 40 * 1091717 * 2
def baseEnd_1091717 : Nat := 560575559684610385916791

theorem tailTrace_1091717 : CollatzResearch.WordTrace tailWord_1091717 prefixEnd_1091717 560575559684610385916791 := by
  unfold tailWord_1091717
  simp only [CollatzResearch.WordTrace]
  refine ⟨39818190185903234264633405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26545460123935489509755603 39818190185903234264633405)
  ·
    refine ⟨14931821319713712849237527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39818190185903234264633405 14931821319713712849237527)
    ·
      refine ⟨22397731979570569273856291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14931821319713712849237527 22397731979570569273856291)
      ·
        refine ⟨33596597969355853910784437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22397731979570569273856291 33596597969355853910784437)
        ·
          refine ⟨3149681059627111304136041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33596597969355853910784437 3149681059627111304136041)
          ·
            refine ⟨2362260794720333478102031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149681059627111304136041 2362260794720333478102031)
            ·
              refine ⟨3543391192080500217153047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362260794720333478102031 3543391192080500217153047)
              ·
                refine ⟨5315086788120750325729571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543391192080500217153047 5315086788120750325729571)
                ·
                  refine ⟨7972630182181125488594357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5315086788120750325729571 7972630182181125488594357)
                  ·
                    refine ⟨747434079579480514555721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7972630182181125488594357 747434079579480514555721)
                    ·
                      refine ⟨560575559684610385916791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747434079579480514555721 560575559684610385916791)
                      ·
                        rfl

theorem cell23_1091717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_1091717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091717 prefixEnd_1091717 := by exact prefixLift 1091717
  have htrace : WordTrace (prefixWord ++ tailWord_1091717) baseStart_1091717 baseEnd_1091717 := by
    simpa [prefixWord, tailWord_1091717, baseEnd_1091717] using wordTrace_append hprefix tailTrace_1091717
  have hstable : (prefixWord ++ tailWord_1091717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091717).length < 2 ^ (prefixWord ++ tailWord_1091717).sum := by decide
  have hdescent : baseEnd_1091717 < baseStart_1091717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091757 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1091757 : Nat := 118140960795 + 1091757 * 2 ^ 59
def prefixEnd_1091757 : Nat := 4983230072969 + 3 ^ 40 * 1091757 * 2
def baseEnd_1091757 : Nat := 186865366303596743138869

theorem tailTrace_1091757 : CollatzResearch.WordTrace tailWord_1091757 prefixEnd_1091757 186865366303596743138869 := by
  unfold tailWord_1091757
  simp only [CollatzResearch.WordTrace]
  refine ⟨39819649105758321096089525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26546432737172214064059683 39819649105758321096089525)
  ·
    refine ⟨3733092103664842602758393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39819649105758321096089525 3733092103664842602758393)
    ·
      refine ⟨2799819077748631952068795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3733092103664842602758393 2799819077748631952068795)
      ·
        refine ⟨4199728616622947928103193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799819077748631952068795 4199728616622947928103193)
        ·
          refine ⟨3149796462467210946077395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199728616622947928103193 3149796462467210946077395)
          ·
            refine ⟨4724694693700816419116093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149796462467210946077395 4724694693700816419116093)
            ·
              refine ⟨1771760510137806157168535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4724694693700816419116093 1771760510137806157168535)
              ·
                refine ⟨2657640765206709235752803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771760510137806157168535 2657640765206709235752803)
                ·
                  refine ⟨3986461147810063853629205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657640765206709235752803 3986461147810063853629205)
                  ·
                    refine ⟨186865366303596743138869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3986461147810063853629205 186865366303596743138869)
                    ·
                      rfl

theorem cell23_1091757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1091757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091757 prefixEnd_1091757 := by exact prefixLift 1091757
  have htrace : WordTrace (prefixWord ++ tailWord_1091757) baseStart_1091757 baseEnd_1091757 := by
    simpa [prefixWord, tailWord_1091757, baseEnd_1091757] using wordTrace_append hprefix tailTrace_1091757
  have hstable : (prefixWord ++ tailWord_1091757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091757).length < 2 ^ (prefixWord ++ tailWord_1091757).sum := by decide
  have hdescent : baseEnd_1091757 < baseStart_1091757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091767 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_1091767 : Nat := 118140960795 + 1091767 * 2 ^ 59
def prefixEnd_1091767 : Nat := 4983230072969 + 3 ^ 40 * 1091767 * 2
def baseEnd_1091767 : Nat := 560601233717335190291561

theorem tailTrace_1091767 : CollatzResearch.WordTrace tailWord_1091767 prefixEnd_1091767 560601233717335190291561 := by
  unfold tailWord_1091767
  simp only [CollatzResearch.WordTrace]
  refine ⟨39820013835722092803953555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26546675890481395202635703 39820013835722092803953555)
  ·
    refine ⟨59730020753583139205930333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39820013835722092803953555 59730020753583139205930333)
    ·
      refine ⟨22398757782593677202223875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59730020753583139205930333 22398757782593677202223875)
      ·
        refine ⟨33598136673890515803335813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22398757782593677202223875 33598136673890515803335813)
        ·
          refine ⟨6299650626354471713125465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33598136673890515803335813 6299650626354471713125465)
          ·
            refine ⟨4724737969765853784844099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6299650626354471713125465 4724737969765853784844099)
            ·
              refine ⟨7087106954648780677266149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724737969765853784844099 7087106954648780677266149)
              ·
                refine ⟨1328832553996646376987403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7087106954648780677266149 1328832553996646376987403)
                ·
                  refine ⟨1993248830994969565481105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328832553996646376987403 1993248830994969565481105)
                  ·
                    refine ⟨1494936623246227174110829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993248830994969565481105 1494936623246227174110829)
                    ·
                      refine ⟨560601233717335190291561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1494936623246227174110829 560601233717335190291561)
                      ·
                        rfl

theorem cell23_1091767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_1091767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091767 prefixEnd_1091767 := by exact prefixLift 1091767
  have htrace : WordTrace (prefixWord ++ tailWord_1091767) baseStart_1091767 baseEnd_1091767 := by
    simpa [prefixWord, tailWord_1091767, baseEnd_1091767] using wordTrace_append hprefix tailTrace_1091767
  have hstable : (prefixWord ++ tailWord_1091767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091767).length < 2 ^ (prefixWord ++ tailWord_1091767).sum := by decide
  have hdescent : baseEnd_1091767 < baseStart_1091767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091770 : List Nat := [3, 1, 1, 1, 2, 2, 6, 7]
def baseStart_1091770 : Nat := 118140960795 + 1091770 * 2 ^ 59
def prefixEnd_1091770 : Nat := 4983230072969 + 3 ^ 40 * 1091770 * 2
def baseEnd_1091770 : Nat := 20763065709603654761261

theorem tailTrace_1091770 : CollatzResearch.WordTrace tailWord_1091770 prefixEnd_1091770 20763065709603654761261 := by
  unfold tailWord_1091770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955030813677806079078191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26546748836474149544208509 9955030813677806079078191)
  ·
    refine ⟨14932546220516709118617287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9955030813677806079078191 14932546220516709118617287)
    ·
      refine ⟨22398819330775063677925931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14932546220516709118617287 22398819330775063677925931)
      ·
        refine ⟨33598228996162595516888897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22398819330775063677925931 33598228996162595516888897)
        ·
          refine ⟨25198671747121946637666673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33598228996162595516888897 25198671747121946637666673)
          ·
            refine ⟨18899003810341459978250005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25198671747121946637666673 18899003810341459978250005)
            ·
              refine ⟨885890803609755936480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18899003810341459978250005 885890803609755936480469)
              ·
                refine ⟨20763065709603654761261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 885890803609755936480469 20763065709603654761261)
                ·
                  rfl

theorem cell23_1091770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_1091770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091770 prefixEnd_1091770 := by exact prefixLift 1091770
  have htrace : WordTrace (prefixWord ++ tailWord_1091770) baseStart_1091770 baseEnd_1091770 := by
    simpa [prefixWord, tailWord_1091770, baseEnd_1091770] using wordTrace_append hprefix tailTrace_1091770
  have hstable : (prefixWord ++ tailWord_1091770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091770).length < 2 ^ (prefixWord ++ tailWord_1091770).sum := by decide
  have hdescent : baseEnd_1091770 < baseStart_1091770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091781 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_1091781 : Nat := 118140960795 + 1091781 * 2 ^ 59
def prefixEnd_1091781 : Nat := 4983230072969 + 3 ^ 40 * 1091781 * 2
def baseEnd_1091781 : Nat := 560608422446498135516497

theorem tailTrace_1091781 : CollatzResearch.WordTrace tailWord_1091781 prefixEnd_1091781 560608422446498135516497 := by
  unfold tailWord_1091781
  simp only [CollatzResearch.WordTrace]
  refine ⟨39820524457671373194963197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547016305114248796642131 39820524457671373194963197)
  ·
    refine ⟨14932696671626764948111199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39820524457671373194963197 14932696671626764948111199)
    ·
      refine ⟨22399045007440147422166799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14932696671626764948111199 22399045007440147422166799)
      ·
        refine ⟨33598567511160221133250199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22399045007440147422166799 33598567511160221133250199)
        ·
          refine ⟨50397851266740331699875299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33598567511160221133250199 50397851266740331699875299)
          ·
            refine ⟨75596776900110497549812949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50397851266740331699875299 75596776900110497549812949)
            ·
              refine ⟨1771799458596339786323741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75596776900110497549812949 1771799458596339786323741)
              ·
                refine ⟨664424796973627419871403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1771799458596339786323741 664424796973627419871403)
                ·
                  refine ⟨996637195460441129807105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664424796973627419871403 996637195460441129807105)
                  ·
                    refine ⟨747477896595330847355329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996637195460441129807105 747477896595330847355329)
                    ·
                      refine ⟨560608422446498135516497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747477896595330847355329 560608422446498135516497)
                      ·
                        rfl

theorem cell23_1091781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_1091781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091781 prefixEnd_1091781 := by exact prefixLift 1091781
  have htrace : WordTrace (prefixWord ++ tailWord_1091781) baseStart_1091781 baseEnd_1091781 := by
    simpa [prefixWord, tailWord_1091781, baseEnd_1091781] using wordTrace_append hprefix tailTrace_1091781
  have hstable : (prefixWord ++ tailWord_1091781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091781).length < 2 ^ (prefixWord ++ tailWord_1091781).sum := by decide
  have hdescent : baseEnd_1091781 < baseStart_1091781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091783 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1091783 : Nat := 118140960795 + 1091783 * 2 ^ 59
def prefixEnd_1091783 : Nat := 4983230072969 + 3 ^ 40 * 1091783 * 2
def baseEnd_1091783 : Nat := 186869816469269042563829

theorem tailTrace_1091783 : CollatzResearch.WordTrace tailWord_1091783 prefixEnd_1091783 186869816469269042563829 := by
  unfold tailWord_1091783
  simp only [CollatzResearch.WordTrace]
  refine ⟨39820597403664127536536003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547064935776085024357335 39820597403664127536536003)
  ·
    refine ⟨59730896105496191304804005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39820597403664127536536003 59730896105496191304804005)
    ·
      refine ⟨11199543019780535869650751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59730896105496191304804005 11199543019780535869650751)
      ·
        refine ⟨16799314529670803804476127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11199543019780535869650751 16799314529670803804476127)
        ·
          refine ⟨25198971794506205706714191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16799314529670803804476127 25198971794506205706714191)
          ·
            refine ⟨37798457691759308560071287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25198971794506205706714191 37798457691759308560071287)
            ·
              refine ⟨56697686537638962840106931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37798457691759308560071287 56697686537638962840106931)
              ·
                refine ⟨85046529806458444260160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56697686537638962840106931 85046529806458444260160397)
                ·
                  refine ⟨31892448677421916597560149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85046529806458444260160397 31892448677421916597560149)
                  ·
                    refine ⟨186869816469269042563829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31892448677421916597560149 186869816469269042563829)
                    ·
                      rfl

theorem cell23_1091783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1091783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091783 prefixEnd_1091783 := by exact prefixLift 1091783
  have htrace : WordTrace (prefixWord ++ tailWord_1091783) baseStart_1091783 baseEnd_1091783 := by
    simpa [prefixWord, tailWord_1091783, baseEnd_1091783] using wordTrace_append hprefix tailTrace_1091783
  have hstable : (prefixWord ++ tailWord_1091783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091783).length < 2 ^ (prefixWord ++ tailWord_1091783).sum := by decide
  have hdescent : baseEnd_1091783 < baseStart_1091783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091798 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1091798 : Nat := 118140960795 + 1091798 * 2 ^ 59
def prefixEnd_1091798 : Nat := 4983230072969 + 3 ^ 40 * 1091798 * 2
def baseEnd_1091798 : Nat := 560617151617624569003919

theorem tailTrace_1091798 : CollatzResearch.WordTrace tailWord_1091798 prefixEnd_1091798 560617151617624569003919 := by
  unfold tailWord_1091798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488821531163111568645753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26547429665739856732221365 2488821531163111568645753)
  ·
    refine ⟨1866616148372333676484315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2488821531163111568645753 1866616148372333676484315)
    ·
      refine ⟨2799924222558500514726473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866616148372333676484315 2799924222558500514726473)
      ·
        refine ⟨2099943166918875386044855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799924222558500514726473 2099943166918875386044855)
        ·
          refine ⟨3149914750378313079067283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099943166918875386044855 3149914750378313079067283)
          ·
            refine ⟨4724872125567469618600925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149914750378313079067283 4724872125567469618600925)
            ·
              refine ⟨1771827047087801106975347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4724872125567469618600925 1771827047087801106975347)
              ·
                refine ⟨2657740570631701660463021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771827047087801106975347 2657740570631701660463021)
                ·
                  refine ⟨996652713986888122673633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2657740570631701660463021 996652713986888122673633)
                  ·
                    refine ⟨747489535490166092005225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996652713986888122673633 747489535490166092005225)
                    ·
                      refine ⟨560617151617624569003919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747489535490166092005225 560617151617624569003919)
                      ·
                        rfl

theorem cell23_1091798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1091798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091798 prefixEnd_1091798 := by exact prefixLift 1091798
  have htrace : WordTrace (prefixWord ++ tailWord_1091798) baseStart_1091798 baseEnd_1091798 := by
    simpa [prefixWord, tailWord_1091798, baseEnd_1091798] using wordTrace_append hprefix tailTrace_1091798
  have hstable : (prefixWord ++ tailWord_1091798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091798).length < 2 ^ (prefixWord ++ tailWord_1091798).sum := by decide
  have hdescent : baseEnd_1091798 < baseStart_1091798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091804 : List Nat := [2, 2, 5, 2, 1, 1, 2, 8]
def baseStart_1091804 : Nat := 118140960795 + 1091804 * 2 ^ 59
def prefixEnd_1091804 : Nat := 4983230072969 + 3 ^ 40 * 1091804 * 2
def baseEnd_1091804 : Nat := 20763712314872279464033

theorem tailTrace_1091804 : CollatzResearch.WordTrace tailWord_1091804 prefixEnd_1091804 20763712314872279464033 := by
  unfold tailWord_1091804
  simp only [CollatzResearch.WordTrace]
  refine ⟨19910681668294024061525233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26547575557725365415366977 19910681668294024061525233)
  ·
    refine ⟨14933011251220518046143925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19910681668294024061525233 14933011251220518046143925)
    ·
      refine ⟨1399969804801923566825993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14933011251220518046143925 1399969804801923566825993)
      ·
        refine ⟨1049977353601442675119495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399969804801923566825993 1049977353601442675119495)
        ·
          refine ⟨1574966030402164012679243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049977353601442675119495 1574966030402164012679243)
          ·
            refine ⟨2362449045603246019018865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574966030402164012679243 2362449045603246019018865)
            ·
              refine ⟨1771836784202434514264149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362449045603246019018865 1771836784202434514264149)
              ·
                refine ⟨20763712314872279464033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1771836784202434514264149 20763712314872279464033)
                ·
                  rfl

theorem cell23_1091804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 8].length) (baseStart_1091804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091804 prefixEnd_1091804 := by exact prefixLift 1091804
  have htrace : WordTrace (prefixWord ++ tailWord_1091804) baseStart_1091804 baseEnd_1091804 := by
    simpa [prefixWord, tailWord_1091804, baseEnd_1091804] using wordTrace_append hprefix tailTrace_1091804
  have hstable : (prefixWord ++ tailWord_1091804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091804).length < 2 ^ (prefixWord ++ tailWord_1091804).sum := by decide
  have hdescent : baseEnd_1091804 < baseStart_1091804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 3, 3, 2]
def baseStart_1091807 : Nat := 118140960795 + 1091807 * 2 ^ 59
def prefixEnd_1091807 : Nat := 4983230072969 + 3 ^ 40 * 1091807 * 2
def baseEnd_1091807 : Nat := 560621772943515033791377

theorem tailTrace_1091807 : CollatzResearch.WordTrace tailWord_1091807 prefixEnd_1091807 560621772943515033791377 := by
  unfold tailWord_1091807
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821472755577179635409675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547648503718119756939783 39821472755577179635409675)
  ·
    refine ⟨59732209133365769453114513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39821472755577179635409675 59732209133365769453114513)
    ·
      refine ⟨44799156850024327089835885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59732209133365769453114513 44799156850024327089835885)
      ·
        refine ⟨16799683818759122658688457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44799156850024327089835885 16799683818759122658688457)
        ·
          refine ⟨12599762864069341994016343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16799683818759122658688457 12599762864069341994016343)
          ·
            refine ⟨18899644296104012991024515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599762864069341994016343 18899644296104012991024515)
            ·
              refine ⟨28349466444156019486536773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899644296104012991024515 28349466444156019486536773)
              ·
                refine ⟨5315524958279253653725645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28349466444156019486536773 5315524958279253653725645)
                ·
                  refine ⟨1993321859354720120147117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5315524958279253653725645 1993321859354720120147117)
                  ·
                    refine ⟨747495697258020045055169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993321859354720120147117 747495697258020045055169)
                    ·
                      refine ⟨560621772943515033791377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747495697258020045055169 560621772943515033791377)
                      ·
                        rfl

theorem cell23_1091807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_1091807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091807 prefixEnd_1091807 := by exact prefixLift 1091807
  have htrace : WordTrace (prefixWord ++ tailWord_1091807) baseStart_1091807 baseEnd_1091807 := by
    simpa [prefixWord, tailWord_1091807, baseEnd_1091807] using wordTrace_append hprefix tailTrace_1091807
  have hstable : (prefixWord ++ tailWord_1091807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091807).length < 2 ^ (prefixWord ++ tailWord_1091807).sum := by decide
  have hdescent : baseEnd_1091807 < baseStart_1091807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091840 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1091840 : Nat := 118140960795 + 1091840 * 2 ^ 59
def prefixEnd_1091840 : Nat := 4983230072969 + 3 ^ 40 * 1091840 * 2
def baseEnd_1091840 : Nat := 560638717805113404678725

theorem tailTrace_1091840 : CollatzResearch.WordTrace tailWord_1091840 prefixEnd_1091840 560638717805113404678725 := by
  unfold tailWord_1091840
  simp only [CollatzResearch.WordTrace]
  refine ⟨19911338182228813135680487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26548450909638417514240649 19911338182228813135680487)
  ·
    refine ⟨29867007273343219703520731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19911338182228813135680487 29867007273343219703520731)
    ·
      refine ⟨44800510910014829555281097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29867007273343219703520731 44800510910014829555281097)
      ·
        refine ⟨33600383182511122166460823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44800510910014829555281097 33600383182511122166460823)
        ·
          refine ⟨50400574773766683249691235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33600383182511122166460823 50400574773766683249691235)
          ·
            refine ⟨75600862160650024874536853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50400574773766683249691235 75600862160650024874536853)
            ·
              refine ⟨3543790413780469915993915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75600862160650024874536853 3543790413780469915993915)
              ·
                refine ⟨5315685620670704873990873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543790413780469915993915 5315685620670704873990873)
                ·
                  refine ⟨3986764215503028655493155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5315685620670704873990873 3986764215503028655493155)
                  ·
                    refine ⟨5980146323254542983239733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986764215503028655493155 5980146323254542983239733)
                    ·
                      refine ⟨560638717805113404678725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5980146323254542983239733 560638717805113404678725)
                      ·
                        rfl

theorem cell23_1091840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1091840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091840 prefixEnd_1091840 := by exact prefixLift 1091840
  have htrace : WordTrace (prefixWord ++ tailWord_1091840) baseStart_1091840 baseEnd_1091840 := by
    simpa [prefixWord, tailWord_1091840, baseEnd_1091840] using wordTrace_append hprefix tailTrace_1091840
  have hstable : (prefixWord ++ tailWord_1091840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091840).length < 2 ^ (prefixWord ++ tailWord_1091840).sum := by decide
  have hdescent : baseEnd_1091840 < baseStart_1091840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091841 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1091841 : Nat := 118140960795 + 1091841 * 2 ^ 59
def prefixEnd_1091841 : Nat := 4983230072969 + 3 ^ 40 * 1091841 * 2
def baseEnd_1091841 : Nat := 560639231285767900766221

theorem tailTrace_1091841 : CollatzResearch.WordTrace tailWord_1091841 prefixEnd_1091841 560639231285767900766221 := by
  unfold tailWord_1091841
  simp only [CollatzResearch.WordTrace]
  refine ⟨39822712837454003442147377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26548475224969335628098251 39822712837454003442147377)
  ·
    refine ⟨29867034628090502581610533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39822712837454003442147377 29867034628090502581610533)
    ·
      refine ⟨5600068992766969234051975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29867034628090502581610533 5600068992766969234051975)
      ·
        refine ⟨8400103489150453851077963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600068992766969234051975 8400103489150453851077963)
        ·
          refine ⟨12600155233725680776616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8400103489150453851077963 12600155233725680776616945)
          ·
            refine ⟨9450116425294260582462709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12600155233725680776616945 9450116425294260582462709)
            ·
              refine ⟨885948414871336929605879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9450116425294260582462709 885948414871336929605879)
              ·
                refine ⟨1328922622307005394408819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885948414871336929605879 1328922622307005394408819)
                ·
                  refine ⟨1993383933460508091613229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328922622307005394408819 1993383933460508091613229)
                  ·
                    refine ⟨747518975047690534354961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993383933460508091613229 747518975047690534354961)
                    ·
                      refine ⟨560639231285767900766221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747518975047690534354961 560639231285767900766221)
                      ·
                        rfl

theorem cell23_1091841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1091841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091841 prefixEnd_1091841 := by exact prefixLift 1091841
  have htrace : WordTrace (prefixWord ++ tailWord_1091841) baseStart_1091841 baseEnd_1091841 := by
    simpa [prefixWord, tailWord_1091841, baseEnd_1091841] using wordTrace_append hprefix tailTrace_1091841
  have hstable : (prefixWord ++ tailWord_1091841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091841).length < 2 ^ (prefixWord ++ tailWord_1091841).sum := by decide
  have hdescent : baseEnd_1091841 < baseStart_1091841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091871 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 2, 2, 2]
def baseStart_1091871 : Nat := 118140960795 + 1091871 * 2 ^ 59
def prefixEnd_1091871 : Nat := 4983230072969 + 3 ^ 40 * 1091871 * 2
def baseEnd_1091871 : Nat := 560654635705402783391083

theorem tailTrace_1091871 : CollatzResearch.WordTrace tailWord_1091871 prefixEnd_1091871 560654635705402783391083 := by
  unfold tailWord_1091871
  simp only [CollatzResearch.WordTrace]
  refine ⟨39823807027345318565739467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26549204684896879043826311 39823807027345318565739467)
  ·
    refine ⟨59735710541017977848609201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39823807027345318565739467 59735710541017977848609201)
    ·
      refine ⟨44801782905763483386456901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59735710541017977848609201 44801782905763483386456901)
      ·
        refine ⟨8400334294830653134960669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44801782905763483386456901 8400334294830653134960669)
        ·
          refine ⟨3150125360561494925610251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8400334294830653134960669 3150125360561494925610251)
          ·
            refine ⟨4725188040842242388415377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150125360561494925610251 4725188040842242388415377)
            ·
              refine ⟨3543891030631681791311533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4725188040842242388415377 3543891030631681791311533)
              ·
                refine ⟨1328959136486880671741825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3543891030631681791311533 1328959136486880671741825)
                ·
                  refine ⟨996719352365160503806369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328959136486880671741825 996719352365160503806369)
                  ·
                    refine ⟨747539514273870377854777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996719352365160503806369 747539514273870377854777)
                    ·
                      refine ⟨560654635705402783391083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747539514273870377854777 560654635705402783391083)
                      ·
                        rfl

theorem cell23_1091871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_1091871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091871 prefixEnd_1091871 := by exact prefixLift 1091871
  have htrace : WordTrace (prefixWord ++ tailWord_1091871) baseStart_1091871 baseEnd_1091871 := by
    simpa [prefixWord, tailWord_1091871, baseEnd_1091871] using wordTrace_append hprefix tailTrace_1091871
  have hstable : (prefixWord ++ tailWord_1091871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091871).length < 2 ^ (prefixWord ++ tailWord_1091871).sum := by decide
  have hdescent : baseEnd_1091871 < baseStart_1091871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091877 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 7]
def baseStart_1091877 : Nat := 118140960795 + 1091877 * 2 ^ 59
def prefixEnd_1091877 : Nat := 4983230072969 + 3 ^ 40 * 1091877 * 2
def baseEnd_1091877 : Nat := 62295301843258862212895

theorem tailTrace_1091877 : CollatzResearch.WordTrace tailWord_1091877 prefixEnd_1091877 62295301843258862212895 := by
  unfold tailWord_1091877
  simp only [CollatzResearch.WordTrace]
  refine ⟨39824025865323581590457885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26549350576882387726971923 39824025865323581590457885)
  ·
    refine ⟨14934009699496343096421707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39824025865323581590457885 14934009699496343096421707)
    ·
      refine ⟨22401014549244514644632561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14934009699496343096421707 22401014549244514644632561)
      ·
        refine ⟨16800760911933385983474421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22401014549244514644632561 16800760911933385983474421)
        ·
          refine ⟨1575071335493754935950727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16800760911933385983474421 1575071335493754935950727)
          ·
            refine ⟨2362607003240632403926091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575071335493754935950727 2362607003240632403926091)
            ·
              refine ⟨3543910504860948605889137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362607003240632403926091 3543910504860948605889137)
              ·
                refine ⟨2657932878645711454416853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543910504860948605889137 2657932878645711454416853)
                ·
                  refine ⟨62295301843258862212895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2657932878645711454416853 62295301843258862212895)
                  ·
                    rfl

theorem cell23_1091877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_1091877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091877 prefixEnd_1091877 := by exact prefixLift 1091877
  have htrace : WordTrace (prefixWord ++ tailWord_1091877) baseStart_1091877 baseEnd_1091877 := by
    simpa [prefixWord, tailWord_1091877, baseEnd_1091877] using wordTrace_append hprefix tailTrace_1091877
  have hstable : (prefixWord ++ tailWord_1091877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091877).length < 2 ^ (prefixWord ++ tailWord_1091877).sum := by decide
  have hdescent : baseEnd_1091877 < baseStart_1091877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091905 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1091905 : Nat := 118140960795 + 1091905 * 2 ^ 59
def prefixEnd_1091905 : Nat := 4983230072969 + 3 ^ 40 * 1091905 * 2
def baseEnd_1091905 : Nat := 560672094047655650365927

theorem tailTrace_1091905 : CollatzResearch.WordTrace tailWord_1091905 prefixEnd_1091905 560672094047655650365927 := by
  unfold tailWord_1091905
  simp only [CollatzResearch.WordTrace]
  refine ⟨39825047109222142372477169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26550031406148094914984779 39825047109222142372477169)
  ·
    refine ⟨29868785331916606779357877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39825047109222142372477169 29868785331916606779357877)
    ·
      refine ⟨2800198624867181885564801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29868785331916606779357877 2800198624867181885564801)
      ·
        refine ⟨2100148968650386414173601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800198624867181885564801 2100148968650386414173601)
        ·
          refine ⟨1575111726487789810630201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100148968650386414173601 1575111726487789810630201)
          ·
            refine ⟨1181333794865842357972651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575111726487789810630201 1181333794865842357972651)
            ·
              refine ⟨1772000692298763536958977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181333794865842357972651 1772000692298763536958977)
              ·
                refine ⟨1329000519224072652719233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772000692298763536958977 1329000519224072652719233)
                ·
                  refine ⟨996750389418054489539425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329000519224072652719233 996750389418054489539425)
                  ·
                    refine ⟨747562792063540867154569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996750389418054489539425 747562792063540867154569)
                    ·
                      refine ⟨560672094047655650365927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747562792063540867154569 560672094047655650365927)
                      ·
                        rfl

theorem cell23_1091905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1091905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091905 prefixEnd_1091905 := by exact prefixLift 1091905
  have htrace : WordTrace (prefixWord ++ tailWord_1091905) baseStart_1091905 baseEnd_1091905 := by
    simpa [prefixWord, tailWord_1091905, baseEnd_1091905] using wordTrace_append hprefix tailTrace_1091905
  have hstable : (prefixWord ++ tailWord_1091905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091905).length < 2 ^ (prefixWord ++ tailWord_1091905).sum := by decide
  have hdescent : baseEnd_1091905 < baseStart_1091905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091971 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 3, 4]
def baseStart_1091971 : Nat := 118140960795 + 1091971 * 2 ^ 59
def prefixEnd_1091971 : Nat := 4983230072969 + 3 ^ 40 * 1091971 * 2
def baseEnd_1091971 : Nat := 186901994590284130713541

theorem tailTrace_1091971 : CollatzResearch.WordTrace tailWord_1091971 prefixEnd_1091971 186901994590284130713541 := by
  unfold tailWord_1091971
  simp only [CollatzResearch.WordTrace]
  refine ⟨39827454326983035644379767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26551636217988690429586511 39827454326983035644379767)
  ·
    refine ⟨59741181490474553466569651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39827454326983035644379767 59741181490474553466569651)
    ·
      refine ⟨89611772235711830199854477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59741181490474553466569651 89611772235711830199854477)
      ·
        refine ⟨33604414588391936324945429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89611772235711830199854477 33604414588391936324945429)
        ·
          refine ⟨1575206933830872015231817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33604414588391936324945429 1575206933830872015231817)
          ·
            refine ⟨1181405200373154011423863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575206933830872015231817 1181405200373154011423863)
            ·
              refine ⟨1772107800559731017135795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181405200373154011423863 1772107800559731017135795)
              ·
                refine ⟨2658161700839596525703693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772107800559731017135795 2658161700839596525703693)
                ·
                  refine ⟨996810637814848697138885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2658161700839596525703693 996810637814848697138885)
                  ·
                    refine ⟨186901994590284130713541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996810637814848697138885 186901994590284130713541)
                    ·
                      rfl

theorem cell23_1091971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 4].length) (baseStart_1091971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091971 prefixEnd_1091971 := by exact prefixLift 1091971
  have htrace : WordTrace (prefixWord ++ tailWord_1091971) baseStart_1091971 baseEnd_1091971 := by
    simpa [prefixWord, tailWord_1091971, baseEnd_1091971] using wordTrace_append hprefix tailTrace_1091971
  have hstable : (prefixWord ++ tailWord_1091971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091971).length < 2 ^ (prefixWord ++ tailWord_1091971).sum := by decide
  have hdescent : baseEnd_1091971 < baseStart_1091971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091998 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1091998 : Nat := 118140960795 + 1091998 * 2 ^ 59
def prefixEnd_1091998 : Nat := 4983230072969 + 3 ^ 40 * 1091998 * 2
def baseEnd_1091998 : Nat := 560719847748523786502999

theorem tailTrace_1091998 : CollatzResearch.WordTrace tailWord_1091998 prefixEnd_1091998 560719847748523786502999 := by
  unfold tailWord_1091998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978554887235652406951581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26552292731923479503741765 4978554887235652406951581)
  ·
    refine ⟨1866958082713369652606843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4978554887235652406951581 1866958082713369652606843)
    ·
      refine ⟨2800437124070054478910265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866958082713369652606843 2800437124070054478910265)
      ·
        refine ⟨2100327843052540859182699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800437124070054478910265 2100327843052540859182699)
        ·
          refine ⟨3150491764578811288774049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100327843052540859182699 3150491764578811288774049)
          ·
            refine ⟨2362868823434108466580537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3150491764578811288774049 2362868823434108466580537)
            ·
              refine ⟨1772151617575581349935403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362868823434108466580537 1772151617575581349935403)
              ·
                refine ⟨2658227426363372024903105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772151617575581349935403 2658227426363372024903105)
                ·
                  refine ⟨1993670569772529018677329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658227426363372024903105 1993670569772529018677329)
                  ·
                    refine ⟨1495252927329396764007997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993670569772529018677329 1495252927329396764007997)
                    ·
                      refine ⟨560719847748523786502999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1495252927329396764007997 560719847748523786502999)
                      ·
                        rfl

theorem cell23_1091998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1091998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1091998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1091998 prefixEnd_1091998 := by exact prefixLift 1091998
  have htrace : WordTrace (prefixWord ++ tailWord_1091998) baseStart_1091998 baseEnd_1091998 := by
    simpa [prefixWord, tailWord_1091998, baseEnd_1091998] using wordTrace_append hprefix tailTrace_1091998
  have hstable : (prefixWord ++ tailWord_1091998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091998).length < 2 ^ (prefixWord ++ tailWord_1091998).sum := by decide
  have hdescent : baseEnd_1091998 < baseStart_1091998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092004 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_1092004 : Nat := 118140960795 + 1092004 * 2 ^ 59
def prefixEnd_1092004 : Nat := 4983230072969 + 3 ^ 40 * 1092004 * 2
def baseEnd_1092004 : Nat := 560722928632450763027971

theorem tailTrace_1092004 : CollatzResearch.WordTrace tailWord_1092004 prefixEnd_1092004 560722928632450763027971 := by
  unfold tailWord_1092004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914328967931741140165533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26552438623908988186887377 19914328967931741140165533)
  ·
    refine ⟨7467873362974402927562075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19914328967931741140165533 7467873362974402927562075)
    ·
      refine ⟨11201810044461604391343113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7467873362974402927562075 11201810044461604391343113)
      ·
        refine ⟨8401357533346203293507335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11201810044461604391343113 8401357533346203293507335)
        ·
          refine ⟨12602036300019304940261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401357533346203293507335 12602036300019304940261003)
          ·
            refine ⟨18903054450028957410391505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602036300019304940261003 18903054450028957410391505)
            ·
              refine ⟨14177290837521718057793629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18903054450028957410391505 14177290837521718057793629)
              ·
                refine ⟨5316484064070644271672611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14177290837521718057793629 5316484064070644271672611)
                ·
                  refine ⟨7974726096105966407508917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316484064070644271672611 7974726096105966407508917)
                  ·
                    refine ⟨747630571509934350703961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7974726096105966407508917 747630571509934350703961)
                    ·
                      refine ⟨560722928632450763027971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747630571509934350703961 560722928632450763027971)
                      ·
                        rfl

theorem cell23_1092004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_1092004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092004 prefixEnd_1092004 := by exact prefixLift 1092004
  have htrace : WordTrace (prefixWord ++ tailWord_1092004) baseStart_1092004 baseEnd_1092004 := by
    simpa [prefixWord, tailWord_1092004, baseEnd_1092004] using wordTrace_append hprefix tailTrace_1092004
  have hstable : (prefixWord ++ tailWord_1092004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092004).length < 2 ^ (prefixWord ++ tailWord_1092004).sum := by decide
  have hdescent : baseEnd_1092004 < baseStart_1092004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092071 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1092071 : Nat := 118140960795 + 1092071 * 2 ^ 59
def prefixEnd_1092071 : Nat := 4983230072969 + 3 ^ 40 * 1092071 * 2
def baseEnd_1092071 : Nat := 560757331836302000890163

theorem tailTrace_1092071 : CollatzResearch.WordTrace tailWord_1092071 prefixEnd_1092071 560757331836302000890163 := by
  unfold tailWord_1092071
  simp only [CollatzResearch.WordTrace]
  refine ⟨39831101626620752723020067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26554067751080501815346711 39831101626620752723020067)
  ·
    refine ⟨59746652439931129084530101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39831101626620752723020067 59746652439931129084530101)
    ·
      refine ⟨5601248666243543351674697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59746652439931129084530101 5601248666243543351674697)
      ·
        refine ⟨4200936499682657513756023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5601248666243543351674697 4200936499682657513756023)
        ·
          refine ⟨6301404749523986270634035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4200936499682657513756023 6301404749523986270634035)
          ·
            refine ⟨9452107124285979405951053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301404749523986270634035 9452107124285979405951053)
            ·
              refine ⟨3544540171607242277231645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9452107124285979405951053 3544540171607242277231645)
              ·
                refine ⟨1329202564352715853961867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544540171607242277231645 1329202564352715853961867)
                ·
                  refine ⟨1993803846529073780942801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329202564352715853961867 1993803846529073780942801)
                  ·
                    refine ⟨1495352884896805335707101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993803846529073780942801 1495352884896805335707101)
                    ·
                      refine ⟨560757331836302000890163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1495352884896805335707101 560757331836302000890163)
                      ·
                        rfl

theorem cell23_1092071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1092071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092071 prefixEnd_1092071 := by exact prefixLift 1092071
  have htrace : WordTrace (prefixWord ++ tailWord_1092071) baseStart_1092071 baseEnd_1092071 := by
    simpa [prefixWord, tailWord_1092071, baseEnd_1092071] using wordTrace_append hprefix tailTrace_1092071
  have hstable : (prefixWord ++ tailWord_1092071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092071).length < 2 ^ (prefixWord ++ tailWord_1092071).sum := by decide
  have hdescent : baseEnd_1092071 < baseStart_1092071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092078 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1092078 : Nat := 118140960795 + 1092078 * 2 ^ 59
def prefixEnd_1092078 : Nat := 4983230072969 + 3 ^ 40 * 1092078 * 2
def baseEnd_1092078 : Nat := 186920308733627824500877

theorem tailTrace_1092078 : CollatzResearch.WordTrace tailWord_1092078 prefixEnd_1092078 186920308733627824500877 := by
  unfold tailWord_1092078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978919617199424114815611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26554237958396928612349925 4978919617199424114815611)
  ·
    refine ⟨7468379425799136172223417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4978919617199424114815611 7468379425799136172223417)
    ·
      refine ⟨5601284569349352129167563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7468379425799136172223417 5601284569349352129167563)
      ·
        refine ⟨8401926854024028193751345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601284569349352129167563 8401926854024028193751345)
        ·
          refine ⟨6301445140518021145313509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401926854024028193751345 6301445140518021145313509)
          ·
            refine ⟨1181520963847128964746283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6301445140518021145313509 1181520963847128964746283)
            ·
              refine ⟨1772281445770693447119425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181520963847128964746283 1772281445770693447119425)
              ·
                refine ⟨1329211084328020085339569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772281445770693447119425 1329211084328020085339569)
                ·
                  refine ⟨996908313246015064004677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329211084328020085339569 996908313246015064004677)
                  ·
                    refine ⟨186920308733627824500877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996908313246015064004677 186920308733627824500877)
                    ·
                      rfl

theorem cell23_1092078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1092078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092078 prefixEnd_1092078 := by exact prefixLift 1092078
  have htrace : WordTrace (prefixWord ++ tailWord_1092078) baseStart_1092078 baseEnd_1092078 := by
    simpa [prefixWord, tailWord_1092078, baseEnd_1092078] using wordTrace_append hprefix tailTrace_1092078
  have hstable : (prefixWord ++ tailWord_1092078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092078).length < 2 ^ (prefixWord ++ tailWord_1092078).sum := by decide
  have hdescent : baseEnd_1092078 < baseStart_1092078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092101 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_1092101 : Nat := 118140960795 + 1092101 * 2 ^ 59
def prefixEnd_1092101 : Nat := 4983230072969 + 3 ^ 40 * 1092101 * 2
def baseEnd_1092101 : Nat := 560772736255936883515025

theorem tailTrace_1092101 : CollatzResearch.WordTrace tailWord_1092101 prefixEnd_1092101 560772736255936883515025 := by
  unfold tailWord_1092101
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832195816512067846612157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26554797211008045231074771 39832195816512067846612157)
  ·
    refine ⟨14937073431192025442479559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39832195816512067846612157 14937073431192025442479559)
    ·
      refine ⟨22405610146788038163719339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14937073431192025442479559 22405610146788038163719339)
      ·
        refine ⟨33608415220182057245579009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22405610146788038163719339 33608415220182057245579009)
        ·
          refine ⟨25206311415136542934184257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33608415220182057245579009 25206311415136542934184257)
          ·
            refine ⟨18904733561352407200638193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25206311415136542934184257 18904733561352407200638193)
            ·
              refine ⟨14178550171014305400478645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18904733561352407200638193 14178550171014305400478645)
              ·
                refine ⟨1329239078532591131294873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14178550171014305400478645 1329239078532591131294873)
                ·
                  refine ⟨996929308899443348471155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329239078532591131294873 996929308899443348471155)
                  ·
                    refine ⟨1495393963349165022706733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996929308899443348471155 1495393963349165022706733)
                    ·
                      refine ⟨560772736255936883515025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1495393963349165022706733 560772736255936883515025)
                      ·
                        rfl

theorem cell23_1092101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_1092101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092101 prefixEnd_1092101 := by exact prefixLift 1092101
  have htrace : WordTrace (prefixWord ++ tailWord_1092101) baseStart_1092101 baseEnd_1092101 := by
    simpa [prefixWord, tailWord_1092101, baseEnd_1092101] using wordTrace_append hprefix tailTrace_1092101
  have hstable : (prefixWord ++ tailWord_1092101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092101).length < 2 ^ (prefixWord ++ tailWord_1092101).sum := by decide
  have hdescent : baseEnd_1092101 < baseStart_1092101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092102 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1092102 : Nat := 118140960795 + 1092102 * 2 ^ 59
def prefixEnd_1092102 : Nat := 4983230072969 + 3 ^ 40 * 1092102 * 2
def baseEnd_1092102 : Nat := 560773249736591379602521

theorem tailTrace_1092102 : CollatzResearch.WordTrace tailWord_1092102 prefixEnd_1092102 560773249736591379602521 := by
  unfold tailWord_1092102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244757259047138906793705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26554821526338963344932373 1244757259047138906793705)
  ·
    refine ⟨933567944285354180095279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1244757259047138906793705 933567944285354180095279)
    ·
      refine ⟨1400351916428031270142919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933567944285354180095279 1400351916428031270142919)
      ·
        refine ⟨2100527874642046905214379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400351916428031270142919 2100527874642046905214379)
        ·
          refine ⟨3150791811963070357821569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100527874642046905214379 3150791811963070357821569)
          ·
            refine ⟨2363093858972302768366177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3150791811963070357821569 2363093858972302768366177)
            ·
              refine ⟨1772320394229227076274633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363093858972302768366177 1772320394229227076274633)
              ·
                refine ⟨1329240295671920307205975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772320394229227076274633 1329240295671920307205975)
                ·
                  refine ⟨1993860443507880460808963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329240295671920307205975 1993860443507880460808963)
                  ·
                    refine ⟨2990790665261820691213445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993860443507880460808963 2990790665261820691213445)
                    ·
                      refine ⟨560773249736591379602521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2990790665261820691213445 560773249736591379602521)
                      ·
                        rfl

theorem cell23_1092102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1092102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092102 prefixEnd_1092102 := by exact prefixLift 1092102
  have htrace : WordTrace (prefixWord ++ tailWord_1092102) baseStart_1092102 baseEnd_1092102 := by
    simpa [prefixWord, tailWord_1092102, baseEnd_1092102] using wordTrace_append hprefix tailTrace_1092102
  have hstable : (prefixWord ++ tailWord_1092102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092102).length < 2 ^ (prefixWord ++ tailWord_1092102).sum := by decide
  have hdescent : baseEnd_1092102 < baseStart_1092102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092111 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 1, 3, 2]
def baseStart_1092111 : Nat := 118140960795 + 1092111 * 2 ^ 59
def prefixEnd_1092111 : Nat := 4983230072969 + 3 ^ 40 * 1092111 * 2
def baseEnd_1092111 : Nat := 560777871062481844389979

theorem tailTrace_1092111 : CollatzResearch.WordTrace tailWord_1092111 prefixEnd_1092111 560777871062481844389979 := by
  unfold tailWord_1092111
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832560546475839554476187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26555040364317226369650791 39832560546475839554476187)
  ·
    refine ⟨59748840819713759331714281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39832560546475839554476187 59748840819713759331714281)
    ·
      refine ⟨44811630614785319498785711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59748840819713759331714281 44811630614785319498785711)
      ·
        refine ⟨67217445922177979248178567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44811630614785319498785711 67217445922177979248178567)
        ·
          refine ⟨100826168883266968872267851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67217445922177979248178567 100826168883266968872267851)
          ·
            refine ⟨151239253324900453308401777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100826168883266968872267851 151239253324900453308401777)
            ·
              refine ⟨113429439993675339981301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151239253324900453308401777 113429439993675339981301333)
              ·
                refine ⟨1329251249925882890405875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 113429439993675339981301333 1329251249925882890405875)
                ·
                  refine ⟨1993876874888824335608813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329251249925882890405875 1993876874888824335608813)
                  ·
                    refine ⟨747703828083309125853305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993876874888824335608813 747703828083309125853305)
                    ·
                      refine ⟨560777871062481844389979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747703828083309125853305 560777871062481844389979)
                      ·
                        rfl

theorem cell23_1092111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 3, 2].length) (baseStart_1092111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092111 prefixEnd_1092111 := by exact prefixLift 1092111
  have htrace : WordTrace (prefixWord ++ tailWord_1092111) baseStart_1092111 baseEnd_1092111 := by
    simpa [prefixWord, tailWord_1092111, baseEnd_1092111] using wordTrace_append hprefix tailTrace_1092111
  have hstable : (prefixWord ++ tailWord_1092111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092111).length < 2 ^ (prefixWord ++ tailWord_1092111).sum := by decide
  have hdescent : baseEnd_1092111 < baseStart_1092111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092119 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1092119 : Nat := 118140960795 + 1092119 * 2 ^ 59
def prefixEnd_1092119 : Nat := 4983230072969 + 3 ^ 40 * 1092119 * 2
def baseEnd_1092119 : Nat := 560781978907717813089943

theorem tailTrace_1092119 : CollatzResearch.WordTrace tailWord_1092119 prefixEnd_1092119 560781978907717813089943 := by
  unfold tailWord_1092119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832852330446856920767411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26555234886964571280511607 39832852330446856920767411)
  ·
    refine ⟨59749278495670285381151117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39832852330446856920767411 59749278495670285381151117)
    ·
      refine ⟨22405979435876357017931669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59749278495670285381151117 22405979435876357017931669)
      ·
        refine ⟨1050280286056704235215547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22405979435876357017931669 1050280286056704235215547)
        ·
          refine ⟨1575420429085056352823321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050280286056704235215547 1575420429085056352823321)
          ·
            refine ⟨1181565321813792264617491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575420429085056352823321 1181565321813792264617491)
            ·
              refine ⟨1772347982720688396926237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181565321813792264617491 1772347982720688396926237)
              ·
                refine ⟨664630493520258148847339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1772347982720688396926237 664630493520258148847339)
                ·
                  refine ⟨996945740280387223271009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664630493520258148847339 996945740280387223271009)
                  ·
                    refine ⟨747709305210290417453257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996945740280387223271009 747709305210290417453257)
                    ·
                      refine ⟨560781978907717813089943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747709305210290417453257 560781978907717813089943)
                      ·
                        rfl

theorem cell23_1092119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1092119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092119 prefixEnd_1092119 := by exact prefixLift 1092119
  have htrace : WordTrace (prefixWord ++ tailWord_1092119) baseStart_1092119 baseEnd_1092119 := by
    simpa [prefixWord, tailWord_1092119, baseEnd_1092119] using wordTrace_append hprefix tailTrace_1092119
  have hstable : (prefixWord ++ tailWord_1092119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092119).length < 2 ^ (prefixWord ++ tailWord_1092119).sum := by decide
  have hdescent : baseEnd_1092119 < baseStart_1092119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092187 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_1092187 : Nat := 118140960795 + 1092187 * 2 ^ 59
def prefixEnd_1092187 : Nat := 4983230072969 + 3 ^ 40 * 1092187 * 2
def baseEnd_1092187 : Nat := 560816895592223547039629

theorem tailTrace_1092187 : CollatzResearch.WordTrace tailWord_1092187 prefixEnd_1092187 560816895592223547039629 := by
  unfold tailWord_1092187
  simp only [CollatzResearch.WordTrace]
  refine ⟨39835332494200504534242815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26556888329467003022828543 39835332494200504534242815)
  ·
    refine ⟨59752998741300756801364223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39835332494200504534242815 59752998741300756801364223)
    ·
      refine ⟨89629498111951135202046335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59752998741300756801364223 89629498111951135202046335)
      ·
        refine ⟨134444247167926702803069503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89629498111951135202046335 134444247167926702803069503)
        ·
          refine ⟨201666370751890054204604255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134444247167926702803069503 201666370751890054204604255)
          ·
            refine ⟨302499556127835081306906383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201666370751890054204604255 302499556127835081306906383)
            ·
              refine ⟨453749334191752621960359575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302499556127835081306906383 453749334191752621960359575)
              ·
                refine ⟨680624001287628932940539363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453749334191752621960359575 680624001287628932940539363)
                ·
                  refine ⟨1020936001931443399410809045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680624001287628932940539363 1020936001931443399410809045)
                  ·
                    refine ⟨23928187545268204673690837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1020936001931443399410809045 23928187545268204673690837)
                    ·
                      refine ⟨560816895592223547039629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23928187545268204673690837 560816895592223547039629)
                      ·
                        rfl

theorem cell23_1092187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_1092187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092187 prefixEnd_1092187 := by exact prefixLift 1092187
  have htrace : WordTrace (prefixWord ++ tailWord_1092187) baseStart_1092187 baseEnd_1092187 := by
    simpa [prefixWord, tailWord_1092187, baseEnd_1092187] using wordTrace_append hprefix tailTrace_1092187
  have hstable : (prefixWord ++ tailWord_1092187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092187).length < 2 ^ (prefixWord ++ tailWord_1092187).sum := by decide
  have hdescent : baseEnd_1092187 < baseStart_1092187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092204 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1092204 : Nat := 118140960795 + 1092204 * 2 ^ 59
def prefixEnd_1092204 : Nat := 4983230072969 + 3 ^ 40 * 1092204 * 2
def baseEnd_1092204 : Nat := 560825624763349980527051

theorem tailTrace_1092204 : CollatzResearch.WordTrace tailWord_1092204 prefixEnd_1092204 560825624763349980527051 := by
  unfold tailWord_1092204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917976267569458218805833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26557301690092610958407777 19917976267569458218805833)
  ·
    refine ⟨14938482200677093664104375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19917976267569458218805833 14938482200677093664104375)
    ·
      refine ⟨22407723301015640496156563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14938482200677093664104375 22407723301015640496156563)
      ·
        refine ⟨33611584951523460744234845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22407723301015640496156563 33611584951523460744234845)
        ·
          refine ⟨12604344356821297779088067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33611584951523460744234845 12604344356821297779088067)
          ·
            refine ⟨18906516535231946668632101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12604344356821297779088067 18906516535231946668632101)
            ·
              refine ⟨3544971850355990000368519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18906516535231946668632101 3544971850355990000368519)
              ·
                refine ⟨5317457775533985000552779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544971850355990000368519 5317457775533985000552779)
                ·
                  refine ⟨7976186663300977500829169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5317457775533985000552779 7976186663300977500829169)
                  ·
                    refine ⟨5982139997475733125621877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7976186663300977500829169 5982139997475733125621877)
                    ·
                      refine ⟨560825624763349980527051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5982139997475733125621877 560825624763349980527051)
                      ·
                        rfl

theorem cell23_1092204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1092204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092204 prefixEnd_1092204 := by exact prefixLift 1092204
  have htrace : WordTrace (prefixWord ++ tailWord_1092204) baseStart_1092204 baseEnd_1092204 := by
    simpa [prefixWord, tailWord_1092204, baseEnd_1092204] using wordTrace_append hprefix tailTrace_1092204
  have hstable : (prefixWord ++ tailWord_1092204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092204).length < 2 ^ (prefixWord ++ tailWord_1092204).sum := by decide
  have hdescent : baseEnd_1092204 < baseStart_1092204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092228 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1092228 : Nat := 118140960795 + 1092228 * 2 ^ 59
def prefixEnd_1092228 : Nat := 4983230072969 + 3 ^ 40 * 1092228 * 2
def baseEnd_1092228 : Nat := 186945982766352628875647

theorem tailTrace_1092228 : CollatzResearch.WordTrace tailWord_1092228 prefixEnd_1092228 186945982766352628875647 := by
  unfold tailWord_1092228
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918413943525984268242669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26557885258034645690990225 19918413943525984268242669)
  ·
    refine ⟨7469405228822244100591001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19918413943525984268242669 7469405228822244100591001)
    ·
      refine ⟨5602053921616683075443251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7469405228822244100591001 5602053921616683075443251)
      ·
        refine ⟨8403080882425024613164877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602053921616683075443251 8403080882425024613164877)
        ·
          refine ⟨3151155330909384229936829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8403080882425024613164877 3151155330909384229936829)
          ·
            refine ⟨1181683249091019086226311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3151155330909384229936829 1181683249091019086226311)
            ·
              refine ⟨1772524873636528629339467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181683249091019086226311 1772524873636528629339467)
              ·
                refine ⟨2658787310454792944009201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772524873636528629339467 2658787310454792944009201)
                ·
                  refine ⟨1994090482841094708006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658787310454792944009201 1994090482841094708006901)
                  ·
                    refine ⟨186945982766352628875647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1994090482841094708006901 186945982766352628875647)
                    ·
                      rfl

theorem cell23_1092228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1092228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092228 prefixEnd_1092228 := by exact prefixLift 1092228
  have htrace : WordTrace (prefixWord ++ tailWord_1092228) baseStart_1092228 baseEnd_1092228 := by
    simpa [prefixWord, tailWord_1092228, baseEnd_1092228] using wordTrace_append hprefix tailTrace_1092228
  have hstable : (prefixWord ++ tailWord_1092228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092228).length < 2 ^ (prefixWord ++ tailWord_1092228).sum := by decide
  have hdescent : baseEnd_1092228 < baseStart_1092228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092231 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_1092231 : Nat := 118140960795 + 1092231 * 2 ^ 59
def prefixEnd_1092231 : Nat := 4983230072969 + 3 ^ 40 * 1092231 * 2
def baseEnd_1092231 : Nat := 560839488741021374889427

theorem tailTrace_1092231 : CollatzResearch.WordTrace tailWord_1092231 prefixEnd_1092231 560839488741021374889427 := by
  unfold tailWord_1092231
  simp only [CollatzResearch.WordTrace]
  refine ⟨39836937306041100048844547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26557958204027400032563031 39836937306041100048844547)
  ·
    refine ⟨59755405959061650073266821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39836937306041100048844547 59755405959061650073266821)
    ·
      refine ⟨11204138617324059388737529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59755405959061650073266821 11204138617324059388737529)
      ·
        refine ⟨8403103962993044541553147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11204138617324059388737529 8403103962993044541553147)
        ·
          refine ⟨12604655944489566812329721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403103962993044541553147 12604655944489566812329721)
          ·
            refine ⟨9453491958367175109247291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12604655944489566812329721 9453491958367175109247291)
            ·
              refine ⟨14180237937550762663870937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453491958367175109247291 14180237937550762663870937)
              ·
                refine ⟨10635178453163071997903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14180237937550762663870937 10635178453163071997903203)
                ·
                  refine ⟨15952767679744607996854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10635178453163071997903203 15952767679744607996854805)
                  ·
                    refine ⟨747785984988028499852569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15952767679744607996854805 747785984988028499852569)
                    ·
                      refine ⟨560839488741021374889427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 747785984988028499852569 560839488741021374889427)
                      ·
                        rfl

theorem cell23_1092231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_1092231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092231 prefixEnd_1092231 := by exact prefixLift 1092231
  have htrace : WordTrace (prefixWord ++ tailWord_1092231) baseStart_1092231 baseEnd_1092231 := by
    simpa [prefixWord, tailWord_1092231, baseEnd_1092231] using wordTrace_append hprefix tailTrace_1092231
  have hstable : (prefixWord ++ tailWord_1092231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092231).length < 2 ^ (prefixWord ++ tailWord_1092231).sum := by decide
  have hdescent : baseEnd_1092231 < baseStart_1092231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1092274 : Nat := 118140960795 + 1092274 * 2 ^ 59
def prefixEnd_1092274 : Nat := 4983230072969 + 3 ^ 40 * 1092274 * 2
def baseEnd_1092274 : Nat := 560861568409164706651729

theorem tailTrace_1092274 : CollatzResearch.WordTrace tailWord_1092274 prefixEnd_1092274 560861568409164706651729 := by
  unfold tailWord_1092274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959626411221329598164969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26559003763256878928439917 9959626411221329598164969)
  ·
    refine ⟨7469719808415997198623727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9959626411221329598164969 7469719808415997198623727)
    ·
      refine ⟨11204579712623995797935591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469719808415997198623727 11204579712623995797935591)
      ·
        refine ⟨16806869568935993696903387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11204579712623995797935591 16806869568935993696903387)
        ·
          refine ⟨25210304353403990545355081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16806869568935993696903387 25210304353403990545355081)
          ·
            refine ⟨18907728265052992909016311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25210304353403990545355081 18907728265052992909016311)
            ·
              refine ⟨28361592397579489363524467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18907728265052992909016311 28361592397579489363524467)
              ·
                refine ⟨42542388596369234045286701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28361592397579489363524467 42542388596369234045286701)
                ·
                  refine ⟨15953395723638462766982513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42542388596369234045286701 15953395723638462766982513)
                  ·
                    refine ⟨11965046792728847075236885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15953395723638462766982513 11965046792728847075236885)
                    ·
                      refine ⟨560861568409164706651729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11965046792728847075236885 560861568409164706651729)
                      ·
                        rfl

theorem cell23_1092274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1092274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092274 prefixEnd_1092274 := by exact prefixLift 1092274
  have htrace : WordTrace (prefixWord ++ tailWord_1092274) baseStart_1092274 baseEnd_1092274 := by
    simpa [prefixWord, tailWord_1092274, baseEnd_1092274] using wordTrace_append hprefix tailTrace_1092274
  have hstable : (prefixWord ++ tailWord_1092274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092274).length < 2 ^ (prefixWord ++ tailWord_1092274).sum := by decide
  have hdescent : baseEnd_1092274 < baseStart_1092274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092292 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1092292 : Nat := 118140960795 + 1092292 * 2 ^ 59
def prefixEnd_1092292 : Nat := 4983230072969 + 3 ^ 40 * 1092292 * 2
def baseEnd_1092292 : Nat := 186956937020315212075549

theorem tailTrace_1092292 : CollatzResearch.WordTrace tailWord_1092292 prefixEnd_1092292 186956937020315212075549 := by
  unfold tailWord_1092292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919581079410053733407565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26559441439213404977876753 19919581079410053733407565)
  ·
    refine ⟨7469842904778770150027837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19919581079410053733407565 7469842904778770150027837)
    ·
      refine ⟨2801191089292038806260439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7469842904778770150027837 2801191089292038806260439)
      ·
        refine ⟨4201786633938058209390659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801191089292038806260439 4201786633938058209390659)
        ·
          refine ⟨6302679950907087314085989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201786633938058209390659 6302679950907087314085989)
          ·
            refine ⟨1181752490795078871391123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6302679950907087314085989 1181752490795078871391123)
            ·
              refine ⟨1772628736192618307086685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181752490795078871391123 1772628736192618307086685)
              ·
                refine ⟨664735776072231865157507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1772628736192618307086685 664735776072231865157507)
                ·
                  refine ⟨997103664108347797736261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664735776072231865157507 997103664108347797736261)
                  ·
                    refine ⟨186956937020315212075549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997103664108347797736261 186956937020315212075549)
                    ·
                      rfl

theorem cell23_1092292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1092292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092292 prefixEnd_1092292 := by exact prefixLift 1092292
  have htrace : WordTrace (prefixWord ++ tailWord_1092292) baseStart_1092292 baseEnd_1092292 := by
    simpa [prefixWord, tailWord_1092292, baseEnd_1092292] using wordTrace_append hprefix tailTrace_1092292
  have hstable : (prefixWord ++ tailWord_1092292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092292).length < 2 ^ (prefixWord ++ tailWord_1092292).sum := by decide
  have hdescent : baseEnd_1092292 < baseStart_1092292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092304 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_1092304 : Nat := 118140960795 + 1092304 * 2 ^ 59
def prefixEnd_1092304 : Nat := 4983230072969 + 3 ^ 40 * 1092304 * 2
def baseEnd_1092304 : Nat := 560876972828799589276591

theorem tailTrace_1092304 : CollatzResearch.WordTrace tailWord_1092304 prefixEnd_1092304 560876972828799589276591 := by
  unfold tailWord_1092304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919799917388316758125983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26559733223184422344167977 19919799917388316758125983)
  ·
    refine ⟨29879699876082475137188975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19919799917388316758125983 29879699876082475137188975)
    ·
      refine ⟨44819549814123712705783463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29879699876082475137188975 44819549814123712705783463)
      ·
        refine ⟨67229324721185569058675195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44819549814123712705783463 67229324721185569058675195)
        ·
          refine ⟨100843987081778353588012793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67229324721185569058675195 100843987081778353588012793)
          ·
            refine ⟨75632990311333765191009595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100843987081778353588012793 75632990311333765191009595)
            ·
              refine ⟨113449485467000647786514393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75632990311333765191009595 113449485467000647786514393)
              ·
                refine ⟨85087114100250485839885795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113449485467000647786514393 85087114100250485839885795)
                ·
                  refine ⟨127630671150375728759828693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85087114100250485839885795 127630671150375728759828693)
                  ·
                    refine ⟨2991343855086931142808485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127630671150375728759828693 2991343855086931142808485)
                    ·
                      refine ⟨560876972828799589276591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2991343855086931142808485 560876972828799589276591)
                      ·
                        rfl

theorem cell23_1092304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_1092304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092304 prefixEnd_1092304 := by exact prefixLift 1092304
  have htrace : WordTrace (prefixWord ++ tailWord_1092304) baseStart_1092304 baseEnd_1092304 := by
    simpa [prefixWord, tailWord_1092304, baseEnd_1092304] using wordTrace_append hprefix tailTrace_1092304
  have hstable : (prefixWord ++ tailWord_1092304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092304).length < 2 ^ (prefixWord ++ tailWord_1092304).sum := by decide
  have hdescent : baseEnd_1092304 < baseStart_1092304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092309 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1092309 : Nat := 118140960795 + 1092309 * 2 ^ 59
def prefixEnd_1092309 : Nat := 4983230072969 + 3 ^ 40 * 1092309 * 2
def baseEnd_1092309 : Nat := 186959846744024023238023

theorem tailTrace_1092309 : CollatzResearch.WordTrace tailWord_1092309 prefixEnd_1092309 186959846744024023238023 := by
  unfold tailWord_1092309
  simp only [CollatzResearch.WordTrace]
  refine ⟨39839782199758519370183981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26559854799839012913455987 39839782199758519370183981)
  ·
    refine ⟨14939918324909444763818993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39839782199758519370183981 14939918324909444763818993)
    ·
      refine ⟨11204938743682083572864245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14939918324909444763818993 11204938743682083572864245)
      ·
        refine ⟨1050463007220195334956023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11204938743682083572864245 1050463007220195334956023)
        ·
          refine ⟨1575694510830293002434035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050463007220195334956023 1575694510830293002434035)
          ·
            refine ⟨2363541766245439503651053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575694510830293002434035 2363541766245439503651053)
            ·
              refine ⟨886328162342039813869145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2363541766245439503651053 886328162342039813869145)
              ·
                refine ⟨664746121756529860401859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886328162342039813869145 664746121756529860401859)
                ·
                  refine ⟨997119182634794790602789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664746121756529860401859 997119182634794790602789)
                  ·
                    refine ⟨186959846744024023238023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997119182634794790602789 186959846744024023238023)
                    ·
                      rfl

theorem cell23_1092309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1092309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092309 prefixEnd_1092309 := by exact prefixLift 1092309
  have htrace : WordTrace (prefixWord ++ tailWord_1092309) baseStart_1092309 baseEnd_1092309 := by
    simpa [prefixWord, tailWord_1092309, baseEnd_1092309] using wordTrace_append hprefix tailTrace_1092309
  have hstable : (prefixWord ++ tailWord_1092309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092309).length < 2 ^ (prefixWord ++ tailWord_1092309).sum := by decide
  have hdescent : baseEnd_1092309 < baseStart_1092309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092338 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1092338 : Nat := 118140960795 + 1092338 * 2 ^ 59
def prefixEnd_1092338 : Nat := 4983230072969 + 3 ^ 40 * 1092338 * 2
def baseEnd_1092338 : Nat := 560894431171052456251435

theorem tailTrace_1092338 : CollatzResearch.WordTrace tailWord_1092338 prefixEnd_1092338 560894431171052456251435 := by
  unfold tailWord_1092338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960209979163364330747417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26560559944435638215326445 9960209979163364330747417)
  ·
    refine ⟨7470157484372523248060563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9960209979163364330747417 7470157484372523248060563)
    ·
      refine ⟨11205236226558784872090845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7470157484372523248060563 11205236226558784872090845)
      ·
        refine ⟨4201963584959544327034067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11205236226558784872090845 4201963584959544327034067)
        ·
          refine ⟨6302945377439316490551101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201963584959544327034067 6302945377439316490551101)
          ·
            refine ⟨2363604516539743683956663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6302945377439316490551101 2363604516539743683956663)
            ·
              refine ⟨3545406774809615525934995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363604516539743683956663 3545406774809615525934995)
              ·
                refine ⟨5318110162214423288902493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545406774809615525934995 5318110162214423288902493)
                ·
                  refine ⟨1994291310830408733338435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5318110162214423288902493 1994291310830408733338435)
                  ·
                    refine ⟨2991436966245613100007653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994291310830408733338435 2991436966245613100007653)
                    ·
                      refine ⟨560894431171052456251435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2991436966245613100007653 560894431171052456251435)
                      ·
                        rfl

theorem cell23_1092338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1092338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092338 prefixEnd_1092338 := by exact prefixLift 1092338
  have htrace : WordTrace (prefixWord ++ tailWord_1092338) baseStart_1092338 baseEnd_1092338 := by
    simpa [prefixWord, tailWord_1092338, baseEnd_1092338] using wordTrace_append hprefix tailTrace_1092338
  have hstable : (prefixWord ++ tailWord_1092338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092338).length < 2 ^ (prefixWord ++ tailWord_1092338).sum := by decide
  have hdescent : baseEnd_1092338 < baseStart_1092338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092344 : List Nat := [2, 1, 2, 1, 1, 2, 3, 11]
def baseStart_1092344 : Nat := 118140960795 + 1092344 * 2 ^ 59
def prefixEnd_1092344 : Nat := 4983230072969 + 3 ^ 40 * 1092344 * 2
def baseEnd_1092344 : Nat := 20773981927962201213941

theorem tailTrace_1092344 : CollatzResearch.WordTrace tailWord_1092344 prefixEnd_1092344 20773981927962201213941 := by
  unfold tailWord_1092344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19920529377315860173854043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26560705836421146898472057 19920529377315860173854043)
  ·
    refine ⟨29880794065973790260781065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19920529377315860173854043 29880794065973790260781065)
    ·
      refine ⟨22410595549480342695585799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29880794065973790260781065 22410595549480342695585799)
      ·
        refine ⟨33615893324220514043378699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22410595549480342695585799 33615893324220514043378699)
        ·
          refine ⟨50423839986330771065068049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33615893324220514043378699 50423839986330771065068049)
          ·
            refine ⟨37817879989748078298801037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50423839986330771065068049 37817879989748078298801037)
            ·
              refine ⟨14181704996155529362050389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37817879989748078298801037 14181704996155529362050389)
              ·
                refine ⟨20773981927962201213941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14181704996155529362050389 20773981927962201213941)
                ·
                  rfl

theorem cell23_1092344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 11].length) (baseStart_1092344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092344 prefixEnd_1092344 := by exact prefixLift 1092344
  have htrace : WordTrace (prefixWord ++ tailWord_1092344) baseStart_1092344 baseEnd_1092344 := by
    simpa [prefixWord, tailWord_1092344, baseEnd_1092344] using wordTrace_append hprefix tailTrace_1092344
  have hstable : (prefixWord ++ tailWord_1092344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092344).length < 2 ^ (prefixWord ++ tailWord_1092344).sum := by decide
  have hdescent : baseEnd_1092344 < baseStart_1092344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092371 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3]
def baseStart_1092371 : Nat := 118140960795 + 1092371 * 2 ^ 59
def prefixEnd_1092371 : Nat := 4983230072969 + 3 ^ 40 * 1092371 * 2
def baseEnd_1092371 : Nat := 560911376032650827138783

theorem tailTrace_1092371 : CollatzResearch.WordTrace tailWord_1092371 prefixEnd_1092371 560911376032650827138783 := by
  unfold tailWord_1092371
  simp only [CollatzResearch.WordTrace]
  refine ⟨39842043525533903958940967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26561362350355935972627311 39842043525533903958940967)
  ·
    refine ⟨59763065288300855938411451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39842043525533903958940967 59763065288300855938411451)
    ·
      refine ⟨89644597932451283907617177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59763065288300855938411451 89644597932451283907617177)
      ·
        refine ⟨67233448449338462930712883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89644597932451283907617177 67233448449338462930712883)
        ·
          refine ⟨100850172674007694396069325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67233448449338462930712883 100850172674007694396069325)
          ·
            refine ⟨37818814752752885398525997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100850172674007694396069325 37818814752752885398525997)
            ·
              refine ⟨14182055532282332024447249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37818814752752885398525997 14182055532282332024447249)
              ·
                refine ⟨10636541649211749018335437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14182055532282332024447249 10636541649211749018335437)
                ·
                  refine ⟨3988703118454405881875789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10636541649211749018335437 3988703118454405881875789)
                  ·
                    refine ⟨1495763669420402205703421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3988703118454405881875789 1495763669420402205703421)
                    ·
                      refine ⟨560911376032650827138783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1495763669420402205703421 560911376032650827138783)
                      ·
                        rfl

theorem cell23_1092371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_1092371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092371 prefixEnd_1092371 := by exact prefixLift 1092371
  have htrace : WordTrace (prefixWord ++ tailWord_1092371) baseStart_1092371 baseEnd_1092371 := by
    simpa [prefixWord, tailWord_1092371, baseEnd_1092371] using wordTrace_append hprefix tailTrace_1092371
  have hstable : (prefixWord ++ tailWord_1092371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092371).length < 2 ^ (prefixWord ++ tailWord_1092371).sum := by decide
  have hdescent : baseEnd_1092371 < baseStart_1092371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092401 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1092401 : Nat := 118140960795 + 1092401 * 2 ^ 59
def prefixEnd_1092401 : Nat := 4983230072969 + 3 ^ 40 * 1092401 * 2
def baseEnd_1092401 : Nat := 560926780452285709763645

theorem tailTrace_1092401 : CollatzResearch.WordTrace tailWord_1092401 prefixEnd_1092401 560926780452285709763645 := by
  unfold tailWord_1092401
  simp only [CollatzResearch.WordTrace]
  refine ⟨39843137715425219082533057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26562091810283479388355371 39843137715425219082533057)
  ·
    refine ⟨29882353286568914311899793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39843137715425219082533057 29882353286568914311899793)
    ·
      refine ⟨22411764964926685733924845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29882353286568914311899793 22411764964926685733924845)
      ·
        refine ⟨8404411861847507150221817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22411764964926685733924845 8404411861847507150221817)
        ·
          refine ⟨6303308896385630362666363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8404411861847507150221817 6303308896385630362666363)
          ·
            refine ⟨9454963344578445543999545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303308896385630362666363 9454963344578445543999545)
            ·
              refine ⟨7091222508433834157999659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454963344578445543999545 7091222508433834157999659)
              ·
                refine ⟨10636833762650751236999489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091222508433834157999659 10636833762650751236999489)
                ·
                  refine ⟨7977625321988063427749617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10636833762650751236999489 7977625321988063427749617)
                  ·
                    refine ⟨5983218991491047570812213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7977625321988063427749617 5983218991491047570812213)
                    ·
                      refine ⟨560926780452285709763645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5983218991491047570812213 560926780452285709763645)
                      ·
                        rfl

theorem cell23_1092401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1092401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092401 prefixEnd_1092401 := by exact prefixLift 1092401
  have htrace : WordTrace (prefixWord ++ tailWord_1092401) baseStart_1092401 baseEnd_1092401 := by
    simpa [prefixWord, tailWord_1092401, baseEnd_1092401] using wordTrace_append hprefix tailTrace_1092401
  have hstable : (prefixWord ++ tailWord_1092401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092401).length < 2 ^ (prefixWord ++ tailWord_1092401).sum := by decide
  have hdescent : baseEnd_1092401 < baseStart_1092401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092406 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1092406 : Nat := 118140960795 + 1092406 * 2 ^ 59
def prefixEnd_1092406 : Nat := 4983230072969 + 3 ^ 40 * 1092406 * 2
def baseEnd_1092406 : Nat := 560929347855558190201123

theorem tailTrace_1092406 : CollatzResearch.WordTrace tailWord_1092406 prefixEnd_1092406 560929347855558190201123 := by
  unfold tailWord_1092406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490207505025444058529067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26562213386938069957643381 2490207505025444058529067)
  ·
    refine ⟨3735311257538166087793601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490207505025444058529067 3735311257538166087793601)
    ·
      refine ⟨2801483443153624565845201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3735311257538166087793601 2801483443153624565845201)
      ·
        refine ⟨2101112582365218424383901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2801483443153624565845201 2101112582365218424383901)
        ·
          refine ⟨787917218386956909143963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2101112582365218424383901 787917218386956909143963)
          ·
            refine ⟨1181875827580435363715945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787917218386956909143963 1181875827580435363715945)
            ·
              refine ⟨886406870685326522786959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181875827580435363715945 886406870685326522786959)
              ·
                refine ⟨1329610306027989784180439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886406870685326522786959 1329610306027989784180439)
                ·
                  refine ⟨1994415459041984676270659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329610306027989784180439 1994415459041984676270659)
                  ·
                    refine ⟨2991623188562977014405989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994415459041984676270659 2991623188562977014405989)
                    ·
                      refine ⟨560929347855558190201123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2991623188562977014405989 560929347855558190201123)
                      ·
                        rfl

theorem cell23_1092406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1092406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092406 prefixEnd_1092406 := by exact prefixLift 1092406
  have htrace : WordTrace (prefixWord ++ tailWord_1092406) baseStart_1092406 baseEnd_1092406 := by
    simpa [prefixWord, tailWord_1092406, baseEnd_1092406] using wordTrace_append hprefix tailTrace_1092406
  have hstable : (prefixWord ++ tailWord_1092406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092406).length < 2 ^ (prefixWord ++ tailWord_1092406).sum := by decide
  have hdescent : baseEnd_1092406 < baseStart_1092406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092491 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_1092491 : Nat := 118140960795 + 1092491 * 2 ^ 59
def prefixEnd_1092491 : Nat := 4983230072969 + 3 ^ 40 * 1092491 * 2
def baseEnd_1092491 : Nat := 560972993711190357638231

theorem tailTrace_1092491 : CollatzResearch.WordTrace tailWord_1092491 prefixEnd_1092491 560972993711190357638231 := by
  unfold tailWord_1092491
  simp only [CollatzResearch.WordTrace]
  refine ⟨39846420285099164453309327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26564280190066109635539551 39846420285099164453309327)
  ·
    refine ⟨59769630427648746679963991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39846420285099164453309327 59769630427648746679963991)
    ·
      refine ⟨89654445641473120019945987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59769630427648746679963991 89654445641473120019945987)
      ·
        refine ⟨134481668462209680029918981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89654445641473120019945987 134481668462209680029918981)
        ·
          refine ⟨25215312836664315005609809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134481668462209680029918981 25215312836664315005609809)
          ·
            refine ⟨18911484627498236254207357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25215312836664315005609809 18911484627498236254207357)
            ·
              refine ⟨7091806735311838595327759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18911484627498236254207357 7091806735311838595327759)
              ·
                refine ⟨10637710102967757892991639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091806735311838595327759 10637710102967757892991639)
                ·
                  refine ⟨15956565154451636839487459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10637710102967757892991639 15956565154451636839487459)
                  ·
                    refine ⟨23934847731677455259231189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15956565154451636839487459 23934847731677455259231189)
                    ·
                      refine ⟨560972993711190357638231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23934847731677455259231189 560972993711190357638231)
                      ·
                        rfl

theorem cell23_1092491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_1092491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092491 prefixEnd_1092491 := by exact prefixLift 1092491
  have htrace : WordTrace (prefixWord ++ tailWord_1092491) baseStart_1092491 baseEnd_1092491 := by
    simpa [prefixWord, tailWord_1092491, baseEnd_1092491] using wordTrace_append hprefix tailTrace_1092491
  have hstable : (prefixWord ++ tailWord_1092491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092491).length < 2 ^ (prefixWord ++ tailWord_1092491).sum := by decide
  have hdescent : baseEnd_1092491 < baseStart_1092491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092532 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1092532 : Nat := 118140960795 + 1092532 * 2 ^ 59
def prefixEnd_1092532 : Nat := 4983230072969 + 3 ^ 40 * 1092532 * 2
def baseEnd_1092532 : Nat := 186998015472674899075181

theorem tailTrace_1092532 : CollatzResearch.WordTrace tailWord_1092532 prefixEnd_1092532 186998015472674899075181 := by
  unfold tailWord_1092532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923957838975314227775925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26565277118633752303701233 19923957838975314227775925)
  ·
    refine ⟨1867871047403935708853993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19923957838975314227775925 1867871047403935708853993)
    ·
      refine ⟨1400903285552951781640495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1867871047403935708853993 1400903285552951781640495)
      ·
        refine ⟨2101354928329427672460743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400903285552951781640495 2101354928329427672460743)
        ·
          refine ⟨3152032392494141508691115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101354928329427672460743 3152032392494141508691115)
          ·
            refine ⟨4728048588741212263036673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152032392494141508691115 4728048588741212263036673)
            ·
              refine ⟨3546036441555909197277505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4728048588741212263036673 3546036441555909197277505)
              ·
                refine ⟨2659527331166931897958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546036441555909197277505 2659527331166931897958129)
                ·
                  refine ⟨1994645498375198923468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659527331166931897958129 1994645498375198923468597)
                  ·
                    refine ⟨186998015472674899075181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1994645498375198923468597 186998015472674899075181)
                    ·
                      rfl

theorem cell23_1092532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1092532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092532 prefixEnd_1092532 := by exact prefixLift 1092532
  have htrace : WordTrace (prefixWord ++ tailWord_1092532) baseStart_1092532 baseEnd_1092532 := by
    simpa [prefixWord, tailWord_1092532, baseEnd_1092532] using wordTrace_append hprefix tailTrace_1092532
  have hstable : (prefixWord ++ tailWord_1092532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092532).length < 2 ^ (prefixWord ++ tailWord_1092532).sum := by decide
  have hdescent : baseEnd_1092532 < baseStart_1092532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092552 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_1092552 : Nat := 118140960795 + 1092552 * 2 ^ 59
def prefixEnd_1092552 : Nat := 4983230072969 + 3 ^ 40 * 1092552 * 2
def baseEnd_1092552 : Nat := 561004316031114618975451

theorem tailTrace_1092552 : CollatzResearch.WordTrace tailWord_1092552 prefixEnd_1092552 561004316031114618975451 := by
  unfold tailWord_1092552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19924322568939085935639955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26565763425252114580853273 19924322568939085935639955)
  ·
    refine ⟨29886483853408628903459933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19924322568939085935639955 29886483853408628903459933)
    ·
      refine ⟨11207431445028235838797475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29886483853408628903459933 11207431445028235838797475)
      ·
        refine ⟨16811147167542353758196213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207431445028235838797475 16811147167542353758196213)
        ·
          refine ⟨1576045046957095664830895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16811147167542353758196213 1576045046957095664830895)
          ·
            refine ⟨2364067570435643497246343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576045046957095664830895 2364067570435643497246343)
            ·
              refine ⟨3546101355653465245869515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364067570435643497246343 3546101355653465245869515)
              ·
                refine ⟨5319152033480197868804273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546101355653465245869515 5319152033480197868804273)
                ·
                  refine ⟨3989364025110148401603205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5319152033480197868804273 3989364025110148401603205)
                  ·
                    refine ⟨748005754708152825300601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989364025110148401603205 748005754708152825300601)
                    ·
                      refine ⟨561004316031114618975451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748005754708152825300601 561004316031114618975451)
                      ·
                        rfl

theorem cell23_1092552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_1092552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092552 prefixEnd_1092552 := by exact prefixLift 1092552
  have htrace : WordTrace (prefixWord ++ tailWord_1092552) baseStart_1092552 baseEnd_1092552 := by
    simpa [prefixWord, tailWord_1092552, baseEnd_1092552] using wordTrace_append hprefix tailTrace_1092552
  have hstable : (prefixWord ++ tailWord_1092552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092552).length < 2 ^ (prefixWord ++ tailWord_1092552).sum := by decide
  have hdescent : baseEnd_1092552 < baseStart_1092552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092562 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1092562 : Nat := 118140960795 + 1092562 * 2 ^ 59
def prefixEnd_1092562 : Nat := 4983230072969 + 3 ^ 40 * 1092562 * 2
def baseEnd_1092562 : Nat := 187003150279219859950135

theorem tailTrace_1092562 : CollatzResearch.WordTrace tailWord_1092562 prefixEnd_1092562 187003150279219859950135 := by
  unfold tailWord_1092562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962252466960485894785985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26566006578561295719429293 9962252466960485894785985)
  ·
    refine ⟨7471689350220364421089489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9962252466960485894785985 7471689350220364421089489)
    ·
      refine ⟨5603767012665273315817117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7471689350220364421089489 5603767012665273315817117)
      ·
        refine ⟨2101412629749477493431419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5603767012665273315817117 2101412629749477493431419)
        ·
          refine ⟨3152118944624216240147129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101412629749477493431419 3152118944624216240147129)
          ·
            refine ⟨2364089208468162180110347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152118944624216240147129 2364089208468162180110347)
            ·
              refine ⟨3546133812702243270165521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364089208468162180110347 3546133812702243270165521)
              ·
                refine ⟨2659600359526682452624141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546133812702243270165521 2659600359526682452624141)
                ·
                  refine ⟨997350134822505919734053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2659600359526682452624141 997350134822505919734053)
                  ·
                    refine ⟨187003150279219859950135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997350134822505919734053 187003150279219859950135)
                    ·
                      rfl

theorem cell23_1092562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1092562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092562 prefixEnd_1092562 := by exact prefixLift 1092562
  have htrace : WordTrace (prefixWord ++ tailWord_1092562) baseStart_1092562 baseEnd_1092562 := by
    simpa [prefixWord, tailWord_1092562, baseEnd_1092562] using wordTrace_append hprefix tailTrace_1092562
  have hstable : (prefixWord ++ tailWord_1092562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092562).length < 2 ^ (prefixWord ++ tailWord_1092562).sum := by decide
  have hdescent : baseEnd_1092562 < baseStart_1092562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092622 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1092622 : Nat := 118140960795 + 1092622 * 2 ^ 59
def prefixEnd_1092622 : Nat := 4983230072969 + 3 ^ 40 * 1092622 * 2
def baseEnd_1092622 : Nat := 187013419892309781700043

theorem tailTrace_1092622 : CollatzResearch.WordTrace tailWord_1092622 prefixEnd_1092622 187013419892309781700043 := by
  unfold tailWord_1092622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981399780953071728291015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26567465498416382550885413 4981399780953071728291015)
  ·
    refine ⟨7472099671429607592436523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981399780953071728291015 7472099671429607592436523)
    ·
      refine ⟨11208149507144411388654785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7472099671429607592436523 11208149507144411388654785)
      ·
        refine ⟨8406112130358308541491089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11208149507144411388654785 8406112130358308541491089)
        ·
          refine ⟨6304584097768731406118317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8406112130358308541491089 6304584097768731406118317)
          ·
            refine ⟨2364219036663274277294369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6304584097768731406118317 2364219036663274277294369)
            ·
              refine ⟨1773164277497455707970777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364219036663274277294369 1773164277497455707970777)
              ·
                refine ⟨1329873208123091780978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773164277497455707970777 1329873208123091780978083)
                ·
                  refine ⟨1994809812184637671467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329873208123091780978083 1994809812184637671467125)
                  ·
                    refine ⟨187013419892309781700043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1994809812184637671467125 187013419892309781700043)
                    ·
                      rfl

theorem cell23_1092622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1092622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092622 prefixEnd_1092622 := by exact prefixLift 1092622
  have htrace : WordTrace (prefixWord ++ tailWord_1092622) baseStart_1092622 baseEnd_1092622 := by
    simpa [prefixWord, tailWord_1092622, baseEnd_1092622] using wordTrace_append hprefix tailTrace_1092622
  have hstable : (prefixWord ++ tailWord_1092622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092622).length < 2 ^ (prefixWord ++ tailWord_1092622).sum := by decide
  have hdescent : baseEnd_1092622 < baseStart_1092622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092642 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1092642 : Nat := 118140960795 + 1092642 * 2 ^ 59
def prefixEnd_1092642 : Nat := 4983230072969 + 3 ^ 40 * 1092642 * 2
def baseEnd_1092642 : Nat := 561050529290019266850037

theorem tailTrace_1092642 : CollatzResearch.WordTrace tailWord_1092642 prefixEnd_1092642 561050529290019266850037 := by
  unfold tailWord_1092642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962981926888029310514045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26567951805034744828037453 9962981926888029310514045)
  ·
    refine ⟨3736118222583010991442767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9962981926888029310514045 3736118222583010991442767)
    ·
      refine ⟨5604177333874516487164151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736118222583010991442767 5604177333874516487164151)
      ·
        refine ⟨8406266000811774730746227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604177333874516487164151 8406266000811774730746227)
        ·
          refine ⟨12609399001217662096119341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8406266000811774730746227 12609399001217662096119341)
          ·
            refine ⟨4728524625456623286044753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12609399001217662096119341 4728524625456623286044753)
            ·
              refine ⟨3546393469092467464533565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4728524625456623286044753 3546393469092467464533565)
              ·
                refine ⟨1329897550909675299200087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3546393469092467464533565 1329897550909675299200087)
                ·
                  refine ⟨1994846326364512948800131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329897550909675299200087 1994846326364512948800131)
                  ·
                    refine ⟨2992269489546769423200197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994846326364512948800131 2992269489546769423200197)
                    ·
                      refine ⟨561050529290019266850037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2992269489546769423200197 561050529290019266850037)
                      ·
                        rfl

theorem cell23_1092642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1092642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092642 prefixEnd_1092642 := by exact prefixLift 1092642
  have htrace : WordTrace (prefixWord ++ tailWord_1092642) baseStart_1092642 baseEnd_1092642 := by
    simpa [prefixWord, tailWord_1092642, baseEnd_1092642] using wordTrace_append hprefix tailTrace_1092642
  have hstable : (prefixWord ++ tailWord_1092642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092642).length < 2 ^ (prefixWord ++ tailWord_1092642).sum := by decide
  have hdescent : baseEnd_1092642 < baseStart_1092642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092645 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_1092645 : Nat := 118140960795 + 1092645 * 2 ^ 59
def prefixEnd_1092645 : Nat := 4983230072969 + 3 ^ 40 * 1092645 * 2
def baseEnd_1092645 : Nat := 561052069731982755112523

theorem tailTrace_1092645 : CollatzResearch.WordTrace tailWord_1092645 prefixEnd_1092645 561052069731982755112523 := by
  unfold tailWord_1092645
  simp only [CollatzResearch.WordTrace]
  refine ⟨39852037126541248754415389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26568024751027499169610259 39852037126541248754415389)
  ·
    refine ⟨14944513922452968282905771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39852037126541248754415389 14944513922452968282905771)
    ·
      refine ⟨22416770883679452424358657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14944513922452968282905771 22416770883679452424358657)
      ·
        refine ⟨16812578162759589318268993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22416770883679452424358657 16812578162759589318268993)
        ·
          refine ⟨12609433622069691988701745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16812578162759589318268993 12609433622069691988701745)
          ·
            refine ⟨9457075216552268991526309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12609433622069691988701745 9457075216552268991526309)
            ·
              refine ⟨1773201603103550435911183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9457075216552268991526309 1773201603103550435911183)
              ·
                refine ⟨2659802404655325653866775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773201603103550435911183 2659802404655325653866775)
                ·
                  refine ⟨3989703606982988480800163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659802404655325653866775 3989703606982988480800163)
                  ·
                    refine ⟨5984555410474482721200245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989703606982988480800163 5984555410474482721200245)
                    ·
                      refine ⟨561052069731982755112523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5984555410474482721200245 561052069731982755112523)
                      ·
                        rfl

theorem cell23_1092645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_1092645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092645 prefixEnd_1092645 := by exact prefixLift 1092645
  have htrace : WordTrace (prefixWord ++ tailWord_1092645) baseStart_1092645 baseEnd_1092645 := by
    simpa [prefixWord, tailWord_1092645, baseEnd_1092645] using wordTrace_append hprefix tailTrace_1092645
  have hstable : (prefixWord ++ tailWord_1092645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092645).length < 2 ^ (prefixWord ++ tailWord_1092645).sum := by decide
  have hdescent : baseEnd_1092645 < baseStart_1092645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092662 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1092662 : Nat := 118140960795 + 1092662 * 2 ^ 59
def prefixEnd_1092662 : Nat := 4983230072969 + 3 ^ 40 * 1092662 * 2
def baseEnd_1092662 : Nat := 561060798903109188599945

theorem tailTrace_1092662 : CollatzResearch.WordTrace tailWord_1092662 prefixEnd_1092662 561060798903109188599945 := by
  unfold tailWord_1092662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490791072967478791111515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26568438111653107105189493 2490791072967478791111515)
  ·
    refine ⟨3736186609451218186667273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490791072967478791111515 3736186609451218186667273)
    ·
      refine ⟨2802139957088413640000455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3736186609451218186667273 2802139957088413640000455)
      ·
        refine ⟨4203209935632620460000683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802139957088413640000455 4203209935632620460000683)
        ·
          refine ⟨6304814903448930690001025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203209935632620460000683 6304814903448930690001025)
          ·
            refine ⟨4728611177586698017500769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6304814903448930690001025 4728611177586698017500769)
            ·
              refine ⟨3546458383190023513125577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4728611177586698017500769 3546458383190023513125577)
              ·
                refine ⟨2659843787392517634844183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546458383190023513125577 2659843787392517634844183)
                ·
                  refine ⟨3989765681088776452266275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659843787392517634844183 3989765681088776452266275)
                  ·
                    refine ⟨5984648521633164678399413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989765681088776452266275 5984648521633164678399413)
                    ·
                      refine ⟨561060798903109188599945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5984648521633164678399413 561060798903109188599945)
                      ·
                        rfl

theorem cell23_1092662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1092662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092662 prefixEnd_1092662 := by exact prefixLift 1092662
  have htrace : WordTrace (prefixWord ++ tailWord_1092662) baseStart_1092662 baseEnd_1092662 := by
    simpa [prefixWord, tailWord_1092662, baseEnd_1092662] using wordTrace_append hprefix tailTrace_1092662
  have hstable : (prefixWord ++ tailWord_1092662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092662).length < 2 ^ (prefixWord ++ tailWord_1092662).sum := by decide
  have hdescent : baseEnd_1092662 < baseStart_1092662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092665 : List Nat := [1, 2, 1, 5, 2, 2, 2, 8]
def baseStart_1092665 : Nat := 118140960795 + 1092665 * 2 ^ 59
def prefixEnd_1092665 : Nat := 4983230072969 + 3 ^ 40 * 1092665 * 2
def baseEnd_1092665 : Nat := 20780086642410099143053

theorem tailTrace_1092665 : CollatzResearch.WordTrace tailWord_1092665 prefixEnd_1092665 20780086642410099143053 := by
  unfold tailWord_1092665
  simp only [CollatzResearch.WordTrace]
  refine ⟨39852766586468792170143449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26568511057645861446762299 39852766586468792170143449)
  ·
    refine ⟨29889574939851594127607587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39852766586468792170143449 29889574939851594127607587)
    ·
      refine ⟨44834362409777391191411381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29889574939851594127607587 44834362409777391191411381)
      ·
        refine ⟨4203221475916630424194817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44834362409777391191411381 4203221475916630424194817)
        ·
          refine ⟨3152416106937472818146113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4203221475916630424194817 3152416106937472818146113)
          ·
            refine ⟨2364312080203104613609585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152416106937472818146113 2364312080203104613609585)
            ·
              refine ⟨1773234060152328460207189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364312080203104613609585 1773234060152328460207189)
              ·
                refine ⟨20780086642410099143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1773234060152328460207189 20780086642410099143053)
                ·
                  rfl

theorem cell23_1092665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 8].length) (baseStart_1092665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092665 prefixEnd_1092665 := by exact prefixLift 1092665
  have htrace : WordTrace (prefixWord ++ tailWord_1092665) baseStart_1092665 baseEnd_1092665 := by
    simpa [prefixWord, tailWord_1092665, baseEnd_1092665] using wordTrace_append hprefix tailTrace_1092665
  have hstable : (prefixWord ++ tailWord_1092665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092665).length < 2 ^ (prefixWord ++ tailWord_1092665).sum := by decide
  have hdescent : baseEnd_1092665 < baseStart_1092665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092669 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_1092669 : Nat := 118140960795 + 1092669 * 2 ^ 59
def prefixEnd_1092669 : Nat := 4983230072969 + 3 ^ 40 * 1092669 * 2
def baseEnd_1092669 : Nat := 187021464422563553737471

theorem tailTrace_1092669 : CollatzResearch.WordTrace tailWord_1092669 prefixEnd_1092669 187021464422563553737471 := by
  unfold tailWord_1092669
  simp only [CollatzResearch.WordTrace]
  refine ⟨39852912478454300853289061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26568608318969533902192707 39852912478454300853289061)
  ·
    refine ⟨7472421089710181409991699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39852912478454300853289061 7472421089710181409991699)
    ·
      refine ⟨11208631634565272114987549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7472421089710181409991699 11208631634565272114987549)
      ·
        refine ⟨4203236862961977043120331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11208631634565272114987549 4203236862961977043120331)
        ·
          refine ⟨6304855294442965564680497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203236862961977043120331 6304855294442965564680497)
          ·
            refine ⟨4728641470832224173510373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6304855294442965564680497 4728641470832224173510373)
            ·
              refine ⟨886620275781042032533195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4728641470832224173510373 886620275781042032533195)
              ·
                refine ⟨1329930413671563048799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886620275781042032533195 1329930413671563048799793)
                ·
                  refine ⟨997447810253672286599845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329930413671563048799793 997447810253672286599845)
                  ·
                    refine ⟨187021464422563553737471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 997447810253672286599845 187021464422563553737471)
                    ·
                      rfl

theorem cell23_1092669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_1092669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092669 prefixEnd_1092669 := by exact prefixLift 1092669
  have htrace : WordTrace (prefixWord ++ tailWord_1092669) baseStart_1092669 baseEnd_1092669 := by
    simpa [prefixWord, tailWord_1092669, baseEnd_1092669] using wordTrace_append hprefix tailTrace_1092669
  have hstable : (prefixWord ++ tailWord_1092669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092669).length < 2 ^ (prefixWord ++ tailWord_1092669).sum := by decide
  have hdescent : baseEnd_1092669 < baseStart_1092669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092675 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3]
def baseStart_1092675 : Nat := 118140960795 + 1092675 * 2 ^ 59
def prefixEnd_1092675 : Nat := 4983230072969 + 3 ^ 40 * 1092675 * 2
def baseEnd_1092675 : Nat := 561067474151617637737385

theorem tailTrace_1092675 : CollatzResearch.WordTrace tailWord_1092675 prefixEnd_1092675 561067474151617637737385 := by
  unfold tailWord_1092675
  simp only [CollatzResearch.WordTrace]
  refine ⟨39853131316432563878007479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26568754210955042585338319 39853131316432563878007479)
  ·
    refine ⟨59779696974648845817011219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39853131316432563878007479 59779696974648845817011219)
    ·
      refine ⟨89669545461973268725516829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59779696974648845817011219 89669545461973268725516829)
      ·
        refine ⟨33626079548239975772068811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89669545461973268725516829 33626079548239975772068811)
        ·
          refine ⟨50439119322359963658103217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33626079548239975772068811 50439119322359963658103217)
          ·
            refine ⟨37829339491769972743577413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50439119322359963658103217 37829339491769972743577413)
            ·
              refine ⟨7093001154706869889420765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37829339491769972743577413 7093001154706869889420765)
              ·
                refine ⟨2659875433015076208532787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7093001154706869889420765 2659875433015076208532787)
                ·
                  refine ⟨3989813149522614312799181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659875433015076208532787 3989813149522614312799181)
                  ·
                    refine ⟨1496179931070980367299693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3989813149522614312799181 1496179931070980367299693)
                    ·
                      refine ⟨561067474151617637737385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496179931070980367299693 561067474151617637737385)
                      ·
                        rfl

theorem cell23_1092675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_1092675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092675 prefixEnd_1092675 := by exact prefixLift 1092675
  have htrace : WordTrace (prefixWord ++ tailWord_1092675) baseStart_1092675 baseEnd_1092675 := by
    simpa [prefixWord, tailWord_1092675, baseEnd_1092675] using wordTrace_append hprefix tailTrace_1092675
  have hstable : (prefixWord ++ tailWord_1092675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092675).length < 2 ^ (prefixWord ++ tailWord_1092675).sum := by decide
  have hdescent : baseEnd_1092675 < baseStart_1092675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092679 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_1092679 : Nat := 118140960795 + 1092679 * 2 ^ 59
def prefixEnd_1092679 : Nat := 4983230072969 + 3 ^ 40 * 1092679 * 2
def baseEnd_1092679 : Nat := 561069528074235622087367

theorem tailTrace_1092679 : CollatzResearch.WordTrace tailWord_1092679 prefixEnd_1092679 561069528074235622087367 := by
  unfold tailWord_1092679
  simp only [CollatzResearch.WordTrace]
  refine ⟨39853277208418072561153091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26568851472278715040768727 39853277208418072561153091)
  ·
    refine ⟨59779915812627108841729637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39853277208418072561153091 59779915812627108841729637)
    ·
      refine ⟨11208734214867582907824307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59779915812627108841729637 11208734214867582907824307)
      ·
        refine ⟨16813101322301374361736461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11208734214867582907824307 16813101322301374361736461)
        ·
          refine ⟨6304912995863015385651173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16813101322301374361736461 6304912995863015385651173)
          ·
            refine ⟨1182171186724315384809595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6304912995863015385651173 1182171186724315384809595)
            ·
              refine ⟨1773256780086473077214393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182171186724315384809595 1773256780086473077214393)
              ·
                refine ⟨1329942585064854807910795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773256780086473077214393 1329942585064854807910795)
                ·
                  refine ⟨1994913877597282211866193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329942585064854807910795 1994913877597282211866193)
                  ·
                    refine ⟨1496185408197961658899645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994913877597282211866193 1496185408197961658899645)
                    ·
                      refine ⟨561069528074235622087367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496185408197961658899645 561069528074235622087367)
                      ·
                        rfl

theorem cell23_1092679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_1092679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092679 prefixEnd_1092679 := by exact prefixLift 1092679
  have htrace : WordTrace (prefixWord ++ tailWord_1092679) baseStart_1092679 baseEnd_1092679 := by
    simpa [prefixWord, tailWord_1092679, baseEnd_1092679] using wordTrace_append hprefix tailTrace_1092679
  have hstable : (prefixWord ++ tailWord_1092679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092679).length < 2 ^ (prefixWord ++ tailWord_1092679).sum := by decide
  have hdescent : baseEnd_1092679 < baseStart_1092679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092688 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1092688 : Nat := 118140960795 + 1092688 * 2 ^ 59
def prefixEnd_1092688 : Nat := 4983230072969 + 3 ^ 40 * 1092688 * 2
def baseEnd_1092688 : Nat := 561074149400126086874825

theorem tailTrace_1092688 : CollatzResearch.WordTrace tailWord_1092688 prefixEnd_1092688 561074149400126086874825 := by
  unfold tailWord_1092688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926802732692733549115359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26569070310256978065487145 19926802732692733549115359)
  ·
    refine ⟨29890204099039100323673039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19926802732692733549115359 29890204099039100323673039)
    ·
      refine ⟨44835306148558650485509559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29890204099039100323673039 44835306148558650485509559)
      ·
        refine ⟨67252959222837975728264339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44835306148558650485509559 67252959222837975728264339)
        ·
          refine ⟨100879438834256963592396509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67252959222837975728264339 100879438834256963592396509)
          ·
            refine ⟨37829789562846361347148691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100879438834256963592396509 37829789562846361347148691)
            ·
              refine ⟨56744684344269542020723037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37829789562846361347148691 56744684344269542020723037)
              ·
                refine ⟨21279256629101078257771139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56744684344269542020723037 21279256629101078257771139)
                ·
                  refine ⟨31918884943651617386656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21279256629101078257771139 31918884943651617386656709)
                  ·
                    refine ⟨5984790926934678259998133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31918884943651617386656709 5984790926934678259998133)
                    ·
                      refine ⟨561074149400126086874825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5984790926934678259998133 561074149400126086874825)
                      ·
                        rfl

theorem cell23_1092688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1092688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092688 prefixEnd_1092688 := by exact prefixLift 1092688
  have htrace : WordTrace (prefixWord ++ tailWord_1092688) baseStart_1092688 baseEnd_1092688 := by
    simpa [prefixWord, tailWord_1092688, baseEnd_1092688] using wordTrace_append hprefix tailTrace_1092688
  have hstable : (prefixWord ++ tailWord_1092688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092688).length < 2 ^ (prefixWord ++ tailWord_1092688).sum := by decide
  have hdescent : baseEnd_1092688 < baseStart_1092688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092692 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1092692 : Nat := 118140960795 + 1092692 * 2 ^ 59
def prefixEnd_1092692 : Nat := 4983230072969 + 3 ^ 40 * 1092692 * 2
def baseEnd_1092692 : Nat := 561076203322744071224807

theorem tailTrace_1092692 : CollatzResearch.WordTrace tailWord_1092692 prefixEnd_1092692 561076203322744071224807 := by
  unfold tailWord_1092692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926875678685487890688165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26569167571580650520917553 19926875678685487890688165)
  ·
    refine ⟨3736289189753528979504031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19926875678685487890688165 3736289189753528979504031)
    ·
      refine ⟨5604433784630293469256047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736289189753528979504031 5604433784630293469256047)
      ·
        refine ⟨8406650676945440203884071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604433784630293469256047 8406650676945440203884071)
        ·
          refine ⟨12609976015418160305826107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8406650676945440203884071 12609976015418160305826107)
          ·
            refine ⟨18914964023127240458739161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12609976015418160305826107 18914964023127240458739161)
            ·
              refine ⟨14186223017345430344054371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18914964023127240458739161 14186223017345430344054371)
              ·
                refine ⟨21279334526018145516081557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14186223017345430344054371 21279334526018145516081557)
                ·
                  refine ⟨997468805907100571066323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21279334526018145516081557 997468805907100571066323)
                  ·
                    refine ⟨1496203208860650856599485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997468805907100571066323 1496203208860650856599485)
                    ·
                      refine ⟨561076203322744071224807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496203208860650856599485 561076203322744071224807)
                      ·
                        rfl

theorem cell23_1092692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1092692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092692 prefixEnd_1092692 := by exact prefixLift 1092692
  have htrace : WordTrace (prefixWord ++ tailWord_1092692) baseStart_1092692 baseEnd_1092692 := by
    simpa [prefixWord, tailWord_1092692, baseEnd_1092692] using wordTrace_append hprefix tailTrace_1092692
  have hstable : (prefixWord ++ tailWord_1092692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092692).length < 2 ^ (prefixWord ++ tailWord_1092692).sum := by decide
  have hdescent : baseEnd_1092692 < baseStart_1092692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092709 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1092709 : Nat := 118140960795 + 1092709 * 2 ^ 59
def prefixEnd_1092709 : Nat := 4983230072969 + 3 ^ 40 * 1092709 * 2
def baseEnd_1092709 : Nat := 561084932493870504712229

theorem tailTrace_1092709 : CollatzResearch.WordTrace tailWord_1092709 prefixEnd_1092709 561084932493870504712229 := by
  unfold tailWord_1092709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39854371398309387684745181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26569580932206258456496787 39854371398309387684745181)
  ·
    refine ⟨14945389274366020381779443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39854371398309387684745181 14945389274366020381779443)
    ·
      refine ⟨22418083911549030572669165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14945389274366020381779443 22418083911549030572669165)
      ·
        refine ⟨8406781466830886464750937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22418083911549030572669165 8406781466830886464750937)
        ·
          refine ⟨6305086100123164848563203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8406781466830886464750937 6305086100123164848563203)
          ·
            refine ⟨9457629150184747272844805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305086100123164848563203 9457629150184747272844805)
            ·
              refine ⟨1773305465659640113658401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9457629150184747272844805 1773305465659640113658401)
              ·
                refine ⟨1329979099244730085243801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773305465659640113658401 1329979099244730085243801)
                ·
                  refine ⟨997484324433547563932851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329979099244730085243801 997484324433547563932851)
                  ·
                    refine ⟨1496226486650321345899277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997484324433547563932851 1496226486650321345899277)
                    ·
                      refine ⟨561084932493870504712229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496226486650321345899277 561084932493870504712229)
                      ·
                        rfl

theorem cell23_1092709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1092709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092709 prefixEnd_1092709 := by exact prefixLift 1092709
  have htrace : WordTrace (prefixWord ++ tailWord_1092709) baseStart_1092709 baseEnd_1092709 := by
    simpa [prefixWord, tailWord_1092709, baseEnd_1092709] using wordTrace_append hprefix tailTrace_1092709
  have hstable : (prefixWord ++ tailWord_1092709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092709).length < 2 ^ (prefixWord ++ tailWord_1092709).sum := by decide
  have hdescent : baseEnd_1092709 < baseStart_1092709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092762 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1092762 : Nat := 118140960795 + 1092762 * 2 ^ 59
def prefixEnd_1092762 : Nat := 4983230072969 + 3 ^ 40 * 1092762 * 2
def baseEnd_1092762 : Nat := 561112146968558797349485

theorem tailTrace_1092762 : CollatzResearch.WordTrace tailWord_1092762 prefixEnd_1092762 561112146968558797349485 := by
  unfold tailWord_1092762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9964076116779344434106135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26570869644744918490949693 9964076116779344434106135)
  ·
    refine ⟨14946114175169016651159203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9964076116779344434106135 14946114175169016651159203)
    ·
      refine ⟨22419171262753524976738805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14946114175169016651159203 22419171262753524976738805)
      ·
        refine ⟨2101797305883142966569263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22419171262753524976738805 2101797305883142966569263)
        ·
          refine ⟨3152695958824714449853895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101797305883142966569263 3152695958824714449853895)
          ·
            refine ⟨4729043938237071674780843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152695958824714449853895 4729043938237071674780843)
            ·
              refine ⟨7093565907355607512171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729043938237071674780843 7093565907355607512171265)
              ·
                refine ⟨5320174430516705634128449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7093565907355607512171265 5320174430516705634128449)
                ·
                  refine ⟨3990130822887529225596337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320174430516705634128449 3990130822887529225596337)
                  ·
                    refine ⟨2992598117165646919197253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990130822887529225596337 2992598117165646919197253)
                    ·
                      refine ⟨561112146968558797349485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2992598117165646919197253 561112146968558797349485)
                      ·
                        rfl

theorem cell23_1092762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1092762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092762 prefixEnd_1092762 := by exact prefixLift 1092762
  have htrace : WordTrace (prefixWord ++ tailWord_1092762) baseStart_1092762 baseEnd_1092762 := by
    simpa [prefixWord, tailWord_1092762, baseEnd_1092762] using wordTrace_append hprefix tailTrace_1092762
  have hstable : (prefixWord ++ tailWord_1092762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092762).length < 2 ^ (prefixWord ++ tailWord_1092762).sum := by decide
  have hdescent : baseEnd_1092762 < baseStart_1092762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092772 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1092772 : Nat := 118140960795 + 1092772 * 2 ^ 59
def prefixEnd_1092772 : Nat := 4983230072969 + 3 ^ 40 * 1092772 * 2
def baseEnd_1092772 : Nat := 62346364641678195358271

theorem tailTrace_1092772 : CollatzResearch.WordTrace tailWord_1092772 prefixEnd_1092772 62346364641678195358271 := by
  unfold tailWord_1092772
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928334598540574722144285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26571112798054099629525713 19928334598540574722144285)
  ·
    refine ⟨7473125474452715520804107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19928334598540574722144285 7473125474452715520804107)
    ·
      refine ⟨11209688211679073281206161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7473125474452715520804107 11209688211679073281206161)
      ·
        refine ⟨8407266158759304960904621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11209688211679073281206161 8407266158759304960904621)
        ·
          refine ⟨3152724809534739360339233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8407266158759304960904621 3152724809534739360339233)
          ·
            refine ⟨2364543607151054520254425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152724809534739360339233 2364543607151054520254425)
            ·
              refine ⟨1773407705363290890190819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364543607151054520254425 1773407705363290890190819)
              ·
                refine ⟨2660111558044936335286229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773407705363290890190819 2660111558044936335286229)
                ·
                  refine ⟨62346364641678195358271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2660111558044936335286229 62346364641678195358271)
                  ·
                    rfl

theorem cell23_1092772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1092772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092772 prefixEnd_1092772 := by exact prefixLift 1092772
  have htrace : WordTrace (prefixWord ++ tailWord_1092772) baseStart_1092772 baseEnd_1092772 := by
    simpa [prefixWord, tailWord_1092772, baseEnd_1092772] using wordTrace_append hprefix tailTrace_1092772
  have hstable : (prefixWord ++ tailWord_1092772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092772).length < 2 ^ (prefixWord ++ tailWord_1092772).sum := by decide
  have hdescent : baseEnd_1092772 < baseStart_1092772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092829 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1092829 : Nat := 118140960795 + 1092829 * 2 ^ 59
def prefixEnd_1092829 : Nat := 4983230072969 + 3 ^ 40 * 1092829 * 2
def baseEnd_1092829 : Nat := 561146550172410035211677

theorem tailTrace_1092829 : CollatzResearch.WordTrace tailWord_1092829 prefixEnd_1092829 561146550172410035211677 := by
  unfold tailWord_1092829
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858748157874648179113541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26572498771916432119409027 39858748157874648179113541)
  ·
    refine ⟨7473515279601496533583789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39858748157874648179113541 7473515279601496533583789)
    ·
      refine ⟨2802568229850561200093921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7473515279601496533583789 2802568229850561200093921)
      ·
        refine ⟨2101926172387920900070441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802568229850561200093921 2101926172387920900070441)
        ·
          refine ⟨1576444629290940675052831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101926172387920900070441 1576444629290940675052831)
          ·
            refine ⟨2364666943936411012579247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576444629290940675052831 2364666943936411012579247)
            ·
              refine ⟨3547000415904616518868871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364666943936411012579247 3547000415904616518868871)
              ·
                refine ⟨5320500623856924778303307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547000415904616518868871 5320500623856924778303307)
                ·
                  refine ⟨7980750935785387167454961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5320500623856924778303307 7980750935785387167454961)
                  ·
                    refine ⟨5985563201839040375591221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7980750935785387167454961 5985563201839040375591221)
                    ·
                      refine ⟨561146550172410035211677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5985563201839040375591221 561146550172410035211677)
                      ·
                        rfl

theorem cell23_1092829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1092829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092829 prefixEnd_1092829 := by exact prefixLift 1092829
  have htrace : WordTrace (prefixWord ++ tailWord_1092829) baseStart_1092829 baseEnd_1092829 := by
    simpa [prefixWord, tailWord_1092829, baseEnd_1092829] using wordTrace_append hprefix tailTrace_1092829
  have hstable : (prefixWord ++ tailWord_1092829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092829).length < 2 ^ (prefixWord ++ tailWord_1092829).sum := by decide
  have hdescent : baseEnd_1092829 < baseStart_1092829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092892 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1092892 : Nat := 118140960795 + 1092892 * 2 ^ 59
def prefixEnd_1092892 : Nat := 4983230072969 + 3 ^ 40 * 1092892 * 2
def baseEnd_1092892 : Nat := 187059633151214429574629

theorem tailTrace_1092892 : CollatzResearch.WordTrace tailWord_1092892 prefixEnd_1092892 187059633151214429574629 := by
  unfold tailWord_1092892
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930522978323204969328465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26574030637764273292437953 19930522978323204969328465)
  ·
    refine ⟨14947892233742403726996349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19930522978323204969328465 14947892233742403726996349)
    ·
      refine ⟨5605459587653401397623631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14947892233742403726996349 5605459587653401397623631)
      ·
        refine ⟨8408189381480102096435447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5605459587653401397623631 8408189381480102096435447)
        ·
          refine ⟨12612284072220153144653171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408189381480102096435447 12612284072220153144653171)
          ·
            refine ⟨18918426108330229716979757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612284072220153144653171 18918426108330229716979757)
            ·
              refine ⟨7094409790623836143867409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18918426108330229716979757 7094409790623836143867409)
              ·
                refine ⟨5320807342967877107900557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094409790623836143867409 5320807342967877107900557)
                ·
                  refine ⟨1995302753612953915462709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5320807342967877107900557 1995302753612953915462709)
                  ·
                    refine ⟨187059633151214429574629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1995302753612953915462709 187059633151214429574629)
                    ·
                      rfl

theorem cell23_1092892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1092892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092892 prefixEnd_1092892 := by exact prefixLift 1092892
  have htrace : WordTrace (prefixWord ++ tailWord_1092892) baseStart_1092892 baseEnd_1092892 := by
    simpa [prefixWord, tailWord_1092892, baseEnd_1092892] using wordTrace_append hprefix tailTrace_1092892
  have hstable : (prefixWord ++ tailWord_1092892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092892).length < 2 ^ (prefixWord ++ tailWord_1092892).sum := by decide
  have hdescent : baseEnd_1092892 < baseStart_1092892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092906 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1092906 : Nat := 118140960795 + 1092906 * 2 ^ 59
def prefixEnd_1092906 : Nat := 4983230072969 + 3 ^ 40 * 1092906 * 2
def baseEnd_1092906 : Nat := 561186088182806233948823

theorem tailTrace_1092906 : CollatzResearch.WordTrace tailWord_1092906 prefixEnd_1092906 561186088182806233948823 := by
  unfold tailWord_1092906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965389144648922582416643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26574371052397126886444381 9965389144648922582416643)
  ·
    refine ⟨14948083716973383873624965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9965389144648922582416643 14948083716973383873624965)
    ·
      refine ⟨2802765696932509476304681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14948083716973383873624965 2802765696932509476304681)
      ·
        refine ⟨2102074272699382107228511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802765696932509476304681 2102074272699382107228511)
        ·
          refine ⟨3153111409049073160842767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102074272699382107228511 3153111409049073160842767)
          ·
            refine ⟨4729667113573609741264151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153111409049073160842767 4729667113573609741264151)
            ·
              refine ⟨7094500670360414611896227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729667113573609741264151 7094500670360414611896227)
              ·
                refine ⟨10641751005540621917844341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7094500670360414611896227 10641751005540621917844341)
                ·
                  refine ⟨997664156769433304797907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10641751005540621917844341 997664156769433304797907)
                  ·
                    refine ⟨1496496235154149957196861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997664156769433304797907 1496496235154149957196861)
                    ·
                      refine ⟨561186088182806233948823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496496235154149957196861 561186088182806233948823)
                      ·
                        rfl

theorem cell23_1092906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1092906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092906 prefixEnd_1092906 := by exact prefixLift 1092906
  have htrace : WordTrace (prefixWord ++ tailWord_1092906) baseStart_1092906 baseEnd_1092906 := by
    simpa [prefixWord, tailWord_1092906, baseEnd_1092906] using wordTrace_append hprefix tailTrace_1092906
  have hstable : (prefixWord ++ tailWord_1092906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092906).length < 2 ^ (prefixWord ++ tailWord_1092906).sum := by decide
  have hdescent : baseEnd_1092906 < baseStart_1092906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092912 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_1092912 : Nat := 118140960795 + 1092912 * 2 ^ 59
def prefixEnd_1092912 : Nat := 4983230072969 + 3 ^ 40 * 1092912 * 2
def baseEnd_1092912 : Nat := 561189169066733210473795

theorem tailTrace_1092912 : CollatzResearch.WordTrace tailWord_1092912 prefixEnd_1092912 561189169066733210473795 := by
  unfold tailWord_1092912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930887708286976677192495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26574516944382635569589993 19930887708286976677192495)
  ·
    refine ⟨29896331562430465015788743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19930887708286976677192495 29896331562430465015788743)
    ·
      refine ⟨44844497343645697523683115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29896331562430465015788743 44844497343645697523683115)
      ·
        refine ⟨67266746015468546285524673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44844497343645697523683115 67266746015468546285524673)
        ·
          refine ⟨50450059511601409714143505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67266746015468546285524673 50450059511601409714143505)
          ·
            refine ⟨37837544633701057285607629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50450059511601409714143505 37837544633701057285607629)
            ·
              refine ⟨14189079237637896482102861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37837544633701057285607629 14189079237637896482102861)
              ·
                refine ⟨5320904714114211180788573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14189079237637896482102861 5320904714114211180788573)
                ·
                  refine ⟨1995339267792829192795715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5320904714114211180788573 1995339267792829192795715)
                  ·
                    refine ⟨2993008901689243789193573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1995339267792829192795715 2993008901689243789193573)
                    ·
                      refine ⟨561189169066733210473795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2993008901689243789193573 561189169066733210473795)
                      ·
                        rfl

theorem cell23_1092912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_1092912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092912 prefixEnd_1092912 := by exact prefixLift 1092912
  have htrace : WordTrace (prefixWord ++ tailWord_1092912) baseStart_1092912 baseEnd_1092912 := by
    simpa [prefixWord, tailWord_1092912, baseEnd_1092912] using wordTrace_append hprefix tailTrace_1092912
  have hstable : (prefixWord ++ tailWord_1092912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092912).length < 2 ^ (prefixWord ++ tailWord_1092912).sum := by decide
  have hdescent : baseEnd_1092912 < baseStart_1092912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092916 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1092916 : Nat := 118140960795 + 1092916 * 2 ^ 59
def prefixEnd_1092916 : Nat := 4983230072969 + 3 ^ 40 * 1092916 * 2
def baseEnd_1092916 : Nat := 561191222989351194823777

theorem tailTrace_1092916 : CollatzResearch.WordTrace tailWord_1092916 prefixEnd_1092916 561191222989351194823777 := by
  unfold tailWord_1092916
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930960654279731018765301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26574614205706308025020401 19930960654279731018765301)
  ·
    refine ⟨1868527561338724783009247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19930960654279731018765301 1868527561338724783009247)
    ·
      refine ⟨2802791342008087174513871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868527561338724783009247 2802791342008087174513871)
      ·
        refine ⟨4204187013012130761770807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802791342008087174513871 4204187013012130761770807)
        ·
          refine ⟨6306280519518196142656211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204187013012130761770807 6306280519518196142656211)
          ·
            refine ⟨9459420779277294213984317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306280519518196142656211 9459420779277294213984317)
            ·
              refine ⟨3547282792228985330244119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9459420779277294213984317 3547282792228985330244119)
              ·
                refine ⟨5320924188343477995366179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547282792228985330244119 5320924188343477995366179)
                ·
                  refine ⟨7981386282515216993049269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5320924188343477995366179 7981386282515216993049269)
                  ·
                    refine ⟨748254963985801593098369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7981386282515216993049269 748254963985801593098369)
                    ·
                      refine ⟨561191222989351194823777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748254963985801593098369 561191222989351194823777)
                      ·
                        rfl

theorem cell23_1092916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1092916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092916 prefixEnd_1092916 := by exact prefixLift 1092916
  have htrace : WordTrace (prefixWord ++ tailWord_1092916) baseStart_1092916 baseEnd_1092916 := by
    simpa [prefixWord, tailWord_1092916, baseEnd_1092916] using wordTrace_append hprefix tailTrace_1092916
  have hstable : (prefixWord ++ tailWord_1092916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092916).length < 2 ^ (prefixWord ++ tailWord_1092916).sum := by decide
  have hdescent : baseEnd_1092916 < baseStart_1092916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092922 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_1092922 : Nat := 118140960795 + 1092922 * 2 ^ 59
def prefixEnd_1092922 : Nat := 4983230072969 + 3 ^ 40 * 1092922 * 2
def baseEnd_1092922 : Nat := 187064767957759390449583

theorem tailTrace_1092922 : CollatzResearch.WordTrace tailWord_1092922 prefixEnd_1092922 187064767957759390449583 := by
  unfold tailWord_1092922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965535036634431265562255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26574760097691816708166013 9965535036634431265562255)
  ·
    refine ⟨14948302554951646898343383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9965535036634431265562255 14948302554951646898343383)
    ·
      refine ⟨22422453832427470347515075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14948302554951646898343383 22422453832427470347515075)
      ·
        refine ⟨33633680748641205521272613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22422453832427470347515075 33633680748641205521272613)
        ·
          refine ⟨6306315140370226035238615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33633680748641205521272613 6306315140370226035238615)
          ·
            refine ⟨9459472710555339052857923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306315140370226035238615 9459472710555339052857923)
            ·
              refine ⟨14189209065833008579286885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459472710555339052857923 14189209065833008579286885)
              ·
                refine ⟨2660476699843689108616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14189209065833008579286885 2660476699843689108616291)
                ·
                  refine ⟨3990715049765533662924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660476699843689108616291 3990715049765533662924437)
                  ·
                    refine ⟨187064767957759390449583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3990715049765533662924437 187064767957759390449583)
                    ·
                      rfl

theorem cell23_1092922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_1092922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092922 prefixEnd_1092922 := by exact prefixLift 1092922
  have htrace : WordTrace (prefixWord ++ tailWord_1092922) baseStart_1092922 baseEnd_1092922 := by
    simpa [prefixWord, tailWord_1092922, baseEnd_1092922] using wordTrace_append hprefix tailTrace_1092922
  have hstable : (prefixWord ++ tailWord_1092922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092922).length < 2 ^ (prefixWord ++ tailWord_1092922).sum := by decide
  have hdescent : baseEnd_1092922 < baseStart_1092922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092942 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1092942 : Nat := 118140960795 + 1092942 * 2 ^ 59
def prefixEnd_1092942 : Nat := 4983230072969 + 3 ^ 40 * 1092942 * 2
def baseEnd_1092942 : Nat := 561204573486368093098657

theorem tailTrace_1092942 : CollatzResearch.WordTrace tailWord_1092942 prefixEnd_1092942 561204573486368093098657 := by
  unfold tailWord_1092942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982858700808158559747135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26575246404310178985318053 4982858700808158559747135)
  ·
    refine ⟨7474288051212237839620703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982858700808158559747135 7474288051212237839620703)
    ·
      refine ⟨11211432076818356759431055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474288051212237839620703 11211432076818356759431055)
      ·
        refine ⟨16817148115227535139146583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11211432076818356759431055 16817148115227535139146583)
        ·
          refine ⟨25225722172841302708719875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16817148115227535139146583 25225722172841302708719875)
          ·
            refine ⟨37838583259261954063079813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25225722172841302708719875 37838583259261954063079813)
            ·
              refine ⟨7094734361111616386827465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37838583259261954063079813 7094734361111616386827465)
              ·
                refine ⟨5321050770833712290120599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094734361111616386827465 5321050770833712290120599)
                ·
                  refine ⟨7981576156250568435180899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321050770833712290120599 7981576156250568435180899)
                  ·
                    refine ⟨11972364234375852652771349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7981576156250568435180899 11972364234375852652771349)
                    ·
                      refine ⟨561204573486368093098657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11972364234375852652771349 561204573486368093098657)
                      ·
                        rfl

theorem cell23_1092942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1092942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092942 prefixEnd_1092942 := by exact prefixLift 1092942
  have htrace : WordTrace (prefixWord ++ tailWord_1092942) baseStart_1092942 baseEnd_1092942 := by
    simpa [prefixWord, tailWord_1092942, baseEnd_1092942] using wordTrace_append hprefix tailTrace_1092942
  have hstable : (prefixWord ++ tailWord_1092942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092942).length < 2 ^ (prefixWord ++ tailWord_1092942).sum := by decide
  have hdescent : baseEnd_1092942 < baseStart_1092942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092949 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1092949 : Nat := 118140960795 + 1092949 * 2 ^ 59
def prefixEnd_1092949 : Nat := 4983230072969 + 3 ^ 40 * 1092949 * 2
def baseEnd_1092949 : Nat := 561208167850949565711125

theorem tailTrace_1092949 : CollatzResearch.WordTrace tailWord_1092949 prefixEnd_1092949 561208167850949565711125 := by
  unfold tailWord_1092949
  simp only [CollatzResearch.WordTrace]
  refine ⟨39863124917439908673481901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26575416611626605782321267 39863124917439908673481901)
  ·
    refine ⟨14948671844039965752555713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39863124917439908673481901 14948671844039965752555713)
    ·
      refine ⟨11211503883029974314416785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14948671844039965752555713 11211503883029974314416785)
      ·
        refine ⟨8408627912272480735812589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11211503883029974314416785 8408627912272480735812589)
        ·
          refine ⟨3153235467102180275929721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8408627912272480735812589 3153235467102180275929721)
          ·
            refine ⟨2364926600326635206947291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3153235467102180275929721 2364926600326635206947291)
            ·
              refine ⟨3547389900489952810420937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364926600326635206947291 3547389900489952810420937)
              ·
                refine ⟨2660542425367464607815703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547389900489952810420937 2660542425367464607815703)
                ·
                  refine ⟨3990813638051196911723555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660542425367464607815703 3990813638051196911723555)
                  ·
                    refine ⟨5986220457076795367585333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3990813638051196911723555 5986220457076795367585333)
                    ·
                      refine ⟨561208167850949565711125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5986220457076795367585333 561208167850949565711125)
                      ·
                        rfl

theorem cell23_1092949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1092949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092949 prefixEnd_1092949 := by exact prefixLift 1092949
  have htrace : WordTrace (prefixWord ++ tailWord_1092949) baseStart_1092949 baseEnd_1092949 := by
    simpa [prefixWord, tailWord_1092949, baseEnd_1092949] using wordTrace_append hprefix tailTrace_1092949
  have hstable : (prefixWord ++ tailWord_1092949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092949).length < 2 ^ (prefixWord ++ tailWord_1092949).sum := by decide
  have hdescent : baseEnd_1092949 < baseStart_1092949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092974 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1092974 : Nat := 118140960795 + 1092974 * 2 ^ 59
def prefixEnd_1092974 : Nat := 4983230072969 + 3 ^ 40 * 1092974 * 2
def baseEnd_1092974 : Nat := 561221004867311967898511

theorem tailTrace_1092974 : CollatzResearch.WordTrace tailWord_1092974 prefixEnd_1092974 561221004867311967898511 := by
  unfold tailWord_1092974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983004592793667242892747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26576024494899558628761317 4983004592793667242892747)
  ·
    refine ⟨7474506889190500864339121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4983004592793667242892747 7474506889190500864339121)
    ·
      refine ⟨5605880166892875648254341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7474506889190500864339121 5605880166892875648254341)
      ·
        refine ⟨1051102531292414184047689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5605880166892875648254341 1051102531292414184047689)
        ·
          refine ⟨788326898469310638035767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051102531292414184047689 788326898469310638035767)
          ·
            refine ⟨1182490347703965957053651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788326898469310638035767 1182490347703965957053651)
            ·
              refine ⟨1773735521555948935580477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182490347703965957053651 1773735521555948935580477)
              ·
                refine ⟨665150820583480850842679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773735521555948935580477 665150820583480850842679)
                ·
                  refine ⟨997726230875221276264019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665150820583480850842679 997726230875221276264019)
                  ·
                    refine ⟨1496589346312831914396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997726230875221276264019 1496589346312831914396029)
                    ·
                      refine ⟨561221004867311967898511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496589346312831914396029 561221004867311967898511)
                      ·
                        rfl

theorem cell23_1092974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1092974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092974 prefixEnd_1092974 := by exact prefixLift 1092974
  have htrace : WordTrace (prefixWord ++ tailWord_1092974) baseStart_1092974 baseEnd_1092974 := by
    simpa [prefixWord, tailWord_1092974, baseEnd_1092974] using wordTrace_append hprefix tailTrace_1092974
  have hstable : (prefixWord ++ tailWord_1092974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092974).length < 2 ^ (prefixWord ++ tailWord_1092974).sum := by decide
  have hdescent : baseEnd_1092974 < baseStart_1092974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092996 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1092996 : Nat := 118140960795 + 1092996 * 2 ^ 59
def prefixEnd_1092996 : Nat := 4983230072969 + 3 ^ 40 * 1092996 * 2
def baseEnd_1092996 : Nat := 561232301441710881823409

theorem tailTrace_1092996 : CollatzResearch.WordTrace tailWord_1092996 prefixEnd_1092996 561232301441710881823409 := by
  unfold tailWord_1092996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932419574134817850221421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26576559432179757133628561 19932419574134817850221421)
  ·
    refine ⟨7474657340300556693833033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19932419574134817850221421 7474657340300556693833033)
    ·
      refine ⟨5605993005225417520374775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7474657340300556693833033 5605993005225417520374775)
      ·
        refine ⟨8408989507838126280562163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5605993005225417520374775 8408989507838126280562163)
        ·
          refine ⟨12613484261757189420843245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408989507838126280562163 12613484261757189420843245)
          ·
            refine ⟨4730056598158946032816217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613484261757189420843245 4730056598158946032816217)
            ·
              refine ⟨3547542448619209524612163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730056598158946032816217 3547542448619209524612163)
              ·
                refine ⟨5321313672928814286918245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547542448619209524612163 5321313672928814286918245)
                ·
                  refine ⟨997746313674152678797171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5321313672928814286918245 997746313674152678797171)
                  ·
                    refine ⟨1496619470511229018195757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997746313674152678797171 1496619470511229018195757)
                    ·
                      refine ⟨561232301441710881823409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496619470511229018195757 561232301441710881823409)
                      ·
                        rfl

theorem cell23_1092996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1092996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1092996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1092996 prefixEnd_1092996 := by exact prefixLift 1092996
  have htrace : WordTrace (prefixWord ++ tailWord_1092996) baseStart_1092996 baseEnd_1092996 := by
    simpa [prefixWord, tailWord_1092996, baseEnd_1092996] using wordTrace_append hprefix tailTrace_1092996
  have hstable : (prefixWord ++ tailWord_1092996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092996).length < 2 ^ (prefixWord ++ tailWord_1092996).sum := by decide
  have hdescent : baseEnd_1092996 < baseStart_1092996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093013 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_1093013 : Nat := 118140960795 + 1093013 * 2 ^ 59
def prefixEnd_1093013 : Nat := 4983230072969 + 3 ^ 40 * 1093013 * 2
def baseEnd_1093013 : Nat := 561241030612837315310831

theorem tailTrace_1093013 : CollatzResearch.WordTrace tailWord_1093013 prefixEnd_1093013 561241030612837315310831 := by
  unfold tailWord_1093013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39865459189208047603811693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26576972792805365069207795 39865459189208047603811693)
  ·
    refine ⟨14949547195953017851429385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39865459189208047603811693 14949547195953017851429385)
    ·
      refine ⟨11212160396964763388572039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14949547195953017851429385 11212160396964763388572039)
      ·
        refine ⟨16818240595447145082858059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212160396964763388572039 16818240595447145082858059)
        ·
          refine ⟨25227360893170717624287089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16818240595447145082858059 25227360893170717624287089)
          ·
            refine ⟨18920520669878038218215317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25227360893170717624287089 18920520669878038218215317)
            ·
              refine ⟨886899406400533041478843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18920520669878038218215317 886899406400533041478843)
              ·
                refine ⟨1330349109600799562218265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886899406400533041478843 1330349109600799562218265)
                ·
                  refine ⟨997761832200599671663699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1330349109600799562218265 997761832200599671663699)
                  ·
                    refine ⟨1496642748300899507495549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997761832200599671663699 1496642748300899507495549)
                    ·
                      refine ⟨561241030612837315310831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496642748300899507495549 561241030612837315310831)
                      ·
                        rfl

theorem cell23_1093013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_1093013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093013 prefixEnd_1093013 := by exact prefixLift 1093013
  have htrace : WordTrace (prefixWord ++ tailWord_1093013) baseStart_1093013 baseEnd_1093013 := by
    simpa [prefixWord, tailWord_1093013, baseEnd_1093013] using wordTrace_append hprefix tailTrace_1093013
  have hstable : (prefixWord ++ tailWord_1093013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093013).length < 2 ^ (prefixWord ++ tailWord_1093013).sum := by decide
  have hdescent : baseEnd_1093013 < baseStart_1093013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093023 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1093023 : Nat := 118140960795 + 1093023 * 2 ^ 59
def prefixEnd_1093023 : Nat := 4983230072969 + 3 ^ 40 * 1093023 * 2
def baseEnd_1093023 : Nat := 561246165419382276185785

theorem tailTrace_1093023 : CollatzResearch.WordTrace tailWord_1093023 prefixEnd_1093023 561246165419382276185785 := by
  unfold tailWord_1093023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39865823919171819311675723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26577215946114546207783815 39865823919171819311675723)
  ·
    refine ⟨59798735878757728967513585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39865823919171819311675723 59798735878757728967513585)
    ·
      refine ⟨44849051909068296725635189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59798735878757728967513585 44849051909068296725635189)
      ·
        refine ⟨4204598616475152818028299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44849051909068296725635189 4204598616475152818028299)
        ·
          refine ⟨6306897924712729227042449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204598616475152818028299 6306897924712729227042449)
          ·
            refine ⟨4730173443534546920281837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6306897924712729227042449 4730173443534546920281837)
            ·
              refine ⟨1773815041325455095105689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4730173443534546920281837 1773815041325455095105689)
              ·
                refine ⟨1330361280994091321329267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773815041325455095105689 1330361280994091321329267)
                ·
                  refine ⟨1995541921491136981993901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330361280994091321329267 1995541921491136981993901)
                  ·
                    refine ⟨748328220559176368247713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995541921491136981993901 748328220559176368247713)
                    ·
                      refine ⟨561246165419382276185785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748328220559176368247713 561246165419382276185785)
                      ·
                        rfl

theorem cell23_1093023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1093023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093023 prefixEnd_1093023 := by exact prefixLift 1093023
  have htrace : WordTrace (prefixWord ++ tailWord_1093023) baseStart_1093023 baseEnd_1093023 := by
    simpa [prefixWord, tailWord_1093023, baseEnd_1093023] using wordTrace_append hprefix tailTrace_1093023
  have hstable : (prefixWord ++ tailWord_1093023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093023).length < 2 ^ (prefixWord ++ tailWord_1093023).sum := by decide
  have hdescent : baseEnd_1093023 < baseStart_1093023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093036 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_1093036 : Nat := 118140960795 + 1093036 * 2 ^ 59
def prefixEnd_1093036 : Nat := 4983230072969 + 3 ^ 40 * 1093036 * 2
def baseEnd_1093036 : Nat := 561252840667890725323225

theorem tailTrace_1093036 : CollatzResearch.WordTrace tailWord_1093036 prefixEnd_1093036 561252840667890725323225 := by
  unfold tailWord_1093036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933149034062361265949481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26577532045416481687932641 19933149034062361265949481)
  ·
    refine ⟨14949861775546770949462111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19933149034062361265949481 14949861775546770949462111)
    ·
      refine ⟨22424792663320156424193167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14949861775546770949462111 22424792663320156424193167)
      ·
        refine ⟨33637188994980234636289751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22424792663320156424193167 33637188994980234636289751)
        ·
          refine ⟨50455783492470351954434627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33637188994980234636289751 50455783492470351954434627)
          ·
            refine ⟨75683675238705527931651941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50455783492470351954434627 75683675238705527931651941)
            ·
              refine ⟨14190689107257286487184739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75683675238705527931651941 14190689107257286487184739)
              ·
                refine ⟨21286033660885929730777109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14190689107257286487184739 21286033660885929730777109)
                ·
                  refine ⟨997782827854027956130177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21286033660885929730777109 997782827854027956130177)
                  ·
                    refine ⟨748337120890520967097633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 997782827854027956130177 748337120890520967097633)
                    ·
                      refine ⟨561252840667890725323225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748337120890520967097633 561252840667890725323225)
                      ·
                        rfl

theorem cell23_1093036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_1093036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093036 prefixEnd_1093036 := by exact prefixLift 1093036
  have htrace : WordTrace (prefixWord ++ tailWord_1093036) baseStart_1093036 baseEnd_1093036 := by
    simpa [prefixWord, tailWord_1093036, baseEnd_1093036] using wordTrace_append hprefix tailTrace_1093036
  have hstable : (prefixWord ++ tailWord_1093036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093036).length < 2 ^ (prefixWord ++ tailWord_1093036).sum := by decide
  have hdescent : baseEnd_1093036 < baseStart_1093036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093042 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_1093042 : Nat := 118140960795 + 1093042 * 2 ^ 59
def prefixEnd_1093042 : Nat := 4983230072969 + 3 ^ 40 * 1093042 * 2
def baseEnd_1093042 : Nat := 62361769061313077983133

theorem tailTrace_1093042 : CollatzResearch.WordTrace tailWord_1093042 prefixEnd_1093042 62361769061313077983133 := by
  unfold tailWord_1093042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966629226525746389154345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26577677937401990371078253 9966629226525746389154345)
  ·
    refine ⟨7474971919894309791865759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9966629226525746389154345 7474971919894309791865759)
    ·
      refine ⟨11212457879841464687798639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474971919894309791865759 11212457879841464687798639)
      ·
        refine ⟨16818686819762197031697959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212457879841464687798639 16818686819762197031697959)
        ·
          refine ⟨25228030229643295547546939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16818686819762197031697959 25228030229643295547546939)
          ·
            refine ⟨37842045344464943321320409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25228030229643295547546939 37842045344464943321320409)
            ·
              refine ⟨28381534008348707490990307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37842045344464943321320409 28381534008348707490990307)
              ·
                refine ⟨42572301012523061236485461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28381534008348707490990307 42572301012523061236485461)
                ·
                  refine ⟨62361769061313077983133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 42572301012523061236485461 62361769061313077983133)
                  ·
                    rfl

theorem cell23_1093042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_1093042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093042 prefixEnd_1093042 := by exact prefixLift 1093042
  have htrace : WordTrace (prefixWord ++ tailWord_1093042) baseStart_1093042 baseEnd_1093042 := by
    simpa [prefixWord, tailWord_1093042, baseEnd_1093042] using wordTrace_append hprefix tailTrace_1093042
  have hstable : (prefixWord ++ tailWord_1093042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093042).length < 2 ^ (prefixWord ++ tailWord_1093042).sum := by decide
  have hdescent : baseEnd_1093042 < baseStart_1093042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093072 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_1093072 : Nat := 118140960795 + 1093072 * 2 ^ 59
def prefixEnd_1093072 : Nat := 4983230072969 + 3 ^ 40 * 1093072 * 2
def baseEnd_1093072 : Nat := 187090441990484194824353

theorem tailTrace_1093072 : CollatzResearch.WordTrace tailWord_1093072 prefixEnd_1093072 187090441990484194824353 := by
  unfold tailWord_1093072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933805547997150340104735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26578407397329533786806313 19933805547997150340104735)
  ·
    refine ⟨29900708321995725510157103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933805547997150340104735 29900708321995725510157103)
    ·
      refine ⟨44851062482993588265235655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29900708321995725510157103 44851062482993588265235655)
      ·
        refine ⟨67276593724490382397853483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44851062482993588265235655 67276593724490382397853483)
        ·
          refine ⟨100914890586735573596780225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67276593724490382397853483 100914890586735573596780225)
          ·
            refine ⟨75686167940051680197585169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100914890586735573596780225 75686167940051680197585169)
            ·
              refine ⟨56764625955038760148188877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75686167940051680197585169 56764625955038760148188877)
              ·
                refine ⟨21286734733139535055570829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56764625955038760148188877 21286734733139535055570829)
                ·
                  refine ⟨7982525524927325645839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21286734733139535055570829 7982525524927325645839061)
                  ·
                    refine ⟨187090441990484194824353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7982525524927325645839061 187090441990484194824353)
                    ·
                      rfl

theorem cell23_1093072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_1093072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093072 prefixEnd_1093072 := by exact prefixLift 1093072
  have htrace : WordTrace (prefixWord ++ tailWord_1093072) baseStart_1093072 baseEnd_1093072 := by
    simpa [prefixWord, tailWord_1093072, baseEnd_1093072] using wordTrace_append hprefix tailTrace_1093072
  have hstable : (prefixWord ++ tailWord_1093072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093072).length < 2 ^ (prefixWord ++ tailWord_1093072).sum := by decide
  have hdescent : baseEnd_1093072 < baseStart_1093072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093076 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1093076 : Nat := 118140960795 + 1093076 * 2 ^ 59
def prefixEnd_1093076 : Nat := 4983230072969 + 3 ^ 40 * 1093076 * 2
def baseEnd_1093076 : Nat := 62363708877118952091449

theorem tailTrace_1093076 : CollatzResearch.WordTrace tailWord_1093076 prefixEnd_1093076 62363708877118952091449 := by
  unfold tailWord_1093076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933878493989904681677541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26578504658653206242236721 19933878493989904681677541)
  ·
    refine ⟨3737602217623107127814539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19933878493989904681677541 3737602217623107127814539)
    ·
      refine ⟨5606403326434660691721809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737602217623107127814539 5606403326434660691721809)
      ·
        refine ⟨4204802494825995518791357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5606403326434660691721809 4204802494825995518791357)
        ·
          refine ⟨1576800935559748319546759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4204802494825995518791357 1576800935559748319546759)
          ·
            refine ⟨2365201403339622479320139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576800935559748319546759 2365201403339622479320139)
            ·
              refine ⟨3547802105009433718980209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365201403339622479320139 3547802105009433718980209)
              ·
                refine ⟨2660851578757075289235157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547802105009433718980209 2660851578757075289235157)
                ·
                  refine ⟨62363708877118952091449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2660851578757075289235157 62363708877118952091449)
                  ·
                    rfl

theorem cell23_1093076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1093076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093076 prefixEnd_1093076 := by exact prefixLift 1093076
  have htrace : WordTrace (prefixWord ++ tailWord_1093076) baseStart_1093076 baseEnd_1093076 := by
    simpa [prefixWord, tailWord_1093076, baseEnd_1093076] using wordTrace_append hprefix tailTrace_1093076
  have hstable : (prefixWord ++ tailWord_1093076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093076).length < 2 ^ (prefixWord ++ tailWord_1093076).sum := by decide
  have hdescent : baseEnd_1093076 < baseStart_1093076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093089 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1093089 : Nat := 118140960795 + 1093089 * 2 ^ 59
def prefixEnd_1093089 : Nat := 4983230072969 + 3 ^ 40 * 1093089 * 2
def baseEnd_1093089 : Nat := 187093351714193005986827

theorem tailTrace_1093089 : CollatzResearch.WordTrace tailWord_1093089 prefixEnd_1093089 187093351714193005986827 := by
  unfold tailWord_1093089
  simp only [CollatzResearch.WordTrace]
  refine ⟨39868231136932712583578321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26578820757955141722385547 39868231136932712583578321)
  ·
    refine ⟨29901173352699534437683741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39868231136932712583578321 29901173352699534437683741)
    ·
      refine ⟨11212940007262325414131403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29901173352699534437683741 11212940007262325414131403)
      ·
        refine ⟨16819410010893488121197105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212940007262325414131403 16819410010893488121197105)
        ·
          refine ⟨12614557508170116090897829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16819410010893488121197105 12614557508170116090897829)
          ·
            refine ⟨2365229532781896767043343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12614557508170116090897829 2365229532781896767043343)
            ·
              refine ⟨3547844299172845150565015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365229532781896767043343 3547844299172845150565015)
              ·
                refine ⟨5321766448759267725847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547844299172845150565015 5321766448759267725847523)
                ·
                  refine ⟨7982649673138901588771285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321766448759267725847523 7982649673138901588771285)
                  ·
                    refine ⟨187093351714193005986827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7982649673138901588771285 187093351714193005986827)
                    ·
                      rfl

theorem cell23_1093089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1093089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093089 prefixEnd_1093089 := by exact prefixLift 1093089
  have htrace : WordTrace (prefixWord ++ tailWord_1093089) baseStart_1093089 baseEnd_1093089 := by
    simpa [prefixWord, tailWord_1093089, baseEnd_1093089] using wordTrace_append hprefix tailTrace_1093089
  have hstable : (prefixWord ++ tailWord_1093089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093089).length < 2 ^ (prefixWord ++ tailWord_1093089).sum := by decide
  have hdescent : baseEnd_1093089 < baseStart_1093089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093093 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 5]
def baseStart_1093093 : Nat := 118140960795 + 1093093 * 2 ^ 59
def prefixEnd_1093093 : Nat := 4983230072969 + 3 ^ 40 * 1093093 * 2
def baseEnd_1093093 : Nat := 62364678785021889145607

theorem tailTrace_1093093 : CollatzResearch.WordTrace tailWord_1093093 prefixEnd_1093093 62364678785021889145607 := by
  unfold tailWord_1093093
  simp only [CollatzResearch.WordTrace]
  refine ⟨39868377028918221266723933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26578918019278814177815955 39868377028918221266723933)
  ·
    refine ⟨14950641385844332975021475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39868377028918221266723933 14950641385844332975021475)
    ·
      refine ⟨22425962078766499462532213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14950641385844332975021475 22425962078766499462532213)
      ·
        refine ⟨2102433944884359324612395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22425962078766499462532213 2102433944884359324612395)
        ·
          refine ⟨3153650917326538986918593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102433944884359324612395 3153650917326538986918593)
          ·
            refine ⟨2365238187994904240188945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3153650917326538986918593 2365238187994904240188945)
            ·
              refine ⟨1773928640996178180141709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365238187994904240188945 1773928640996178180141709)
              ·
                refine ⟨665223240373566817553141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773928640996178180141709 665223240373566817553141)
                ·
                  refine ⟨62364678785021889145607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665223240373566817553141 62364678785021889145607)
                  ·
                    rfl

theorem cell23_1093093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_1093093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093093 prefixEnd_1093093 := by exact prefixLift 1093093
  have htrace : WordTrace (prefixWord ++ tailWord_1093093) baseStart_1093093 baseEnd_1093093 := by
    simpa [prefixWord, tailWord_1093093, baseEnd_1093093] using wordTrace_append hprefix tailTrace_1093093
  have hstable : (prefixWord ++ tailWord_1093093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093093).length < 2 ^ (prefixWord ++ tailWord_1093093).sum := by decide
  have hdescent : baseEnd_1093093 < baseStart_1093093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093129 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_1093129 : Nat := 118140960795 + 1093129 * 2 ^ 59
def prefixEnd_1093129 : Nat := 4983230072969 + 3 ^ 40 * 1093129 * 2
def baseEnd_1093129 : Nat := 561300594368758861460297

theorem tailTrace_1093129 : CollatzResearch.WordTrace tailWord_1093129 prefixEnd_1093129 561300594368758861460297 := by
  unfold tailWord_1093129
  simp only [CollatzResearch.WordTrace]
  refine ⟨39869690056787799415034441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26579793371191866276689627 39869690056787799415034441)
  ·
    refine ⟨29902267542590849561275831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39869690056787799415034441 29902267542590849561275831)
    ·
      refine ⟨44853401313886274341913747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29902267542590849561275831 44853401313886274341913747)
      ·
        refine ⟨67280101970829411512870621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44853401313886274341913747 67280101970829411512870621)
        ·
          refine ⟨25230038239061029317326483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67280101970829411512870621 25230038239061029317326483)
          ·
            refine ⟨37845057358591543975989725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25230038239061029317326483 37845057358591543975989725)
            ·
              refine ⟨14191896509471828990996147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37845057358591543975989725 14191896509471828990996147)
              ·
                refine ⟨21287844764207743486494221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14191896509471828990996147 21287844764207743486494221)
                ·
                  refine ⟨7982941786577903807435333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21287844764207743486494221 7982941786577903807435333)
                  ·
                    refine ⟨1496801584983356963894125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7982941786577903807435333 1496801584983356963894125)
                    ·
                      refine ⟨561300594368758861460297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496801584983356963894125 561300594368758861460297)
                      ·
                        rfl

theorem cell23_1093129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_1093129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093129 prefixEnd_1093129 := by exact prefixLift 1093129
  have htrace : WordTrace (prefixWord ++ tailWord_1093129) baseStart_1093129 baseEnd_1093129 := by
    simpa [prefixWord, tailWord_1093129, baseEnd_1093129] using wordTrace_append hprefix tailTrace_1093129
  have hstable : (prefixWord ++ tailWord_1093129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093129).length < 2 ^ (prefixWord ++ tailWord_1093129).sum := by decide
  have hdescent : baseEnd_1093129 < baseStart_1093129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093146 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1093146 : Nat := 118140960795 + 1093146 * 2 ^ 59
def prefixEnd_1093146 : Nat := 4983230072969 + 3 ^ 40 * 1093146 * 2
def baseEnd_1093146 : Nat := 561309323539885294947719

theorem tailTrace_1093146 : CollatzResearch.WordTrace tailWord_1093146 prefixEnd_1093146 561309323539885294947719 := by
  unfold tailWord_1093146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967577524431552829600823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26580206731817474212268861 9967577524431552829600823)
  ·
    refine ⟨14951366286647329244401235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9967577524431552829600823 14951366286647329244401235)
    ·
      refine ⟨22427049429970993866601853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951366286647329244401235 22427049429970993866601853)
      ·
        refine ⟨8410143536239122699975695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22427049429970993866601853 8410143536239122699975695)
        ·
          refine ⟨12615215304358684049963543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410143536239122699975695 12615215304358684049963543)
          ·
            refine ⟨18922822956538026074945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615215304358684049963543 18922822956538026074945315)
            ·
              refine ⟨28384234434807039112417973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18922822956538026074945315 28384234434807039112417973)
              ·
                refine ⟨2661021978263159916789185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28384234434807039112417973 2661021978263159916789185)
                ·
                  refine ⟨1995766483697369937591889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661021978263159916789185 1995766483697369937591889)
                  ·
                    refine ⟨1496824862773027453193917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995766483697369937591889 1496824862773027453193917)
                    ·
                      refine ⟨561309323539885294947719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496824862773027453193917 561309323539885294947719)
                      ·
                        rfl

theorem cell23_1093146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1093146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093146 prefixEnd_1093146 := by exact prefixLift 1093146
  have htrace : WordTrace (prefixWord ++ tailWord_1093146) baseStart_1093146 baseEnd_1093146 := by
    simpa [prefixWord, tailWord_1093146, baseEnd_1093146] using wordTrace_append hprefix tailTrace_1093146
  have hstable : (prefixWord ++ tailWord_1093146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093146).length < 2 ^ (prefixWord ++ tailWord_1093146).sum := by decide
  have hdescent : baseEnd_1093146 < baseStart_1093146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093149 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 10]
def baseStart_1093149 : Nat := 118140960795 + 1093149 * 2 ^ 59
def prefixEnd_1093149 : Nat := 4983230072969 + 3 ^ 40 * 1093149 * 2
def baseEnd_1093149 : Nat := 62367873775760975912245

theorem tailTrace_1093149 : CollatzResearch.WordTrace tailWord_1093149 prefixEnd_1093149 62367873775760975912245 := by
  unfold tailWord_1093149
  simp only [CollatzResearch.WordTrace]
  refine ⟨39870419516715342830762501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26580279677810228553841667 39870419516715342830762501)
  ·
    refine ⟨7475703659384126780767969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39870419516715342830762501 7475703659384126780767969)
    ·
      refine ⟨5606777744538095085575977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7475703659384126780767969 5606777744538095085575977)
      ·
        refine ⟨4205083308403571314181983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5606777744538095085575977 4205083308403571314181983)
        ·
          refine ⟨6307624962605356971272975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205083308403571314181983 6307624962605356971272975)
          ·
            refine ⟨9461437443908035456909463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6307624962605356971272975 9461437443908035456909463)
            ·
              refine ⟨14192156165862053185364195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461437443908035456909463 14192156165862053185364195)
              ·
                refine ⟨21288234248793079778046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14192156165862053185364195 21288234248793079778046293)
                ·
                  refine ⟨62367873775760975912245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21288234248793079778046293 62367873775760975912245)
                  ·
                    rfl

theorem cell23_1093149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_1093149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093149 prefixEnd_1093149 := by exact prefixLift 1093149
  have htrace : WordTrace (prefixWord ++ tailWord_1093149) baseStart_1093149 baseEnd_1093149 := by
    simpa [prefixWord, tailWord_1093149, baseEnd_1093149] using wordTrace_append hprefix tailTrace_1093149
  have hstable : (prefixWord ++ tailWord_1093149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093149).length < 2 ^ (prefixWord ++ tailWord_1093149).sum := by decide
  have hdescent : baseEnd_1093149 < baseStart_1093149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093166 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_1093166 : Nat := 118140960795 + 1093166 * 2 ^ 59
def prefixEnd_1093166 : Nat := 4983230072969 + 3 ^ 40 * 1093166 * 2
def baseEnd_1093166 : Nat := 62368843683663912966403

theorem tailTrace_1093166 : CollatzResearch.WordTrace tailWord_1093166 prefixEnd_1093166 62368843683663912966403 := by
  unfold tailWord_1093166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983879944706719341766419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26580693038435836489420901 4983879944706719341766419)
  ·
    refine ⟨7475819917060079012649629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4983879944706719341766419 7475819917060079012649629)
    ·
      refine ⟨2803432468897529629743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7475819917060079012649629 2803432468897529629743611)
      ·
        refine ⟨4205148703346294444615417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803432468897529629743611 4205148703346294444615417)
        ·
          refine ⟨3153861527509720833461563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4205148703346294444615417 3153861527509720833461563)
          ·
            refine ⟨4730792291264581250192345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153861527509720833461563 4730792291264581250192345)
            ·
              refine ⟨3548094218448435937644259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730792291264581250192345 3548094218448435937644259)
              ·
                refine ⟨5322141327672653906466389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548094218448435937644259 5322141327672653906466389)
                ·
                  refine ⟨62368843683663912966403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5322141327672653906466389 62368843683663912966403)
                  ·
                    rfl

theorem cell23_1093166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_1093166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093166 prefixEnd_1093166 := by exact prefixLift 1093166
  have htrace : WordTrace (prefixWord ++ tailWord_1093166) baseStart_1093166 baseEnd_1093166 := by
    simpa [prefixWord, tailWord_1093166, baseEnd_1093166] using wordTrace_append hprefix tailTrace_1093166
  have hstable : (prefixWord ++ tailWord_1093166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093166).length < 2 ^ (prefixWord ++ tailWord_1093166).sum := by decide
  have hdescent : baseEnd_1093166 < baseStart_1093166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093183 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 6]
def baseStart_1093183 : Nat := 118140960795 + 1093183 * 2 ^ 59
def prefixEnd_1093183 : Nat := 4983230072969 + 3 ^ 40 * 1093183 * 2
def baseEnd_1093183 : Nat := 62369813591566850020561

theorem tailTrace_1093183 : CollatzResearch.WordTrace tailWord_1093183 prefixEnd_1093183 62369813591566850020561 := by
  unfold tailWord_1093183
  simp only [CollatzResearch.WordTrace]
  refine ⟨39871659598592166637500203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26581106399061444425000135 39871659598592166637500203)
  ·
    refine ⟨59807489397888249956250305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39871659598592166637500203 59807489397888249956250305)
    ·
      refine ⟨44855617048416187467187729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59807489397888249956250305 44855617048416187467187729)
      ·
        refine ⟨33641712786312140600390797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44855617048416187467187729 33641712786312140600390797)
        ·
          refine ⟨12615642294867052725146549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33641712786312140600390797 12615642294867052725146549)
          ·
            refine ⟨1182716465143786192982489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12615642294867052725146549 1182716465143786192982489)
            ·
              refine ⟨887037348857839644736867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182716465143786192982489 887037348857839644736867)
              ·
                refine ⟨1330556023286759467105301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887037348857839644736867 1330556023286759467105301)
                ·
                  refine ⟨62369813591566850020561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1330556023286759467105301 62369813591566850020561)
                  ·
                    rfl

theorem cell23_1093183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 6].length) (baseStart_1093183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093183 prefixEnd_1093183 := by exact prefixLift 1093183
  have htrace : WordTrace (prefixWord ++ tailWord_1093183) baseStart_1093183 baseEnd_1093183 := by
    simpa [prefixWord, tailWord_1093183, baseEnd_1093183] using wordTrace_append hprefix tailTrace_1093183
  have hstable : (prefixWord ++ tailWord_1093183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093183).length < 2 ^ (prefixWord ++ tailWord_1093183).sum := by decide
  have hdescent : baseEnd_1093183 < baseStart_1093183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093196 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1093196 : Nat := 118140960795 + 1093196 * 2 ^ 59
def prefixEnd_1093196 : Nat := 4983230072969 + 3 ^ 40 * 1093196 * 2
def baseEnd_1093196 : Nat := 187111665857536699774163

theorem tailTrace_1093196 : CollatzResearch.WordTrace tailWord_1093196 prefixEnd_1093196 187111665857536699774163 := by
  unfold tailWord_1093196
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936066873772534928861721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26581422498363379905148961 19936066873772534928861721)
  ·
    refine ⟨14952050155329401196646291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19936066873772534928861721 14952050155329401196646291)
    ·
      refine ⟨22428075232994101794969437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14952050155329401196646291 22428075232994101794969437)
      ·
        refine ⟨8410528212372788173113539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22428075232994101794969437 8410528212372788173113539)
        ·
          refine ⟨12615792318559182259670309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410528212372788173113539 12615792318559182259670309)
          ·
            refine ⟨2365461059729846673688183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12615792318559182259670309 2365461059729846673688183)
            ·
              refine ⟨3548191589594770010532275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365461059729846673688183 3548191589594770010532275)
              ·
                refine ⟨5322287384392155015798413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548191589594770010532275 5322287384392155015798413)
                ·
                  refine ⟨1995857769147058130924405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5322287384392155015798413 1995857769147058130924405)
                  ·
                    refine ⟨187111665857536699774163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1995857769147058130924405 187111665857536699774163)
                    ·
                      rfl

theorem cell23_1093196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1093196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093196 prefixEnd_1093196 := by exact prefixLift 1093196
  have htrace : WordTrace (prefixWord ++ tailWord_1093196) baseStart_1093196 baseEnd_1093196 := by
    simpa [prefixWord, tailWord_1093196, baseEnd_1093196] using wordTrace_append hprefix tailTrace_1093196
  have hstable : (prefixWord ++ tailWord_1093196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093196).length < 2 ^ (prefixWord ++ tailWord_1093196).sum := by decide
  have hdescent : baseEnd_1093196 < baseStart_1093196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093233 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_1093233 : Nat := 118140960795 + 1093233 * 2 ^ 59
def prefixEnd_1093233 : Nat := 4983230072969 + 3 ^ 40 * 1093233 * 2
def baseEnd_1093233 : Nat := 561353996356826454559819

theorem tailTrace_1093233 : CollatzResearch.WordTrace tailWord_1093233 prefixEnd_1093233 561353996356826454559819 := by
  unfold tailWord_1093233
  simp only [CollatzResearch.WordTrace]
  refine ⟨39873483248411025176820353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26582322165607350117880235 39873483248411025176820353)
  ·
    refine ⟨29905112436308268882615265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39873483248411025176820353 29905112436308268882615265)
    ·
      refine ⟨22428834327231201661961449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29905112436308268882615265 22428834327231201661961449)
      ·
        refine ⟨16821625745423401246471087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22428834327231201661961449 16821625745423401246471087)
        ·
          refine ⟨25232438618135101869706631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16821625745423401246471087 25232438618135101869706631)
          ·
            refine ⟨37848657927202652804559947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25232438618135101869706631 37848657927202652804559947)
            ·
              refine ⟨56772986890803979206839921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37848657927202652804559947 56772986890803979206839921)
              ·
                refine ⟨42579740168102984405129941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56772986890803979206839921 42579740168102984405129941)
                ·
                  refine ⟨997962660189913696995233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 42579740168102984405129941 997962660189913696995233)
                  ·
                    refine ⟨748471995142435272746425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 997962660189913696995233 748471995142435272746425)
                    ·
                      refine ⟨561353996356826454559819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748471995142435272746425 561353996356826454559819)
                      ·
                        rfl

theorem cell23_1093233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_1093233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093233 prefixEnd_1093233 := by exact prefixLift 1093233
  have htrace : WordTrace (prefixWord ++ tailWord_1093233) baseStart_1093233 baseEnd_1093233 := by
    simpa [prefixWord, tailWord_1093233, baseEnd_1093233] using wordTrace_append hprefix tailTrace_1093233
  have hstable : (prefixWord ++ tailWord_1093233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093233).length < 2 ^ (prefixWord ++ tailWord_1093233).sum := by decide
  have hdescent : baseEnd_1093233 < baseStart_1093233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093253 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_1093253 : Nat := 118140960795 + 1093253 * 2 ^ 59
def prefixEnd_1093253 : Nat := 4983230072969 + 3 ^ 40 * 1093253 * 2
def baseEnd_1093253 : Nat := 561364265969916376309727

theorem tailTrace_1093253 : CollatzResearch.WordTrace tailWord_1093253 prefixEnd_1093253 561364265969916376309727 := by
  unfold tailWord_1093253
  simp only [CollatzResearch.WordTrace]
  refine ⟨39874212708338568592548413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26582808472225712395032275 39874212708338568592548413)
  ·
    refine ⟨14952829765626963222205655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39874212708338568592548413 14952829765626963222205655)
    ·
      refine ⟨22429244648440444833308483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14952829765626963222205655 22429244648440444833308483)
      ·
        refine ⟨33643866972660667249962725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22429244648440444833308483 33643866972660667249962725)
        ·
          refine ⟨6308225057373875109368011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33643866972660667249962725 6308225057373875109368011)
          ·
            refine ⟨9462337586060812664052017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308225057373875109368011 9462337586060812664052017)
            ·
              refine ⟨7096753189545609498039013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9462337586060812664052017 7096753189545609498039013)
              ·
                refine ⟨1330641223039801780882315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7096753189545609498039013 1330641223039801780882315)
                ·
                  refine ⟨1995961834559702671323473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330641223039801780882315 1995961834559702671323473)
                  ·
                    refine ⟨1496971375919777003492605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995961834559702671323473 1496971375919777003492605)
                    ·
                      refine ⟨561364265969916376309727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1496971375919777003492605 561364265969916376309727)
                      ·
                        rfl

theorem cell23_1093253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_1093253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093253 prefixEnd_1093253 := by exact prefixLift 1093253
  have htrace : WordTrace (prefixWord ++ tailWord_1093253) baseStart_1093253 baseEnd_1093253 := by
    simpa [prefixWord, tailWord_1093253, baseEnd_1093253] using wordTrace_append hprefix tailTrace_1093253
  have hstable : (prefixWord ++ tailWord_1093253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093253).length < 2 ^ (prefixWord ++ tailWord_1093253).sum := by decide
  have hdescent : baseEnd_1093253 < baseStart_1093253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093283 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 3]
def baseStart_1093283 : Nat := 118140960795 + 1093283 * 2 ^ 59
def prefixEnd_1093283 : Nat := 4983230072969 + 3 ^ 40 * 1093283 * 2
def baseEnd_1093283 : Nat := 561379670389551258934589

theorem tailTrace_1093283 : CollatzResearch.WordTrace tailWord_1093283 prefixEnd_1093283 561379670389551258934589 := by
  unfold tailWord_1093283
  simp only [CollatzResearch.WordTrace]
  refine ⟨39875306898229883716140503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26583537932153255810760335 39875306898229883716140503)
  ·
    refine ⟨59812960347344825574210755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39875306898229883716140503 59812960347344825574210755)
    ·
      refine ⟨89719440521017238361316133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59812960347344825574210755 89719440521017238361316133)
      ·
        refine ⟨16822395097690732192746775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89719440521017238361316133 16822395097690732192746775)
        ·
          refine ⟨25233592646536098289120163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16822395097690732192746775 25233592646536098289120163)
          ·
            refine ⟨37850388969804147433680245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25233592646536098289120163 37850388969804147433680245)
            ·
              refine ⟨3548473965919138821907523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37850388969804147433680245 3548473965919138821907523)
              ·
                refine ⟨5322710948878708232861285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548473965919138821907523 5322710948878708232861285)
                ·
                  refine ⟨998008302914757793661491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5322710948878708232861285 998008302914757793661491)
                  ·
                    refine ⟨1497012454372136690492237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998008302914757793661491 1497012454372136690492237)
                    ·
                      refine ⟨561379670389551258934589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497012454372136690492237 561379670389551258934589)
                      ·
                        rfl

theorem cell23_1093283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_1093283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093283 prefixEnd_1093283 := by exact prefixLift 1093283
  have htrace : WordTrace (prefixWord ++ tailWord_1093283) baseStart_1093283 baseEnd_1093283 := by
    simpa [prefixWord, tailWord_1093283, baseEnd_1093283] using wordTrace_append hprefix tailTrace_1093283
  have hstable : (prefixWord ++ tailWord_1093283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093283).length < 2 ^ (prefixWord ++ tailWord_1093283).sum := by decide
  have hdescent : baseEnd_1093283 < baseStart_1093283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093289 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_1093289 : Nat := 118140960795 + 1093289 * 2 ^ 59
def prefixEnd_1093289 : Nat := 4983230072969 + 3 ^ 40 * 1093289 * 2
def baseEnd_1093289 : Nat := 561382751273478235459561

theorem tailTrace_1093289 : CollatzResearch.WordTrace tailWord_1093289 prefixEnd_1093289 561382751273478235459561 := by
  unfold tailWord_1093289
  simp only [CollatzResearch.WordTrace]
  refine ⟨39875525736208146740858921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26583683824138764493905947 39875525736208146740858921)
  ·
    refine ⟨29906644302156110055644191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39875525736208146740858921 29906644302156110055644191)
    ·
      refine ⟨44859966453234165083466287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29906644302156110055644191 44859966453234165083466287)
      ·
        refine ⟨67289949679851247625199431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44859966453234165083466287 67289949679851247625199431)
        ·
          refine ⟨100934924519776871437799147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67289949679851247625199431 100934924519776871437799147)
          ·
            refine ⟨151402386779665307156698721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100934924519776871437799147 151402386779665307156698721)
            ·
              refine ⟨113551790084748980367524041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151402386779665307156698721 113551790084748980367524041)
              ·
                refine ⟨85163842563561735275643031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113551790084748980367524041 85163842563561735275643031)
                ·
                  refine ⟨127745763845342602913464547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85163842563561735275643031 127745763845342602913464547)
                  ·
                    refine ⟨191618645768013904370196821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127745763845342602913464547 191618645768013904370196821)
                    ·
                      refine ⟨561382751273478235459561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 191618645768013904370196821 561382751273478235459561)
                      ·
                        rfl

theorem cell23_1093289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_1093289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093289 prefixEnd_1093289 := by exact prefixLift 1093289
  have htrace : WordTrace (prefixWord ++ tailWord_1093289) baseStart_1093289 baseEnd_1093289 := by
    simpa [prefixWord, tailWord_1093289, baseEnd_1093289] using wordTrace_append hprefix tailTrace_1093289
  have hstable : (prefixWord ++ tailWord_1093289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093289).length < 2 ^ (prefixWord ++ tailWord_1093289).sum := by decide
  have hdescent : baseEnd_1093289 < baseStart_1093289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093294 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1093294 : Nat := 118140960795 + 1093294 * 2 ^ 59
def prefixEnd_1093294 : Nat := 4983230072969 + 3 ^ 40 * 1093294 * 2
def baseEnd_1093294 : Nat := 187128439558916905299013

theorem tailTrace_1093294 : CollatzResearch.WordTrace tailWord_1093294 prefixEnd_1093294 187128439558916905299013 := by
  unfold tailWord_1093294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4984463512648754074348867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26583805400793355063193957 4984463512648754074348867)
  ·
    refine ⟨7476695268973131111523301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4984463512648754074348867 7476695268973131111523301)
    ·
      refine ⟨1401880362932462083410619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7476695268973131111523301 1401880362932462083410619)
      ·
        refine ⟨2102820544398693125115929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401880362932462083410619 2102820544398693125115929)
        ·
          refine ⟨1577115408299019843836947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102820544398693125115929 1577115408299019843836947)
          ·
            refine ⟨2365673112448529765755421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577115408299019843836947 2365673112448529765755421)
            ·
              refine ⟨887127417168198662158283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2365673112448529765755421 887127417168198662158283)
              ·
                refine ⟨1330691125752297993237425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887127417168198662158283 1330691125752297993237425)
                ·
                  refine ⟨998018344314223494928069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1330691125752297993237425 998018344314223494928069)
                  ·
                    refine ⟨187128439558916905299013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998018344314223494928069 187128439558916905299013)
                    ·
                      rfl

theorem cell23_1093294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1093294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093294 prefixEnd_1093294 := by exact prefixLift 1093294
  have htrace : WordTrace (prefixWord ++ tailWord_1093294) baseStart_1093294 baseEnd_1093294 := by
    simpa [prefixWord, tailWord_1093294, baseEnd_1093294] using wordTrace_append hprefix tailTrace_1093294
  have hstable : (prefixWord ++ tailWord_1093294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093294).length < 2 ^ (prefixWord ++ tailWord_1093294).sum := by decide
  have hdescent : baseEnd_1093294 < baseStart_1093294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093318 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1093318 : Nat := 118140960795 + 1093318 * 2 ^ 59
def prefixEnd_1093318 : Nat := 4983230072969 + 3 ^ 40 * 1093318 * 2
def baseEnd_1093318 : Nat := 561397642212458621996929

theorem tailTrace_1093318 : CollatzResearch.WordTrace tailWord_1093318 prefixEnd_1093318 561397642212458621996929 := by
  unfold tailWord_1093318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246143232909471396677019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26584388968735389795776405 1246143232909471396677019)
  ·
    refine ⟨1869214849364207095015529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246143232909471396677019 1869214849364207095015529)
    ·
      refine ⟨1401911137023155321261647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1869214849364207095015529 1401911137023155321261647)
      ·
        refine ⟨2102866705534732981892471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401911137023155321261647 2102866705534732981892471)
        ·
          refine ⟨3154300058302099472838707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102866705534732981892471 3154300058302099472838707)
          ·
            refine ⟨4731450087453149209258061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154300058302099472838707 4731450087453149209258061)
            ·
              refine ⟨1774293782794930953471773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4731450087453149209258061 1774293782794930953471773)
              ·
                refine ⟨665360168548099107551915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1774293782794930953471773 665360168548099107551915)
                ·
                  refine ⟨998040252822148661327873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665360168548099107551915 998040252822148661327873)
                  ·
                    refine ⟨748530189616611495995905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998040252822148661327873 748530189616611495995905)
                    ·
                      refine ⟨561397642212458621996929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748530189616611495995905 561397642212458621996929)
                      ·
                        rfl

theorem cell23_1093318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1093318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093318 prefixEnd_1093318 := by exact prefixLift 1093318
  have htrace : WordTrace (prefixWord ++ tailWord_1093318) baseStart_1093318 baseEnd_1093318 := by
    simpa [prefixWord, tailWord_1093318, baseEnd_1093318] using wordTrace_append hprefix tailTrace_1093318
  have hstable : (prefixWord ++ tailWord_1093318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093318).length < 2 ^ (prefixWord ++ tailWord_1093318).sum := by decide
  have hdescent : baseEnd_1093318 < baseStart_1093318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093323 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 4, 2]
def baseStart_1093323 : Nat := 118140960795 + 1093323 * 2 ^ 59
def prefixEnd_1093323 : Nat := 4983230072969 + 3 ^ 40 * 1093323 * 2
def baseEnd_1093323 : Nat := 561400209615731102434405

theorem tailTrace_1093323 : CollatzResearch.WordTrace tailWord_1093323 prefixEnd_1093323 561400209615731102434405 := by
  unfold tailWord_1093323
  simp only [CollatzResearch.WordTrace]
  refine ⟨39876765818084970547596623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26584510545389980365064415 39876765818084970547596623)
  ·
    refine ⟨59815148727127455821394935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39876765818084970547596623 59815148727127455821394935)
    ·
      refine ⟨89722723090691183732092403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59815148727127455821394935 89722723090691183732092403)
      ·
        refine ⟨134584084636036775598138605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89722723090691183732092403 134584084636036775598138605)
        ·
          refine ⟨50469031738513790849301977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134584084636036775598138605 50469031738513790849301977)
          ·
            refine ⟨37851773803885343136976483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50469031738513790849301977 37851773803885343136976483)
            ·
              refine ⟨56777660705828014705464725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37851773803885343136976483 56777660705828014705464725)
              ·
                refine ⟨2661452845585688189318659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56777660705828014705464725 2661452845585688189318659)
                ·
                  refine ⟨3992179268378532283977989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661452845585688189318659 3992179268378532283977989)
                  ·
                    refine ⟨748533612820974803245873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3992179268378532283977989 748533612820974803245873)
                    ·
                      refine ⟨561400209615731102434405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748533612820974803245873 561400209615731102434405)
                      ·
                        rfl

theorem cell23_1093323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 4, 2].length) (baseStart_1093323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093323 prefixEnd_1093323 := by exact prefixLift 1093323
  have htrace : WordTrace (prefixWord ++ tailWord_1093323) baseStart_1093323 baseEnd_1093323 := by
    simpa [prefixWord, tailWord_1093323, baseEnd_1093323] using wordTrace_append hprefix tailTrace_1093323
  have hstable : (prefixWord ++ tailWord_1093323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093323).length < 2 ^ (prefixWord ++ tailWord_1093323).sum := by decide
  have hdescent : baseEnd_1093323 < baseStart_1093323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093351 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1093351 : Nat := 118140960795 + 1093351 * 2 ^ 59
def prefixEnd_1093351 : Nat := 4983230072969 + 3 ^ 40 * 1093351 * 2
def baseEnd_1093351 : Nat := 561414587074056992884277

theorem tailTrace_1093351 : CollatzResearch.WordTrace tailWord_1093351 prefixEnd_1093351 561414587074056992884277 := by
  unfold tailWord_1093351
  simp only [CollatzResearch.WordTrace]
  refine ⟨39877787061983531329615907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26585191374655687553077271 39877787061983531329615907)
  ·
    refine ⟨59816680592975296994423861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39877787061983531329615907 59816680592975296994423861)
    ·
      refine ⟨5607813805591434093227237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59816680592975296994423861 5607813805591434093227237)
      ·
        refine ⟨1051465088548393892480107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5607813805591434093227237 1051465088548393892480107)
        ·
          refine ⟨1577197632822590838720161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051465088548393892480107 1577197632822590838720161)
          ·
            refine ⟨1182898224616943129040121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577197632822590838720161 1182898224616943129040121)
            ·
              refine ⟨887173668462707346780091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182898224616943129040121 887173668462707346780091)
              ·
                refine ⟨1330760502694061020170137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887173668462707346780091 1330760502694061020170137)
                ·
                  refine ⟨998070377020545765127603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1330760502694061020170137 998070377020545765127603)
                  ·
                    refine ⟨1497105565530818647691405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998070377020545765127603 1497105565530818647691405)
                    ·
                      refine ⟨561414587074056992884277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497105565530818647691405 561414587074056992884277)
                      ·
                        rfl

theorem cell23_1093351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1093351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093351 prefixEnd_1093351 := by exact prefixLift 1093351
  have htrace : WordTrace (prefixWord ++ tailWord_1093351) baseStart_1093351 baseEnd_1093351 := by
    simpa [prefixWord, tailWord_1093351, baseEnd_1093351] using wordTrace_append hprefix tailTrace_1093351
  have hstable : (prefixWord ++ tailWord_1093351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093351).length < 2 ^ (prefixWord ++ tailWord_1093351).sum := by decide
  have hdescent : baseEnd_1093351 < baseStart_1093351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093376 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_1093376 : Nat := 118140960795 + 1093376 * 2 ^ 59
def prefixEnd_1093376 : Nat := 4983230072969 + 3 ^ 40 * 1093376 * 2
def baseEnd_1093376 : Nat := 187142474696806465023887

theorem tailTrace_1093376 : CollatzResearch.WordTrace tailWord_1093376 prefixEnd_1093376 187142474696806465023887 := by
  unfold tailWord_1093376
  simp only [CollatzResearch.WordTrace]
  refine ⟨19939349443446480299637991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26585799257928640399517321 19939349443446480299637991)
  ·
    refine ⟨29909024165169720449456987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19939349443446480299637991 29909024165169720449456987)
    ·
      refine ⟨44863536247754580674185481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29909024165169720449456987 44863536247754580674185481)
      ·
        refine ⟨33647652185815935505639111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44863536247754580674185481 33647652185815935505639111)
        ·
          refine ⟨50471478278723903258458667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33647652185815935505639111 50471478278723903258458667)
          ·
            refine ⟨75707217418085854887688001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50471478278723903258458667 75707217418085854887688001)
            ·
              refine ⟨56780413063564391165766001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75707217418085854887688001 56780413063564391165766001)
              ·
                refine ⟨42585309797673293374324501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56780413063564391165766001 42585309797673293374324501)
                ·
                  refine ⟨1996186396765935626921461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42585309797673293374324501 1996186396765935626921461)
                  ·
                    refine ⟨187142474696806465023887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996186396765935626921461 187142474696806465023887)
                    ·
                      rfl

theorem cell23_1093376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_1093376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093376 prefixEnd_1093376 := by exact prefixLift 1093376
  have htrace : WordTrace (prefixWord ++ tailWord_1093376) baseStart_1093376 baseEnd_1093376 := by
    simpa [prefixWord, tailWord_1093376, baseEnd_1093376] using wordTrace_append hprefix tailTrace_1093376
  have hstable : (prefixWord ++ tailWord_1093376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093376).length < 2 ^ (prefixWord ++ tailWord_1093376).sum := by decide
  have hdescent : baseEnd_1093376 < baseStart_1093376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093397 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 5]
def baseStart_1093397 : Nat := 118140960795 + 1093397 * 2 ^ 59
def prefixEnd_1093397 : Nat := 4983230072969 + 3 ^ 40 * 1093397 * 2
def baseEnd_1093397 : Nat := 62382023020462645878785

theorem tailTrace_1093397 : CollatzResearch.WordTrace tailWord_1093397 prefixEnd_1093397 62382023020462645878785 := by
  unfold tailWord_1093397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39879464819816881185790445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26586309879877920790526963 39879464819816881185790445)
  ·
    refine ⟨14954799307431330444671417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39879464819816881185790445 14954799307431330444671417)
    ·
      refine ⟨11216099480573497833503563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14954799307431330444671417 11216099480573497833503563)
      ·
        refine ⟨16824149220860246750255345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216099480573497833503563 16824149220860246750255345)
        ·
          refine ⟨12618111915645185062691509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16824149220860246750255345 12618111915645185062691509)
          ·
            refine ⟨1182947992091736099627329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12618111915645185062691509 1182947992091736099627329)
            ·
              refine ⟨887210994068802074720497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182947992091736099627329 887210994068802074720497)
              ·
                refine ⟨665408245551601556040373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887210994068802074720497 665408245551601556040373)
                ·
                  refine ⟨62382023020462645878785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665408245551601556040373 62382023020462645878785)
                  ·
                    rfl

theorem cell23_1093397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_1093397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093397 prefixEnd_1093397 := by exact prefixLift 1093397
  have htrace : WordTrace (prefixWord ++ tailWord_1093397) baseStart_1093397 baseEnd_1093397 := by
    simpa [prefixWord, tailWord_1093397, baseEnd_1093397] using wordTrace_append hprefix tailTrace_1093397
  have hstable : (prefixWord ++ tailWord_1093397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093397).length < 2 ^ (prefixWord ++ tailWord_1093397).sum := by decide
  have hdescent : baseEnd_1093397 < baseStart_1093397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093423 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 3, 4]
def baseStart_1093423 : Nat := 118140960795 + 1093423 * 2 ^ 59
def prefixEnd_1093423 : Nat := 4983230072969 + 3 ^ 40 * 1093423 * 2
def baseEnd_1093423 : Nat := 187150519227060237061315

theorem tailTrace_1093423 : CollatzResearch.WordTrace tailWord_1093423 prefixEnd_1093423 187150519227060237061315 := by
  unfold tailWord_1093423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39880413117722687626236923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26586942078481791750824615 39880413117722687626236923)
  ·
    refine ⟨59820619676584031439355385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39880413117722687626236923 59820619676584031439355385)
    ·
      refine ⟨44865464757438023579516539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59820619676584031439355385 44865464757438023579516539)
      ·
        refine ⟨67298197136157035369274809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44865464757438023579516539 67298197136157035369274809)
        ·
          refine ⟨50473647852117776526956107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67298197136157035369274809 50473647852117776526956107)
          ·
            refine ⟨75710471778176664790434161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50473647852117776526956107 75710471778176664790434161)
            ·
              refine ⟨56782853833632498592825621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75710471778176664790434161 56782853833632498592825621)
              ·
                refine ⟨2661696273451523371538701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56782853833632498592825621 2661696273451523371538701)
                ·
                  refine ⟨998136102544321264327013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2661696273451523371538701 998136102544321264327013)
                  ·
                    refine ⟨187150519227060237061315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998136102544321264327013 187150519227060237061315)
                    ·
                      rfl

theorem cell23_1093423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_1093423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093423 prefixEnd_1093423 := by exact prefixLift 1093423
  have htrace : WordTrace (prefixWord ++ tailWord_1093423) baseStart_1093423 baseEnd_1093423 := by
    simpa [prefixWord, tailWord_1093423, baseEnd_1093423] using wordTrace_append hprefix tailTrace_1093423
  have hstable : (prefixWord ++ tailWord_1093423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093423).length < 2 ^ (prefixWord ++ tailWord_1093423).sum := by decide
  have hdescent : baseEnd_1093423 < baseStart_1093423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093427 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 2, 5]
def baseStart_1093427 : Nat := 118140960795 + 1093427 * 2 ^ 59
def prefixEnd_1093427 : Nat := 4983230072969 + 3 ^ 40 * 1093427 * 2
def baseEnd_1093427 : Nat := 187151203867932898511309

theorem tailTrace_1093427 : CollatzResearch.WordTrace tailWord_1093427 prefixEnd_1093427 187151203867932898511309 := by
  unfold tailWord_1093427
  simp only [CollatzResearch.WordTrace]
  refine ⟨39880559009708196309382535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26587039339805464206255023 39880559009708196309382535)
  ·
    refine ⟨59820838514562294464073803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39880559009708196309382535 59820838514562294464073803)
    ·
      refine ⟨89731257771843441696110705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59820838514562294464073803 89731257771843441696110705)
      ·
        refine ⟨67298443328882581272083029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89731257771843441696110705 67298443328882581272083029)
        ·
          refine ⟨788653632760342749282223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 67298443328882581272083029 788653632760342749282223)
          ·
            refine ⟨1182980449140514123923335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788653632760342749282223 1182980449140514123923335)
            ·
              refine ⟨1774470673710771185885003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182980449140514123923335 1774470673710771185885003)
              ·
                refine ⟨2661706010566156778827505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774470673710771185885003 2661706010566156778827505)
                ·
                  refine ⟨1996279507924617584120629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661706010566156778827505 1996279507924617584120629)
                  ·
                    refine ⟨187151203867932898511309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996279507924617584120629 187151203867932898511309)
                    ·
                      rfl

theorem cell23_1093427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 5].length) (baseStart_1093427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093427 prefixEnd_1093427 := by exact prefixLift 1093427
  have htrace : WordTrace (prefixWord ++ tailWord_1093427) baseStart_1093427 baseEnd_1093427 := by
    simpa [prefixWord, tailWord_1093427, baseEnd_1093427] using wordTrace_append hprefix tailTrace_1093427
  have hstable : (prefixWord ++ tailWord_1093427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093427).length < 2 ^ (prefixWord ++ tailWord_1093427).sum := by decide
  have hdescent : baseEnd_1093427 < baseStart_1093427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093457 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1093457 : Nat := 118140960795 + 1093457 * 2 ^ 59
def prefixEnd_1093457 : Nat := 4983230072969 + 3 ^ 40 * 1093457 * 2
def baseEnd_1093457 : Nat := 187156338674477859386263

theorem tailTrace_1093457 : CollatzResearch.WordTrace tailWord_1093457 prefixEnd_1093457 187156338674477859386263 := by
  unfold tailWord_1093457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39881653199599511432974625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26587768799733007621983083 39881653199599511432974625)
  ·
    refine ⟨29911239899699633574730969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39881653199599511432974625 29911239899699633574730969)
    ·
      refine ⟨22433429924774725181048227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29911239899699633574730969 22433429924774725181048227)
      ·
        refine ⟨33650144887162087771572341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22433429924774725181048227 33650144887162087771572341)
        ·
          refine ⟨3154701083171445728584907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33650144887162087771572341 3154701083171445728584907)
          ·
            refine ⟨4732051624757168592877361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154701083171445728584907 4732051624757168592877361)
            ·
              refine ⟨3549038718567876444658021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4732051624757168592877361 3549038718567876444658021)
              ·
                refine ⟨665444759731476833373379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3549038718567876444658021 665444759731476833373379)
                ·
                  refine ⟨998167139597215250060069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665444759731476833373379 998167139597215250060069)
                  ·
                    refine ⟨187156338674477859386263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998167139597215250060069 187156338674477859386263)
                    ·
                      rfl

theorem cell23_1093457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1093457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093457 prefixEnd_1093457 := by exact prefixLift 1093457
  have htrace : WordTrace (prefixWord ++ tailWord_1093457) baseStart_1093457 baseEnd_1093457 := by
    simpa [prefixWord, tailWord_1093457, baseEnd_1093457] using wordTrace_append hprefix tailTrace_1093457
  have hstable : (prefixWord ++ tailWord_1093457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093457).length < 2 ^ (prefixWord ++ tailWord_1093457).sum := by decide
  have hdescent : baseEnd_1093457 < baseStart_1093457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093503 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1093503 : Nat := 118140960795 + 1093503 * 2 ^ 59
def prefixEnd_1093503 : Nat := 4983230072969 + 3 ^ 40 * 1093503 * 2
def baseEnd_1093503 : Nat := 561492636133540398183577

theorem tailTrace_1093503 : CollatzResearch.WordTrace tailWord_1093503 prefixEnd_1093503 561492636133540398183577 := by
  unfold tailWord_1093503
  simp only [CollatzResearch.WordTrace]
  refine ⟨39883330957432861289149163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26588887304955240859432775 39883330957432861289149163)
  ·
    refine ⟨59824996436149291933723745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39883330957432861289149163 59824996436149291933723745)
    ·
      refine ⟨44868747327111968950292809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59824996436149291933723745 44868747327111968950292809)
      ·
        refine ⟨33651560495333976712719607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44868747327111968950292809 33651560495333976712719607)
        ·
          refine ⟨50477340743000965069079411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33651560495333976712719607 50477340743000965069079411)
          ·
            refine ⟨75716011114501447603619117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50477340743000965069079411 75716011114501447603619117)
            ·
              refine ⟨28393504167938042851357169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75716011114501447603619117 28393504167938042851357169)
              ·
                refine ⟨21295128125953532138517877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28393504167938042851357169 21295128125953532138517877)
                ·
                  refine ⟨1996418261808143637986051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21295128125953532138517877 1996418261808143637986051)
                  ·
                    refine ⟨2994627392712215456979077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996418261808143637986051 2994627392712215456979077)
                    ·
                      refine ⟨561492636133540398183577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2994627392712215456979077 561492636133540398183577)
                      ·
                        rfl

theorem cell23_1093503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1093503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093503 prefixEnd_1093503 := by exact prefixLift 1093503
  have htrace : WordTrace (prefixWord ++ tailWord_1093503) baseStart_1093503 baseEnd_1093503 := by
    simpa [prefixWord, tailWord_1093503, baseEnd_1093503] using wordTrace_append hprefix tailTrace_1093503
  have hstable : (prefixWord ++ tailWord_1093503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093503).length < 2 ^ (prefixWord ++ tailWord_1093503).sum := by decide
  have hdescent : baseEnd_1093503 < baseStart_1093503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093507 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 2, 3, 2]
def baseStart_1093507 : Nat := 118140960795 + 1093507 * 2 ^ 59
def prefixEnd_1093507 : Nat := 4983230072969 + 3 ^ 40 * 1093507 * 2
def baseEnd_1093507 : Nat := 561494690056158382533559

theorem tailTrace_1093507 : CollatzResearch.WordTrace tailWord_1093507 prefixEnd_1093507 561494690056158382533559 := by
  unfold tailWord_1093507
  simp only [CollatzResearch.WordTrace]
  refine ⟨39883476849418369972294775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26588984566278913314863183 39883476849418369972294775)
  ·
    refine ⟨59825215274127554958442163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39883476849418369972294775 59825215274127554958442163)
    ·
      refine ⟨89737822911191332437663245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59825215274127554958442163 89737822911191332437663245)
      ·
        refine ⟨33651683591696749664123717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89737822911191332437663245 33651683591696749664123717)
        ·
          refine ⟨6309690673443140562023197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33651683591696749664123717 6309690673443140562023197)
          ·
            refine ⟨2366134002541177710758699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6309690673443140562023197 2366134002541177710758699)
            ·
              refine ⟨3549201003811766566138049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366134002541177710758699 3549201003811766566138049)
              ·
                refine ⟨2661900752858824924603537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549201003811766566138049 2661900752858824924603537)
                ·
                  refine ⟨1996425564644118693452653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2661900752858824924603537 1996425564644118693452653)
                  ·
                    refine ⟨748659586741544510044745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996425564644118693452653 748659586741544510044745)
                    ·
                      refine ⟨561494690056158382533559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 748659586741544510044745 561494690056158382533559)
                      ·
                        rfl

theorem cell23_1093507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_1093507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093507 prefixEnd_1093507 := by exact prefixLift 1093507
  have htrace : WordTrace (prefixWord ++ tailWord_1093507) baseStart_1093507 baseEnd_1093507 := by
    simpa [prefixWord, tailWord_1093507, baseEnd_1093507] using wordTrace_append hprefix tailTrace_1093507
  have hstable : (prefixWord ++ tailWord_1093507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093507).length < 2 ^ (prefixWord ++ tailWord_1093507).sum := by decide
  have hdescent : baseEnd_1093507 < baseStart_1093507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093534 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1093534 : Nat := 118140960795 + 1093534 * 2 ^ 59
def prefixEnd_1093534 : Nat := 4983230072969 + 3 ^ 40 * 1093534 * 2
def baseEnd_1093534 : Nat := 187169518011276592298645

theorem tailTrace_1093534 : CollatzResearch.WordTrace tailWord_1093534 prefixEnd_1093534 187169518011276592298645 := by
  unfold tailWord_1093534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4985557702540069197940957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26589641080213702389018437 4985557702540069197940957)
  ·
    refine ⟨1869584138452525949227859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4985557702540069197940957 1869584138452525949227859)
    ·
      refine ⟨2804376207678788923841789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869584138452525949227859 2804376207678788923841789)
      ·
        refine ⟨1051641077879545846440671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2804376207678788923841789 1051641077879545846440671)
        ·
          refine ⟨1577461616819318769661007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051641077879545846440671 1577461616819318769661007)
          ·
            refine ⟨2366192425228978154491511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577461616819318769661007 2366192425228978154491511)
            ·
              refine ⟨3549288637843467231737267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366192425228978154491511 3549288637843467231737267)
              ·
                refine ⟨5323932956765200847605901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549288637843467231737267 5323932956765200847605901)
                ·
                  refine ⟨1996474858786950317852213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5323932956765200847605901 1996474858786950317852213)
                  ·
                    refine ⟨187169518011276592298645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996474858786950317852213 187169518011276592298645)
                    ·
                      rfl

theorem cell23_1093534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1093534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093534 prefixEnd_1093534 := by exact prefixLift 1093534
  have htrace : WordTrace (prefixWord ++ tailWord_1093534) baseStart_1093534 baseEnd_1093534 := by
    simpa [prefixWord, tailWord_1093534, baseEnd_1093534] using wordTrace_append hprefix tailTrace_1093534
  have hstable : (prefixWord ++ tailWord_1093534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093534).length < 2 ^ (prefixWord ++ tailWord_1093534).sum := by decide
  have hdescent : baseEnd_1093534 < baseStart_1093534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093537 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1093537 : Nat := 118140960795 + 1093537 * 2 ^ 59
def prefixEnd_1093537 : Nat := 4983230072969 + 3 ^ 40 * 1093537 * 2
def baseEnd_1093537 : Nat := 561510094475793265158421

theorem tailTrace_1093537 : CollatzResearch.WordTrace tailWord_1093537 prefixEnd_1093537 561510094475793265158421 := by
  unfold tailWord_1093537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39884571039309685095886865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26589714026206456730591243 39884571039309685095886865)
  ·
    refine ⟨29913428279482263821915149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39884571039309685095886865 29913428279482263821915149)
    ·
      refine ⟨11217535604805848933218181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29913428279482263821915149 11217535604805848933218181)
      ·
        refine ⟨2103287925901096674978409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11217535604805848933218181 2103287925901096674978409)
        ·
          refine ⟨1577465944425822506233807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103287925901096674978409 1577465944425822506233807)
          ·
            refine ⟨2366198916638733759350711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577465944425822506233807 2366198916638733759350711)
            ·
              refine ⟨3549298374958100639026067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366198916638733759350711 3549298374958100639026067)
              ·
                refine ⟨5323947562437150958539101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549298374958100639026067 5323947562437150958539101)
                ·
                  refine ⟨1996480335913931609452163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5323947562437150958539101 1996480335913931609452163)
                  ·
                    refine ⟨2994720503870897414178245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996480335913931609452163 2994720503870897414178245)
                    ·
                      refine ⟨561510094475793265158421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2994720503870897414178245 561510094475793265158421)
                      ·
                        rfl

theorem cell23_1093537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1093537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093537 prefixEnd_1093537 := by exact prefixLift 1093537
  have htrace : WordTrace (prefixWord ++ tailWord_1093537) baseStart_1093537 baseEnd_1093537 := by
    simpa [prefixWord, tailWord_1093537, baseEnd_1093537] using wordTrace_append hprefix tailTrace_1093537
  have hstable : (prefixWord ++ tailWord_1093537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093537).length < 2 ^ (prefixWord ++ tailWord_1093537).sum := by decide
  have hdescent : baseEnd_1093537 < baseStart_1093537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093557 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1093557 : Nat := 118140960795 + 1093557 * 2 ^ 59
def prefixEnd_1093557 : Nat := 4983230072969 + 3 ^ 40 * 1093557 * 2
def baseEnd_1093557 : Nat := 561520364088883186908329

theorem tailTrace_1093557 : CollatzResearch.WordTrace tailWord_1093557 prefixEnd_1093557 561520364088883186908329 := by
  unfold tailWord_1093557
  simp only [CollatzResearch.WordTrace]
  refine ⟨39885300499237228511614925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26590200332824819007743283 39885300499237228511614925)
  ·
    refine ⟨14956987687213960691855597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39885300499237228511614925 14956987687213960691855597)
    ·
      refine ⟨5608870382705235259445849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14956987687213960691855597 5608870382705235259445849)
      ·
        refine ⟨4206652787028926444584387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5608870382705235259445849 4206652787028926444584387)
        ·
          refine ⟨6309979180543389666876581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206652787028926444584387 6309979180543389666876581)
          ·
            refine ⟨1183121096351885562539359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6309979180543389666876581 1183121096351885562539359)
            ·
              refine ⟨1774681644527828343809039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183121096351885562539359 1774681644527828343809039)
              ·
                refine ⟨2662022466791742515713559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774681644527828343809039 2662022466791742515713559)
                ·
                  refine ⟨3993033700187613773570339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662022466791742515713559 3993033700187613773570339)
                  ·
                    refine ⟨5989550550281420660355509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993033700187613773570339 5989550550281420660355509)
                    ·
                      refine ⟨561520364088883186908329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5989550550281420660355509 561520364088883186908329)
                      ·
                        rfl

theorem cell23_1093557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1093557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093557 prefixEnd_1093557 := by exact prefixLift 1093557
  have htrace : WordTrace (prefixWord ++ tailWord_1093557) baseStart_1093557 baseEnd_1093557 := by
    simpa [prefixWord, tailWord_1093557, baseEnd_1093557] using wordTrace_append hprefix tailTrace_1093557
  have hstable : (prefixWord ++ tailWord_1093557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093557).length < 2 ^ (prefixWord ++ tailWord_1093557).sum := by decide
  have hdescent : baseEnd_1093557 < baseStart_1093557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093640 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1093640 : Nat := 118140960795 + 1093640 * 2 ^ 59
def prefixEnd_1093640 : Nat := 4983230072969 + 3 ^ 40 * 1093640 * 2
def baseEnd_1093640 : Nat := 561562982983206362170447

theorem tailTrace_1093640 : CollatzResearch.WordTrace tailWord_1093640 prefixEnd_1093640 561562982983206362170447 := by
  unfold tailWord_1093640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944163878968266843443187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26592218505291022457924249 19944163878968266843443187)
  ·
    refine ⟨29916245818452400265164781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944163878968266843443187 29916245818452400265164781)
    ·
      refine ⟨11218592181919650099436793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29916245818452400265164781 11218592181919650099436793)
      ·
        refine ⟨8413944136439737574577595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11218592181919650099436793 8413944136439737574577595)
        ·
          refine ⟨12620916204659606361866393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8413944136439737574577595 12620916204659606361866393)
          ·
            refine ⟨9465687153494704771399795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12620916204659606361866393 9465687153494704771399795)
            ·
              refine ⟨14198530730242057157099693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465687153494704771399795 14198530730242057157099693)
              ·
                refine ⟨5324449023840771433912385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14198530730242057157099693 5324449023840771433912385)
                ·
                  refine ⟨3993336767880578575434289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324449023840771433912385 3993336767880578575434289)
                  ·
                    refine ⟨2995002575910433931575717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993336767880578575434289 2995002575910433931575717)
                    ·
                      refine ⟨561562982983206362170447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2995002575910433931575717 561562982983206362170447)
                      ·
                        rfl

theorem cell23_1093640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1093640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093640 prefixEnd_1093640 := by exact prefixLift 1093640
  have htrace : WordTrace (prefixWord ++ tailWord_1093640) baseStart_1093640 baseEnd_1093640 := by
    simpa [prefixWord, tailWord_1093640, baseEnd_1093640] using wordTrace_append hprefix tailTrace_1093640
  have hstable : (prefixWord ++ tailWord_1093640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093640).length < 2 ^ (prefixWord ++ tailWord_1093640).sum := by decide
  have hdescent : baseEnd_1093640 < baseStart_1093640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093680 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_1093680 : Nat := 118140960795 + 1093680 * 2 ^ 59
def prefixEnd_1093680 : Nat := 4983230072969 + 3 ^ 40 * 1093680 * 2
def baseEnd_1093680 : Nat := 187194507403128735223421

theorem tailTrace_1093680 : CollatzResearch.WordTrace tailWord_1093680 prefixEnd_1093680 187194507403128735223421 := by
  unfold tailWord_1093680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944893338895810259171247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26593191118527747012228329 19944893338895810259171247)
  ·
    refine ⟨29917340008343715388756871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944893338895810259171247 29917340008343715388756871)
    ·
      refine ⟨44876010012515573083135307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29917340008343715388756871 44876010012515573083135307)
      ·
        refine ⟨67314015018773359624702961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44876010012515573083135307 67314015018773359624702961)
        ·
          refine ⟨50485511264080019718527221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67314015018773359624702961 50485511264080019718527221)
          ·
            refine ⟨4733016681007501848611927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50485511264080019718527221 4733016681007501848611927)
            ·
              refine ⟨7099525021511252772917891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733016681007501848611927 7099525021511252772917891)
              ·
                refine ⟨10649287532266879159376837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099525021511252772917891 10649287532266879159376837)
                ·
                  refine ⟨1996741412300039842383157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10649287532266879159376837 1996741412300039842383157)
                  ·
                    refine ⟨187194507403128735223421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996741412300039842383157 187194507403128735223421)
                    ·
                      rfl

theorem cell23_1093680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_1093680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093680 prefixEnd_1093680 := by exact prefixLift 1093680
  have htrace : WordTrace (prefixWord ++ tailWord_1093680) baseStart_1093680 baseEnd_1093680 := by
    simpa [prefixWord, tailWord_1093680, baseEnd_1093680] using wordTrace_append hprefix tailTrace_1093680
  have hstable : (prefixWord ++ tailWord_1093680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093680).length < 2 ^ (prefixWord ++ tailWord_1093680).sum := by decide
  have hdescent : baseEnd_1093680 < baseStart_1093680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093714 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1093714 : Nat := 118140960795 + 1093714 * 2 ^ 59
def prefixEnd_1093714 : Nat := 4983230072969 + 3 ^ 40 * 1093714 * 2
def baseEnd_1093714 : Nat := 187200326850546357548369

theorem tailTrace_1093714 : CollatzResearch.WordTrace tailWord_1093714 prefixEnd_1093714 187200326850546357548369 := by
  unfold tailWord_1093714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972756689917111081270049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26594017839778962883386797 9972756689917111081270049)
  ·
    refine ⟨7479567517437833310952537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9972756689917111081270049 7479567517437833310952537)
    ·
      refine ⟨5609675638078374983214403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7479567517437833310952537 5609675638078374983214403)
      ·
        refine ⟨8414513457117562474821605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609675638078374983214403 8414513457117562474821605)
        ·
          refine ⟨1577721273209542964029051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8414513457117562474821605 1577721273209542964029051)
          ·
            refine ⟨2366581909814314446043577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577721273209542964029051 2366581909814314446043577)
            ·
              refine ⟨1774936432360735834532683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2366581909814314446043577 1774936432360735834532683)
              ·
                refine ⟨2662404648541103751799025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774936432360735834532683 2662404648541103751799025)
                ·
                  refine ⟨1996803486405827813849269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662404648541103751799025 1996803486405827813849269)
                  ·
                    refine ⟨187200326850546357548369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1996803486405827813849269 187200326850546357548369)
                    ·
                      rfl

theorem cell23_1093714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1093714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093714 prefixEnd_1093714 := by exact prefixLift 1093714
  have htrace : WordTrace (prefixWord ++ tailWord_1093714) baseStart_1093714 baseEnd_1093714 := by
    simpa [prefixWord, tailWord_1093714, baseEnd_1093714] using wordTrace_append hprefix tailTrace_1093714
  have hstable : (prefixWord ++ tailWord_1093714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093714).length < 2 ^ (prefixWord ++ tailWord_1093714).sum := by decide
  have hdescent : baseEnd_1093714 < baseStart_1093714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093717 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1093717 : Nat := 118140960795 + 1093717 * 2 ^ 59
def prefixEnd_1093717 : Nat := 4983230072969 + 3 ^ 40 * 1093717 * 2
def baseEnd_1093717 : Nat := 561602520993602560907593

theorem tailTrace_1093717 : CollatzResearch.WordTrace tailWord_1093717 prefixEnd_1093717 561602520993602560907593 := by
  unfold tailWord_1093717
  simp only [CollatzResearch.WordTrace]
  refine ⟨39891136178657575837439405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26594090785771717224959603 39891136178657575837439405)
  ·
    refine ⟨14959176066996590939039777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39891136178657575837439405 14959176066996590939039777)
    ·
      refine ⟨11219382050247443204279833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14959176066996590939039777 11219382050247443204279833)
      ·
        refine ⟨8414536537685582403209875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11219382050247443204279833 8414536537685582403209875)
        ·
          refine ⟨12621804806528373604814813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8414536537685582403209875 12621804806528373604814813)
          ·
            refine ⟨4733176802448140101805555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12621804806528373604814813 4733176802448140101805555)
            ·
              refine ⟨7099765203672210152708333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733176802448140101805555 7099765203672210152708333)
              ·
                refine ⟨2662411951377078807265625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7099765203672210152708333 2662411951377078807265625)
                ·
                  refine ⟨1996808963532809105449219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662411951377078807265625 1996808963532809105449219)
                  ·
                    refine ⟨2995213445299213658173829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996808963532809105449219 2995213445299213658173829)
                    ·
                      refine ⟨561602520993602560907593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2995213445299213658173829 561602520993602560907593)
                      ·
                        rfl

theorem cell23_1093717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1093717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093717 prefixEnd_1093717 := by exact prefixLift 1093717
  have htrace : WordTrace (prefixWord ++ tailWord_1093717) baseStart_1093717 baseEnd_1093717 := by
    simpa [prefixWord, tailWord_1093717, baseEnd_1093717] using wordTrace_append hprefix tailTrace_1093717
  have hstable : (prefixWord ++ tailWord_1093717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093717).length < 2 ^ (prefixWord ++ tailWord_1093717).sum := by decide
  have hdescent : baseEnd_1093717 < baseStart_1093717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093737 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_1093737 : Nat := 118140960795 + 1093737 * 2 ^ 59
def prefixEnd_1093737 : Nat := 4983230072969 + 3 ^ 40 * 1093737 * 2
def baseEnd_1093737 : Nat := 561612790606692482657501

theorem tailTrace_1093737 : CollatzResearch.WordTrace tailWord_1093737 prefixEnd_1093737 561612790606692482657501 := by
  unfold tailWord_1093737
  simp only [CollatzResearch.WordTrace]
  refine ⟨39891865638585119253167465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26594577092390079502111643 39891865638585119253167465)
  ·
    refine ⟨29918899228938839439875599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39891865638585119253167465 29918899228938839439875599)
    ·
      refine ⟨44878348843408259159813399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29918899228938839439875599 44878348843408259159813399)
      ·
        refine ⟨67317523265112388739720099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44878348843408259159813399 67317523265112388739720099)
        ·
          refine ⟨100976284897668583109580149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67317523265112388739720099 100976284897668583109580149)
          ·
            refine ⟨9466526709156429666523139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100976284897668583109580149 9466526709156429666523139)
            ·
              refine ⟨14199790063734644499784709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466526709156429666523139 14199790063734644499784709)
              ·
                refine ⟨2662460636950245843709633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14199790063734644499784709 2662460636950245843709633)
                ·
                  refine ⟨1996845477712684382782225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662460636950245843709633 1996845477712684382782225)
                  ·
                    refine ⟨1497634108284513287086669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1996845477712684382782225 1497634108284513287086669)
                    ·
                      refine ⟨561612790606692482657501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497634108284513287086669 561612790606692482657501)
                      ·
                        rfl

theorem cell23_1093737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_1093737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093737 prefixEnd_1093737 := by exact prefixLift 1093737
  have htrace : WordTrace (prefixWord ++ tailWord_1093737) baseStart_1093737 baseEnd_1093737 := by
    simpa [prefixWord, tailWord_1093737, baseEnd_1093737] using wordTrace_append hprefix tailTrace_1093737
  have hstable : (prefixWord ++ tailWord_1093737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093737).length < 2 ^ (prefixWord ++ tailWord_1093737).sum := by decide
  have hdescent : baseEnd_1093737 < baseStart_1093737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093757 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1093757 : Nat := 118140960795 + 1093757 * 2 ^ 59
def prefixEnd_1093757 : Nat := 4983230072969 + 3 ^ 40 * 1093757 * 2
def baseEnd_1093757 : Nat := 62402562246642489378601

theorem tailTrace_1093757 : CollatzResearch.WordTrace tailWord_1093757 prefixEnd_1093757 62402562246642489378601 := by
  unfold tailWord_1093757
  simp only [CollatzResearch.WordTrace]
  refine ⟨39892595098512662668895525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26595063399008441779263683 39892595098512662668895525)
  ·
    refine ⟨7479861580971124250417911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39892595098512662668895525 7479861580971124250417911)
    ·
      refine ⟨11219792371456686375626867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7479861580971124250417911 11219792371456686375626867)
      ·
        refine ⟨16829688557185029563440301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11219792371456686375626867 16829688557185029563440301)
        ·
          refine ⟨6311133208944386086290113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16829688557185029563440301 6311133208944386086290113)
          ·
            refine ⟨4733349906708289564717585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311133208944386086290113 4733349906708289564717585)
            ·
              refine ⟨3550012430031217173538189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4733349906708289564717585 3550012430031217173538189)
              ·
                refine ⟨1331254661261706440076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3550012430031217173538189 1331254661261706440076821)
                ·
                  refine ⟨62402562246642489378601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1331254661261706440076821 62402562246642489378601)
                  ·
                    rfl

theorem cell23_1093757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1093757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093757 prefixEnd_1093757 := by exact prefixLift 1093757
  have htrace : WordTrace (prefixWord ++ tailWord_1093757) baseStart_1093757 baseEnd_1093757 := by
    simpa [prefixWord, tailWord_1093757, baseEnd_1093757] using wordTrace_append hprefix tailTrace_1093757
  have hstable : (prefixWord ++ tailWord_1093757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093757).length < 2 ^ (prefixWord ++ tailWord_1093757).sum := by decide
  have hdescent : baseEnd_1093757 < baseStart_1093757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093824 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_1093824 : Nat := 118140960795 + 1093824 * 2 ^ 59
def prefixEnd_1093824 : Nat := 4983230072969 + 3 ^ 40 * 1093824 * 2
def baseEnd_1093824 : Nat := 561657463423633642269601

theorem tailTrace_1093824 : CollatzResearch.WordTrace tailWord_1093824 prefixEnd_1093824 561657463423633642269601 := by
  unfold tailWord_1093824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19947519394634966555792263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26596692526179955407723017 19947519394634966555792263)
  ·
    refine ⟨29921279091952449833688395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19947519394634966555792263 29921279091952449833688395)
    ·
      refine ⟨44881918637928674750532593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29921279091952449833688395 44881918637928674750532593)
      ·
        refine ⟨33661438978446506062899445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44881918637928674750532593 33661438978446506062899445)
        ·
          refine ⟨3155759904229359943396823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33661438978446506062899445 3155759904229359943396823)
          ·
            refine ⟨4733639856344039915095235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155759904229359943396823 4733639856344039915095235)
            ·
              refine ⟨7100459784516059872642853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733639856344039915095235 7100459784516059872642853)
              ·
                refine ⟨1331336209596761226120535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7100459784516059872642853 1331336209596761226120535)
                ·
                  refine ⟨1997004314395141839180803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331336209596761226120535 1997004314395141839180803)
                  ·
                    refine ⟨2995506471592712758771205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1997004314395141839180803 2995506471592712758771205)
                    ·
                      refine ⟨561657463423633642269601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2995506471592712758771205 561657463423633642269601)
                      ·
                        rfl

theorem cell23_1093824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_1093824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093824 prefixEnd_1093824 := by exact prefixLift 1093824
  have htrace : WordTrace (prefixWord ++ tailWord_1093824) baseStart_1093824 baseEnd_1093824 := by
    simpa [prefixWord, tailWord_1093824, baseEnd_1093824] using wordTrace_append hprefix tailTrace_1093824
  have hstable : (prefixWord ++ tailWord_1093824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093824).length < 2 ^ (prefixWord ++ tailWord_1093824).sum := by decide
  have hdescent : baseEnd_1093824 < baseStart_1093824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093827 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3]
def baseStart_1093827 : Nat := 118140960795 + 1093827 * 2 ^ 59
def prefixEnd_1093827 : Nat := 4983230072969 + 3 ^ 40 * 1093827 * 2
def baseEnd_1093827 : Nat := 561659003865597130532087

theorem tailTrace_1093827 : CollatzResearch.WordTrace tailWord_1093827 prefixEnd_1093827 561659003865597130532087 := by
  unfold tailWord_1093827
  simp only [CollatzResearch.WordTrace]
  refine ⟨39895148208259064623943735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26596765472172709749295823 39895148208259064623943735)
  ·
    refine ⟨59842722312388596935915603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39895148208259064623943735 59842722312388596935915603)
    ·
      refine ⟨89764083468582895403873405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59842722312388596935915603 89764083468582895403873405)
      ·
        refine ⟨33661531300718585776452527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89764083468582895403873405 33661531300718585776452527)
        ·
          refine ⟨50492296951077878664678791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33661531300718585776452527 50492296951077878664678791)
          ·
            refine ⟨75738445426616817997018187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50492296951077878664678791 75738445426616817997018187)
            ·
              refine ⟨113607668139925226995527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75738445426616817997018187 113607668139925226995527281)
              ·
                refine ⟨85205751104943920246645461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113607668139925226995527281 85205751104943920246645461)
                ·
                  refine ⟨1997009791522123130780753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 85205751104943920246645461 1997009791522123130780753)
                  ·
                    refine ⟨1497757343641592348085565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997009791522123130780753 1497757343641592348085565)
                    ·
                      refine ⟨561659003865597130532087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497757343641592348085565 561659003865597130532087)
                      ·
                        rfl

theorem cell23_1093827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_1093827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093827 prefixEnd_1093827 := by exact prefixLift 1093827
  have htrace : WordTrace (prefixWord ++ tailWord_1093827) baseStart_1093827 baseEnd_1093827 := by
    simpa [prefixWord, tailWord_1093827, baseEnd_1093827] using wordTrace_append hprefix tailTrace_1093827
  have hstable : (prefixWord ++ tailWord_1093827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093827).length < 2 ^ (prefixWord ++ tailWord_1093827).sum := by decide
  have hdescent : baseEnd_1093827 < baseStart_1093827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093852 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1093852 : Nat := 118140960795 + 1093852 * 2 ^ 59
def prefixEnd_1093852 : Nat := 4983230072969 + 3 ^ 40 * 1093852 * 2
def baseEnd_1093852 : Nat := 561671840881959532719473

theorem tailTrace_1093852 : CollatzResearch.WordTrace tailWord_1093852 prefixEnd_1093852 561671840881959532719473 := by
  unfold tailWord_1093852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948030016584246946801905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26597373355445662595735873 19948030016584246946801905)
  ·
    refine ⟨14961022512438185210101429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19948030016584246946801905 14961022512438185210101429)
    ·
      refine ⟨1402595860541079863447009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14961022512438185210101429 1402595860541079863447009)
      ·
        refine ⟨1051946895405809897585257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402595860541079863447009 1051946895405809897585257)
        ·
          refine ⟨788960171554357423188943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051946895405809897585257 788960171554357423188943)
          ·
            refine ⟨1183440257331536134783415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788960171554357423188943 1183440257331536134783415)
            ·
              refine ⟨1775160385997304202175123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183440257331536134783415 1775160385997304202175123)
              ·
                refine ⟨2662740578995956303262685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775160385997304202175123 2662740578995956303262685)
                ·
                  refine ⟨998527717123483613723507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2662740578995956303262685 998527717123483613723507)
                  ·
                    refine ⟨1497791575685225420585261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998527717123483613723507 1497791575685225420585261)
                    ·
                      refine ⟨561671840881959532719473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497791575685225420585261 561671840881959532719473)
                      ·
                        rfl

theorem cell23_1093852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1093852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093852 prefixEnd_1093852 := by exact prefixLift 1093852
  have htrace : WordTrace (prefixWord ++ tailWord_1093852) baseStart_1093852 baseEnd_1093852 := by
    simpa [prefixWord, tailWord_1093852, baseEnd_1093852] using wordTrace_append hprefix tailTrace_1093852
  have hstable : (prefixWord ++ tailWord_1093852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093852).length < 2 ^ (prefixWord ++ tailWord_1093852).sum := by decide
  have hdescent : baseEnd_1093852 < baseStart_1093852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093895 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1093895 : Nat := 118140960795 + 1093895 * 2 ^ 59
def prefixEnd_1093895 : Nat := 4983230072969 + 3 ^ 40 * 1093895 * 2
def baseEnd_1093895 : Nat := 561693920550102864481775

theorem tailTrace_1093895 : CollatzResearch.WordTrace tailWord_1093895 prefixEnd_1093895 561693920550102864481775 := by
  unfold tailWord_1093895
  simp only [CollatzResearch.WordTrace]
  refine ⟨39897628372012712237419139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26598418914675141491612759 39897628372012712237419139)
  ·
    refine ⟨59846442558019068356128709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39897628372012712237419139 59846442558019068356128709)
    ·
      refine ⟨11221207979628575316774133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59846442558019068356128709 11221207979628575316774133)
      ·
        refine ⟨1051988248090178935947575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11221207979628575316774133 1051988248090178935947575)
        ·
          refine ⟨1577982372135268403921363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051988248090178935947575 1577982372135268403921363)
          ·
            refine ⟨2366973558202902605882045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577982372135268403921363 2366973558202902605882045)
            ·
              refine ⟨887615084326088477205767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2366973558202902605882045 887615084326088477205767)
              ·
                refine ⟨1331422626489132715808651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887615084326088477205767 1331422626489132715808651)
                ·
                  refine ⟨1997133939733699073712977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331422626489132715808651 1997133939733699073712977)
                  ·
                    refine ⟨1497850454800274305284733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1997133939733699073712977 1497850454800274305284733)
                    ·
                      refine ⟨561693920550102864481775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497850454800274305284733 561693920550102864481775)
                      ·
                        rfl

theorem cell23_1093895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1093895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093895 prefixEnd_1093895 := by exact prefixLift 1093895
  have htrace : WordTrace (prefixWord ++ tailWord_1093895) baseStart_1093895 baseEnd_1093895 := by
    simpa [prefixWord, tailWord_1093895, baseEnd_1093895] using wordTrace_append hprefix tailTrace_1093895
  have hstable : (prefixWord ++ tailWord_1093895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093895).length < 2 ^ (prefixWord ++ tailWord_1093895).sum := by decide
  have hdescent : baseEnd_1093895 < baseStart_1093895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093924 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1093924 : Nat := 118140960795 + 1093924 * 2 ^ 59
def prefixEnd_1093924 : Nat := 4983230072969 + 3 ^ 40 * 1093924 * 2
def baseEnd_1093924 : Nat := 187236270496361083673047

theorem tailTrace_1093924 : CollatzResearch.WordTrace tailWord_1093924 prefixEnd_1093924 187236270496361083673047 := by
  unfold tailWord_1093924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949343044453825095112413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26599124059271766793483217 19949343044453825095112413)
  ·
    refine ⟨7481003641670184410667155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19949343044453825095112413 7481003641670184410667155)
    ·
      refine ⟨11221505462505276616000733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481003641670184410667155 11221505462505276616000733)
      ·
        refine ⟨4208064548439478731000275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11221505462505276616000733 4208064548439478731000275)
        ·
          refine ⟨6312096822659218096500413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208064548439478731000275 6312096822659218096500413)
          ·
            refine ⟨2367036308497206786187655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6312096822659218096500413 2367036308497206786187655)
            ·
              refine ⟨3550554462745810179281483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367036308497206786187655 3550554462745810179281483)
              ·
                refine ⟨5325831694118715268922225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550554462745810179281483 5325831694118715268922225)
                ·
                  refine ⟨3994373770589036451691669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325831694118715268922225 3994373770589036451691669)
                  ·
                    refine ⟨187236270496361083673047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3994373770589036451691669 187236270496361083673047)
                    ·
                      rfl

theorem cell23_1093924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1093924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093924 prefixEnd_1093924 := by exact prefixLift 1093924
  have htrace : WordTrace (prefixWord ++ tailWord_1093924) baseStart_1093924 baseEnd_1093924 := by
    simpa [prefixWord, tailWord_1093924, baseEnd_1093924] using wordTrace_append hprefix tailTrace_1093924
  have hstable : (prefixWord ++ tailWord_1093924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093924).length < 2 ^ (prefixWord ++ tailWord_1093924).sum := by decide
  have hdescent : baseEnd_1093924 < baseStart_1093924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093964 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1093964 : Nat := 118140960795 + 1093964 * 2 ^ 59
def prefixEnd_1093964 : Nat := 4983230072969 + 3 ^ 40 * 1093964 * 2
def baseEnd_1093964 : Nat := 561729350715263094518957

theorem tailTrace_1093964 : CollatzResearch.WordTrace tailWord_1093964 prefixEnd_1093964 561729350715263094518957 := by
  unfold tailWord_1093964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950072504381368510840473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26600096672508491347787297 19950072504381368510840473)
  ·
    refine ⟨14962554378286026383130355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19950072504381368510840473 14962554378286026383130355)
    ·
      refine ⟨22443831567429039574695533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14962554378286026383130355 22443831567429039574695533)
      ·
        refine ⟨8416436837785889840510825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22443831567429039574695533 8416436837785889840510825)
        ·
          refine ⟨6312327628339417380383119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8416436837785889840510825 6312327628339417380383119)
          ·
            refine ⟨9468491442509126070574679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6312327628339417380383119 9468491442509126070574679)
            ·
              refine ⟨14202737163763689105862019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9468491442509126070574679 14202737163763689105862019)
              ·
                refine ⟨21304105745645533658793029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14202737163763689105862019 21304105745645533658793029)
                ·
                  refine ⟨3994519827308537561023693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21304105745645533658793029 3994519827308537561023693)
                  ·
                    refine ⟨1497944935240701585383885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3994519827308537561023693 1497944935240701585383885)
                    ·
                      refine ⟨561729350715263094518957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1497944935240701585383885 561729350715263094518957)
                      ·
                        rfl

theorem cell23_1093964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1093964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093964 prefixEnd_1093964 := by exact prefixLift 1093964
  have htrace : WordTrace (prefixWord ++ tailWord_1093964) baseStart_1093964 baseEnd_1093964 := by
    simpa [prefixWord, tailWord_1093964, baseEnd_1093964] using wordTrace_append hprefix tailTrace_1093964
  have hstable : (prefixWord ++ tailWord_1093964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093964).length < 2 ^ (prefixWord ++ tailWord_1093964).sum := by decide
  have hdescent : baseEnd_1093964 < baseStart_1093964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093977 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_1093977 : Nat := 118140960795 + 1093977 * 2 ^ 59
def prefixEnd_1093977 : Nat := 4983230072969 + 3 ^ 40 * 1093977 * 2
def baseEnd_1093977 : Nat := 561736025963771543656397

theorem tailTrace_1093977 : CollatzResearch.WordTrace tailWord_1093977 prefixEnd_1093977 561736025963771543656397 := by
  unfold tailWord_1093977
  simp only [CollatzResearch.WordTrace]
  refine ⟨39900619157715640241904185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26600412771810426827936123 39900619157715640241904185)
  ·
    refine ⟨29925464368286730181428139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39900619157715640241904185 29925464368286730181428139)
    ·
      refine ⟨44888196552430095272142209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29925464368286730181428139 44888196552430095272142209)
      ·
        refine ⟨33666147414322571454106657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44888196552430095272142209 33666147414322571454106657)
        ·
          refine ⟨25249610560741928590579993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33666147414322571454106657 25249610560741928590579993)
          ·
            refine ⟨18937207920556446442934995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25249610560741928590579993 18937207920556446442934995)
            ·
              refine ⟨28405811880834669664402493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18937207920556446442934995 28405811880834669664402493)
              ·
                refine ⟨10652179455313001124150935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28405811880834669664402493 10652179455313001124150935)
                ·
                  refine ⟨15978269182969501686226403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10652179455313001124150935 15978269182969501686226403)
                  ·
                    refine ⟨23967403774454252529339605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15978269182969501686226403 23967403774454252529339605)
                    ·
                      refine ⟨561736025963771543656397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23967403774454252529339605 561736025963771543656397)
                      ·
                        rfl

theorem cell23_1093977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_1093977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1093977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1093977 prefixEnd_1093977 := by exact prefixLift 1093977
  have htrace : WordTrace (prefixWord ++ tailWord_1093977) baseStart_1093977 baseEnd_1093977 := by
    simpa [prefixWord, tailWord_1093977, baseEnd_1093977] using wordTrace_append hprefix tailTrace_1093977
  have hstable : (prefixWord ++ tailWord_1093977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093977).length < 2 ^ (prefixWord ++ tailWord_1093977).sum := by decide
  have hdescent : baseEnd_1093977 < baseStart_1093977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094111 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1094111 : Nat := 118140960795 + 1094111 * 2 ^ 59
def prefixEnd_1094111 : Nat := 4983230072969 + 3 ^ 40 * 1094111 * 2
def baseEnd_1094111 : Nat := 561804832371474019380781

theorem tailTrace_1094111 : CollatzResearch.WordTrace tailWord_1094111 prefixEnd_1094111 561804832371474019380781 := by
  unfold tailWord_1094111
  simp only [CollatzResearch.WordTrace]
  refine ⟨39905506539230181127282187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26603671026153454084854791 39905506539230181127282187)
  ·
    refine ⟨59858259808845271690923281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39905506539230181127282187 59858259808845271690923281)
    ·
      refine ⟨44893694856633953768192461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59858259808845271690923281 44893694856633953768192461)
      ·
        refine ⟨16835135571237732663072173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44893694856633953768192461 16835135571237732663072173)
        ·
          refine ⟨6313175839214149748652065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16835135571237732663072173 6313175839214149748652065)
          ·
            refine ⟨4734881879410612311489049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6313175839214149748652065 4734881879410612311489049)
            ·
              refine ⟨3551161409557959233616787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734881879410612311489049 3551161409557959233616787)
              ·
                refine ⟨5326742114336938850425181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551161409557959233616787 5326742114336938850425181)
                ·
                  refine ⟨1997528292876352068909443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5326742114336938850425181 1997528292876352068909443)
                  ·
                    refine ⟨2996292439314528103364165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1997528292876352068909443 2996292439314528103364165)
                    ·
                      refine ⟨561804832371474019380781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2996292439314528103364165 561804832371474019380781)
                      ·
                        rfl

theorem cell23_1094111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1094111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094111 prefixEnd_1094111 := by exact prefixLift 1094111
  have htrace : WordTrace (prefixWord ++ tailWord_1094111) baseStart_1094111 baseEnd_1094111 := by
    simpa [prefixWord, tailWord_1094111, baseEnd_1094111] using wordTrace_append hprefix tailTrace_1094111
  have hstable : (prefixWord ++ tailWord_1094111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094111).length < 2 ^ (prefixWord ++ tailWord_1094111).sum := by decide
  have hdescent : baseEnd_1094111 < baseStart_1094111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094122 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_1094122 : Nat := 118140960795 + 1094122 * 2 ^ 59
def prefixEnd_1094122 : Nat := 4983230072969 + 3 ^ 40 * 1094122 * 2
def baseEnd_1094122 : Nat := 561810480658673476343231

theorem tailTrace_1094122 : CollatzResearch.WordTrace tailWord_1094122 prefixEnd_1094122 561810480658673476343231 := by
  unfold tailWord_1094122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976476935547582501483155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26603938494793553337288413 9976476935547582501483155)
  ·
    refine ⟨14964715403321373752224733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9976476935547582501483155 14964715403321373752224733)
    ·
      refine ⟨5611768276245515157084275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14964715403321373752224733 5611768276245515157084275)
      ·
        refine ⟨8417652414368272735626413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611768276245515157084275 8417652414368272735626413)
        ·
          refine ⟨3156619655388102275859905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8417652414368272735626413 3156619655388102275859905)
          ·
            refine ⟨2367464741541076706894929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3156619655388102275859905 2367464741541076706894929)
            ·
              refine ⟨1775598556155807530171197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367464741541076706894929 1775598556155807530171197)
              ·
                refine ⟨665849458558427823814199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775598556155807530171197 665849458558427823814199)
                ·
                  refine ⟨998774187837641735721299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665849458558427823814199 998774187837641735721299)
                  ·
                    refine ⟨1498161281756462603581949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998774187837641735721299 1498161281756462603581949)
                    ·
                      refine ⟨561810480658673476343231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1498161281756462603581949 561810480658673476343231)
                      ·
                        rfl

theorem cell23_1094122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_1094122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094122 prefixEnd_1094122 := by exact prefixLift 1094122
  have htrace : WordTrace (prefixWord ++ tailWord_1094122) baseStart_1094122 baseEnd_1094122 := by
    simpa [prefixWord, tailWord_1094122, baseEnd_1094122] using wordTrace_append hprefix tailTrace_1094122
  have hstable : (prefixWord ++ tailWord_1094122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094122).length < 2 ^ (prefixWord ++ tailWord_1094122).sum := by decide
  have hdescent : baseEnd_1094122 < baseStart_1094122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094125 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1094125 : Nat := 118140960795 + 1094125 * 2 ^ 59
def prefixEnd_1094125 : Nat := 4983230072969 + 3 ^ 40 * 1094125 * 2
def baseEnd_1094125 : Nat := 187270673700212321535239

theorem tailTrace_1094125 : CollatzResearch.WordTrace tailWord_1094125 prefixEnd_1094125 187270673700212321535239 := by
  unfold tailWord_1094125
  simp only [CollatzResearch.WordTrace]
  refine ⟨39906017161179461518291829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604011440786307678861219 39906017161179461518291829)
  ·
    refine ⟨3741189108860574517339859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39906017161179461518291829 3741189108860574517339859)
    ·
      refine ⟨5611783663290861776009789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741189108860574517339859 5611783663290861776009789)
      ·
        refine ⟨2104418873734073166003671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5611783663290861776009789 2104418873734073166003671)
        ·
          refine ⟨3156628310601109749005507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104418873734073166003671 3156628310601109749005507)
          ·
            refine ⟨4734942465901664623508261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156628310601109749005507 4734942465901664623508261)
            ·
              refine ⟨887801712356562116907799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4734942465901664623508261 887801712356562116907799)
              ·
                refine ⟨1331702568534843175361699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887801712356562116907799 1331702568534843175361699)
                ·
                  refine ⟨1997553852802264763042549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331702568534843175361699 1997553852802264763042549)
                  ·
                    refine ⟨187270673700212321535239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1997553852802264763042549 187270673700212321535239)
                    ·
                      rfl

theorem cell23_1094125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1094125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094125 prefixEnd_1094125 := by exact prefixLift 1094125
  have htrace : WordTrace (prefixWord ++ tailWord_1094125) baseStart_1094125 baseEnd_1094125 := by
    simpa [prefixWord, tailWord_1094125, baseEnd_1094125] using wordTrace_append hprefix tailTrace_1094125
  have hstable : (prefixWord ++ tailWord_1094125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094125).length < 2 ^ (prefixWord ++ tailWord_1094125).sum := by decide
  have hdescent : baseEnd_1094125 < baseStart_1094125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094128 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2]
def baseStart_1094128 : Nat := 118140960795 + 1094128 * 2 ^ 59
def prefixEnd_1094128 : Nat := 4983230072969 + 3 ^ 40 * 1094128 * 2
def baseEnd_1094128 : Nat := 561813561542600452868203

theorem tailTrace_1094128 : CollatzResearch.WordTrace tailWord_1094128 prefixEnd_1094128 561813561542600452868203 := by
  unfold tailWord_1094128
  simp only [CollatzResearch.WordTrace]
  refine ⟨19953063290084296515325519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26604084386779062020434025 19953063290084296515325519)
  ·
    refine ⟨29929594935126444772988279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19953063290084296515325519 29929594935126444772988279)
    ·
      refine ⟨44894392402689667159482419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29929594935126444772988279 44894392402689667159482419)
      ·
        refine ⟨67341588604034500739223629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44894392402689667159482419 67341588604034500739223629)
        ·
          refine ⟨25253095726512937777208861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67341588604034500739223629 25253095726512937777208861)
          ·
            refine ⟨9469910897442351666453323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25253095726512937777208861 9469910897442351666453323)
            ·
              refine ⟨14204866346163527499679985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469910897442351666453323 14204866346163527499679985)
              ·
                refine ⟨10653649759622645624759989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14204866346163527499679985 10653649759622645624759989)
                ·
                  refine ⟨998779664964623027321249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10653649759622645624759989 998779664964623027321249)
                  ·
                    refine ⟨749084748723467270490937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998779664964623027321249 749084748723467270490937)
                    ·
                      refine ⟨561813561542600452868203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749084748723467270490937 561813561542600452868203)
                      ·
                        rfl

theorem cell23_1094128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2].length) (baseStart_1094128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094128 prefixEnd_1094128 := by exact prefixLift 1094128
  have htrace : WordTrace (prefixWord ++ tailWord_1094128) baseStart_1094128 baseEnd_1094128 := by
    simpa [prefixWord, tailWord_1094128, baseEnd_1094128] using wordTrace_append hprefix tailTrace_1094128
  have hstable : (prefixWord ++ tailWord_1094128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094128).length < 2 ^ (prefixWord ++ tailWord_1094128).sum := by decide
  have hdescent : baseEnd_1094128 < baseStart_1094128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094145 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1094145 : Nat := 118140960795 + 1094145 * 2 ^ 59
def prefixEnd_1094145 : Nat := 4983230072969 + 3 ^ 40 * 1094145 * 2
def baseEnd_1094145 : Nat := 561822290713726886355625

theorem tailTrace_1094145 : CollatzResearch.WordTrace tailWord_1094145 prefixEnd_1094145 561822290713726886355625 := by
  unfold tailWord_1094145
  simp only [CollatzResearch.WordTrace]
  refine ⟨39906746621107004934019889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604497747404669956013259 39906746621107004934019889)
  ·
    refine ⟨29930059965830253700514917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39906746621107004934019889 29930059965830253700514917)
    ·
      refine ⟨5611886243593172568846547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29930059965830253700514917 5611886243593172568846547)
      ·
        refine ⟨8417829365389758853269821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611886243593172568846547 8417829365389758853269821)
        ·
          refine ⟨3156686012021159569976183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8417829365389758853269821 3156686012021159569976183)
          ·
            refine ⟨4735029018031739354964275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156686012021159569976183 4735029018031739354964275)
            ·
              refine ⟨7102543527047609032446413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735029018031739354964275 7102543527047609032446413)
              ·
                refine ⟨2663453822642853387167405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7102543527047609032446413 2663453822642853387167405)
                ·
                  refine ⟨998795183491070020187777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2663453822642853387167405 998795183491070020187777)
                  ·
                    refine ⟨749096387618302515140833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998795183491070020187777 749096387618302515140833)
                    ·
                      refine ⟨561822290713726886355625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749096387618302515140833 561822290713726886355625)
                      ·
                        rfl

theorem cell23_1094145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1094145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094145 prefixEnd_1094145 := by exact prefixLift 1094145
  have htrace : WordTrace (prefixWord ++ tailWord_1094145) baseStart_1094145 baseEnd_1094145 := by
    simpa [prefixWord, tailWord_1094145, baseEnd_1094145] using wordTrace_append hprefix tailTrace_1094145
  have hstable : (prefixWord ++ tailWord_1094145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094145).length < 2 ^ (prefixWord ++ tailWord_1094145).sum := by decide
  have hdescent : baseEnd_1094145 < baseStart_1094145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094148 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1094148 : Nat := 118140960795 + 1094148 * 2 ^ 59
def prefixEnd_1094148 : Nat := 4983230072969 + 3 ^ 40 * 1094148 * 2
def baseEnd_1094148 : Nat := 561823831155690374618111

theorem tailTrace_1094148 : CollatzResearch.WordTrace tailWord_1094148 prefixEnd_1094148 561823831155690374618111 := by
  unfold tailWord_1094148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19953428020048068223189549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26604570693397424297586065 19953428020048068223189549)
  ·
    refine ⟨7482535507518025583696081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19953428020048068223189549 7482535507518025583696081)
    ·
      refine ⟨5611901630638519187772061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7482535507518025583696081 5611901630638519187772061)
      ·
        refine ⟨2104463111489444695414523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5611901630638519187772061 2104463111489444695414523)
        ·
          refine ⟨3156694667234167043121785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104463111489444695414523 3156694667234167043121785)
          ·
            refine ⟨2367521000425625282341339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3156694667234167043121785 2367521000425625282341339)
            ·
              refine ⟨3551281500638437923512009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367521000425625282341339 3551281500638437923512009)
              ·
                refine ⟨2663461125478828442634007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551281500638437923512009 2663461125478828442634007)
                ·
                  refine ⟨3995191688218242663951011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663461125478828442634007 3995191688218242663951011)
                  ·
                    refine ⟨5992787532327363995926517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995191688218242663951011 5992787532327363995926517)
                    ·
                      refine ⟨561823831155690374618111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5992787532327363995926517 561823831155690374618111)
                      ·
                        rfl

theorem cell23_1094148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1094148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094148 prefixEnd_1094148 := by exact prefixLift 1094148
  have htrace : WordTrace (prefixWord ++ tailWord_1094148) baseStart_1094148 baseEnd_1094148 := by
    simpa [prefixWord, tailWord_1094148, baseEnd_1094148] using wordTrace_append hprefix tailTrace_1094148
  have hstable : (prefixWord ++ tailWord_1094148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094148).length < 2 ^ (prefixWord ++ tailWord_1094148).sum := by decide
  have hdescent : baseEnd_1094148 < baseStart_1094148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094155 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 2, 4]
def baseStart_1094155 : Nat := 118140960795 + 1094155 * 2 ^ 59
def prefixEnd_1094155 : Nat := 4983230072969 + 3 ^ 40 * 1094155 * 2
def baseEnd_1094155 : Nat := 187275808506757282410193

theorem tailTrace_1094155 : CollatzResearch.WordTrace tailWord_1094155 prefixEnd_1094155 187275808506757282410193 := by
  unfold tailWord_1094155
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907111351070776641883919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604740900713851094589279 39907111351070776641883919)
  ·
    refine ⟨59860667026606164962825879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39907111351070776641883919 59860667026606164962825879)
    ·
      refine ⟨89791000539909247444238819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59860667026606164962825879 89791000539909247444238819)
      ·
        refine ⟨134686500809863871166358229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89791000539909247444238819 134686500809863871166358229)
        ·
          refine ⟨3156714862731184480461521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 134686500809863871166358229 3156714862731184480461521)
          ·
            refine ⟨2367536147048388360346141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3156714862731184480461521 2367536147048388360346141)
            ·
              refine ⟨887826055143145635129803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2367536147048388360346141 887826055143145635129803)
              ·
                refine ⟨1331739082714718452694705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887826055143145635129803 1331739082714718452694705)
                ·
                  refine ⟨998804312036038839521029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331739082714718452694705 998804312036038839521029)
                  ·
                    refine ⟨187275808506757282410193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998804312036038839521029 187275808506757282410193)
                    ·
                      rfl

theorem cell23_1094155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 4].length) (baseStart_1094155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094155 prefixEnd_1094155 := by exact prefixLift 1094155
  have htrace : WordTrace (prefixWord ++ tailWord_1094155) baseStart_1094155 baseEnd_1094155 := by
    simpa [prefixWord, tailWord_1094155, baseEnd_1094155] using wordTrace_append hprefix tailTrace_1094155
  have hstable : (prefixWord ++ tailWord_1094155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094155).length < 2 ^ (prefixWord ++ tailWord_1094155).sum := by decide
  have hdescent : baseEnd_1094155 < baseStart_1094155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094158 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1094158 : Nat := 118140960795 + 1094158 * 2 ^ 59
def prefixEnd_1094158 : Nat := 4983230072969 + 3 ^ 40 * 1094158 * 2
def baseEnd_1094158 : Nat := 561828965962235335493065

theorem tailTrace_1094158 : CollatzResearch.WordTrace tailWord_1094158 prefixEnd_1094158 561828965962235335493065 := by
  unfold tailWord_1094158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988402596257488519280391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26604813846706605436162085 4988402596257488519280391)
  ·
    refine ⟨7482603894386232778920587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988402596257488519280391 7482603894386232778920587)
    ·
      refine ⟨11223905841579349168380881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482603894386232778920587 11223905841579349168380881)
      ·
        refine ⟨8417929381184511876285661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11223905841579349168380881 8417929381184511876285661)
        ·
          refine ⟨3156723517944191953607123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8417929381184511876285661 3156723517944191953607123)
          ·
            refine ⟨4735085276916287930410685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156723517944191953607123 4735085276916287930410685)
            ·
              refine ⟨1775656978843607973904007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4735085276916287930410685 1775656978843607973904007)
              ·
                refine ⟨2663485468265411960856011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775656978843607973904007 2663485468265411960856011)
                ·
                  refine ⟨3995228202398117941284017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663485468265411960856011 3995228202398117941284017)
                  ·
                    refine ⟨2996421151798588455963013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995228202398117941284017 2996421151798588455963013)
                    ·
                      refine ⟨561828965962235335493065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2996421151798588455963013 561828965962235335493065)
                      ·
                        rfl

theorem cell23_1094158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1094158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094158 prefixEnd_1094158 := by exact prefixLift 1094158
  have htrace : WordTrace (prefixWord ++ tailWord_1094158) baseStart_1094158 baseEnd_1094158 := by
    simpa [prefixWord, tailWord_1094158, baseEnd_1094158] using wordTrace_append hprefix tailTrace_1094158
  have hstable : (prefixWord ++ tailWord_1094158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094158).length < 2 ^ (prefixWord ++ tailWord_1094158).sum := by decide
  have hdescent : baseEnd_1094158 < baseStart_1094158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094161 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_1094161 : Nat := 118140960795 + 1094161 * 2 ^ 59
def prefixEnd_1094161 : Nat := 4983230072969 + 3 ^ 40 * 1094161 * 2
def baseEnd_1094161 : Nat := 561830506404198823755551

theorem tailTrace_1094161 : CollatzResearch.WordTrace tailWord_1094161 prefixEnd_1094161 561830506404198823755551 := by
  unfold tailWord_1094161
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907330189049039666602337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604886792699359777734891 39907330189049039666602337)
  ·
    refine ⟨29930497641786779749951753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39907330189049039666602337 29930497641786779749951753)
    ·
      refine ⟨22447873231340084812463815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29930497641786779749951753 22447873231340084812463815)
      ·
        refine ⟨33671809847010127218695723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22447873231340084812463815 33671809847010127218695723)
        ·
          refine ⟨50507714770515190828043585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33671809847010127218695723 50507714770515190828043585)
          ·
            refine ⟨37880786077886393121032689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50507714770515190828043585 37880786077886393121032689)
            ·
              refine ⟨28410589558414794840774517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37880786077886393121032689 28410589558414794840774517)
              ·
                refine ⟨2663492771101387016322611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28410589558414794840774517 2663492771101387016322611)
                ·
                  refine ⟨3995239156652080524483917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663492771101387016322611 3995239156652080524483917)
                  ·
                    refine ⟨1498214683744530196681469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3995239156652080524483917 1498214683744530196681469)
                    ·
                      refine ⟨561830506404198823755551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1498214683744530196681469 561830506404198823755551)
                      ·
                        rfl

theorem cell23_1094161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_1094161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094161 prefixEnd_1094161 := by exact prefixLift 1094161
  have htrace : WordTrace (prefixWord ++ tailWord_1094161) baseStart_1094161 baseEnd_1094161 := by
    simpa [prefixWord, tailWord_1094161, baseEnd_1094161] using wordTrace_append hprefix tailTrace_1094161
  have hstable : (prefixWord ++ tailWord_1094161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094161).length < 2 ^ (prefixWord ++ tailWord_1094161).sum := by decide
  have hdescent : baseEnd_1094161 < baseStart_1094161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094168 : List Nat := [2, 1, 2, 3, 3, 3, 2, 7]
def baseStart_1094168 : Nat := 118140960795 + 1094168 * 2 ^ 59
def prefixEnd_1094168 : Nat := 4983230072969 + 3 ^ 40 * 1094168 * 2
def baseEnd_1094168 : Nat := 20808670398843714680297

theorem tailTrace_1094168 : CollatzResearch.WordTrace tailWord_1094168 prefixEnd_1094168 20808670398843714680297 := by
  unfold tailWord_1094168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19953792750011839931053579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26605057000015786574738105 19953792750011839931053579)
  ·
    refine ⟨29930689125017759896580369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19953792750011839931053579 29930689125017759896580369)
    ·
      refine ⟨22448016843763319922435277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29930689125017759896580369 22448016843763319922435277)
      ·
        refine ⟨8418006316411244970913229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22448016843763319922435277 8418006316411244970913229)
        ·
          refine ⟨3156752368654216864092461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8418006316411244970913229 3156752368654216864092461)
          ·
            refine ⟨1183782138245331324034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3156752368654216864092461 1183782138245331324034673)
            ·
              refine ⟨887836603683998493026005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183782138245331324034673 887836603683998493026005)
              ·
                refine ⟨20808670398843714680297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 887836603683998493026005 20808670398843714680297)
                ·
                  rfl

theorem cell23_1094168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 7].length) (baseStart_1094168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094168 prefixEnd_1094168 := by exact prefixLift 1094168
  have htrace : WordTrace (prefixWord ++ tailWord_1094168) baseStart_1094168 baseEnd_1094168 := by
    simpa [prefixWord, tailWord_1094168, baseEnd_1094168] using wordTrace_append hprefix tailTrace_1094168
  have hstable : (prefixWord ++ tailWord_1094168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094168).length < 2 ^ (prefixWord ++ tailWord_1094168).sum := by decide
  have hdescent : baseEnd_1094168 < baseStart_1094168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 7, 2]
def baseStart_1094171 : Nat := 118140960795 + 1094171 * 2 ^ 59
def prefixEnd_1094171 : Nat := 4983230072969 + 3 ^ 40 * 1094171 * 2
def baseEnd_1094171 : Nat := 561835641210743784630505

theorem tailTrace_1094171 : CollatzResearch.WordTrace tailWord_1094171 prefixEnd_1094171 561835641210743784630505 := by
  unfold tailWord_1094171
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907694919012811374466367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26605129946008540916310911 39907694919012811374466367)
  ·
    refine ⟨59861542378519217061699551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39907694919012811374466367 59861542378519217061699551)
    ·
      refine ⟨89792313567778825592549327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59861542378519217061699551 89792313567778825592549327)
      ·
        refine ⟨134688470351668238388823991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89792313567778825592549327 134688470351668238388823991)
        ·
          refine ⟨202032705527502357583235987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134688470351668238388823991 202032705527502357583235987)
          ·
            refine ⟨303049058291253536374853981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202032705527502357583235987 303049058291253536374853981)
            ·
              refine ⟨113643396859220076140570243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303049058291253536374853981 113643396859220076140570243)
              ·
                refine ⟨170465095288830114210855365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113643396859220076140570243 170465095288830114210855365)
                ·
                  refine ⟨31962205366655646414535381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170465095288830114210855365 31962205366655646414535381)
                  ·
                    refine ⟨749114188280991712840673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31962205366655646414535381 749114188280991712840673)
                    ·
                      refine ⟨561835641210743784630505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749114188280991712840673 561835641210743784630505)
                      ·
                        rfl

theorem cell23_1094171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7, 2].length) (baseStart_1094171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094171 prefixEnd_1094171 := by exact prefixLift 1094171
  have htrace : WordTrace (prefixWord ++ tailWord_1094171) baseStart_1094171 baseEnd_1094171 := by
    simpa [prefixWord, tailWord_1094171, baseEnd_1094171] using wordTrace_append hprefix tailTrace_1094171
  have hstable : (prefixWord ++ tailWord_1094171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094171).length < 2 ^ (prefixWord ++ tailWord_1094171).sum := by decide
  have hdescent : baseEnd_1094171 < baseStart_1094171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094179 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 1, 2, 2]
def baseStart_1094179 : Nat := 118140960795 + 1094179 * 2 ^ 59
def prefixEnd_1094179 : Nat := 4983230072969 + 3 ^ 40 * 1094179 * 2
def baseEnd_1094179 : Nat := 561839749055979753330469

theorem tailTrace_1094179 : CollatzResearch.WordTrace tailWord_1094179 prefixEnd_1094179 561839749055979753330469 := by
  unfold tailWord_1094179
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907986702983828740757591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26605324468655885827171727 39907986702983828740757591)
  ·
    refine ⟨59861980054475743111136387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39907986702983828740757591 59861980054475743111136387)
    ·
      refine ⟨89792970081713614666704581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59861980054475743111136387 89792970081713614666704581)
      ·
        refine ⟨16836181890321302750007109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89792970081713614666704581 16836181890321302750007109)
        ·
          refine ⟨3156784104435244265626333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16836181890321302750007109 3156784104435244265626333)
          ·
            refine ⟨1183794039163216599609875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3156784104435244265626333 1183794039163216599609875)
            ·
              refine ⟨1775691058744824899414813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183794039163216599609875 1775691058744824899414813)
              ·
                refine ⟨665884147029309337280555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775691058744824899414813 665884147029309337280555)
                ·
                  refine ⟨998826220543964005920833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665884147029309337280555 998826220543964005920833)
                  ·
                    refine ⟨749119665407973004440625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998826220543964005920833 749119665407973004440625)
                    ·
                      refine ⟨561839749055979753330469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749119665407973004440625 561839749055979753330469)
                      ·
                        rfl

theorem cell23_1094179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_1094179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094179 prefixEnd_1094179 := by exact prefixLift 1094179
  have htrace : WordTrace (prefixWord ++ tailWord_1094179) baseStart_1094179 baseEnd_1094179 := by
    simpa [prefixWord, tailWord_1094179, baseEnd_1094179] using wordTrace_append hprefix tailTrace_1094179
  have hstable : (prefixWord ++ tailWord_1094179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094179).length < 2 ^ (prefixWord ++ tailWord_1094179).sum := by decide
  have hdescent : baseEnd_1094179 < baseStart_1094179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094196 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1094196 : Nat := 118140960795 + 1094196 * 2 ^ 59
def prefixEnd_1094196 : Nat := 4983230072969 + 3 ^ 40 * 1094196 * 2
def baseEnd_1094196 : Nat := 561848478227106186817891

theorem tailTrace_1094196 : CollatzResearch.WordTrace tailWord_1094196 prefixEnd_1094196 561848478227106186817891 := by
  unfold tailWord_1094196
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954303371961120322063221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26605737829281493762750961 19954303371961120322063221)
  ·
    refine ⟨1870715941121355030193427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19954303371961120322063221 1870715941121355030193427)
    ·
      refine ⟨2806073911682032545290141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870715941121355030193427 2806073911682032545290141)
      ·
        refine ⟨1052277716880762204483803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2806073911682032545290141 1052277716880762204483803)
        ·
          refine ⟨1578416575321143306725705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052277716880762204483803 1578416575321143306725705)
          ·
            refine ⟨1183812431490857480044279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578416575321143306725705 1183812431490857480044279)
            ·
              refine ⟨1775718647236286220066419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183812431490857480044279 1775718647236286220066419)
              ·
                refine ⟨2663577970854429330099629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775718647236286220066419 2663577970854429330099629)
                ·
                  refine ⟨998841739070410998787361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2663577970854429330099629 998841739070410998787361)
                  ·
                    refine ⟨749131304302808249090521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998841739070410998787361 749131304302808249090521)
                    ·
                      refine ⟨561848478227106186817891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749131304302808249090521 561848478227106186817891)
                      ·
                        rfl

theorem cell23_1094196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1094196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094196 prefixEnd_1094196 := by exact prefixLift 1094196
  have htrace : WordTrace (prefixWord ++ tailWord_1094196) baseStart_1094196 baseEnd_1094196 := by
    simpa [prefixWord, tailWord_1094196, baseEnd_1094196] using wordTrace_append hprefix tailTrace_1094196
  have hstable : (prefixWord ++ tailWord_1094196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094196).length < 2 ^ (prefixWord ++ tailWord_1094196).sum := by decide
  have hdescent : baseEnd_1094196 < baseStart_1094196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094201 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1094201 : Nat := 118140960795 + 1094201 * 2 ^ 59
def prefixEnd_1094201 : Nat := 4983230072969 + 3 ^ 40 * 1094201 * 2
def baseEnd_1094201 : Nat := 561851045630378667255367

theorem tailTrace_1094201 : CollatzResearch.WordTrace tailWord_1094201 prefixEnd_1094201 561851045630378667255367 := by
  unfold tailWord_1094201
  simp only [CollatzResearch.WordTrace]
  refine ⟨39908789108904126498058457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26605859405936084332038971 39908789108904126498058457)
  ·
    refine ⟨29931591831678094873543843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39908789108904126498058457 29931591831678094873543843)
    ·
      refine ⟨44897387747517142310315765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29931591831678094873543843 44897387747517142310315765)
      ·
        refine ⟨4209130101329732091592103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44897387747517142310315765 4209130101329732091592103)
        ·
          refine ⟨6313695151994598137388155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209130101329732091592103 6313695151994598137388155)
          ·
            refine ⟨9470542727991897206082233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313695151994598137388155 9470542727991897206082233)
            ·
              refine ⟨7102907045993922904561675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9470542727991897206082233 7102907045993922904561675)
              ·
                refine ⟨10654360568990884356842513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7102907045993922904561675 10654360568990884356842513)
                ·
                  refine ⟨7990770426743163267631885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10654360568990884356842513 7990770426743163267631885)
                  ·
                    refine ⟨2996538910028686225361957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7990770426743163267631885 2996538910028686225361957)
                    ·
                      refine ⟨561851045630378667255367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2996538910028686225361957 561851045630378667255367)
                      ·
                        rfl

theorem cell23_1094201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1094201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094201 prefixEnd_1094201 := by exact prefixLift 1094201
  have htrace : WordTrace (prefixWord ++ tailWord_1094201) baseStart_1094201 baseEnd_1094201 := by
    simpa [prefixWord, tailWord_1094201, baseEnd_1094201] using wordTrace_append hprefix tailTrace_1094201
  have hstable : (prefixWord ++ tailWord_1094201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094201).length < 2 ^ (prefixWord ++ tailWord_1094201).sum := by decide
  have hdescent : baseEnd_1094201 < baseStart_1094201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094206 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1094206 : Nat := 118140960795 + 1094206 * 2 ^ 59
def prefixEnd_1094206 : Nat := 4983230072969 + 3 ^ 40 * 1094206 * 2
def baseEnd_1094206 : Nat := 187284537677883715897615

theorem tailTrace_1094206 : CollatzResearch.WordTrace tailWord_1094206 prefixEnd_1094206 187284537677883715897615 := by
  unfold tailWord_1094206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988621434235751543998809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26605980982590674901326981 4988621434235751543998809)
  ·
    refine ⟨3741466075676813657999107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4988621434235751543998809 3741466075676813657999107)
    ·
      refine ⟨5612199113515220486998661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741466075676813657999107 5612199113515220486998661)
      ·
        refine ⟨1052287333784103841312249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5612199113515220486998661 1052287333784103841312249)
        ·
          refine ⟨789215500338077880984187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1052287333784103841312249 789215500338077880984187)
          ·
            refine ⟨1183823250507116821476281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789215500338077880984187 1183823250507116821476281)
            ·
              refine ⟨887867437880337616107211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183823250507116821476281 887867437880337616107211)
              ·
                refine ⟨1331801156820506424160817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887867437880337616107211 1331801156820506424160817)
                ·
                  refine ⟨998850867615379818120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331801156820506424160817 998850867615379818120613)
                  ·
                    refine ⟨187284537677883715897615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998850867615379818120613 187284537677883715897615)
                    ·
                      rfl

theorem cell23_1094206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1094206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094206 prefixEnd_1094206 := by exact prefixLift 1094206
  have htrace : WordTrace (prefixWord ++ tailWord_1094206) baseStart_1094206 baseEnd_1094206 := by
    simpa [prefixWord, tailWord_1094206, baseEnd_1094206] using wordTrace_append hprefix tailTrace_1094206
  have hstable : (prefixWord ++ tailWord_1094206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094206).length < 2 ^ (prefixWord ++ tailWord_1094206).sum := by decide
  have hdescent : baseEnd_1094206 < baseStart_1094206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094291 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_1094291 : Nat := 118140960795 + 1094291 * 2 ^ 59
def prefixEnd_1094291 : Nat := 4983230072969 + 3 ^ 40 * 1094291 * 2
def baseEnd_1094291 : Nat := 561897258889283315129953

theorem tailTrace_1094291 : CollatzResearch.WordTrace tailWord_1094291 prefixEnd_1094291 561897258889283315129953 := by
  unfold tailWord_1094291
  simp only [CollatzResearch.WordTrace]
  refine ⟨39912071678578071868834727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26608047785718714579223151 39912071678578071868834727)
  ·
    refine ⟨59868107517867107803252091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39912071678578071868834727 59868107517867107803252091)
    ·
      refine ⟨89802161276800661704878137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59868107517867107803252091 89802161276800661704878137)
      ·
        refine ⟨67351620957600496278658603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89802161276800661704878137 67351620957600496278658603)
        ·
          refine ⟨101027431436400744417987905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67351620957600496278658603 101027431436400744417987905)
          ·
            refine ⟨75770573577300558313490929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101027431436400744417987905 75770573577300558313490929)
            ·
              refine ⟨56827930182975418735118197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75770573577300558313490929 56827930182975418735118197)
              ·
                refine ⟨5327618454653945506417331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56827930182975418735118197 5327618454653945506417331)
                ·
                  refine ⟨7991427681980918259625997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327618454653945506417331 7991427681980918259625997)
                  ·
                    refine ⟨2996785380742844347359749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7991427681980918259625997 2996785380742844347359749)
                    ·
                      refine ⟨561897258889283315129953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2996785380742844347359749 561897258889283315129953)
                      ·
                        rfl

theorem cell23_1094291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_1094291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094291 prefixEnd_1094291 := by exact prefixLift 1094291
  have htrace : WordTrace (prefixWord ++ tailWord_1094291) baseStart_1094291 baseEnd_1094291 := by
    simpa [prefixWord, tailWord_1094291, baseEnd_1094291] using wordTrace_append hprefix tailTrace_1094291
  have hstable : (prefixWord ++ tailWord_1094291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094291).length < 2 ^ (prefixWord ++ tailWord_1094291).sum := by decide
  have hdescent : baseEnd_1094291 < baseStart_1094291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094292 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1094292 : Nat := 118140960795 + 1094292 * 2 ^ 59
def prefixEnd_1094292 : Nat := 4983230072969 + 3 ^ 40 * 1094292 * 2
def baseEnd_1094292 : Nat := 62433085818881979024161

theorem tailTrace_1094292 : CollatzResearch.WordTrace tailWord_1094292 prefixEnd_1094292 62433085818881979024161 := by
  unfold tailWord_1094292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19956054075787224519810565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26608072101049632693080753 19956054075787224519810565)
  ·
    refine ⟨3741760139210104597464481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19956054075787224519810565 3741760139210104597464481)
    ·
      refine ⟨2806320104407578448098361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3741760139210104597464481 2806320104407578448098361)
      ·
        refine ⟨2104740078305683836073771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2806320104407578448098361 2104740078305683836073771)
        ·
          refine ⟨3157110117458525754110657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104740078305683836073771 3157110117458525754110657)
          ·
            refine ⟨2367832588093894315582993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157110117458525754110657 2367832588093894315582993)
            ·
              refine ⟨1775874441070420736687245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367832588093894315582993 1775874441070420736687245)
              ·
                refine ⟨665952915401407776257717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775874441070420736687245 665952915401407776257717)
                ·
                  refine ⟨62433085818881979024161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665952915401407776257717 62433085818881979024161)
                  ·
                    rfl

theorem cell23_1094292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1094292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094292 prefixEnd_1094292 := by exact prefixLift 1094292
  have htrace : WordTrace (prefixWord ++ tailWord_1094292) baseStart_1094292 baseEnd_1094292 := by
    simpa [prefixWord, tailWord_1094292, baseEnd_1094292] using wordTrace_append hprefix tailTrace_1094292
  have hstable : (prefixWord ++ tailWord_1094292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094292).length < 2 ^ (prefixWord ++ tailWord_1094292).sum := by decide
  have hdescent : baseEnd_1094292 < baseStart_1094292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094308 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1094308 : Nat := 118140960795 + 1094308 * 2 ^ 59
def prefixEnd_1094308 : Nat := 4983230072969 + 3 ^ 40 * 1094308 * 2
def baseEnd_1094308 : Nat := 561905988060409748617375

theorem tailTrace_1094308 : CollatzResearch.WordTrace tailWord_1094308 prefixEnd_1094308 561905988060409748617375 := by
  unfold tailWord_1094308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19956345859758241886101789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26608461146344322514802385 19956345859758241886101789)
  ·
    refine ⟨7483629697409340707288171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19956345859758241886101789 7483629697409340707288171)
    ·
      refine ⟨11225444546114011060932257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7483629697409340707288171 11225444546114011060932257)
      ·
        refine ⟨8419083409585508295699193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11225444546114011060932257 8419083409585508295699193)
        ·
          refine ⟨6314312557189131221774395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8419083409585508295699193 6314312557189131221774395)
          ·
            refine ⟨9471468835783696832661593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314312557189131221774395 9471468835783696832661593)
            ·
              refine ⟨7103601626837772624496195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471468835783696832661593 7103601626837772624496195)
              ·
                refine ⟨10655402440256658936744293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103601626837772624496195 10655402440256658936744293)
                ·
                  refine ⟨1997887957548123550639555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10655402440256658936744293 1997887957548123550639555)
                  ·
                    refine ⟨2996831936322185325959333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1997887957548123550639555 2996831936322185325959333)
                    ·
                      refine ⟨561905988060409748617375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2996831936322185325959333 561905988060409748617375)
                      ·
                        rfl

theorem cell23_1094308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1094308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094308 prefixEnd_1094308 := by exact prefixLift 1094308
  have htrace : WordTrace (prefixWord ++ tailWord_1094308) baseStart_1094308 baseEnd_1094308 := by
    simpa [prefixWord, tailWord_1094308, baseEnd_1094308] using wordTrace_append hprefix tailTrace_1094308
  have hstable : (prefixWord ++ tailWord_1094308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094308).length < 2 ^ (prefixWord ++ tailWord_1094308).sum := by decide
  have hdescent : baseEnd_1094308 < baseStart_1094308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094348 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 8]
def baseStart_1094348 : Nat := 118140960795 + 1094348 * 2 ^ 59
def prefixEnd_1094348 : Nat := 4983230072969 + 3 ^ 40 * 1094348 * 2
def baseEnd_1094348 : Nat := 62436280809621065790799

theorem tailTrace_1094348 : CollatzResearch.WordTrace tailWord_1094348 prefixEnd_1094348 62436280809621065790799 := by
  unfold tailWord_1094348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957075319685785301829849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26609433759581047069106465 19957075319685785301829849)
  ·
    refine ⟨14967806489764338976372387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19957075319685785301829849 14967806489764338976372387)
    ·
      refine ⟨22451709734646508464558581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14967806489764338976372387 22451709734646508464558581)
      ·
        refine ⟨2104847787623110168552367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22451709734646508464558581 2104847787623110168552367)
        ·
          refine ⟨3157271681434665252828551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104847787623110168552367 3157271681434665252828551)
          ·
            refine ⟨4735907522151997879242827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157271681434665252828551 4735907522151997879242827)
            ·
              refine ⟨7103861283227996818864241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735907522151997879242827 7103861283227996818864241)
              ·
                refine ⟨5327895962420997614148181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7103861283227996818864241 5327895962420997614148181)
                ·
                  refine ⟨62436280809621065790799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5327895962420997614148181 62436280809621065790799)
                  ·
                    rfl

theorem cell23_1094348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_1094348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094348 prefixEnd_1094348 := by exact prefixLift 1094348
  have htrace : WordTrace (prefixWord ++ tailWord_1094348) baseStart_1094348 baseEnd_1094348 := by
    simpa [prefixWord, tailWord_1094348, baseEnd_1094348] using wordTrace_append hprefix tailTrace_1094348
  have hstable : (prefixWord ++ tailWord_1094348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094348).length < 2 ^ (prefixWord ++ tailWord_1094348).sum := by decide
  have hdescent : baseEnd_1094348 < baseStart_1094348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094369 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1094369 : Nat := 118140960795 + 1094369 * 2 ^ 59
def prefixEnd_1094369 : Nat := 4983230072969 + 3 ^ 40 * 1094369 * 2
def baseEnd_1094369 : Nat := 187312436793444669984865

theorem tailTrace_1094369 : CollatzResearch.WordTrace tailWord_1094369 prefixEnd_1094369 187312436793444669984865 := by
  unfold tailWord_1094369
  simp only [CollatzResearch.WordTrace]
  refine ⟨39914916572295491190174161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26609944381530327460116107 39914916572295491190174161)
  ·
    refine ⟨29936187429221618392630621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39914916572295491190174161 29936187429221618392630621)
    ·
      refine ⟨11226070285958106897236483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29936187429221618392630621 11226070285958106897236483)
      ·
        refine ⟨16839105428937160345854725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11226070285958106897236483 16839105428937160345854725)
        ·
          refine ⟨3157332267925717564847761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16839105428937160345854725 3157332267925717564847761)
          ·
            refine ⟨2367999200944288173635821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157332267925717564847761 2367999200944288173635821)
            ·
              refine ⟨887999700354108065113433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2367999200944288173635821 887999700354108065113433)
              ·
                refine ⟨665999775265581048835075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887999700354108065113433 665999775265581048835075)
                ·
                  refine ⟨998999662898371573252613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665999775265581048835075 998999662898371573252613)
                  ·
                    refine ⟨187312436793444669984865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998999662898371573252613 187312436793444669984865)
                    ·
                      rfl

theorem cell23_1094369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1094369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094369 prefixEnd_1094369 := by exact prefixLift 1094369
  have htrace : WordTrace (prefixWord ++ tailWord_1094369) baseStart_1094369 baseEnd_1094369 := by
    simpa [prefixWord, tailWord_1094369, baseEnd_1094369] using wordTrace_append hprefix tailTrace_1094369
  have hstable : (prefixWord ++ tailWord_1094369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094369).length < 2 ^ (prefixWord ++ tailWord_1094369).sum := by decide
  have hdescent : baseEnd_1094369 < baseStart_1094369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094378 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1094378 : Nat := 118140960795 + 1094378 * 2 ^ 59
def prefixEnd_1094378 : Nat := 4983230072969 + 3 ^ 40 * 1094378 * 2
def baseEnd_1094378 : Nat := 187313977235408158247351

theorem tailTrace_1094378 : CollatzResearch.WordTrace tailWord_1094378 prefixEnd_1094378 187313977235408158247351 := by
  unfold tailWord_1094378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978811207315721431812947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26610163219508590484834525 9978811207315721431812947)
  ·
    refine ⟨14968216810973582147719421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9978811207315721431812947 14968216810973582147719421)
    ·
      refine ⟨5613081304115093305394783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14968216810973582147719421 5613081304115093305394783)
      ·
        refine ⟨8419621956172639958092175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613081304115093305394783 8419621956172639958092175)
        ·
          refine ⟨12629432934258959937138263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419621956172639958092175 12629432934258959937138263)
          ·
            refine ⟨18944149401388439905707395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629432934258959937138263 18944149401388439905707395)
            ·
              refine ⟨28416224102082659858561093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18944149401388439905707395 28416224102082659858561093)
              ·
                refine ⟨5328042019140498723480205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28416224102082659858561093 5328042019140498723480205)
                ·
                  refine ⟨1998015757177687021305077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5328042019140498723480205 1998015757177687021305077)
                  ·
                    refine ⟨187313977235408158247351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1998015757177687021305077 187313977235408158247351)
                    ·
                      rfl

theorem cell23_1094378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1094378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094378 prefixEnd_1094378 := by exact prefixLift 1094378
  have htrace : WordTrace (prefixWord ++ tailWord_1094378) baseStart_1094378 baseEnd_1094378 := by
    simpa [prefixWord, tailWord_1094378, baseEnd_1094378] using wordTrace_append hprefix tailTrace_1094378
  have hstable : (prefixWord ++ tailWord_1094378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094378).length < 2 ^ (prefixWord ++ tailWord_1094378).sum := by decide
  have hdescent : baseEnd_1094378 < baseStart_1094378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094382 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_1094382 : Nat := 118140960795 + 1094382 * 2 ^ 59
def prefixEnd_1094382 : Nat := 4983230072969 + 3 ^ 40 * 1094382 * 2
def baseEnd_1094382 : Nat := 62438220625426939899115

theorem tailTrace_1094382 : CollatzResearch.WordTrace tailWord_1094382 prefixEnd_1094382 62438220625426939899115 := by
  unfold tailWord_1094382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989423840156049301299675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26610260480832262940264933 4989423840156049301299675)
  ·
    refine ⟨7484135760234073951949513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989423840156049301299675 7484135760234073951949513)
    ·
      refine ⟨5613101820175555463962135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7484135760234073951949513 5613101820175555463962135)
      ·
        refine ⟨8419652730263333195943203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613101820175555463962135 8419652730263333195943203)
        ·
          refine ⟨12629479095394999793914805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419652730263333195943203 12629479095394999793914805)
          ·
            refine ⟨1184013665193281230679513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12629479095394999793914805 1184013665193281230679513)
            ·
              refine ⟨888010248894960923009635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184013665193281230679513 888010248894960923009635)
              ·
                refine ⟨1332015373342441384514453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888010248894960923009635 1332015373342441384514453)
                ·
                  refine ⟨62438220625426939899115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1332015373342441384514453 62438220625426939899115)
                  ·
                    rfl

theorem cell23_1094382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_1094382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094382 prefixEnd_1094382 := by exact prefixLift 1094382
  have htrace : WordTrace (prefixWord ++ tailWord_1094382) baseStart_1094382 baseEnd_1094382 := by
    simpa [prefixWord, tailWord_1094382, baseEnd_1094382] using wordTrace_append hprefix tailTrace_1094382
  have hstable : (prefixWord ++ tailWord_1094382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094382).length < 2 ^ (prefixWord ++ tailWord_1094382).sum := by decide
  have hdescent : baseEnd_1094382 < baseStart_1094382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094385 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_1094385 : Nat := 118140960795 + 1094385 * 2 ^ 59
def prefixEnd_1094385 : Nat := 4983230072969 + 3 ^ 40 * 1094385 * 2
def baseEnd_1094385 : Nat := 561945526070805947354521

theorem tailTrace_1094385 : CollatzResearch.WordTrace tailWord_1094385 prefixEnd_1094385 561945526070805947354521 := by
  unfold tailWord_1094385
  simp only [CollatzResearch.WordTrace]
  refine ⟨39915500140237525922756609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26610333426825017281837739 39915500140237525922756609)
  ·
    refine ⟨29936625105178144442067457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39915500140237525922756609 29936625105178144442067457)
    ·
      refine ⟨22452468828883608331550593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29936625105178144442067457 22452468828883608331550593)
      ·
        refine ⟨16839351621662706248662945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22452468828883608331550593 16839351621662706248662945)
        ·
          refine ⟨12629513716247029686497209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16839351621662706248662945 12629513716247029686497209)
          ·
            refine ⟨9472135287185272264872907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12629513716247029686497209 9472135287185272264872907)
            ·
              refine ⟨14208202930777908397309361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9472135287185272264872907 14208202930777908397309361)
              ·
                refine ⟨10656152198083431297982021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14208202930777908397309361 10656152198083431297982021)
                ·
                  refine ⟨1998028537140643368371629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10656152198083431297982021 1998028537140643368371629)
                  ·
                    refine ⟨749260701427741263139361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998028537140643368371629 749260701427741263139361)
                    ·
                      refine ⟨561945526070805947354521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749260701427741263139361 561945526070805947354521)
                      ·
                        rfl

theorem cell23_1094385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_1094385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094385 prefixEnd_1094385 := by exact prefixLift 1094385
  have htrace : WordTrace (prefixWord ++ tailWord_1094385) baseStart_1094385 baseEnd_1094385 := by
    simpa [prefixWord, tailWord_1094385, baseEnd_1094385] using wordTrace_append hprefix tailTrace_1094385
  have hstable : (prefixWord ++ tailWord_1094385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094385).length < 2 ^ (prefixWord ++ tailWord_1094385).sum := by decide
  have hdescent : baseEnd_1094385 < baseStart_1094385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094408 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_1094408 : Nat := 118140960795 + 1094408 * 2 ^ 59
def prefixEnd_1094408 : Nat := 4983230072969 + 3 ^ 40 * 1094408 * 2
def baseEnd_1094408 : Nat := 187319112041953119122305

theorem tailTrace_1094408 : CollatzResearch.WordTrace tailWord_1094408 prefixEnd_1094408 187319112041953119122305 := by
  unfold tailWord_1094408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958169509577100425421939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26610892679436133900562585 19958169509577100425421939)
  ·
    refine ⟨29937254264365650638132909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19958169509577100425421939 29937254264365650638132909)
    ·
      refine ⟨11226470349137118989299841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29937254264365650638132909 11226470349137118989299841)
      ·
        refine ⟨8419852761852839241974881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11226470349137118989299841 8419852761852839241974881)
        ·
          refine ⟨6314889571389629431481161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8419852761852839241974881 6314889571389629431481161)
          ·
            refine ⟨4736167178542222073610871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6314889571389629431481161 4736167178542222073610871)
            ·
              refine ⟨7104250767813333110416307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736167178542222073610871 7104250767813333110416307)
              ·
                refine ⟨10656376151719999665624461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104250767813333110416307 10656376151719999665624461)
                ·
                  refine ⟨3996141056894999874609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10656376151719999665624461 3996141056894999874609173)
                  ·
                    refine ⟨187319112041953119122305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3996141056894999874609173 187319112041953119122305)
                    ·
                      rfl

theorem cell23_1094408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_1094408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094408 prefixEnd_1094408 := by exact prefixLift 1094408
  have htrace : WordTrace (prefixWord ++ tailWord_1094408) baseStart_1094408 baseEnd_1094408 := by
    simpa [prefixWord, tailWord_1094408, baseEnd_1094408] using wordTrace_append hprefix tailTrace_1094408
  have hstable : (prefixWord ++ tailWord_1094408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094408).length < 2 ^ (prefixWord ++ tailWord_1094408).sum := by decide
  have hdescent : baseEnd_1094408 < baseStart_1094408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094482 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1094482 : Nat := 118140960795 + 1094482 * 2 ^ 59
def prefixEnd_1094482 : Nat := 4983230072969 + 3 ^ 40 * 1094482 * 2
def baseEnd_1094482 : Nat := 561995333694292067841575

theorem tailTrace_1094482 : CollatzResearch.WordTrace tailWord_1094482 prefixEnd_1094482 561995333694292067841575 := by
  unfold tailWord_1094482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979759505221527872259425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26612692013924074326025133 9979759505221527872259425)
  ·
    refine ⟨7484819628916145904194569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9979759505221527872259425 7484819628916145904194569)
    ·
      refine ⟨5613614721687109428145927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7484819628916145904194569 5613614721687109428145927)
      ·
        refine ⟨8420422082530664142218891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613614721687109428145927 8420422082530664142218891)
        ·
          refine ⟨12630633123795996213328337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420422082530664142218891 12630633123795996213328337)
          ·
            refine ⟨9472974842846997159996253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12630633123795996213328337 9472974842846997159996253)
            ·
              refine ⟨3552365566067623934998595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9472974842846997159996253 3552365566067623934998595)
              ·
                refine ⟨5328548349101435902497893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552365566067623934998595 5328548349101435902497893)
                ·
                  refine ⟨999102815456519231718355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5328548349101435902497893 999102815456519231718355)
                  ·
                    refine ⟨1498654223184778847577533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 999102815456519231718355 1498654223184778847577533)
                    ·
                      refine ⟨561995333694292067841575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1498654223184778847577533 561995333694292067841575)
                      ·
                        rfl

theorem cell23_1094482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1094482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094482 prefixEnd_1094482 := by exact prefixLift 1094482
  have htrace : WordTrace (prefixWord ++ tailWord_1094482) baseStart_1094482 baseEnd_1094482 := by
    simpa [prefixWord, tailWord_1094482, baseEnd_1094482] using wordTrace_append hprefix tailTrace_1094482
  have hstable : (prefixWord ++ tailWord_1094482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094482).length < 2 ^ (prefixWord ++ tailWord_1094482).sum := by decide
  have hdescent : baseEnd_1094482 < baseStart_1094482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094488 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1094488 : Nat := 118140960795 + 1094488 * 2 ^ 59
def prefixEnd_1094488 : Nat := 4983230072969 + 3 ^ 40 * 1094488 * 2
def baseEnd_1094488 : Nat := 561998414578219044366547

theorem tailTrace_1094488 : CollatzResearch.WordTrace tailWord_1094488 prefixEnd_1094488 561998414578219044366547 := by
  unfold tailWord_1094488
  simp only [CollatzResearch.WordTrace]
  refine ⟨19959628429432187256878059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26612837905909583009170745 19959628429432187256878059)
  ·
    refine ⟨29939442644148280885317089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19959628429432187256878059 29939442644148280885317089)
    ·
      refine ⟨22454581983111210663987817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29939442644148280885317089 22454581983111210663987817)
      ·
        refine ⟨16840936487333407997990863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22454581983111210663987817 16840936487333407997990863)
        ·
          refine ⟨25261404731000111996986295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16840936487333407997990863 25261404731000111996986295)
          ·
            refine ⟨37892107096500167995479443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25261404731000111996986295 37892107096500167995479443)
            ·
              refine ⟨56838160644750251993219165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37892107096500167995479443 56838160644750251993219165)
              ·
                refine ⟨21314310241781344497457187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56838160644750251993219165 21314310241781344497457187)
                ·
                  refine ⟨31971465362672016746185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21314310241781344497457187 31971465362672016746185781)
                  ·
                    refine ⟨2997324877750501569954917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31971465362672016746185781 2997324877750501569954917)
                    ·
                      refine ⟨561998414578219044366547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2997324877750501569954917 561998414578219044366547)
                      ·
                        rfl

theorem cell23_1094488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1094488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094488 prefixEnd_1094488 := by exact prefixLift 1094488
  have htrace : WordTrace (prefixWord ++ tailWord_1094488) baseStart_1094488 baseEnd_1094488 := by
    simpa [prefixWord, tailWord_1094488, baseEnd_1094488] using wordTrace_append hprefix tailTrace_1094488
  have hstable : (prefixWord ++ tailWord_1094488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094488).length < 2 ^ (prefixWord ++ tailWord_1094488).sum := by decide
  have hdescent : baseEnd_1094488 < baseStart_1094488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094550 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1094550 : Nat := 118140960795 + 1094550 * 2 ^ 59
def prefixEnd_1094550 : Nat := 4983230072969 + 3 ^ 40 * 1094550 * 2
def baseEnd_1094550 : Nat := 562030250378797801791263

theorem tailTrace_1094550 : CollatzResearch.WordTrace tailWord_1094550 prefixEnd_1094550 562030250378797801791263 := by
  unfold tailWord_1094550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495094886539984943907069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26614345456426506068342069 2495094886539984943907069)
  ·
    refine ⟨935660582452494353965151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2495094886539984943907069 935660582452494353965151)
    ·
      refine ⟨1403490873678741530947727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935660582452494353965151 1403490873678741530947727)
      ·
        refine ⟨2105236310518112296421591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403490873678741530947727 2105236310518112296421591)
        ·
          refine ⟨3157854465777168444632387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105236310518112296421591 3157854465777168444632387)
          ·
            refine ⟨4736781698665752666948581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157854465777168444632387 4736781698665752666948581)
            ·
              refine ⟨888146568499828625052859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4736781698665752666948581 888146568499828625052859)
              ·
                refine ⟨1332219852749742937579289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888146568499828625052859 1332219852749742937579289)
                ·
                  refine ⟨999164889562307203184467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332219852749742937579289 999164889562307203184467)
                  ·
                    refine ⟨1498747334343460804776701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 999164889562307203184467 1498747334343460804776701)
                    ·
                      refine ⟨562030250378797801791263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1498747334343460804776701 562030250378797801791263)
                      ·
                        rfl

theorem cell23_1094550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1094550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094550 prefixEnd_1094550 := by exact prefixLift 1094550
  have htrace : WordTrace (prefixWord ++ tailWord_1094550) baseStart_1094550 baseEnd_1094550 := by
    simpa [prefixWord, tailWord_1094550, baseEnd_1094550] using wordTrace_append hprefix tailTrace_1094550
  have hstable : (prefixWord ++ tailWord_1094550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094550).length < 2 ^ (prefixWord ++ tailWord_1094550).sum := by decide
  have hdescent : baseEnd_1094550 < baseStart_1094550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094585 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1094585 : Nat := 118140960795 + 1094585 * 2 ^ 59
def prefixEnd_1094585 : Nat := 4983230072969 + 3 ^ 40 * 1094585 * 2
def baseEnd_1094585 : Nat := 562048222201705164853601

theorem tailTrace_1094585 : CollatzResearch.WordTrace tailWord_1094585 prefixEnd_1094585 562048222201705164853601 := by
  unfold tailWord_1094585
  simp only [CollatzResearch.WordTrace]
  refine ⟨39922794739512960080037209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26615196493008640053358139 39922794739512960080037209)
  ·
    refine ⟨29942096054634720060027907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39922794739512960080037209 29942096054634720060027907)
    ·
      refine ⟨44913144081952080090041861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29942096054634720060027907 44913144081952080090041861)
      ·
        refine ⟨8421214515366015016882849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44913144081952080090041861 8421214515366015016882849)
        ·
          refine ⟨6315910886524511262662137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8421214515366015016882849 6315910886524511262662137)
          ·
            refine ⟨4736933164893383446996603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6315910886524511262662137 4736933164893383446996603)
            ·
              refine ⟨7105399747340075170494905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736933164893383446996603 7105399747340075170494905)
              ·
                refine ⟨5329049810505056377871179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105399747340075170494905 5329049810505056377871179)
                ·
                  refine ⟨7993574715757584566806769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329049810505056377871179 7993574715757584566806769)
                  ·
                    refine ⟨5995181036818188425105077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7993574715757584566806769 5995181036818188425105077)
                    ·
                      refine ⟨562048222201705164853601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5995181036818188425105077 562048222201705164853601)
                      ·
                        rfl

theorem cell23_1094585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1094585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094585 prefixEnd_1094585 := by exact prefixLift 1094585
  have htrace : WordTrace (prefixWord ++ tailWord_1094585) baseStart_1094585 baseEnd_1094585 := by
    simpa [prefixWord, tailWord_1094585, baseEnd_1094585] using wordTrace_append hprefix tailTrace_1094585
  have hstable : (prefixWord ++ tailWord_1094585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094585).length < 2 ^ (prefixWord ++ tailWord_1094585).sum := by decide
  have hdescent : baseEnd_1094585 < baseStart_1094585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094596 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1094596 : Nat := 118140960795 + 1094596 * 2 ^ 59
def prefixEnd_1094596 : Nat := 4983230072969 + 3 ^ 40 * 1094596 * 2
def baseEnd_1094596 : Nat := 62450430054322735757339

theorem tailTrace_1094596 : CollatzResearch.WordTrace tailWord_1094596 prefixEnd_1094596 62450430054322735757339 := by
  unfold tailWord_1094596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19961597971236554479343821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26615463961648739305791761 19961597971236554479343821)
  ·
    refine ⟨7485599239213707929753933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19961597971236554479343821 7485599239213707929753933)
    ·
      refine ⟨2807099714705140473657725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7485599239213707929753933 2807099714705140473657725)
      ·
        refine ⟨1052662393014427677621647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2807099714705140473657725 1052662393014427677621647)
        ·
          refine ⟨1578993589521641516432471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052662393014427677621647 1578993589521641516432471)
          ·
            refine ⟨2368490384282462274648707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578993589521641516432471 2368490384282462274648707)
            ·
              refine ⟨3552735576423693411973061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368490384282462274648707 3552735576423693411973061)
              ·
                refine ⟨666137920579442514744949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3552735576423693411973061 666137920579442514744949)
                ·
                  refine ⟨62450430054322735757339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666137920579442514744949 62450430054322735757339)
                  ·
                    rfl

theorem cell23_1094596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1094596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094596 prefixEnd_1094596 := by exact prefixLift 1094596
  have htrace : WordTrace (prefixWord ++ tailWord_1094596) baseStart_1094596 baseEnd_1094596 := by
    simpa [prefixWord, tailWord_1094596, baseEnd_1094596] using wordTrace_append hprefix tailTrace_1094596
  have hstable : (prefixWord ++ tailWord_1094596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094596).length < 2 ^ (prefixWord ++ tailWord_1094596).sum := by decide
  have hdescent : baseEnd_1094596 < baseStart_1094596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094626 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1094626 : Nat := 118140960795 + 1094626 * 2 ^ 59
def prefixEnd_1094626 : Nat := 4983230072969 + 3 ^ 40 * 1094626 * 2
def baseEnd_1094626 : Nat := 187356424969513168146971

theorem tailTrace_1094626 : CollatzResearch.WordTrace tailWord_1094626 prefixEnd_1094626 187356424969513168146971 := by
  unfold tailWord_1094626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981072533091106020569933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26616193421576282721519821 9981072533091106020569933)
  ·
    refine ⟨3742902199909164757713725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9981072533091106020569933 3742902199909164757713725)
    ·
      refine ⟨1403588324965936784142647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3742902199909164757713725 1403588324965936784142647)
      ·
        refine ⟨2105382487448905176213971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403588324965936784142647 2105382487448905176213971)
        ·
          refine ⟨3158073731173357764320957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105382487448905176213971 3158073731173357764320957)
          ·
            refine ⟨1184277649190009161620359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3158073731173357764320957 1184277649190009161620359)
            ·
              refine ⟨1776416473785013742430539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184277649190009161620359 1776416473785013742430539)
              ·
                refine ⟨2664624710677520613645809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776416473785013742430539 2664624710677520613645809)
                ·
                  refine ⟨1998468533008140460234357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2664624710677520613645809 1998468533008140460234357)
                  ·
                    refine ⟨187356424969513168146971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1998468533008140460234357 187356424969513168146971)
                    ·
                      rfl

theorem cell23_1094626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1094626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094626 prefixEnd_1094626 := by exact prefixLift 1094626
  have htrace : WordTrace (prefixWord ++ tailWord_1094626) baseStart_1094626 baseEnd_1094626 := by
    simpa [prefixWord, tailWord_1094626, baseEnd_1094626] using wordTrace_append hprefix tailTrace_1094626
  have hstable : (prefixWord ++ tailWord_1094626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094626).length < 2 ^ (prefixWord ++ tailWord_1094626).sum := by decide
  have hdescent : baseEnd_1094626 < baseStart_1094626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094629 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1094629 : Nat := 118140960795 + 1094629 * 2 ^ 59
def prefixEnd_1094629 : Nat := 4983230072969 + 3 ^ 40 * 1094629 * 2
def baseEnd_1094629 : Nat := 562070815350502992703399

theorem tailTrace_1094629 : CollatzResearch.WordTrace tailWord_1094629 prefixEnd_1094629 562070815350502992703399 := by
  unfold tailWord_1094629
  simp only [CollatzResearch.WordTrace]
  refine ⟨39924399551353555594638941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26616266367569037063092627 39924399551353555594638941)
  ·
    refine ⟨14971649831757583347989603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39924399551353555594638941 14971649831757583347989603)
    ·
      refine ⟨22457474747636375021984405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14971649831757583347989603 22457474747636375021984405)
      ·
        refine ⟨1052694128795455079155519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22457474747636375021984405 1052694128795455079155519)
        ·
          refine ⟨1579041193193182618733279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052694128795455079155519 1579041193193182618733279)
          ·
            refine ⟨2368561789789773928099919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579041193193182618733279 2368561789789773928099919)
            ·
              refine ⟨3552842684684660892149879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368561789789773928099919 3552842684684660892149879)
              ·
                refine ⟨5329264027026991338224819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552842684684660892149879 5329264027026991338224819)
                ·
                  refine ⟨7993896040540487007337229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329264027026991338224819 7993896040540487007337229)
                  ·
                    refine ⟨2997711015202682627751461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7993896040540487007337229 2997711015202682627751461)
                    ·
                      refine ⟨562070815350502992703399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2997711015202682627751461 562070815350502992703399)
                      ·
                        rfl

theorem cell23_1094629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1094629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094629 prefixEnd_1094629 := by exact prefixLift 1094629
  have htrace : WordTrace (prefixWord ++ tailWord_1094629) baseStart_1094629 baseEnd_1094629 := by
    simpa [prefixWord, tailWord_1094629, baseEnd_1094629] using wordTrace_append hprefix tailTrace_1094629
  have hstable : (prefixWord ++ tailWord_1094629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094629).length < 2 ^ (prefixWord ++ tailWord_1094629).sum := by decide
  have hdescent : baseEnd_1094629 < baseStart_1094629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094639 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 1, 4]
def baseStart_1094639 : Nat := 118140960795 + 1094639 * 2 ^ 59
def prefixEnd_1094639 : Nat := 4983230072969 + 3 ^ 40 * 1094639 * 2
def baseEnd_1094639 : Nat := 187358650052349317859451

theorem tailTrace_1094639 : CollatzResearch.WordTrace tailWord_1094639 prefixEnd_1094639 187358650052349317859451 := by
  unfold tailWord_1094639
  simp only [CollatzResearch.WordTrace]
  refine ⟨39924764281317327302502971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26616509520878218201668647 39924764281317327302502971)
  ·
    refine ⟨59887146421975990953754457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39924764281317327302502971 59887146421975990953754457)
    ·
      refine ⟨44915359816481993215315843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59887146421975990953754457 44915359816481993215315843)
      ·
        refine ⟨67373039724722989822973765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44915359816481993215315843 67373039724722989822973765)
        ·
          refine ⟨12632444948385560591807581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67373039724722989822973765 12632444948385560591807581)
          ·
            refine ⟨4737166855644585221927843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12632444948385560591807581 4737166855644585221927843)
            ·
              refine ⟨7105750283466877832891765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737166855644585221927843 7105750283466877832891765)
              ·
                refine ⟨666164089075019796833603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7105750283466877832891765 666164089075019796833603)
                ·
                  refine ⟨999246133612529695250405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666164089075019796833603 999246133612529695250405)
                  ·
                    refine ⟨187358650052349317859451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 999246133612529695250405 187358650052349317859451)
                    ·
                      rfl

theorem cell23_1094639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_1094639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094639 prefixEnd_1094639 := by exact prefixLift 1094639
  have htrace : WordTrace (prefixWord ++ tailWord_1094639) baseStart_1094639 baseEnd_1094639 := by
    simpa [prefixWord, tailWord_1094639, baseEnd_1094639] using wordTrace_append hprefix tailTrace_1094639
  have hstable : (prefixWord ++ tailWord_1094639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094639).length < 2 ^ (prefixWord ++ tailWord_1094639).sum := by decide
  have hdescent : baseEnd_1094639 < baseStart_1094639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094652 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 6]
def baseStart_1094652 : Nat := 118140960795 + 1094652 * 2 ^ 59
def prefixEnd_1094652 : Nat := 4983230072969 + 3 ^ 40 * 1094652 * 2
def baseEnd_1094652 : Nat := 62453625045061822523977

theorem tailTrace_1094652 : CollatzResearch.WordTrace tailWord_1094652 prefixEnd_1094652 62453625045061822523977 := by
  unfold tailWord_1094652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19962619215135115261363105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26616825620180153681817473 19962619215135115261363105)
  ·
    refine ⟨14971964411351336446022329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19962619215135115261363105 14971964411351336446022329)
    ·
      refine ⟨11228973308513502334516747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14971964411351336446022329 11228973308513502334516747)
      ·
        refine ⟨16843459962770253501775121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228973308513502334516747 16843459962770253501775121)
        ·
          refine ⟨12632594972077690126331341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16843459962770253501775121 12632594972077690126331341)
          ·
            refine ⟨4737223114529133797374253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12632594972077690126331341 4737223114529133797374253)
            ·
              refine ⟨1776458667948425174015345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4737223114529133797374253 1776458667948425174015345)
              ·
                refine ⟨1332344000961318880511509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776458667948425174015345 1332344000961318880511509)
                ·
                  refine ⟨62453625045061822523977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1332344000961318880511509 62453625045061822523977)
                  ·
                    rfl

theorem cell23_1094652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_1094652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094652 prefixEnd_1094652 := by exact prefixLift 1094652
  have htrace : WordTrace (prefixWord ++ tailWord_1094652) baseStart_1094652 baseEnd_1094652 := by
    simpa [prefixWord, tailWord_1094652, baseEnd_1094652] using wordTrace_append hprefix tailTrace_1094652
  have hstable : (prefixWord ++ tailWord_1094652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094652).length < 2 ^ (prefixWord ++ tailWord_1094652).sum := by decide
  have hdescent : baseEnd_1094652 < baseStart_1094652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094665 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_1094665 : Nat := 118140960795 + 1094665 * 2 ^ 59
def prefixEnd_1094665 : Nat := 4983230072969 + 3 ^ 40 * 1094665 * 2
def baseEnd_1094665 : Nat := 187363100218021617284411

theorem tailTrace_1094665 : CollatzResearch.WordTrace tailWord_1094665 prefixEnd_1094665 187363100218021617284411 := by
  unfold tailWord_1094665
  simp only [CollatzResearch.WordTrace]
  refine ⟨39925712579223133742949449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26617141719482089161966299 39925712579223133742949449)
  ·
    refine ⟨29944284434417350307212087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39925712579223133742949449 29944284434417350307212087)
    ·
      refine ⟨44916426651626025460818131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29944284434417350307212087 44916426651626025460818131)
      ·
        refine ⟨67374639977439038191227197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44916426651626025460818131 67374639977439038191227197)
        ·
          refine ⟨25265489991539639321710199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67374639977439038191227197 25265489991539639321710199)
          ·
            refine ⟨37898234987309458982565299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25265489991539639321710199 37898234987309458982565299)
            ·
              refine ⟨56847352480964188473847949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37898234987309458982565299 56847352480964188473847949)
              ·
                refine ⟨21317757180361570677692981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56847352480964188473847949 21317757180361570677692981)
                ·
                  refine ⟨1998539735658897251033717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21317757180361570677692981 1998539735658897251033717)
                  ·
                    refine ⟨187363100218021617284411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1998539735658897251033717 187363100218021617284411)
                    ·
                      rfl

theorem cell23_1094665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_1094665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094665 prefixEnd_1094665 := by exact prefixLift 1094665
  have htrace : WordTrace (prefixWord ++ tailWord_1094665) baseStart_1094665 baseEnd_1094665 := by
    simpa [prefixWord, tailWord_1094665, baseEnd_1094665] using wordTrace_append hprefix tailTrace_1094665
  have hstable : (prefixWord ++ tailWord_1094665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094665).length < 2 ^ (prefixWord ++ tailWord_1094665).sum := by decide
  have hdescent : baseEnd_1094665 < baseStart_1094665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094689 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1094689 : Nat := 118140960795 + 1094689 * 2 ^ 59
def prefixEnd_1094689 : Nat := 4983230072969 + 3 ^ 40 * 1094689 * 2
def baseEnd_1094689 : Nat := 562101624189772757953123

theorem tailTrace_1094689 : CollatzResearch.WordTrace tailWord_1094689 prefixEnd_1094689 562101624189772757953123 := by
  unfold tailWord_1094689
  simp only [CollatzResearch.WordTrace]
  refine ⟨39926587931136185841823121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26617725287424123894548747 39926587931136185841823121)
  ·
    refine ⟨29944940948352139381367341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39926587931136185841823121 29944940948352139381367341)
    ·
      refine ⟨11229352855632052268012753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29944940948352139381367341 11229352855632052268012753)
      ·
        refine ⟨8422014641724039201009565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11229352855632052268012753 8422014641724039201009565)
        ·
          refine ⟨3158255490646514700378587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8422014641724039201009565 3158255490646514700378587)
          ·
            refine ⟨4737383235969772050567881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158255490646514700378587 4737383235969772050567881)
            ·
              refine ⟨3553037426977329037925911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4737383235969772050567881 3553037426977329037925911)
              ·
                refine ⟨5329556140465993556888867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553037426977329037925911 5329556140465993556888867)
                ·
                  refine ⟨7994334210698990335333301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329556140465993556888867 7994334210698990335333301)
                  ·
                    refine ⟨749468832253030343937497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7994334210698990335333301 749468832253030343937497)
                    ·
                      refine ⟨562101624189772757953123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749468832253030343937497 562101624189772757953123)
                      ·
                        rfl

theorem cell23_1094689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1094689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094689 prefixEnd_1094689 := by exact prefixLift 1094689
  have htrace : WordTrace (prefixWord ++ tailWord_1094689) baseStart_1094689 baseEnd_1094689 := by
    simpa [prefixWord, tailWord_1094689, baseEnd_1094689] using wordTrace_append hprefix tailTrace_1094689
  have hstable : (prefixWord ++ tailWord_1094689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094689).length < 2 ^ (prefixWord ++ tailWord_1094689).sum := by decide
  have hdescent : baseEnd_1094689 < baseStart_1094689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094715 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_1094715 : Nat := 118140960795 + 1094715 * 2 ^ 59
def prefixEnd_1094715 : Nat := 4983230072969 + 3 ^ 40 * 1094715 * 2
def baseEnd_1094715 : Nat := 562114974686789656228003

theorem tailTrace_1094715 : CollatzResearch.WordTrace tailWord_1094715 prefixEnd_1094715 562114974686789656228003 := by
  unfold tailWord_1094715
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927536229041992282269599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26618357486027994854846399 39927536229041992282269599)
  ·
    refine ⟨59891304343562988423404399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39927536229041992282269599 59891304343562988423404399)
    ·
      refine ⟨89836956515344482635106599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59891304343562988423404399 89836956515344482635106599)
      ·
        refine ⟨134755434773016723952659899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89836956515344482635106599 134755434773016723952659899)
        ·
          refine ⟨202133152159525085928989849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134755434773016723952659899 202133152159525085928989849)
          ·
            refine ⟨151599864119643814446742387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202133152159525085928989849 151599864119643814446742387)
            ·
              refine ⟨227399796179465721670113581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151599864119643814446742387 227399796179465721670113581)
              ·
                refine ⟨85274923567299645626292593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227399796179465721670113581 85274923567299645626292593)
                ·
                  refine ⟨63956192675474734219719445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85274923567299645626292593 63956192675474734219719445)
                  ·
                    refine ⟨2997946531662878166549349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63956192675474734219719445 2997946531662878166549349)
                    ·
                      refine ⟨562114974686789656228003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2997946531662878166549349 562114974686789656228003)
                      ·
                        rfl

theorem cell23_1094715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_1094715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094715 prefixEnd_1094715 := by exact prefixLift 1094715
  have htrace : WordTrace (prefixWord ++ tailWord_1094715) baseStart_1094715 baseEnd_1094715 := by
    simpa [prefixWord, tailWord_1094715, baseEnd_1094715] using wordTrace_append hprefix tailTrace_1094715
  have hstable : (prefixWord ++ tailWord_1094715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094715).length < 2 ^ (prefixWord ++ tailWord_1094715).sum := by decide
  have hdescent : baseEnd_1094715 < baseStart_1094715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094725 : List Nat := [1, 3, 1, 1, 1, 3, 3, 10]
def baseStart_1094725 : Nat := 118140960795 + 1094725 * 2 ^ 59
def prefixEnd_1094725 : Nat := 4983230072969 + 3 ^ 40 * 1094725 * 2
def baseEnd_1094725 : Nat := 20819263314567948781591

theorem tailTrace_1094725 : CollatzResearch.WordTrace tailWord_1094725 prefixEnd_1094725 20819263314567948781591 := by
  unfold tailWord_1094725
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927900959005763990133629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26618600639337175993422419 39927900959005763990133629)
  ·
    refine ⟨14972962859627161496300111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39927900959005763990133629 14972962859627161496300111)
    ·
      refine ⟨22459444289440742244450167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14972962859627161496300111 22459444289440742244450167)
      ·
        refine ⟨33689166434161113366675251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22459444289440742244450167 33689166434161113366675251)
        ·
          refine ⟨50533749651241670050012877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33689166434161113366675251 50533749651241670050012877)
          ·
            refine ⟨18950156119215626268754829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50533749651241670050012877 18950156119215626268754829)
            ·
              refine ⟨7106308544705859850783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18950156119215626268754829 7106308544705859850783061)
              ·
                refine ⟨20819263314567948781591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7106308544705859850783061 20819263314567948781591)
                ·
                  rfl

theorem cell23_1094725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 10].length) (baseStart_1094725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094725 prefixEnd_1094725 := by exact prefixLift 1094725
  have htrace : WordTrace (prefixWord ++ tailWord_1094725) baseStart_1094725 baseEnd_1094725 := by
    simpa [prefixWord, tailWord_1094725, baseEnd_1094725] using wordTrace_append hprefix tailTrace_1094725
  have hstable : (prefixWord ++ tailWord_1094725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094725).length < 2 ^ (prefixWord ++ tailWord_1094725).sum := by decide
  have hdescent : baseEnd_1094725 < baseStart_1094725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094732 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1094732 : Nat := 118140960795 + 1094732 * 2 ^ 59
def prefixEnd_1094732 : Nat := 4983230072969 + 3 ^ 40 * 1094732 * 2
def baseEnd_1094732 : Nat := 562123703857916089715425

theorem tailTrace_1094732 : CollatzResearch.WordTrace tailWord_1094732 prefixEnd_1094732 562123703857916089715425 := by
  unfold tailWord_1094732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19964078134990202092819225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26618770846653602790425633 19964078134990202092819225)
  ·
    refine ⟨14973058601242651569614419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19964078134990202092819225 14973058601242651569614419)
    ·
      refine ⟨22459587901863977354421629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14973058601242651569614419 22459587901863977354421629)
      ·
        refine ⟨8422345463198991507908111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22459587901863977354421629 8422345463198991507908111)
        ·
          refine ⟨12633518194798487261862167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422345463198991507908111 12633518194798487261862167)
          ·
            refine ⟨18950277292197730892793251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12633518194798487261862167 18950277292197730892793251)
            ·
              refine ⟨28425415938296596339189877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18950277292197730892793251 28425415938296596339189877)
              ·
                refine ⟨2664882744215305906799051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28425415938296596339189877 2664882744215305906799051)
                ·
                  refine ⟨3997324116322958860198577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664882744215305906799051 3997324116322958860198577)
                  ·
                    refine ⟨2997993087242219145148933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3997324116322958860198577 2997993087242219145148933)
                    ·
                      refine ⟨562123703857916089715425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2997993087242219145148933 562123703857916089715425)
                      ·
                        rfl

theorem cell23_1094732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1094732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094732 prefixEnd_1094732 := by exact prefixLift 1094732
  have htrace : WordTrace (prefixWord ++ tailWord_1094732) baseStart_1094732 baseEnd_1094732 := by
    simpa [prefixWord, tailWord_1094732, baseEnd_1094732] using wordTrace_append hprefix tailTrace_1094732
  have hstable : (prefixWord ++ tailWord_1094732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094732).length < 2 ^ (prefixWord ++ tailWord_1094732).sum := by decide
  have hdescent : baseEnd_1094732 < baseStart_1094732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094750 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1094750 : Nat := 118140960795 + 1094750 * 2 ^ 59
def prefixEnd_1094750 : Nat := 4983230072969 + 3 ^ 40 * 1094750 * 2
def baseEnd_1094750 : Nat := 187377648836565673096781

theorem tailTrace_1094750 : CollatzResearch.WordTrace tailWord_1094750 prefixEnd_1094750 187377648836565673096781 := by
  unfold tailWord_1094750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991101597989399157474213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26619208522610128839862469 4991101597989399157474213)
  ·
    refine ⟨935831549623012342026415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4991101597989399157474213 935831549623012342026415)
    ·
      refine ⟨1403747324434518513039623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935831549623012342026415 1403747324434518513039623)
      ·
        refine ⟨2105620986651777769559435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403747324434518513039623 2105620986651777769559435)
        ·
          refine ⟨3158431479977666654339153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105620986651777769559435 3158431479977666654339153)
          ·
            refine ⟨2368823609983249990754365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3158431479977666654339153 2368823609983249990754365)
            ·
              refine ⟨888308853743718746532887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368823609983249990754365 888308853743718746532887)
              ·
                refine ⟨1332463280615578119799331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888308853743718746532887 1332463280615578119799331)
                ·
                  refine ⟨1998694920923367179698997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332463280615578119799331 1998694920923367179698997)
                  ·
                    refine ⟨187377648836565673096781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1998694920923367179698997 187377648836565673096781)
                    ·
                      rfl

theorem cell23_1094750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1094750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094750 prefixEnd_1094750 := by exact prefixLift 1094750
  have htrace : WordTrace (prefixWord ++ tailWord_1094750) baseStart_1094750 baseEnd_1094750 := by
    simpa [prefixWord, tailWord_1094750, baseEnd_1094750] using wordTrace_append hprefix tailTrace_1094750
  have hstable : (prefixWord ++ tailWord_1094750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094750).length < 2 ^ (prefixWord ++ tailWord_1094750).sum := by decide
  have hdescent : baseEnd_1094750 < baseStart_1094750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094912 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1094912 : Nat := 118140960795 + 1094912 * 2 ^ 59
def prefixEnd_1094912 : Nat := 4983230072969 + 3 ^ 40 * 1094912 * 2
def baseEnd_1094912 : Nat := 562216130375725385464597

theorem tailTrace_1094912 : CollatzResearch.WordTrace tailWord_1094912 prefixEnd_1094912 562216130375725385464597 := by
  unfold tailWord_1094912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967360704664147463595495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26623147606218863284793993 19967360704664147463595495)
  ·
    refine ⟨29951041056996221195393243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19967360704664147463595495 29951041056996221195393243)
    ·
      refine ⟨44926561585494331793089865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29951041056996221195393243 44926561585494331793089865)
      ·
        refine ⟨33694921189120748844817399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44926561585494331793089865 33694921189120748844817399)
        ·
          refine ⟨50542381783681123267226099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33694921189120748844817399 50542381783681123267226099)
          ·
            refine ⟨75813572675521684900839149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50542381783681123267226099 75813572675521684900839149)
            ·
              refine ⟨28430089753320631837814681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75813572675521684900839149 28430089753320631837814681)
              ·
                refine ⟨21322567314990473878361011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28430089753320631837814681 21322567314990473878361011)
                ·
                  refine ⟨31983850972485710817541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21322567314990473878361011 31983850972485710817541517)
                  ·
                    refine ⟨11993944114682141556578069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31983850972485710817541517 11993944114682141556578069)
                    ·
                      refine ⟨562216130375725385464597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11993944114682141556578069 562216130375725385464597)
                      ·
                        rfl

theorem cell23_1094912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1094912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094912 prefixEnd_1094912 := by exact prefixLift 1094912
  have htrace : WordTrace (prefixWord ++ tailWord_1094912) baseStart_1094912 baseEnd_1094912 := by
    simpa [prefixWord, tailWord_1094912, baseEnd_1094912] using wordTrace_append hprefix tailTrace_1094912
  have hstable : (prefixWord ++ tailWord_1094912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094912).length < 2 ^ (prefixWord ++ tailWord_1094912).sum := by decide
  have hdescent : baseEnd_1094912 < baseStart_1094912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094916 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1094916 : Nat := 118140960795 + 1094916 * 2 ^ 59
def prefixEnd_1094916 : Nat := 4983230072969 + 3 ^ 40 * 1094916 * 2
def baseEnd_1094916 : Nat := 562218184298343369814579

theorem tailTrace_1094916 : CollatzResearch.WordTrace tailWord_1094916 prefixEnd_1094916 562218184298343369814579 := by
  unfold tailWord_1094916
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967433650656901805168301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26623244867542535740224401 19967433650656901805168301)
  ·
    refine ⟨7487787618996338176938113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19967433650656901805168301 7487787618996338176938113)
    ·
      refine ⟨5615840714247253632703585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7487787618996338176938113 5615840714247253632703585)
      ·
        refine ⟨4211880535685440224527689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615840714247253632703585 4211880535685440224527689)
        ·
          refine ⟨3158910401764080168395767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4211880535685440224527689 3158910401764080168395767)
          ·
            refine ⟨4738365602646120252593651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158910401764080168395767 4738365602646120252593651)
            ·
              refine ⟨7107548403969180378890477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738365602646120252593651 7107548403969180378890477)
              ·
                refine ⟨2665330651488442642083929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7107548403969180378890477 2665330651488442642083929)
                ·
                  refine ⟨1998997988616331981562947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665330651488442642083929 1998997988616331981562947)
                  ·
                    refine ⟨2998496982924497972344421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1998997988616331981562947 2998496982924497972344421)
                    ·
                      refine ⟨562218184298343369814579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2998496982924497972344421 562218184298343369814579)
                      ·
                        rfl

theorem cell23_1094916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1094916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094916 prefixEnd_1094916 := by exact prefixLift 1094916
  have htrace : WordTrace (prefixWord ++ tailWord_1094916) baseStart_1094916 baseEnd_1094916 := by
    simpa [prefixWord, tailWord_1094916, baseEnd_1094916] using wordTrace_append hprefix tailTrace_1094916
  have hstable : (prefixWord ++ tailWord_1094916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094916).length < 2 ^ (prefixWord ++ tailWord_1094916).sum := by decide
  have hdescent : baseEnd_1094916 < baseStart_1094916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094936 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1094936 : Nat := 118140960795 + 1094936 * 2 ^ 59
def prefixEnd_1094936 : Nat := 4983230072969 + 3 ^ 40 * 1094936 * 2
def baseEnd_1094936 : Nat := 562228453911433291564487

theorem tailTrace_1094936 : CollatzResearch.WordTrace tailWord_1094936 prefixEnd_1094936 562228453911433291564487 := by
  unfold tailWord_1094936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967798380620673513032331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26623731174160898017376441 19967798380620673513032331)
  ·
    refine ⟨29951697570931010269548497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19967798380620673513032331 29951697570931010269548497)
    ·
      refine ⟨22463773178198257702161373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29951697570931010269548497 22463773178198257702161373)
      ·
        refine ⟨8423914941824346638310515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22463773178198257702161373 8423914941824346638310515)
        ·
          refine ⟨12635872412736519957465773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8423914941824346638310515 12635872412736519957465773)
          ·
            refine ⟨4738452154776194984049665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12635872412736519957465773 4738452154776194984049665)
            ·
              refine ⟨3553839116082146238037249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738452154776194984049665 3553839116082146238037249)
              ·
                refine ⟨2665379337061609678527937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553839116082146238037249 2665379337061609678527937)
                ·
                  refine ⟨1999034502796207258895953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665379337061609678527937 1999034502796207258895953)
                  ·
                    refine ⟨1499275877097155444171965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999034502796207258895953 1499275877097155444171965)
                    ·
                      refine ⟨562228453911433291564487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1499275877097155444171965 562228453911433291564487)
                      ·
                        rfl

theorem cell23_1094936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1094936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094936 prefixEnd_1094936 := by exact prefixLift 1094936
  have htrace : WordTrace (prefixWord ++ tailWord_1094936) baseStart_1094936 baseEnd_1094936 := by
    simpa [prefixWord, tailWord_1094936, baseEnd_1094936] using wordTrace_append hprefix tailTrace_1094936
  have hstable : (prefixWord ++ tailWord_1094936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094936).length < 2 ^ (prefixWord ++ tailWord_1094936).sum := by decide
  have hdescent : baseEnd_1094936 < baseStart_1094936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094976 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2]
def baseStart_1094976 : Nat := 118140960795 + 1094976 * 2 ^ 59
def prefixEnd_1094976 : Nat := 4983230072969 + 3 ^ 40 * 1094976 * 2
def baseEnd_1094976 : Nat := 562248993137613135064303

theorem tailTrace_1094976 : CollatzResearch.WordTrace tailWord_1094976 prefixEnd_1094976 562248993137613135064303 := by
  unfold tailWord_1094976
  simp only [CollatzResearch.WordTrace]
  refine ⟨19968527840548216928760391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26624703787397622571680521 19968527840548216928760391)
  ·
    refine ⟨29952791760822325393140587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19968527840548216928760391 29952791760822325393140587)
    ·
      refine ⟨44929187641233488089710881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29952791760822325393140587 44929187641233488089710881)
      ·
        refine ⟨33696890730925116067283161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44929187641233488089710881 33696890730925116067283161)
        ·
          refine ⟨25272668048193837050462371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33696890730925116067283161 25272668048193837050462371)
          ·
            refine ⟨37909002072290755575693557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25272668048193837050462371 37909002072290755575693557)
            ·
              refine ⟨3553968944277258335221271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37909002072290755575693557 3553968944277258335221271)
              ·
                refine ⟨5330953416415887502831907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553968944277258335221271 5330953416415887502831907)
                ·
                  refine ⟨7996430124623831254247861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330953416415887502831907 7996430124623831254247861)
                  ·
                    refine ⟨749665324183484180085737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7996430124623831254247861 749665324183484180085737)
                    ·
                      refine ⟨562248993137613135064303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749665324183484180085737 562248993137613135064303)
                      ·
                        rfl

theorem cell23_1094976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_1094976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1094976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1094976 prefixEnd_1094976 := by exact prefixLift 1094976
  have htrace : WordTrace (prefixWord ++ tailWord_1094976) baseStart_1094976 baseEnd_1094976 := by
    simpa [prefixWord, tailWord_1094976, baseEnd_1094976] using wordTrace_append hprefix tailTrace_1094976
  have hstable : (prefixWord ++ tailWord_1094976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094976).length < 2 ^ (prefixWord ++ tailWord_1094976).sum := by decide
  have hdescent : baseEnd_1094976 < baseStart_1094976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095023 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 3, 2, 2]
def baseStart_1095023 : Nat := 118140960795 + 1095023 * 2 ^ 59
def prefixEnd_1095023 : Nat := 4983230072969 + 3 ^ 40 * 1095023 * 2
def baseEnd_1095023 : Nat := 562273126728374451176587

theorem tailTrace_1095023 : CollatzResearch.WordTrace tailWord_1095023 prefixEnd_1095023 562273126728374451176587 := by
  unfold tailWord_1095023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39938769911926160884481723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26625846607950773922987815 39938769911926160884481723)
  ·
    refine ⟨59908154867889241326722585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39938769911926160884481723 59908154867889241326722585)
    ·
      refine ⟨44931116150916930995041939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59908154867889241326722585 44931116150916930995041939)
      ·
        refine ⟨67396674226375396492562909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44931116150916930995041939 67396674226375396492562909)
        ·
          refine ⟨25273752834890773684711091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67396674226375396492562909 25273752834890773684711091)
          ·
            refine ⟨37910629252336160527066637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25273752834890773684711091 37910629252336160527066637)
            ·
              refine ⟨14216485969626060197649989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37910629252336160527066637 14216485969626060197649989)
              ·
                refine ⟨2665591119304886287059373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14216485969626060197649989 2665591119304886287059373)
                ·
                  refine ⟨999596669739332357647265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2665591119304886287059373 999596669739332357647265)
                  ·
                    refine ⟨749697502304499268235449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999596669739332357647265 749697502304499268235449)
                    ·
                      refine ⟨562273126728374451176587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749697502304499268235449 562273126728374451176587)
                      ·
                        rfl

theorem cell23_1095023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2, 2].length) (baseStart_1095023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095023 prefixEnd_1095023 := by exact prefixLift 1095023
  have htrace : WordTrace (prefixWord ++ tailWord_1095023) baseStart_1095023 baseEnd_1095023 := by
    simpa [prefixWord, tailWord_1095023, baseEnd_1095023] using wordTrace_append hprefix tailTrace_1095023
  have hstable : (prefixWord ++ tailWord_1095023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095023).length < 2 ^ (prefixWord ++ tailWord_1095023).sum := by decide
  have hdescent : baseEnd_1095023 < baseStart_1095023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095043 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 3]
def baseStart_1095043 : Nat := 118140960795 + 1095043 * 2 ^ 59
def prefixEnd_1095043 : Nat := 4983230072969 + 3 ^ 40 * 1095043 * 2
def baseEnd_1095043 : Nat := 562283396341464372926495

theorem tailTrace_1095043 : CollatzResearch.WordTrace tailWord_1095043 prefixEnd_1095043 562283396341464372926495 := by
  unfold tailWord_1095043
  simp only [CollatzResearch.WordTrace]
  refine ⟨39939499371853704300209783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26626332914569136200139855 39939499371853704300209783)
  ·
    refine ⟨59909249057780556450314675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39939499371853704300209783 59909249057780556450314675)
    ·
      refine ⟨89863873586670834675472013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59909249057780556450314675 89863873586670834675472013)
      ·
        refine ⟨33698952595001563003302005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89863873586670834675472013 33698952595001563003302005)
        ·
          refine ⟨3159276805781396531559563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33698952595001563003302005 3159276805781396531559563)
          ·
            refine ⟨4738915208672094797339345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159276805781396531559563 4738915208672094797339345)
            ·
              refine ⟨3554186406504071098004509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738915208672094797339345 3554186406504071098004509)
              ·
                refine ⟨1332819902439026661751691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3554186406504071098004509 1332819902439026661751691)
                ·
                  refine ⟨1999229853658539992627537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332819902439026661751691 1999229853658539992627537)
                  ·
                    refine ⟨1499422390243904994470653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999229853658539992627537 1499422390243904994470653)
                    ·
                      refine ⟨562283396341464372926495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1499422390243904994470653 562283396341464372926495)
                      ·
                        rfl

theorem cell23_1095043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_1095043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095043 prefixEnd_1095043 := by exact prefixLift 1095043
  have htrace : WordTrace (prefixWord ++ tailWord_1095043) baseStart_1095043 baseEnd_1095043 := by
    simpa [prefixWord, tailWord_1095043, baseEnd_1095043] using wordTrace_append hprefix tailTrace_1095043
  have hstable : (prefixWord ++ tailWord_1095043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095043).length < 2 ^ (prefixWord ++ tailWord_1095043).sum := by decide
  have hdescent : baseEnd_1095043 < baseStart_1095043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095130 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_1095130 : Nat := 118140960795 + 1095130 * 2 ^ 59
def prefixEnd_1095130 : Nat := 4983230072969 + 3 ^ 40 * 1095130 * 2
def baseEnd_1095130 : Nat := 562328069158405532538595

theorem tailTrace_1095130 : CollatzResearch.WordTrace tailWord_1095130 prefixEnd_1095130 562328069158405532538595 := by
  unfold tailWord_1095130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985668130634629539656711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26628448348359012105751229 9985668130634629539656711)
  ·
    refine ⟨14978502195951944309485067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9985668130634629539656711 14978502195951944309485067)
    ·
      refine ⟨22467753293927916464227601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14978502195951944309485067 22467753293927916464227601)
      ·
        refine ⟨16850814970445937348170701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22467753293927916464227601 16850814970445937348170701)
        ·
          refine ⟨6319055613917226505564013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16850814970445937348170701 6319055613917226505564013)
          ·
            refine ⟨2369645855218959939586505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6319055613917226505564013 2369645855218959939586505)
            ·
              refine ⟨1777234391414219954689879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369645855218959939586505 1777234391414219954689879)
              ·
                refine ⟨2665851587121329932034819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777234391414219954689879 2665851587121329932034819)
                ·
                  refine ⟨3998777380681994898052229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665851587121329932034819 3998777380681994898052229)
                  ·
                    refine ⟨749770758877874043384793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998777380681994898052229 749770758877874043384793)
                    ·
                      refine ⟨562328069158405532538595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749770758877874043384793 562328069158405532538595)
                      ·
                        rfl

theorem cell23_1095130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_1095130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095130 prefixEnd_1095130 := by exact prefixLift 1095130
  have htrace : WordTrace (prefixWord ++ tailWord_1095130) baseStart_1095130 baseEnd_1095130 := by
    simpa [prefixWord, tailWord_1095130, baseEnd_1095130] using wordTrace_append hprefix tailTrace_1095130
  have hstable : (prefixWord ++ tailWord_1095130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095130).length < 2 ^ (prefixWord ++ tailWord_1095130).sum := by decide
  have hdescent : baseEnd_1095130 < baseStart_1095130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095153 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 5]
def baseStart_1095153 : Nat := 118140960795 + 1095153 * 2 ^ 59
def prefixEnd_1095153 : Nat := 4983230072969 + 3 ^ 40 * 1095153 * 2
def baseEnd_1095153 : Nat := 62482208801495438061221

theorem tailTrace_1095153 : CollatzResearch.WordTrace tailWord_1095153 prefixEnd_1095153 62482208801495438061221 := by
  unfold tailWord_1095153
  simp only [CollatzResearch.WordTrace]
  refine ⟨39943511401455193086714113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26629007600970128724476075 39943511401455193086714113)
  ·
    refine ⟨29957633551091394815035585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39943511401455193086714113 29957633551091394815035585)
    ·
      refine ⟨22468225163318546111276689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29957633551091394815035585 22468225163318546111276689)
      ·
        refine ⟨16851168872488909583457517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22468225163318546111276689 16851168872488909583457517)
        ·
          refine ⟨6319188327183341093796569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16851168872488909583457517 6319188327183341093796569)
          ·
            refine ⟨4739391245387505820347427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319188327183341093796569 4739391245387505820347427)
            ·
              refine ⟨7109086868081258730521141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739391245387505820347427 7109086868081258730521141)
              ·
                refine ⟨666476893882618005986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7109086868081258730521141 666476893882618005986357)
                ·
                  refine ⟨62482208801495438061221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666476893882618005986357 62482208801495438061221)
                  ·
                    rfl

theorem cell23_1095153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 5].length) (baseStart_1095153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095153 prefixEnd_1095153 := by exact prefixLift 1095153
  have htrace : WordTrace (prefixWord ++ tailWord_1095153) baseStart_1095153 baseEnd_1095153 := by
    simpa [prefixWord, tailWord_1095153, baseEnd_1095153] using wordTrace_append hprefix tailTrace_1095153
  have hstable : (prefixWord ++ tailWord_1095153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095153).length < 2 ^ (prefixWord ++ tailWord_1095153).sum := by decide
  have hdescent : baseEnd_1095153 < baseStart_1095153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095170 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1095170 : Nat := 118140960795 + 1095170 * 2 ^ 59
def prefixEnd_1095170 : Nat := 4983230072969 + 3 ^ 40 * 1095170 * 2
def baseEnd_1095170 : Nat := 62483178709398375115379

theorem tailTrace_1095170 : CollatzResearch.WordTrace tailWord_1095170 prefixEnd_1095170 62483178709398375115379 := by
  unfold tailWord_1095170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986032860598401247520741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26629420961595736660055309 9986032860598401247520741)
  ·
    refine ⟨1872381161362200233910139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9986032860598401247520741 1872381161362200233910139)
    ·
      refine ⟨2808571742043300350865209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872381161362200233910139 2808571742043300350865209)
      ·
        refine ⟨2106428806532475263148907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2808571742043300350865209 2106428806532475263148907)
        ·
          refine ⟨3159643209798712894723361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106428806532475263148907 3159643209798712894723361)
          ·
            refine ⟨2369732407349034671042521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159643209798712894723361 2369732407349034671042521)
            ·
              refine ⟨1777299305511776003281891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369732407349034671042521 1777299305511776003281891)
              ·
                refine ⟨2665948958267664004922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777299305511776003281891 2665948958267664004922837)
                ·
                  refine ⟨62483178709398375115379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2665948958267664004922837 62483178709398375115379)
                  ·
                    rfl

theorem cell23_1095170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1095170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095170 prefixEnd_1095170 := by exact prefixLift 1095170
  have htrace : WordTrace (prefixWord ++ tailWord_1095170) baseStart_1095170 baseEnd_1095170 := by
    simpa [prefixWord, tailWord_1095170, baseEnd_1095170] using wordTrace_append hprefix tailTrace_1095170
  have hstable : (prefixWord ++ tailWord_1095170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095170).length < 2 ^ (prefixWord ++ tailWord_1095170).sum := by decide
  have hdescent : baseEnd_1095170 < baseStart_1095170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095176 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1095176 : Nat := 118140960795 + 1095176 * 2 ^ 59
def prefixEnd_1095176 : Nat := 4983230072969 + 3 ^ 40 * 1095176 * 2
def baseEnd_1095176 : Nat := 562351689268512352563383

theorem tailTrace_1095176 : CollatzResearch.WordTrace tailWord_1095176 prefixEnd_1095176 562351689268512352563383 := by
  unfold tailWord_1095176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19972175140185934007400691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26629566853581245343200921 19972175140185934007400691)
  ·
    refine ⟨29958262710278901011101037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19972175140185934007400691 29958262710278901011101037)
    ·
      refine ⟨11234348516354587879162889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29958262710278901011101037 11234348516354587879162889)
      ·
        refine ⟨8425761387265940909372167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11234348516354587879162889 8425761387265940909372167)
        ·
          refine ⟨12638642080898911364058251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425761387265940909372167 12638642080898911364058251)
          ·
            refine ⟨18957963121348367046087377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12638642080898911364058251 18957963121348367046087377)
            ·
              refine ⟨14218472341011275284565533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18957963121348367046087377 14218472341011275284565533)
              ·
                refine ⟨5331927127879228231712075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14218472341011275284565533 5331927127879228231712075)
                ·
                  refine ⟨7997890691818842347568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331927127879228231712075 7997890691818842347568113)
                  ·
                    refine ⟨5998418018864131760676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7997890691818842347568113 5998418018864131760676085)
                    ·
                      refine ⟨562351689268512352563383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5998418018864131760676085 562351689268512352563383)
                      ·
                        rfl

theorem cell23_1095176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1095176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095176 prefixEnd_1095176 := by exact prefixLift 1095176
  have htrace : WordTrace (prefixWord ++ tailWord_1095176) baseStart_1095176 baseEnd_1095176 := by
    simpa [prefixWord, tailWord_1095176, baseEnd_1095176] using wordTrace_append hprefix tailTrace_1095176
  have hstable : (prefixWord ++ tailWord_1095176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095176).length < 2 ^ (prefixWord ++ tailWord_1095176).sum := by decide
  have hdescent : baseEnd_1095176 < baseStart_1095176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
