import V185TrunkScan23Chunk1389

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8232836 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_8232836 : Nat := 118140960795 + 8232836 * 2 ^ 59
def prefixEnd_8232836 : Nat := 4983230072969 + 3 ^ 40 * 8232836 * 2
def baseEnd_8232836 : Nat := 4227402017639056224987883

theorem tailTrace_8232836 : CollatzResearch.WordTrace tailWord_8232836 prefixEnd_8232836 4227402017639056224987883 := by
  unfold tailWord_8232836
  simp only [CollatzResearch.WordTrace]
  refine ⟨150138098800924351646019181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200184131734565802194692241 150138098800924351646019181)
  ·
    refine ⟨56301787050346631867257193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150138098800924351646019181 56301787050346631867257193)
    ·
      refine ⟨42226340287759973900442895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56301787050346631867257193 42226340287759973900442895)
      ·
        refine ⟨63339510431639960850664343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42226340287759973900442895 63339510431639960850664343)
        ·
          refine ⟨95009265647459941275996515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63339510431639960850664343 95009265647459941275996515)
          ·
            refine ⟨142513898471189911913994773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95009265647459941275996515 142513898471189911913994773)
            ·
              refine ⟨6680338990837027120968505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142513898471189911913994773 6680338990837027120968505)
              ·
                refine ⟨5010254243127770340726379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680338990837027120968505 5010254243127770340726379)
                ·
                  refine ⟨7515381364691655511089569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010254243127770340726379 7515381364691655511089569)
                  ·
                    refine ⟨5636536023518741633317177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515381364691655511089569 5636536023518741633317177)
                    ·
                      refine ⟨4227402017639056224987883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636536023518741633317177 4227402017639056224987883)
                      ·
                        rfl

theorem cell23_8232836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_8232836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232836 prefixEnd_8232836 := by exact prefixLift 8232836
  have htrace : WordTrace (prefixWord ++ tailWord_8232836) baseStart_8232836 baseEnd_8232836 := by
    simpa [prefixWord, tailWord_8232836, baseEnd_8232836] using wordTrace_append hprefix tailTrace_8232836
  have hstable : (prefixWord ++ tailWord_8232836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232836).length < 2 ^ (prefixWord ++ tailWord_8232836).sum := by decide
  have hdescent : baseEnd_8232836 < baseStart_8232836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232842 : List Nat := [3, 1, 2, 4, 3, 1, 1, 8]
def baseStart_8232842 : Nat := 118140960795 + 8232842 * 2 ^ 59
def prefixEnd_8232842 : Nat := 4983230072969 + 3 ^ 40 * 8232842 * 2
def baseEnd_8232842 : Nat := 156570559204554933389365

theorem tailTrace_8232842 : CollatzResearch.WordTrace tailWord_8232842 prefixEnd_8232842 156570559204554933389365 := by
  unfold tailWord_8232842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75069104109956741579189195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200184277626551310877837853 75069104109956741579189195)
  ·
    refine ⟨112603656164935112368783793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75069104109956741579189195 112603656164935112368783793)
    ·
      refine ⟨84452742123701334276587845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112603656164935112368783793 84452742123701334276587845)
      ·
        refine ⟨15834889148194000176860221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84452742123701334276587845 15834889148194000176860221)
        ·
          refine ⟨5938083430572750066322583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15834889148194000176860221 5938083430572750066322583)
          ·
            refine ⟨8907125145859125099483875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938083430572750066322583 8907125145859125099483875)
            ·
              refine ⟨13360687718788687649225813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907125145859125099483875 13360687718788687649225813)
              ·
                refine ⟨156570559204554933389365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13360687718788687649225813 156570559204554933389365)
                ·
                  rfl

theorem cell23_8232842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_8232842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232842 prefixEnd_8232842 := by exact prefixLift 8232842
  have htrace : WordTrace (prefixWord ++ tailWord_8232842) baseStart_8232842 baseEnd_8232842 := by
    simpa [prefixWord, tailWord_8232842, baseEnd_8232842] using wordTrace_append hprefix tailTrace_8232842
  have hstable : (prefixWord ++ tailWord_8232842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232842).length < 2 ^ (prefixWord ++ tailWord_8232842).sum := by decide
  have hdescent : baseEnd_8232842 < baseStart_8232842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232852 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_8232852 : Nat := 118140960795 + 8232852 * 2 ^ 59
def prefixEnd_8232852 : Nat := 4983230072969 + 3 ^ 40 * 8232852 * 2
def baseEnd_8232852 : Nat := 4227410233329528162387809

theorem tailTrace_8232852 : CollatzResearch.WordTrace tailWord_8232852 prefixEnd_8232852 4227410233329528162387809 := by
  unfold tailWord_8232852
  simp only [CollatzResearch.WordTrace]
  refine ⟨150138390584895369012310405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200184520779860492016413873 150138390584895369012310405)
  ·
    refine ⟨28150948234667881689808201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150138390584895369012310405 28150948234667881689808201)
    ·
      refine ⟨21113211176000911267356151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28150948234667881689808201 21113211176000911267356151)
      ·
        refine ⟨31669816764001366901034227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113211176000911267356151 31669816764001366901034227)
        ·
          refine ⟨47504725146002050351551341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31669816764001366901034227 47504725146002050351551341)
          ·
            refine ⟨17814271929750768881831753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47504725146002050351551341 17814271929750768881831753)
            ·
              refine ⟨13360703947313076661373815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17814271929750768881831753 13360703947313076661373815)
              ·
                refine ⟨20041055920969614992060723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360703947313076661373815 20041055920969614992060723)
                ·
                  refine ⟨30061583881454422488091085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20041055920969614992060723 30061583881454422488091085)
                  ·
                    refine ⟨11273093955545408433034157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30061583881454422488091085 11273093955545408433034157)
                    ·
                      refine ⟨4227410233329528162387809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11273093955545408433034157 4227410233329528162387809)
                      ·
                        rfl

theorem cell23_8232852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_8232852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232852 prefixEnd_8232852 := by exact prefixLift 8232852
  have htrace : WordTrace (prefixWord ++ tailWord_8232852) baseStart_8232852 baseEnd_8232852 := by
    simpa [prefixWord, tailWord_8232852, baseEnd_8232852] using wordTrace_append hprefix tailTrace_8232852
  have hstable : (prefixWord ++ tailWord_8232852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232852).length < 2 ^ (prefixWord ++ tailWord_8232852).sum := by decide
  have hdescent : baseEnd_8232852 < baseStart_8232852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232888 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_8232888 : Nat := 118140960795 + 8232888 * 2 ^ 59
def prefixEnd_8232888 : Nat := 4983230072969 + 3 ^ 40 * 8232888 * 2
def baseEnd_8232888 : Nat := 4227428718633090021537643

theorem tailTrace_8232888 : CollatzResearch.WordTrace tailWord_8232888 prefixEnd_8232888 4227428718633090021537643 := by
  unfold tailWord_8232888
  simp only [CollatzResearch.WordTrace]
  refine ⟨150139047098830158086465659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200185396131773544115287545 150139047098830158086465659)
  ·
    refine ⟨225208570648245237129698489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150139047098830158086465659 225208570648245237129698489)
    ·
      refine ⟨168906427986183927847273867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225208570648245237129698489 168906427986183927847273867)
      ·
        refine ⟨253359641979275891770910801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168906427986183927847273867 253359641979275891770910801)
        ·
          refine ⟨190019731484456918828183101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253359641979275891770910801 190019731484456918828183101)
          ·
            refine ⟨71257399306671344560568663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190019731484456918828183101 71257399306671344560568663)
            ·
              refine ⟨106886098960007016840852995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71257399306671344560568663 106886098960007016840852995)
              ·
                refine ⟨160329148440010525261279493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106886098960007016840852995 160329148440010525261279493)
                ·
                  refine ⟨30061715332501973486489905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160329148440010525261279493 30061715332501973486489905)
                  ·
                    refine ⟨22546286499376480114867429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30061715332501973486489905 22546286499376480114867429)
                    ·
                      refine ⟨4227428718633090021537643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22546286499376480114867429 4227428718633090021537643)
                      ·
                        rfl

theorem cell23_8232888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_8232888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232888 prefixEnd_8232888 := by exact prefixLift 8232888
  have htrace : WordTrace (prefixWord ++ tailWord_8232888) baseStart_8232888 baseEnd_8232888 := by
    simpa [prefixWord, tailWord_8232888, baseEnd_8232888] using wordTrace_append hprefix tailTrace_8232888
  have hstable : (prefixWord ++ tailWord_8232888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232888).length < 2 ^ (prefixWord ++ tailWord_8232888).sum := by decide
  have hdescent : baseEnd_8232888 < baseStart_8232888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232928 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_8232928 : Nat := 118140960795 + 8232928 * 2 ^ 59
def prefixEnd_8232928 : Nat := 4983230072969 + 3 ^ 40 * 8232928 * 2
def baseEnd_8232928 : Nat := 1409149752619756621679153

theorem tailTrace_8232928 : CollatzResearch.WordTrace tailWord_8232928 prefixEnd_8232928 1409149752619756621679153 := by
  unfold tailWord_8232928
  simp only [CollatzResearch.WordTrace]
  refine ⟨150139776558757701502193719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200186368745010268669591625 150139776558757701502193719)
  ·
    refine ⟨225209664838136552253290579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150139776558757701502193719 225209664838136552253290579)
    ·
      refine ⟨337814497257204828379935869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225209664838136552253290579 337814497257204828379935869)
      ·
        refine ⟨126680436471451810642475951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337814497257204828379935869 126680436471451810642475951)
        ·
          refine ⟨190020654707177715963713927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126680436471451810642475951 190020654707177715963713927)
          ·
            refine ⟨285030982060766573945570891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190020654707177715963713927 285030982060766573945570891)
            ·
              refine ⟨427546473091149860918356337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285030982060766573945570891 427546473091149860918356337)
              ·
                refine ⟨320659854818362395688767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427546473091149860918356337 320659854818362395688767253)
                ·
                  refine ⟨15030930694610737297910965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320659854818362395688767253 15030930694610737297910965)
                  ·
                    refine ⟨1409149752619756621679153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15030930694610737297910965 1409149752619756621679153)
                    ·
                      rfl

theorem cell23_8232928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_8232928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232928 prefixEnd_8232928 := by exact prefixLift 8232928
  have htrace : WordTrace (prefixWord ++ tailWord_8232928) baseStart_8232928 baseEnd_8232928 := by
    simpa [prefixWord, tailWord_8232928, baseEnd_8232928] using wordTrace_append hprefix tailTrace_8232928
  have hstable : (prefixWord ++ tailWord_8232928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232928).length < 2 ^ (prefixWord ++ tailWord_8232928).sum := by decide
  have hdescent : baseEnd_8232928 < baseStart_8232928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233009 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 1, 4]
def baseStart_8233009 : Nat := 118140960795 + 8233009 * 2 ^ 59
def prefixEnd_8233009 : Nat := 4983230072969 + 3 ^ 40 * 8233009 * 2
def baseEnd_8233009 : Nat := 1409163616597428016041529

theorem tailTrace_8233009 : CollatzResearch.WordTrace tailWord_8233009 prefixEnd_8233009 1409163616597428016041529 := by
  unfold tailWord_8233009
  simp only [CollatzResearch.WordTrace]
  refine ⟨300282507430221953838086081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200188338286814635892057387 300282507430221953838086081)
  ·
    refine ⟨225211880572666465378564561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300282507430221953838086081 225211880572666465378564561)
    ·
      refine ⟨168908910429499849033923421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225211880572666465378564561 168908910429499849033923421)
      ·
        refine ⟨63340841411062443387721283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168908910429499849033923421 63340841411062443387721283)
        ·
          refine ⟨95011262116593665081581925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63340841411062443387721283 95011262116593665081581925)
          ·
            refine ⟨17814611646861312202796611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95011262116593665081581925 17814611646861312202796611)
            ·
              refine ⟨26721917470291968304194917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17814611646861312202796611 26721917470291968304194917)
              ·
                refine ⟨5010359525679744057036547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26721917470291968304194917 5010359525679744057036547)
                ·
                  refine ⟨7515539288519616085554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010359525679744057036547 7515539288519616085554821)
                  ·
                    refine ⟨1409163616597428016041529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515539288519616085554821 1409163616597428016041529)
                    ·
                      rfl

theorem cell23_8233009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_8233009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233009 prefixEnd_8233009 := by exact prefixLift 8233009
  have htrace : WordTrace (prefixWord ++ tailWord_8233009) baseStart_8233009 baseEnd_8233009 := by
    simpa [prefixWord, tailWord_8233009, baseEnd_8233009] using wordTrace_append hprefix tailTrace_8233009
  have hstable : (prefixWord ++ tailWord_8233009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233009).length < 2 ^ (prefixWord ++ tailWord_8233009).sum := by decide
  have hdescent : baseEnd_8233009 < baseStart_8233009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233055 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_8233055 : Nat := 118140960795 + 8233055 * 2 ^ 59
def prefixEnd_8233055 : Nat := 4983230072969 + 3 ^ 40 * 8233055 * 2
def baseEnd_8233055 : Nat := 4227514469902390868149375

theorem tailTrace_8233055 : CollatzResearch.WordTrace tailWord_8233055 prefixEnd_8233055 4227514469902390868149375 := by
  unfold tailWord_8233055
  simp only [CollatzResearch.WordTrace]
  refine ⟨300284185188055303694260619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200189456792036869129507079 300284185188055303694260619)
  ·
    refine ⟨450426277782082955541390929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300284185188055303694260619 450426277782082955541390929)
    ·
      refine ⟨337819708336562216656043197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450426277782082955541390929 337819708336562216656043197)
      ·
        refine ⟨126682390626210831246016199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337819708336562216656043197 126682390626210831246016199)
        ·
          refine ⟨190023585939316246869024299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126682390626210831246016199 190023585939316246869024299)
          ·
            refine ⟨285035378908974370303536449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190023585939316246869024299 285035378908974370303536449)
            ·
              refine ⟨213776534181730777727652337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285035378908974370303536449 213776534181730777727652337)
              ·
                refine ⟨160332400636298083295739253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213776534181730777727652337 160332400636298083295739253)
                ·
                  refine ⟨15031162559652945308975555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160332400636298083295739253 15031162559652945308975555)
                  ·
                    refine ⟨22546743839479417963463333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15031162559652945308975555 22546743839479417963463333)
                    ·
                      refine ⟨4227514469902390868149375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22546743839479417963463333 4227514469902390868149375)
                      ·
                        rfl

theorem cell23_8233055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_8233055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233055 prefixEnd_8233055 := by exact prefixLift 8233055
  have htrace : WordTrace (prefixWord ++ tailWord_8233055) baseStart_8233055 baseEnd_8233055 := by
    simpa [prefixWord, tailWord_8233055, baseEnd_8233055] using wordTrace_append hprefix tailTrace_8233055
  have hstable : (prefixWord ++ tailWord_8233055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233055).length < 2 ^ (prefixWord ++ tailWord_8233055).sum := by decide
  have hdescent : baseEnd_8233055 < baseStart_8233055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233066 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_8233066 : Nat := 118140960795 + 8233066 * 2 ^ 59
def prefixEnd_8233066 : Nat := 4983230072969 + 3 ^ 40 * 8233066 * 2
def baseEnd_8233066 : Nat := 4227520118189590325111825

theorem tailTrace_8233066 : CollatzResearch.WordTrace tailWord_8233066 prefixEnd_8233066 4227520118189590325111825 := by
  unfold tailWord_8233066
  simp only [CollatzResearch.WordTrace]
  refine ⟨75071146597753863143227763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200189724260676968381940701 75071146597753863143227763)
  ·
    refine ⟨112606719896630794714841645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75071146597753863143227763 112606719896630794714841645)
    ·
      refine ⟨42227519961236548018065617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112606719896630794714841645 42227519961236548018065617)
      ·
        refine ⟨31670639970927411013549213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42227519961236548018065617 31670639970927411013549213)
        ·
          refine ⟨11876489989097779130080955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31670639970927411013549213 11876489989097779130080955)
          ·
            refine ⟨17814734983646668695121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11876489989097779130080955 17814734983646668695121433)
            ·
              refine ⟨13361051237735001521341075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17814734983646668695121433 13361051237735001521341075)
              ·
                refine ⟨20041576856602502282011613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361051237735001521341075 20041576856602502282011613)
                ·
                  refine ⟨7515591321225938355754355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20041576856602502282011613 7515591321225938355754355)
                  ·
                    refine ⟨11273386981838907533631533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7515591321225938355754355 11273386981838907533631533)
                    ·
                      refine ⟨4227520118189590325111825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11273386981838907533631533 4227520118189590325111825)
                      ·
                        rfl

theorem cell23_8233066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_8233066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233066 prefixEnd_8233066 := by exact prefixLift 8233066
  have htrace : WordTrace (prefixWord ++ tailWord_8233066) baseStart_8233066 baseEnd_8233066 := by
    simpa [prefixWord, tailWord_8233066, baseEnd_8233066] using wordTrace_append hprefix tailTrace_8233066
  have hstable : (prefixWord ++ tailWord_8233066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233066).length < 2 ^ (prefixWord ++ tailWord_8233066).sum := by decide
  have hdescent : baseEnd_8233066 < baseStart_8233066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233112 : List Nat := [2, 1, 2, 4, 3, 2, 9]
def baseStart_8233112 : Nat := 118140960795 + 8233112 * 2 ^ 59
def prefixEnd_8233112 : Nat := 4983230072969 + 3 ^ 40 * 8233112 * 2
def baseEnd_8233112 : Nat := 52191898003699964754773

theorem tailTrace_8233112 : CollatzResearch.WordTrace tailWord_8233112 prefixEnd_8233112 52191898003699964754773 := by
  unfold tailWord_8233112
  simp only [CollatzResearch.WordTrace]
  refine ⟨150143132074424401214542795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200190842765899201619390393 150143132074424401214542795)
  ·
    refine ⟨225214698111636601821814193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150143132074424401214542795 225214698111636601821814193)
    ·
      refine ⟨168911023583727451366360645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225214698111636601821814193 168911023583727451366360645)
      ·
        refine ⟨31670816921948897131192621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168911023583727451366360645 31670816921948897131192621)
        ·
          refine ⟨11876556345730836424197233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31670816921948897131192621 11876556345730836424197233)
          ·
            refine ⟨8907417259298127318147925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11876556345730836424197233 8907417259298127318147925)
            ·
              refine ⟨52191898003699964754773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8907417259298127318147925 52191898003699964754773)
              ·
                rfl

theorem cell23_8233112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 9].length) (baseStart_8233112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233112 prefixEnd_8233112 := by exact prefixLift 8233112
  have htrace : WordTrace (prefixWord ++ tailWord_8233112) baseStart_8233112 baseEnd_8233112 := by
    simpa [prefixWord, tailWord_8233112, baseEnd_8233112] using wordTrace_append hprefix tailTrace_8233112
  have hstable : (prefixWord ++ tailWord_8233112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233112).length < 2 ^ (prefixWord ++ tailWord_8233112).sum := by decide
  have hdescent : baseEnd_8233112 < baseStart_8233112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233125 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_8233125 : Nat := 118140960795 + 8233125 * 2 ^ 59
def prefixEnd_8233125 : Nat := 4983230072969 + 3 ^ 40 * 8233125 * 2
def baseEnd_8233125 : Nat := 1409183471182735198091351

theorem tailTrace_8233125 : CollatzResearch.WordTrace tailWord_8233125 prefixEnd_8233125 1409183471182735198091351 := by
  unfold tailWord_8233125
  simp only [CollatzResearch.WordTrace]
  refine ⟨300286738297801705649308829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200191158865201137099539219 300286738297801705649308829)
  ·
    refine ⟨112607526861675639618490811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300286738297801705649308829 112607526861675639618490811)
    ·
      refine ⟨168911290292513459427736217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112607526861675639618490811 168911290292513459427736217)
      ·
        refine ⟨126683467719385094570802163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168911290292513459427736217 126683467719385094570802163)
        ·
          refine ⟨190025201579077641856203245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126683467719385094570802163 190025201579077641856203245)
          ·
            refine ⟨71259450592154115696076217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190025201579077641856203245 71259450592154115696076217)
            ·
              refine ⟨53444587944115586772057163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71259450592154115696076217 53444587944115586772057163)
              ·
                refine ⟨80166881916173380158085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53444587944115586772057163 80166881916173380158085745)
                ·
                  refine ⟨60125161437130035118564309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80166881916173380158085745 60125161437130035118564309)
                  ·
                    refine ⟨1409183471182735198091351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60125161437130035118564309 1409183471182735198091351)
                    ·
                      rfl

theorem cell23_8233125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_8233125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233125 prefixEnd_8233125 := by exact prefixLift 8233125
  have htrace : WordTrace (prefixWord ++ tailWord_8233125) baseStart_8233125 baseEnd_8233125 := by
    simpa [prefixWord, tailWord_8233125, baseEnd_8233125] using wordTrace_append hprefix tailTrace_8233125
  have hstable : (prefixWord ++ tailWord_8233125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233125).length < 2 ^ (prefixWord ++ tailWord_8233125).sum := by decide
  have hdescent : baseEnd_8233125 < baseStart_8233125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233133 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_8233133 : Nat := 118140960795 + 8233133 * 2 ^ 59
def prefixEnd_8233133 : Nat := 4983230072969 + 3 ^ 40 * 8233133 * 2
def baseEnd_8233133 : Nat := 1409184840464480520991339

theorem tailTrace_8233133 : CollatzResearch.WordTrace tailWord_8233133 prefixEnd_8233133 1409184840464480520991339 := by
  unfold tailWord_8233133
  simp only [CollatzResearch.WordTrace]
  refine ⟨300287030081772723015600053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200191353387848482010400035 300287030081772723015600053)
  ·
    refine ⟨28151909070166192782712505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300287030081772723015600053 28151909070166192782712505)
    ·
      refine ⟨21113931802624644587034379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28151909070166192782712505 21113931802624644587034379)
      ·
        refine ⟨31670897703936966880551569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113931802624644587034379 31670897703936966880551569)
        ·
          refine ⟨23753173277952725160413677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31670897703936966880551569 23753173277952725160413677)
          ·
            refine ⟨8907439979232271935155129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23753173277952725160413677 8907439979232271935155129)
            ·
              refine ⟨6680579984424203951366347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907439979232271935155129 6680579984424203951366347)
              ·
                refine ⟨10020869976636305927049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680579984424203951366347 10020869976636305927049521)
                ·
                  refine ⟨7515652482477229445287141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020869976636305927049521 7515652482477229445287141)
                  ·
                    refine ⟨1409184840464480520991339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515652482477229445287141 1409184840464480520991339)
                    ·
                      rfl

theorem cell23_8233133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_8233133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233133 prefixEnd_8233133 := by exact prefixLift 8233133
  have htrace : WordTrace (prefixWord ++ tailWord_8233133) baseStart_8233133 baseEnd_8233133 := by
    simpa [prefixWord, tailWord_8233133, baseEnd_8233133] using wordTrace_append hprefix tailTrace_8233133
  have hstable : (prefixWord ++ tailWord_8233133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233133).length < 2 ^ (prefixWord ++ tailWord_8233133).sum := by decide
  have hdescent : baseEnd_8233133 < baseStart_8233133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233173 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8233173 : Nat := 118140960795 + 8233173 * 2 ^ 59
def prefixEnd_8233173 : Nat := 4983230072969 + 3 ^ 40 * 8233173 * 2
def baseEnd_8233173 : Nat := 4227575060619621406473833

theorem tailTrace_8233173 : CollatzResearch.WordTrace tailWord_8233173 prefixEnd_8233173 4227575060619621406473833 := by
  unfold tailWord_8233173
  simp only [CollatzResearch.WordTrace]
  refine ⟨300288489001627809847056173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200192326001085206564704115 300288489001627809847056173)
  ·
    refine ⟨112608183375610428692646065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300288489001627809847056173 112608183375610428692646065)
    ·
      refine ⟨84456137531707821519484549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112608183375610428692646065 84456137531707821519484549)
      ·
        refine ⟨15835525787195216534903353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84456137531707821519484549 15835525787195216534903353)
        ·
          refine ⟨11876644340396412401177515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15835525787195216534903353 11876644340396412401177515)
          ·
            refine ⟨17814966510594618601766273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11876644340396412401177515 17814966510594618601766273)
            ·
              refine ⟨13361224882945963951324705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17814966510594618601766273 13361224882945963951324705)
              ·
                refine ⟨10020918662209472963493529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13361224882945963951324705 10020918662209472963493529)
                ·
                  refine ⟨7515688996657104722620147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020918662209472963493529 7515688996657104722620147)
                  ·
                    refine ⟨11273533494985657083930221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7515688996657104722620147 11273533494985657083930221)
                    ·
                      refine ⟨4227575060619621406473833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11273533494985657083930221 4227575060619621406473833)
                      ·
                        rfl

theorem cell23_8233173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8233173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233173 prefixEnd_8233173 := by exact prefixLift 8233173
  have htrace : WordTrace (prefixWord ++ tailWord_8233173) baseStart_8233173 baseEnd_8233173 := by
    simpa [prefixWord, tailWord_8233173, baseEnd_8233173] using wordTrace_append hprefix tailTrace_8233173
  have hstable : (prefixWord ++ tailWord_8233173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233173).length < 2 ^ (prefixWord ++ tailWord_8233173).sum := by decide
  have hdescent : baseEnd_8233173 < baseStart_8233173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233174 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_8233174 : Nat := 118140960795 + 8233174 * 2 ^ 59
def prefixEnd_8233174 : Nat := 4983230072969 + 3 ^ 40 * 8233174 * 2
def baseEnd_8233174 : Nat := 4227575574100275902561329

theorem tailTrace_8233174 : CollatzResearch.WordTrace tailWord_8233174 prefixEnd_8233174 4227575574100275902561329 := by
  unfold tailWord_8233174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768032842164011688615161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200192350316416124678561717 18768032842164011688615161)
  ·
    refine ⟨14076024631623008766461371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18768032842164011688615161 14076024631623008766461371)
    ·
      refine ⟨21114036947434513149692057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14076024631623008766461371 21114036947434513149692057)
      ·
        refine ⟨15835527710575884862269043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21114036947434513149692057 15835527710575884862269043)
        ·
          refine ⟨23753291565863827293403565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835527710575884862269043 23753291565863827293403565)
          ·
            refine ⟨8907484337198935235026337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23753291565863827293403565 8907484337198935235026337)
            ·
              refine ⟨6680613252899201426269753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907484337198935235026337 6680613252899201426269753)
              ·
                refine ⟨5010459939674401069702315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680613252899201426269753 5010459939674401069702315)
                ·
                  refine ⟨7515689909511601604553473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010459939674401069702315 7515689909511601604553473)
                  ·
                    refine ⟨5636767432133701203415105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515689909511601604553473 5636767432133701203415105)
                    ·
                      refine ⟨4227575574100275902561329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636767432133701203415105 4227575574100275902561329)
                      ·
                        rfl

theorem cell23_8233174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_8233174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233174 prefixEnd_8233174 := by exact prefixLift 8233174
  have htrace : WordTrace (prefixWord ++ tailWord_8233174) baseStart_8233174 baseEnd_8233174 := by
    simpa [prefixWord, tailWord_8233174, baseEnd_8233174] using wordTrace_append hprefix tailTrace_8233174
  have hstable : (prefixWord ++ tailWord_8233174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233174).length < 2 ^ (prefixWord ++ tailWord_8233174).sum := by decide
  have hdescent : baseEnd_8233174 < baseStart_8233174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233175 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_8233175 : Nat := 118140960795 + 8233175 * 2 ^ 59
def prefixEnd_8233175 : Nat := 4983230072969 + 3 ^ 40 * 8233175 * 2
def baseEnd_8233175 : Nat := 4227576087580930398648823

theorem tailTrace_8233175 : CollatzResearch.WordTrace tailWord_8233175 prefixEnd_8233175 4227576087580930398648823 := by
  unfold tailWord_8233175
  simp only [CollatzResearch.WordTrace]
  refine ⟨300288561947620564188628979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200192374631747042792419319 300288561947620564188628979)
  ·
    refine ⟨450432842921430846282943469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300288561947620564188628979 450432842921430846282943469)
    ·
      refine ⟨168912316095536567356103801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450432842921430846282943469 168912316095536567356103801)
      ·
        refine ⟨126684237071652425517077851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168912316095536567356103801 126684237071652425517077851)
        ·
          refine ⟨190026355607478638275616777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126684237071652425517077851 190026355607478638275616777)
          ·
            refine ⟨142519766705608978706712583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190026355607478638275616777 142519766705608978706712583)
            ·
              refine ⟨213779650058413468060068875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142519766705608978706712583 213779650058413468060068875)
              ·
                refine ⟨320669475087620202090103313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213779650058413468060068875 320669475087620202090103313)
                ·
                  refine ⟨240502106315715151567577485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320669475087620202090103313 240502106315715151567577485)
                  ·
                    refine ⟨90188289868393181837841557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240502106315715151567577485 90188289868393181837841557)
                    ·
                      refine ⟨4227576087580930398648823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90188289868393181837841557 4227576087580930398648823)
                      ·
                        rfl

theorem cell23_8233175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_8233175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233175 prefixEnd_8233175 := by exact prefixLift 8233175
  have htrace : WordTrace (prefixWord ++ tailWord_8233175) baseStart_8233175 baseEnd_8233175 := by
    simpa [prefixWord, tailWord_8233175, baseEnd_8233175] using wordTrace_append hprefix tailTrace_8233175
  have hstable : (prefixWord ++ tailWord_8233175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233175).length < 2 ^ (prefixWord ++ tailWord_8233175).sum := by decide
  have hdescent : baseEnd_8233175 < baseStart_8233175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233192 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_8233192 : Nat := 118140960795 + 8233192 * 2 ^ 59
def prefixEnd_8233192 : Nat := 4983230072969 + 3 ^ 40 * 8233192 * 2
def baseEnd_8233192 : Nat := 4227584816752056832136245

theorem tailTrace_8233192 : CollatzResearch.WordTrace tailWord_8233192 prefixEnd_8233192 4227584816752056832136245 := by
  unfold tailWord_8233192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150144590994279488045998915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200192787992372650727998553 150144590994279488045998915)
  ·
    refine ⟨225216886491419232068998373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150144590994279488045998915 225216886491419232068998373)
    ·
      refine ⟨42228166217141106012937195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225216886491419232068998373 42228166217141106012937195)
      ·
        refine ⟨63342249325711659019405793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42228166217141106012937195 63342249325711659019405793)
        ·
          refine ⟨47506686994283744264554345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63342249325711659019405793 47506686994283744264554345)
          ·
            refine ⟨35630015245712808198415759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47506686994283744264554345 35630015245712808198415759)
            ·
              refine ⟨53445022868569212297623639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35630015245712808198415759 53445022868569212297623639)
              ·
                refine ⟨80167534302853818446435459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53445022868569212297623639 80167534302853818446435459)
                ·
                  refine ⟨120251301454280727669653189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80167534302853818446435459 120251301454280727669653189)
                  ·
                    refine ⟨22547119022677636438059973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120251301454280727669653189 22547119022677636438059973)
                    ·
                      refine ⟨4227584816752056832136245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22547119022677636438059973 4227584816752056832136245)
                      ·
                        rfl

theorem cell23_8233192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_8233192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233192 prefixEnd_8233192 := by exact prefixLift 8233192
  have htrace : WordTrace (prefixWord ++ tailWord_8233192) baseStart_8233192 baseEnd_8233192 := by
    simpa [prefixWord, tailWord_8233192, baseEnd_8233192] using wordTrace_append hprefix tailTrace_8233192
  have hstable : (prefixWord ++ tailWord_8233192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233192).length < 2 ^ (prefixWord ++ tailWord_8233192).sum := by decide
  have hdescent : baseEnd_8233192 < baseStart_8233192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233196 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_8233196 : Nat := 118140960795 + 8233196 * 2 ^ 59
def prefixEnd_8233196 : Nat := 4983230072969 + 3 ^ 40 * 8233196 * 2
def baseEnd_8233196 : Nat := 4227586870674674816486227

theorem tailTrace_8233196 : CollatzResearch.WordTrace tailWord_8233196 prefixEnd_8233196 4227586870674674816486227 := by
  unfold tailWord_8233196
  simp only [CollatzResearch.WordTrace]
  refine ⟨150144663940272242387571721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200192885253696323183428961 150144663940272242387571721)
  ·
    refine ⟨112608497955204181790678791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150144663940272242387571721 112608497955204181790678791)
    ·
      refine ⟨168912746932806272686018187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112608497955204181790678791 168912746932806272686018187)
      ·
        refine ⟨253369120399209409029027281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168912746932806272686018187 253369120399209409029027281)
        ·
          refine ⟨190026840299407056771770461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253369120399209409029027281 190026840299407056771770461)
          ·
            refine ⟨71260065112277646289413923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190026840299407056771770461 71260065112277646289413923)
            ·
              refine ⟨106890097668416469434120885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71260065112277646289413923 106890097668416469434120885)
              ·
                refine ⟨10020946656414044009448833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106890097668416469434120885 10020946656414044009448833)
                ·
                  refine ⟨7515709992310533007086625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020946656414044009448833 7515709992310533007086625)
                  ·
                    refine ⟨5636782494232899755314969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515709992310533007086625 5636782494232899755314969)
                    ·
                      refine ⟨4227586870674674816486227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636782494232899755314969 4227586870674674816486227)
                      ·
                        rfl

theorem cell23_8233196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_8233196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233196 prefixEnd_8233196 := by exact prefixLift 8233196
  have htrace : WordTrace (prefixWord ++ tailWord_8233196) baseStart_8233196 baseEnd_8233196 := by
    simpa [prefixWord, tailWord_8233196, baseEnd_8233196] using wordTrace_append hprefix tailTrace_8233196
  have hstable : (prefixWord ++ tailWord_8233196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233196).length < 2 ^ (prefixWord ++ tailWord_8233196).sum := by decide
  have hdescent : baseEnd_8233196 < baseStart_8233196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233202 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_8233202 : Nat := 118140960795 + 8233202 * 2 ^ 59
def prefixEnd_8233202 : Nat := 4983230072969 + 3 ^ 40 * 8233202 * 2
def baseEnd_8233202 : Nat := 469732216839844643667911

theorem tailTrace_8233202 : CollatzResearch.WordTrace tailWord_8233202 prefixEnd_8233202 469732216839844643667911 := by
  unfold tailWord_8233202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75072386679630686949965465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200193031145681831866574573 75072386679630686949965465)
  ·
    refine ⟨56304290009723015212474099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75072386679630686949965465 56304290009723015212474099)
    ·
      refine ⟨84456435014584522818711149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56304290009723015212474099 84456435014584522818711149)
      ·
        refine ⟨31671163130469196057016681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84456435014584522818711149 31671163130469196057016681)
        ·
          refine ⟨23753372347851897042762511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31671163130469196057016681 23753372347851897042762511)
          ·
            refine ⟨35630058521777845564143767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23753372347851897042762511 35630058521777845564143767)
            ·
              refine ⟨53445087782666768346215651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35630058521777845564143767 53445087782666768346215651)
              ·
                refine ⟨80167631674000152519323477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53445087782666768346215651 80167631674000152519323477)
                ·
                  refine ⟨469732216839844643667911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80167631674000152519323477 469732216839844643667911)
                  ·
                    rfl

theorem cell23_8233202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_8233202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233202 prefixEnd_8233202 := by exact prefixLift 8233202
  have htrace : WordTrace (prefixWord ++ tailWord_8233202) baseStart_8233202 baseEnd_8233202 := by
    simpa [prefixWord, tailWord_8233202, baseEnd_8233202] using wordTrace_append hprefix tailTrace_8233202
  have hstable : (prefixWord ++ tailWord_8233202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233202).length < 2 ^ (prefixWord ++ tailWord_8233202).sum := by decide
  have hdescent : baseEnd_8233202 < baseStart_8233202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233219 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 5]
def baseStart_8233219 : Nat := 118140960795 + 8233219 * 2 ^ 59
def prefixEnd_8233219 : Nat := 4983230072969 + 3 ^ 40 * 8233219 * 2
def baseEnd_8233219 : Nat := 469733186747747580722069

theorem tailTrace_8233219 : CollatzResearch.WordTrace tailWord_8233219 prefixEnd_8233219 469733186747747580722069 := by
  unfold tailWord_8233219
  simp only [CollatzResearch.WordTrace]
  refine ⟨300290166759461159703230711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200193444506307439802153807 300290166759461159703230711)
  ·
    refine ⟨450435250139191739554846067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300290166759461159703230711 450435250139191739554846067)
    ·
      refine ⟨675652875208787609332269101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450435250139191739554846067 675652875208787609332269101)
      ·
        refine ⟨253369828203295353499600913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675652875208787609332269101 253369828203295353499600913)
        ·
          refine ⟨190027371152471515124700685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253369828203295353499600913 190027371152471515124700685)
          ·
            refine ⟨71260264182176818171762757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190027371152471515124700685 71260264182176818171762757)
            ·
              refine ⟨13361299534158153407205517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71260264182176818171762757 13361299534158153407205517)
              ·
                refine ⟨5010487325309307527702069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13361299534158153407205517 5010487325309307527702069)
                ·
                  refine ⟨469733186747747580722069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5010487325309307527702069 469733186747747580722069)
                  ·
                    rfl

theorem cell23_8233219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 5].length) (baseStart_8233219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233219 prefixEnd_8233219 := by exact prefixLift 8233219
  have htrace : WordTrace (prefixWord ++ tailWord_8233219) baseStart_8233219 baseEnd_8233219 := by
    simpa [prefixWord, tailWord_8233219, baseEnd_8233219] using wordTrace_append hprefix tailTrace_8233219
  have hstable : (prefixWord ++ tailWord_8233219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233219).length < 2 ^ (prefixWord ++ tailWord_8233219).sum := by decide
  have hdescent : baseEnd_8233219 < baseStart_8233219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233269 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_8233269 : Nat := 118140960795 + 8233269 * 2 ^ 59
def prefixEnd_8233269 : Nat := 4983230072969 + 3 ^ 40 * 8233269 * 2
def baseEnd_8233269 : Nat := 4227624354762453030873391

theorem tailTrace_8233269 : CollatzResearch.WordTrace tailWord_8233269 prefixEnd_8233269 4227624354762453030873391 := by
  unfold tailWord_8233269
  simp only [CollatzResearch.WordTrace]
  refine ⟨300291990409280018242550861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200194660272853345495033907 300291990409280018242550861)
  ·
    refine ⟨112609496403480006840956573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300291990409280018242550861 112609496403480006840956573)
    ·
      refine ⟨42228561151305002565358715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112609496403480006840956573 42228561151305002565358715)
      ·
        refine ⟨63342841726957503848038073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42228561151305002565358715 63342841726957503848038073)
        ·
          refine ⟨47507131295218127886028555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63342841726957503848038073 47507131295218127886028555)
          ·
            refine ⟨71260696942827191829042833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47507131295218127886028555 71260696942827191829042833)
            ·
              refine ⟨53445522707120393871782125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71260696942827191829042833 53445522707120393871782125)
              ·
                refine ⟨20042071015170147701918297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53445522707120393871782125 20042071015170147701918297)
                ·
                  refine ⟨15031553261377610776438723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20042071015170147701918297 15031553261377610776438723)
                  ·
                    refine ⟨22547329892066416164658085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15031553261377610776438723 22547329892066416164658085)
                    ·
                      refine ⟨4227624354762453030873391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22547329892066416164658085 4227624354762453030873391)
                      ·
                        rfl

theorem cell23_8233269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_8233269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233269 prefixEnd_8233269 := by exact prefixLift 8233269
  have htrace : WordTrace (prefixWord ++ tailWord_8233269) baseStart_8233269 baseEnd_8233269 := by
    simpa [prefixWord, tailWord_8233269, baseEnd_8233269] using wordTrace_append hprefix tailTrace_8233269
  have hstable : (prefixWord ++ tailWord_8233269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233269).length < 2 ^ (prefixWord ++ tailWord_8233269).sum := by decide
  have hdescent : baseEnd_8233269 < baseStart_8233269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233292 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 8]
def baseStart_8233292 : Nat := 118140960795 + 8233292 * 2 ^ 59
def prefixEnd_8233292 : Nat := 4983230072969 + 3 ^ 40 * 8233292 * 2
def baseEnd_8233292 : Nat := 469737351646389604542865

theorem tailTrace_8233292 : CollatzResearch.WordTrace tailWord_8233292 prefixEnd_8233292 469737351646389604542865 := by
  unfold tailWord_8233292
  simp only [CollatzResearch.WordTrace]
  refine ⟨150146414644098346585319065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200195219525464462113758753 150146414644098346585319065)
  ·
    refine ⟨112609810983073759938989299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150146414644098346585319065 112609810983073759938989299)
    ·
      refine ⟨168914716474610639908483949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112609810983073759938989299 168914716474610639908483949)
      ·
        refine ⟨63343018677978989965681481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168914716474610639908483949 63343018677978989965681481)
        ·
          refine ⟨47507264008484242474261111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63343018677978989965681481 47507264008484242474261111)
          ·
            refine ⟨71260896012726363711391667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47507264008484242474261111 71260896012726363711391667)
            ·
              refine ⟨106891344019089545567087501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71260896012726363711391667 106891344019089545567087501)
              ·
                refine ⟨40084254007158579587657813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106891344019089545567087501 40084254007158579587657813)
                ·
                  refine ⟨469737351646389604542865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40084254007158579587657813 469737351646389604542865)
                  ·
                    rfl

theorem cell23_8233292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_8233292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233292 prefixEnd_8233292 := by exact prefixLift 8233292
  have htrace : WordTrace (prefixWord ++ tailWord_8233292) baseStart_8233292 baseEnd_8233292 := by
    simpa [prefixWord, tailWord_8233292, baseEnd_8233292] using wordTrace_append hprefix tailTrace_8233292
  have hstable : (prefixWord ++ tailWord_8233292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233292).length < 2 ^ (prefixWord ++ tailWord_8233292).sum := by decide
  have hdescent : baseEnd_8233292 < baseStart_8233292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233296 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_8233296 : Nat := 118140960795 + 8233296 * 2 ^ 59
def prefixEnd_8233296 : Nat := 4983230072969 + 3 ^ 40 * 8233296 * 2
def baseEnd_8233296 : Nat := 1409212739580041475078589

theorem tailTrace_8233296 : CollatzResearch.WordTrace tailWord_8233296 prefixEnd_8233296 1409212739580041475078589 := by
  unfold tailWord_8233296
  simp only [CollatzResearch.WordTrace]
  refine ⟨150146487590091100926891871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200195316786788134569189161 150146487590091100926891871)
  ·
    refine ⟨225219731385136651390337807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150146487590091100926891871 225219731385136651390337807)
    ·
      refine ⟨337829597077704977085506711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225219731385136651390337807 337829597077704977085506711)
      ·
        refine ⟨506744395616557465628260067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337829597077704977085506711 506744395616557465628260067)
        ·
          refine ⟨760116593424836198442390101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506744395616557465628260067 760116593424836198442390101)
          ·
            refine ⟨8907616329197299200496759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 760116593424836198442390101 8907616329197299200496759)
            ·
              refine ⟨13361424493795948800745139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907616329197299200496759 13361424493795948800745139)
              ·
                refine ⟨20042136740693923201117709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361424493795948800745139 20042136740693923201117709)
                ·
                  refine ⟨7515801277760221200419141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20042136740693923201117709 7515801277760221200419141)
                  ·
                    refine ⟨1409212739580041475078589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515801277760221200419141 1409212739580041475078589)
                    ·
                      rfl

theorem cell23_8233296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_8233296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233296 prefixEnd_8233296 := by exact prefixLift 8233296
  have htrace : WordTrace (prefixWord ++ tailWord_8233296) baseStart_8233296 baseEnd_8233296 := by
    simpa [prefixWord, tailWord_8233296, baseEnd_8233296] using wordTrace_append hprefix tailTrace_8233296
  have hstable : (prefixWord ++ tailWord_8233296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233296).length < 2 ^ (prefixWord ++ tailWord_8233296).sum := by decide
  have hdescent : baseEnd_8233296 < baseStart_8233296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233347 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 1, 4]
def baseStart_8233347 : Nat := 118140960795 + 8233347 * 2 ^ 59
def prefixEnd_8233347 : Nat := 4983230072969 + 3 ^ 40 * 8233347 * 2
def baseEnd_8233347 : Nat := 1409221468751167908566011

theorem tailTrace_8233347 : CollatzResearch.WordTrace tailWord_8233347 prefixEnd_8233347 1409221468751167908566011 := by
  unfold tailWord_8233347
  simp only [CollatzResearch.WordTrace]
  refine ⟨300294835302997437563890295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200196556868664958375926863 300294835302997437563890295)
  ·
    refine ⟨450442252954496156345835443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300294835302997437563890295 450442252954496156345835443)
    ·
      refine ⟨675663379431744234518753165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450442252954496156345835443 675663379431744234518753165)
      ·
        refine ⟨253373767286904087944532437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675663379431744234518753165 253373767286904087944532437)
        ·
          refine ⟨5938447670786814561199979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253373767286904087944532437 5938447670786814561199979)
          ·
            refine ⟨8907671506180221841799969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938447670786814561199979 8907671506180221841799969)
            ·
              refine ⟨6680753629635166381349977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907671506180221841799969 6680753629635166381349977)
              ·
                refine ⟨5010565222226374786012483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680753629635166381349977 5010565222226374786012483)
                ·
                  refine ⟨7515847833339562179018725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010565222226374786012483 7515847833339562179018725)
                  ·
                    refine ⟨1409221468751167908566011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515847833339562179018725 1409221468751167908566011)
                    ·
                      rfl

theorem cell23_8233347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 4].length) (baseStart_8233347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233347 prefixEnd_8233347 := by exact prefixLift 8233347
  have htrace : WordTrace (prefixWord ++ tailWord_8233347) baseStart_8233347 baseEnd_8233347 := by
    simpa [prefixWord, tailWord_8233347, baseEnd_8233347] using wordTrace_append hprefix tailTrace_8233347
  have hstable : (prefixWord ++ tailWord_8233347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233347).length < 2 ^ (prefixWord ++ tailWord_8233347).sum := by decide
  have hdescent : baseEnd_8233347 < baseStart_8233347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233369 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_8233369 : Nat := 118140960795 + 8233369 * 2 ^ 59
def prefixEnd_8233369 : Nat := 4983230072969 + 3 ^ 40 * 8233369 * 2
def baseEnd_8233369 : Nat := 1409225234275967546540977

theorem tailTrace_8233369 : CollatzResearch.WordTrace tailWord_8233369 prefixEnd_8233369 1409225234275967546540977 := by
  unfold tailWord_8233369
  simp only [CollatzResearch.WordTrace]
  refine ⟨300295637708917735321191161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200197091805945156880794107 300295637708917735321191161)
  ·
    refine ⟨225221728281688301490893371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300295637708917735321191161 225221728281688301490893371)
    ·
      refine ⟨337832592422532452236340057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225221728281688301490893371 337832592422532452236340057)
      ·
        refine ⟨253374444316899339177255043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337832592422532452236340057 253374444316899339177255043)
        ·
          refine ⟨380061666475349008765882565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253374444316899339177255043 380061666475349008765882565)
          ·
            refine ⟨71261562464127939143602981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380061666475349008765882565 71261562464127939143602981)
            ·
              refine ⟨13361542962023988589425559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71261562464127939143602981 13361542962023988589425559)
              ·
                refine ⟨20042314443035982884138339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361542962023988589425559 20042314443035982884138339)
                ·
                  refine ⟨30063471664553974326207509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20042314443035982884138339 30063471664553974326207509)
                  ·
                    refine ⟨1409225234275967546540977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30063471664553974326207509 1409225234275967546540977)
                    ·
                      rfl

theorem cell23_8233369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_8233369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233369 prefixEnd_8233369 := by exact prefixLift 8233369
  have htrace : WordTrace (prefixWord ++ tailWord_8233369) baseStart_8233369 baseEnd_8233369 := by
    simpa [prefixWord, tailWord_8233369, baseEnd_8233369] using wordTrace_append hprefix tailTrace_8233369
  have hstable : (prefixWord ++ tailWord_8233369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233369).length < 2 ^ (prefixWord ++ tailWord_8233369).sum := by decide
  have hdescent : baseEnd_8233369 < baseStart_8233369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233392 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_8233392 : Nat := 118140960795 + 8233392 * 2 ^ 59
def prefixEnd_8233392 : Nat := 4983230072969 + 3 ^ 40 * 8233392 * 2
def baseEnd_8233392 : Nat := 4227687512882956049635325

theorem tailTrace_8233392 : CollatzResearch.WordTrace tailWord_8233392 prefixEnd_8233392 4227687512882956049635325 := by
  unfold tailWord_8233392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150148238293917205124639215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200197651058556273499518953 150148238293917205124639215)
  ·
    refine ⟨225222357440875807686958823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150148238293917205124639215 225222357440875807686958823)
    ·
      refine ⟨337833536161313711530438235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225222357440875807686958823 337833536161313711530438235)
      ·
        refine ⟨506750304241970567295657353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337833536161313711530438235 506750304241970567295657353)
        ·
          refine ⟨380062728181477925471743015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506750304241970567295657353 380062728181477925471743015)
          ·
            refine ⟨570094092272216888207614523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380062728181477925471743015 570094092272216888207614523)
            ·
              refine ⟨855141138408325332311421785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570094092272216888207614523 855141138408325332311421785)
              ·
                refine ⟨641355853806243999233566339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855141138408325332311421785 641355853806243999233566339)
                ·
                  refine ⟨962033780709365998850349509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641355853806243999233566339 962033780709365998850349509)
                  ·
                    refine ⟨180381333883006124784440533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962033780709365998850349509 180381333883006124784440533)
                    ·
                      refine ⟨4227687512882956049635325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180381333883006124784440533 4227687512882956049635325)
                      ·
                        rfl

theorem cell23_8233392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_8233392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233392 prefixEnd_8233392 := by exact prefixLift 8233392
  have htrace : WordTrace (prefixWord ++ tailWord_8233392) baseStart_8233392 baseEnd_8233392 := by
    simpa [prefixWord, tailWord_8233392, baseEnd_8233392] using wordTrace_append hprefix tailTrace_8233392
  have hstable : (prefixWord ++ tailWord_8233392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233392).length < 2 ^ (prefixWord ++ tailWord_8233392).sum := by decide
  have hdescent : baseEnd_8233392 < baseStart_8233392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233393 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_8233393 : Nat := 118140960795 + 8233393 * 2 ^ 59
def prefixEnd_8233393 : Nat := 4983230072969 + 3 ^ 40 * 8233393 * 2
def baseEnd_8233393 : Nat := 4227688026363610545722821

theorem tailTrace_8233393 : CollatzResearch.WordTrace tailWord_8233393 prefixEnd_8233393 4227688026363610545722821 := by
  unfold tailWord_8233393
  simp only [CollatzResearch.WordTrace]
  refine ⟨300296513060830787420064833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200197675373887191613376555 300296513060830787420064833)
  ·
    refine ⟨225222384795623090565048625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300296513060830787420064833 225222384795623090565048625)
    ·
      refine ⟨168916788596717317923786469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225222384795623090565048625 168916788596717317923786469)
      ·
        refine ⟨31671897861884497110709963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168916788596717317923786469 31671897861884497110709963)
        ·
          refine ⟨47507846792826745666064945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31671897861884497110709963 47507846792826745666064945)
          ·
            refine ⟨35630885094620059249548709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47507846792826745666064945 35630885094620059249548709)
            ·
              refine ⟨6680790955241261109290383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35630885094620059249548709 6680790955241261109290383)
              ·
                refine ⟨10021186432861891663935575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680790955241261109290383 10021186432861891663935575)
                ·
                  refine ⟨15031779649292837495903363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021186432861891663935575 15031779649292837495903363)
                  ·
                    refine ⟨22547669473939256243855045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15031779649292837495903363 22547669473939256243855045)
                    ·
                      refine ⟨4227688026363610545722821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22547669473939256243855045 4227688026363610545722821)
                      ·
                        rfl

theorem cell23_8233393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_8233393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233393 prefixEnd_8233393 := by exact prefixLift 8233393
  have htrace : WordTrace (prefixWord ++ tailWord_8233393) baseStart_8233393 baseEnd_8233393 := by
    simpa [prefixWord, tailWord_8233393, baseEnd_8233393] using wordTrace_append hprefix tailTrace_8233393
  have hstable : (prefixWord ++ tailWord_8233393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233393).length < 2 ^ (prefixWord ++ tailWord_8233393).sum := by decide
  have hdescent : baseEnd_8233393 < baseStart_8233393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233420 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_8233420 : Nat := 118140960795 + 8233420 * 2 ^ 59
def prefixEnd_8233420 : Nat := 4983230072969 + 3 ^ 40 * 8233420 * 2
def baseEnd_8233420 : Nat := 1409233963447093980028399

theorem tailTrace_8233420 : CollatzResearch.WordTrace tailWord_8233420 prefixEnd_8233420 1409233963447093980028399 := by
  unfold tailWord_8233420
  simp only [CollatzResearch.WordTrace]
  refine ⟨150148748915866485515648857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200198331887821980687531809 150148748915866485515648857)
  ·
    refine ⟨112611561686899864136736643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150148748915866485515648857 112611561686899864136736643)
    ·
      refine ⟨168917342530349796205104965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112611561686899864136736643 168917342530349796205104965)
      ·
        refine ⟨31672001724440586788457181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168917342530349796205104965 31672001724440586788457181)
        ·
          refine ⟨11877000646665220045671443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31672001724440586788457181 11877000646665220045671443)
          ·
            refine ⟨17815500969997830068507165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877000646665220045671443 17815500969997830068507165)
            ·
              refine ⟨6680812863749186275690187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17815500969997830068507165 6680812863749186275690187)
              ·
                refine ⟨10021219295623779413535281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680812863749186275690187 10021219295623779413535281)
                ·
                  refine ⟨7515914471717834560151461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021219295623779413535281 7515914471717834560151461)
                  ·
                    refine ⟨1409233963447093980028399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515914471717834560151461 1409233963447093980028399)
                    ·
                      rfl

theorem cell23_8233420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_8233420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233420 prefixEnd_8233420 := by exact prefixLift 8233420
  have htrace : WordTrace (prefixWord ++ tailWord_8233420) baseStart_8233420 baseEnd_8233420 := by
    simpa [prefixWord, tailWord_8233420, baseEnd_8233420] using wordTrace_append hprefix tailTrace_8233420
  have hstable : (prefixWord ++ tailWord_8233420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233420).length < 2 ^ (prefixWord ++ tailWord_8233420).sum := by decide
  have hdescent : baseEnd_8233420 < baseStart_8233420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233430 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_8233430 : Nat := 118140960795 + 8233430 * 2 ^ 59
def prefixEnd_8233430 : Nat := 4983230072969 + 3 ^ 40 * 8233430 * 2
def baseEnd_8233430 : Nat := 4227707025147826900960151

theorem tailTrace_8233430 : CollatzResearch.WordTrace tailWord_8233430 prefixEnd_8233430 4227707025147826900960151 := by
  unfold tailWord_8233430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768616410106046421197609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200198575041131161826107829 18768616410106046421197609)
  ·
    refine ⟨14076462307579534815898207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18768616410106046421197609 14076462307579534815898207)
    ·
      refine ⟨21114693461369302223847311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14076462307579534815898207 21114693461369302223847311)
      ·
        refine ⟨31672040192053953335770967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21114693461369302223847311 31672040192053953335770967)
        ·
          refine ⟨47508060288080930003656451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31672040192053953335770967 47508060288080930003656451)
          ·
            refine ⟨71262090432121395005484677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47508060288080930003656451 71262090432121395005484677)
            ·
              refine ⟨13361641956022761563528377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71262090432121395005484677 13361641956022761563528377)
              ·
                refine ⟨10021231467017071172646283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13361641956022761563528377 10021231467017071172646283)
                ·
                  refine ⟨15031847200525606758969425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021231467017071172646283 15031847200525606758969425)
                  ·
                    refine ⟨11273885400394205069227069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15031847200525606758969425 11273885400394205069227069)
                    ·
                      refine ⟨4227707025147826900960151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11273885400394205069227069 4227707025147826900960151)
                      ·
                        rfl

theorem cell23_8233430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_8233430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233430 prefixEnd_8233430 := by exact prefixLift 8233430
  have htrace : WordTrace (prefixWord ++ tailWord_8233430) baseStart_8233430 baseEnd_8233430 := by
    simpa [prefixWord, tailWord_8233430, baseEnd_8233430] using wordTrace_append hprefix tailTrace_8233430
  have hstable : (prefixWord ++ tailWord_8233430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233430).length < 2 ^ (prefixWord ++ tailWord_8233430).sum := by decide
  have hdescent : baseEnd_8233430 < baseStart_8233430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233439 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_8233439 : Nat := 118140960795 + 8233439 * 2 ^ 59
def prefixEnd_8233439 : Nat := 4983230072969 + 3 ^ 40 * 8233439 * 2
def baseEnd_8233439 : Nat := 4227711646473717365747609

theorem tailTrace_8233439 : CollatzResearch.WordTrace tailWord_8233439 prefixEnd_8233439 4227711646473717365747609 := by
  unfold tailWord_8233439
  simp only [CollatzResearch.WordTrace]
  refine ⟨300298190818664137276239371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200198793879109424850826247 300298190818664137276239371)
  ·
    refine ⟨450447286227996205914359057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300298190818664137276239371 450447286227996205914359057)
    ·
      refine ⟨337835464670997154435769293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450447286227996205914359057 337835464670997154435769293)
      ·
        refine ⟨126688299251623932913413485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337835464670997154435769293 126688299251623932913413485)
        ·
          refine ⟨47508112219358974842530057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126688299251623932913413485 47508112219358974842530057)
          ·
            refine ⟨35631084164519231131897543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47508112219358974842530057 35631084164519231131897543)
            ·
              refine ⟨53446626246778846697846315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35631084164519231131897543 53446626246778846697846315)
              ·
                refine ⟨80169939370168270046769473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53446626246778846697846315 80169939370168270046769473)
                ·
                  refine ⟨60127454527626202535077105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80169939370168270046769473 60127454527626202535077105)
                  ·
                    refine ⟨45095590895719651901307829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60127454527626202535077105 45095590895719651901307829)
                    ·
                      refine ⟨4227711646473717365747609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45095590895719651901307829 4227711646473717365747609)
                      ·
                        rfl

theorem cell23_8233439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_8233439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233439 prefixEnd_8233439 := by exact prefixLift 8233439
  have htrace : WordTrace (prefixWord ++ tailWord_8233439) baseStart_8233439 baseEnd_8233439 := by
    simpa [prefixWord, tailWord_8233439, baseEnd_8233439] using wordTrace_append hprefix tailTrace_8233439
  have hstable : (prefixWord ++ tailWord_8233439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233439).length < 2 ^ (prefixWord ++ tailWord_8233439).sum := by decide
  have hdescent : baseEnd_8233439 < baseStart_8233439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233461 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_8233461 : Nat := 118140960795 + 8233461 * 2 ^ 59
def prefixEnd_8233461 : Nat := 4983230072969 + 3 ^ 40 * 8233461 * 2
def baseEnd_8233461 : Nat := 4227722943048116279672509

theorem tailTrace_8233461 : CollatzResearch.WordTrace tailWord_8233461 prefixEnd_8233461 4227722943048116279672509 := by
  unfold tailWord_8233461
  simp only [CollatzResearch.WordTrace]
  refine ⟨300298993224584435033540237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200199328816389623355693491 300298993224584435033540237)
  ·
    refine ⟨112612122459219163137577589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300298993224584435033540237 112612122459219163137577589)
    ·
      refine ⟨10557386480551796544147899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112612122459219163137577589 10557386480551796544147899)
      ·
        refine ⟨15836079720827694816221849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557386480551796544147899 15836079720827694816221849)
        ·
          refine ⟨11877059790620771112166387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15836079720827694816221849 11877059790620771112166387)
          ·
            refine ⟨17815589685931156668249581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877059790620771112166387 17815589685931156668249581)
            ·
              refine ⟨6680846132224183750593593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17815589685931156668249581 6680846132224183750593593)
              ·
                refine ⟨5010634599168137812945195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680846132224183750593593 5010634599168137812945195)
                ·
                  refine ⟨7515951898752206719417793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010634599168137812945195 7515951898752206719417793)
                  ·
                    refine ⟨5636963924064155039563345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515951898752206719417793 5636963924064155039563345)
                    ·
                      refine ⟨4227722943048116279672509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636963924064155039563345 4227722943048116279672509)
                      ·
                        rfl

theorem cell23_8233461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_8233461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233461 prefixEnd_8233461 := by exact prefixLift 8233461
  have htrace : WordTrace (prefixWord ++ tailWord_8233461) baseStart_8233461 baseEnd_8233461 := by
    simpa [prefixWord, tailWord_8233461, baseEnd_8233461] using wordTrace_append hprefix tailTrace_8233461
  have hstable : (prefixWord ++ tailWord_8233461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233461).length < 2 ^ (prefixWord ++ tailWord_8233461).sum := by decide
  have hdescent : baseEnd_8233461 < baseStart_8233461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_8233466 : Nat := 118140960795 + 8233466 * 2 ^ 59
def prefixEnd_8233466 : Nat := 4983230072969 + 3 ^ 40 * 8233466 * 2
def baseEnd_8233466 : Nat := 4227725510451388760109985

theorem tailTrace_8233466 : CollatzResearch.WordTrace tailWord_8233466 prefixEnd_8233466 4227725510451388760109985 := by
  unfold tailWord_8233466
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074793897391580221868063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200199450393044213924981501 75074793897391580221868063)
  ·
    refine ⟨112612190846087370332802095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75074793897391580221868063 112612190846087370332802095)
    ·
      refine ⟨168918286269131055499203143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112612190846087370332802095 168918286269131055499203143)
      ·
        refine ⟨253377429403696583248804715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168918286269131055499203143 253377429403696583248804715)
        ·
          refine ⟨380066144105544874873207073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253377429403696583248804715 380066144105544874873207073)
          ·
            refine ⟨285049608079158656154905305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380066144105544874873207073 285049608079158656154905305)
            ·
              refine ⟨213787206059368992116178979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285049608079158656154905305 213787206059368992116178979)
              ·
                refine ⟨320680809089053488174268469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213787206059368992116178979 320680809089053488174268469)
                ·
                  refine ⟨30063825852098764516337669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320680809089053488174268469 30063825852098764516337669)
                  ·
                    refine ⟨5636967347268518346813313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30063825852098764516337669 5636967347268518346813313)
                    ·
                      refine ⟨4227725510451388760109985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636967347268518346813313 4227725510451388760109985)
                      ·
                        rfl

theorem cell23_8233466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_8233466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233466 prefixEnd_8233466 := by exact prefixLift 8233466
  have htrace : WordTrace (prefixWord ++ tailWord_8233466) baseStart_8233466 baseEnd_8233466 := by
    simpa [prefixWord, tailWord_8233466, baseEnd_8233466] using wordTrace_append hprefix tailTrace_8233466
  have hstable : (prefixWord ++ tailWord_8233466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233466).length < 2 ^ (prefixWord ++ tailWord_8233466).sum := by decide
  have hdescent : baseEnd_8233466 < baseStart_8233466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233469 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_8233469 : Nat := 118140960795 + 8233469 * 2 ^ 59
def prefixEnd_8233469 : Nat := 4983230072969 + 3 ^ 40 * 8233469 * 2
def baseEnd_8233469 : Nat := 4227727050893352248372471

theorem tailTrace_8233469 : CollatzResearch.WordTrace tailWord_8233469 prefixEnd_8233469 4227727050893352248372471 := by
  unfold tailWord_8233469
  simp only [CollatzResearch.WordTrace]
  refine ⟨300299285008555452399831461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200199523339036968266554307 300299285008555452399831461)
  ·
    refine ⟨56306115939104147324968399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300299285008555452399831461 56306115939104147324968399)
    ·
      refine ⟨84459173908656220987452599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56306115939104147324968399 84459173908656220987452599)
      ·
        refine ⟨126688760862984331481178899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84459173908656220987452599 126688760862984331481178899)
        ·
          refine ⟨190033141294476497221768349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126688760862984331481178899 190033141294476497221768349)
          ·
            refine ⟨71262427985428686458163131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190033141294476497221768349 71262427985428686458163131)
            ·
              refine ⟨106893641978143029687244697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71262427985428686458163131 106893641978143029687244697)
              ·
                refine ⟨80170231483607272265433523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106893641978143029687244697 80170231483607272265433523)
                ·
                  refine ⟨120255347225410908398150285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80170231483607272265433523 120255347225410908398150285)
                  ·
                    refine ⟨45095755209529090649306357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120255347225410908398150285 45095755209529090649306357)
                    ·
                      refine ⟨4227727050893352248372471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45095755209529090649306357 4227727050893352248372471)
                      ·
                        rfl

theorem cell23_8233469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_8233469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233469 prefixEnd_8233469 := by exact prefixLift 8233469
  have htrace : WordTrace (prefixWord ++ tailWord_8233469) baseStart_8233469 baseEnd_8233469 := by
    simpa [prefixWord, tailWord_8233469, baseEnd_8233469] using wordTrace_append hprefix tailTrace_8233469
  have hstable : (prefixWord ++ tailWord_8233469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233469).length < 2 ^ (prefixWord ++ tailWord_8233469).sum := by decide
  have hdescent : baseEnd_8233469 < baseStart_8233469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233486 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_8233486 : Nat := 118140960795 + 8233486 * 2 ^ 59
def prefixEnd_8233486 : Nat := 4983230072969 + 3 ^ 40 * 8233486 * 2
def baseEnd_8233486 : Nat := 4227735780064478681859893

theorem tailTrace_8233486 : CollatzResearch.WordTrace tailWord_8233486 prefixEnd_8233486 4227735780064478681859893 := by
  unfold tailWord_8233486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537488131186733037900039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200199936699662576202133541 37537488131186733037900039)
  ·
    refine ⟨56306232196780099556850059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37537488131186733037900039 56306232196780099556850059)
    ·
      refine ⟨84459348295170149335275089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56306232196780099556850059 84459348295170149335275089)
      ·
        refine ⟨63344511221377612001456317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84459348295170149335275089 63344511221377612001456317)
        ·
          refine ⟨23754191708016604500546119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63344511221377612001456317 23754191708016604500546119)
          ·
            refine ⟨35631287562024906750819179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23754191708016604500546119 35631287562024906750819179)
            ·
              refine ⟨53446931343037360126228769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35631287562024906750819179 53446931343037360126228769)
              ·
                refine ⟨40085198507278020094671577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53446931343037360126228769 40085198507278020094671577)
                ·
                  refine ⟨30063898880458515071003683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40085198507278020094671577 30063898880458515071003683)
                  ·
                    refine ⟨45095848320687772606505525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30063898880458515071003683 45095848320687772606505525)
                    ·
                      refine ⟨4227735780064478681859893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45095848320687772606505525 4227735780064478681859893)
                      ·
                        rfl

theorem cell23_8233486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_8233486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233486 prefixEnd_8233486 := by exact prefixLift 8233486
  have htrace : WordTrace (prefixWord ++ tailWord_8233486) baseStart_8233486 baseEnd_8233486 := by
    simpa [prefixWord, tailWord_8233486, baseEnd_8233486] using wordTrace_append hprefix tailTrace_8233486
  have hstable : (prefixWord ++ tailWord_8233486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233486).length < 2 ^ (prefixWord ++ tailWord_8233486).sum := by decide
  have hdescent : baseEnd_8233486 < baseStart_8233486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233533 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_8233533 : Nat := 118140960795 + 8233533 * 2 ^ 59
def prefixEnd_8233533 : Nat := 4983230072969 + 3 ^ 40 * 8233533 * 2
def baseEnd_8233533 : Nat := 4227759913655239997972177

theorem tailTrace_8233533 : CollatzResearch.WordTrace tailWord_8233533 prefixEnd_8233533 4227759913655239997972177 := by
  unfold tailWord_8233533
  simp only [CollatzResearch.WordTrace]
  refine ⟨300301619280323591330161253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200201079520215727553440835 300301619280323591330161253)
  ·
    refine ⟨56306553615060673374405235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300301619280323591330161253 56306553615060673374405235)
    ·
      refine ⟨84459830422591010061607853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56306553615060673374405235 84459830422591010061607853)
      ·
        refine ⟨31672436408471628773102945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84459830422591010061607853 31672436408471628773102945)
        ·
          refine ⟨23754327306353721579827209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31672436408471628773102945 23754327306353721579827209)
          ·
            refine ⟨17815745479765291184870407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23754327306353721579827209 17815745479765291184870407)
            ·
              refine ⟨26723618219647936777305611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17815745479765291184870407 26723618219647936777305611)
              ·
                refine ⟨40085427329471905165958417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26723618219647936777305611 40085427329471905165958417)
                ·
                  refine ⟨30064070497103928874468813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40085427329471905165958417 30064070497103928874468813)
                  ·
                    refine ⟨11274026436413973327925805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30064070497103928874468813 11274026436413973327925805)
                    ·
                      refine ⟨4227759913655239997972177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11274026436413973327925805 4227759913655239997972177)
                      ·
                        rfl

theorem cell23_8233533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_8233533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233533 prefixEnd_8233533 := by exact prefixLift 8233533
  have htrace : WordTrace (prefixWord ++ tailWord_8233533) baseStart_8233533 baseEnd_8233533 := by
    simpa [prefixWord, tailWord_8233533, baseEnd_8233533] using wordTrace_append hprefix tailTrace_8233533
  have hstable : (prefixWord ++ tailWord_8233533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233533).length < 2 ^ (prefixWord ++ tailWord_8233533).sum := by decide
  have hdescent : baseEnd_8233533 < baseStart_8233533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233553 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_8233553 : Nat := 118140960795 + 8233553 * 2 ^ 59
def prefixEnd_8233553 : Nat := 4983230072969 + 3 ^ 40 * 8233553 * 2
def baseEnd_8233553 : Nat := 1409256727756109973240695

theorem tailTrace_8233553 : CollatzResearch.WordTrace tailWord_8233553 prefixEnd_8233553 1409256727756109973240695 := by
  unfold tailWord_8233553
  simp only [CollatzResearch.WordTrace]
  refine ⟨300302348740251134745889313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200201565826834089830592875 300302348740251134745889313)
  ·
    refine ⟨225226761555188351059416985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300302348740251134745889313 225226761555188351059416985)
    ·
      refine ⟨168920071166391263294562739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225226761555188351059416985 168920071166391263294562739)
      ·
        refine ⟨253380106749586894941844109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168920071166391263294562739 253380106749586894941844109)
        ·
          refine ⟨95017540031095085603191541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253380106749586894941844109 95017540031095085603191541)
          ·
            refine ⟨8907894377915164275299207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95017540031095085603191541 8907894377915164275299207)
            ·
              refine ⟨13361841566872746412948811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907894377915164275299207 13361841566872746412948811)
              ·
                refine ⟨20042762350309119619423217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361841566872746412948811 20042762350309119619423217)
                ·
                  refine ⟨15032071762731839714567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20042762350309119619423217 15032071762731839714567413)
                  ·
                    refine ⟨1409256727756109973240695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15032071762731839714567413 1409256727756109973240695)
                    ·
                      rfl

theorem cell23_8233553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_8233553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233553 prefixEnd_8233553 := by exact prefixLift 8233553
  have htrace : WordTrace (prefixWord ++ tailWord_8233553) baseStart_8233553 baseEnd_8233553 := by
    simpa [prefixWord, tailWord_8233553, baseEnd_8233553] using wordTrace_append hprefix tailTrace_8233553
  have hstable : (prefixWord ++ tailWord_8233553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233553).length < 2 ^ (prefixWord ++ tailWord_8233553).sum := by decide
  have hdescent : baseEnd_8233553 < baseStart_8233553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233596 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 6]
def baseStart_8233596 : Nat := 118140960795 + 8233596 * 2 ^ 59
def prefixEnd_8233596 : Nat := 4983230072969 + 3 ^ 40 * 8233596 * 2
def baseEnd_8233596 : Nat := 469754695881830361276043

theorem tailTrace_8233596 : CollatzResearch.WordTrace tailWord_8233596 prefixEnd_8233596 469754695881830361276043 := by
  unfold tailWord_8233596
  simp only [CollatzResearch.WordTrace]
  refine ⟨150151958539547676544852321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200202611386063568726469761 150151958539547676544852321)
  ·
    refine ⟨112613968904660757408639241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150151958539547676544852321 112613968904660757408639241)
    ·
      refine ⟨84460476678495568056479431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112613968904660757408639241 84460476678495568056479431)
      ·
        refine ⟨126690715017743352084719147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84460476678495568056479431 126690715017743352084719147)
        ·
          refine ⟨190036072526615028127078721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126690715017743352084719147 190036072526615028127078721)
          ·
            refine ⟨142527054394961271095309041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190036072526615028127078721 142527054394961271095309041)
            ·
              refine ⟨106895290796220953321481781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142527054394961271095309041 106895290796220953321481781)
              ·
                refine ⟨10021433512145714373888917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106895290796220953321481781 10021433512145714373888917)
                ·
                  refine ⟨469754695881830361276043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10021433512145714373888917 469754695881830361276043)
                  ·
                    rfl

theorem cell23_8233596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_8233596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233596 prefixEnd_8233596 := by exact prefixLift 8233596
  have htrace : WordTrace (prefixWord ++ tailWord_8233596) baseStart_8233596 baseEnd_8233596 := by
    simpa [prefixWord, tailWord_8233596, baseEnd_8233596] using wordTrace_append hprefix tailTrace_8233596
  have hstable : (prefixWord ++ tailWord_8233596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233596).length < 2 ^ (prefixWord ++ tailWord_8233596).sum := by decide
  have hdescent : baseEnd_8233596 < baseStart_8233596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233663 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_8233663 : Nat := 118140960795 + 8233663 * 2 ^ 59
def prefixEnd_8233663 : Nat := 4983230072969 + 3 ^ 40 * 8233663 * 2
def baseEnd_8233663 : Nat := 4227826666140324489346579

theorem tailTrace_8233663 : CollatzResearch.WordTrace tailWord_8233663 prefixEnd_8233663 4227826666140324489346579 := by
  unfold tailWord_8233663
  simp only [CollatzResearch.WordTrace]
  refine ⟨300306360769852623532393643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200204240513235082354929095 300306360769852623532393643)
  ·
    refine ⟨450459541154778935298590465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300306360769852623532393643 450459541154778935298590465)
    ·
      refine ⟨337844655866084201473942849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450459541154778935298590465 337844655866084201473942849)
      ·
        refine ⟨253383491899563151105457137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337844655866084201473942849 253383491899563151105457137)
        ·
          refine ⟨190037618924672363329092853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253383491899563151105457137 190037618924672363329092853)
          ·
            refine ⟨17816026774188034062102455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190037618924672363329092853 17816026774188034062102455)
            ·
              refine ⟨26724040161282051093153683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17816026774188034062102455 26724040161282051093153683)
              ·
                refine ⟨40086060241923076639730525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26724040161282051093153683 40086060241923076639730525)
                ·
                  refine ⟨15032272590721153739898947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40086060241923076639730525 15032272590721153739898947)
                  ·
                    refine ⟨22548408886081730609848421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15032272590721153739898947 22548408886081730609848421)
                    ·
                      refine ⟨4227826666140324489346579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22548408886081730609848421 4227826666140324489346579)
                      ·
                        rfl

theorem cell23_8233663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_8233663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233663 prefixEnd_8233663 := by exact prefixLift 8233663
  have htrace : WordTrace (prefixWord ++ tailWord_8233663) baseStart_8233663 baseEnd_8233663 := by
    simpa [prefixWord, tailWord_8233663, baseEnd_8233663] using wordTrace_append hprefix tailTrace_8233663
  have hstable : (prefixWord ++ tailWord_8233663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233663).length < 2 ^ (prefixWord ++ tailWord_8233663).sum := by decide
  have hdescent : baseEnd_8233663 < baseStart_8233663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233690 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_8233690 : Nat := 118140960795 + 8233690 * 2 ^ 59
def prefixEnd_8233690 : Nat := 4983230072969 + 3 ^ 40 * 8233690 * 2
def baseEnd_8233690 : Nat := 1409280176705998627902985

theorem tailTrace_8233690 : CollatzResearch.WordTrace tailWord_8233690 prefixEnd_8233690 1409280176705998627902985 := by
  unfold tailWord_8233690
  simp only [CollatzResearch.WordTrace]
  refine ⟨75076836385188701785906631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200204897027169871429084349 75076836385188701785906631)
  ·
    refine ⟨112615254577783052678859947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75076836385188701785906631 112615254577783052678859947)
    ·
      refine ⟨168922881866674579018289921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112615254577783052678859947 168922881866674579018289921)
      ·
        refine ⟨126692161400005934263717441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168922881866674579018289921 126692161400005934263717441)
        ·
          refine ⟨95019121050004450697788081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126692161400005934263717441 95019121050004450697788081)
          ·
            refine ⟨71264340787503338023341061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95019121050004450697788081 71264340787503338023341061)
            ·
              refine ⟨13362063897656875879376449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71264340787503338023341061 13362063897656875879376449)
              ·
                refine ⟨10021547923242656909532337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13362063897656875879376449 10021547923242656909532337)
                ·
                  refine ⟨7516160942431992682149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021547923242656909532337 7516160942431992682149253)
                  ·
                    refine ⟨1409280176705998627902985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516160942431992682149253 1409280176705998627902985)
                    ·
                      rfl

theorem cell23_8233690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_8233690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233690 prefixEnd_8233690 := by exact prefixLift 8233690
  have htrace : WordTrace (prefixWord ++ tailWord_8233690) baseStart_8233690 baseEnd_8233690 := by
    simpa [prefixWord, tailWord_8233690, baseEnd_8233690] using wordTrace_append hprefix tailTrace_8233690
  have hstable : (prefixWord ++ tailWord_8233690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233690).length < 2 ^ (prefixWord ++ tailWord_8233690).sum := by decide
  have hdescent : baseEnd_8233690 < baseStart_8233690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233710 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_8233710 : Nat := 118140960795 + 8233710 * 2 ^ 59
def prefixEnd_8233710 : Nat := 4983230072969 + 3 ^ 40 * 8233710 * 2
def baseEnd_8233710 : Nat := 4227850799731085805458863

theorem tailTrace_8233710 : CollatzResearch.WordTrace tailWord_8233710 prefixEnd_8233710 4227850799731085805458863 := by
  unfold tailWord_8233710
  simp only [CollatzResearch.WordTrace]
  refine ⟨37538509375085293819919323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200205383333788233706236389 37538509375085293819919323)
  ·
    refine ⟨56307764062627940729878985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37538509375085293819919323 56307764062627940729878985)
    ·
      refine ⟨42230823046970955547409239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56307764062627940729878985 42230823046970955547409239)
      ·
        refine ⟨63346234570456433321113859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42230823046970955547409239 63346234570456433321113859)
        ·
          refine ⟨95019351855684649981670789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63346234570456433321113859 95019351855684649981670789)
          ·
            refine ⟨17816128472940871871563273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95019351855684649981670789 17816128472940871871563273)
            ·
              refine ⟨13362096354705653903672455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17816128472940871871563273 13362096354705653903672455)
              ·
                refine ⟨20043144532058480855508683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13362096354705653903672455 20043144532058480855508683)
                ·
                  refine ⟨30064716798087721283263025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20043144532058480855508683 30064716798087721283263025)
                  ·
                    refine ⟨22548537598565790962447269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30064716798087721283263025 22548537598565790962447269)
                    ·
                      refine ⟨4227850799731085805458863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22548537598565790962447269 4227850799731085805458863)
                      ·
                        rfl

theorem cell23_8233710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_8233710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233710 prefixEnd_8233710 := by exact prefixLift 8233710
  have htrace : WordTrace (prefixWord ++ tailWord_8233710) baseStart_8233710 baseEnd_8233710 := by
    simpa [prefixWord, tailWord_8233710, baseEnd_8233710] using wordTrace_append hprefix tailTrace_8233710
  have hstable : (prefixWord ++ tailWord_8233710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233710).length < 2 ^ (prefixWord ++ tailWord_8233710).sum := by decide
  have hdescent : baseEnd_8233710 < baseStart_8233710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233764 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_8233764 : Nat := 118140960795 + 8233764 * 2 ^ 59
def prefixEnd_8233764 : Nat := 4983230072969 + 3 ^ 40 * 8233764 * 2
def baseEnd_8233764 : Nat := 4227878527686428594183615

theorem tailTrace_8233764 : CollatzResearch.WordTrace tailWord_8233764 prefixEnd_8233764 4227878527686428594183615 := by
  unfold tailWord_8233764
  simp only [CollatzResearch.WordTrace]
  refine ⟨150155022271243358890910173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200206696361657811854546897 150155022271243358890910173)
  ·
    refine ⟨56308133351716259584091315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150155022271243358890910173 56308133351716259584091315)
    ·
      refine ⟨84462200027574389376136973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56308133351716259584091315 84462200027574389376136973)
      ·
        refine ⟨31673325010340396016051365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84462200027574389376136973 31673325010340396016051365)
        ·
          refine ⟨5938748439438824253009631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31673325010340396016051365 5938748439438824253009631)
          ·
            refine ⟨8908122659158236379514447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938748439438824253009631 8908122659158236379514447)
            ·
              refine ⟨13362183988737354569271671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8908122659158236379514447 13362183988737354569271671)
              ·
                refine ⟨20043275983106031853907507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13362183988737354569271671 20043275983106031853907507)
                ·
                  refine ⟨30064913974659047780861261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20043275983106031853907507 30064913974659047780861261)
                  ·
                    refine ⟨11274342740497142917822973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30064913974659047780861261 11274342740497142917822973)
                    ·
                      refine ⟨4227878527686428594183615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11274342740497142917822973 4227878527686428594183615)
                      ·
                        rfl

theorem cell23_8233764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_8233764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233764 prefixEnd_8233764 := by exact prefixLift 8233764
  have htrace : WordTrace (prefixWord ++ tailWord_8233764) baseStart_8233764 baseEnd_8233764 := by
    simpa [prefixWord, tailWord_8233764, baseEnd_8233764] using wordTrace_append hprefix tailTrace_8233764
  have hstable : (prefixWord ++ tailWord_8233764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233764).length < 2 ^ (prefixWord ++ tailWord_8233764).sum := by decide
  have hdescent : baseEnd_8233764 < baseStart_8233764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233774 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_8233774 : Nat := 118140960795 + 8233774 * 2 ^ 59
def prefixEnd_8233774 : Nat := 4983230072969 + 3 ^ 40 * 8233774 * 2
def baseEnd_8233774 : Nat := 4227883662492973555058569

theorem tailTrace_8233774 : CollatzResearch.WordTrace tailWord_8233774 prefixEnd_8233774 4227883662492973555058569 := by
  unfold tailWord_8233774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37538801159056311186210547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200206939514966992993122917 37538801159056311186210547)
  ·
    refine ⟨56308201738584466779315821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37538801159056311186210547 56308201738584466779315821)
    ·
      refine ⟨21115575651969175042243433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56308201738584466779315821 21115575651969175042243433)
      ·
        refine ⟨15836681738976881281682575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21115575651969175042243433 15836681738976881281682575)
        ·
          refine ⟨23755022608465321922523863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15836681738976881281682575 23755022608465321922523863)
          ·
            refine ⟨35632533912697982883785795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23755022608465321922523863 35632533912697982883785795)
            ·
              refine ⟨53448800869046974325678693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35632533912697982883785795 53448800869046974325678693)
              ·
                refine ⟨10021650162946307686064755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53448800869046974325678693 10021650162946307686064755)
                ·
                  refine ⟨15032475244419461529097133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021650162946307686064755 15032475244419461529097133)
                  ·
                    refine ⟨5637178216657298073411425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15032475244419461529097133 5637178216657298073411425)
                    ·
                      refine ⟨4227883662492973555058569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637178216657298073411425 4227883662492973555058569)
                      ·
                        rfl

theorem cell23_8233774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_8233774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233774 prefixEnd_8233774 := by exact prefixLift 8233774
  have htrace : WordTrace (prefixWord ++ tailWord_8233774) baseStart_8233774 baseEnd_8233774 := by
    simpa [prefixWord, tailWord_8233774, baseEnd_8233774] using wordTrace_append hprefix tailTrace_8233774
  have hstable : (prefixWord ++ tailWord_8233774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233774).length < 2 ^ (prefixWord ++ tailWord_8233774).sum := by decide
  have hdescent : baseEnd_8233774 < baseStart_8233774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233823 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 4, 5]
def baseStart_8233823 : Nat := 118140960795 + 8233823 * 2 ^ 59
def prefixEnd_8233823 : Nat := 4983230072969 + 3 ^ 40 * 8233823 * 2
def baseEnd_8233823 : Nat := 1409302941015014621115281

theorem tailTrace_8233823 : CollatzResearch.WordTrace tailWord_8233823 prefixEnd_8233823 1409302941015014621115281 := by
  unfold tailWord_8233823
  simp only [CollatzResearch.WordTrace]
  refine ⟨300312196449272970858218123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200208130966181980572145415 300312196449272970858218123)
  ·
    refine ⟨450468294673909456287327185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300312196449272970858218123 450468294673909456287327185)
    ·
      refine ⟨337851221005432092215495389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450468294673909456287327185 337851221005432092215495389)
      ·
        refine ⟨126694207877037034580810771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337851221005432092215495389 126694207877037034580810771)
        ·
          refine ⟨190041311815555551871216157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126694207877037034580810771 190041311815555551871216157)
          ·
            refine ⟨71265491930833331951706059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190041311815555551871216157 71265491930833331951706059)
            ·
              refine ⟨106898237896249997927559089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71265491930833331951706059 106898237896249997927559089)
              ·
                refine ⟨80173678422187498445669317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106898237896249997927559089 80173678422187498445669317)
                ·
                  refine ⟨15032564704160155958562997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80173678422187498445669317 15032564704160155958562997)
                  ·
                    refine ⟨1409302941015014621115281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15032564704160155958562997 1409302941015014621115281)
                    ·
                      rfl

theorem cell23_8233823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_8233823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233823 prefixEnd_8233823 := by exact prefixLift 8233823
  have htrace : WordTrace (prefixWord ++ tailWord_8233823) baseStart_8233823 baseEnd_8233823 := by
    simpa [prefixWord, tailWord_8233823, baseEnd_8233823] using wordTrace_append hprefix tailTrace_8233823
  have hstable : (prefixWord ++ tailWord_8233823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233823).length < 2 ^ (prefixWord ++ tailWord_8233823).sum := by decide
  have hdescent : baseEnd_8233823 < baseStart_8233823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233843 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_8233843 : Nat := 118140960795 + 8233843 * 2 ^ 59
def prefixEnd_8233843 : Nat := 4983230072969 + 3 ^ 40 * 8233843 * 2
def baseEnd_8233843 : Nat := 4227919092658133785095751

theorem tailTrace_8233843 : CollatzResearch.WordTrace tailWord_8233843 prefixEnd_8233843 4227919092658133785095751 := by
  unfold tailWord_8233843
  simp only [CollatzResearch.WordTrace]
  refine ⟨300312925909200514273946183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200208617272800342849297455 300312925909200514273946183)
  ·
    refine ⟨450469388863800771410919275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300312925909200514273946183 450469388863800771410919275)
    ·
      refine ⟨675704083295701157116378913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450469388863800771410919275 675704083295701157116378913)
      ·
        refine ⟨506778062471775867837284185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675704083295701157116378913 506778062471775867837284185)
        ·
          refine ⟨380083546853831900877963139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506778062471775867837284185 380083546853831900877963139)
          ·
            refine ⟨570125320280747851316944709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380083546853831900877963139 570125320280747851316944709)
            ·
              refine ⟨106898497552640222121927133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570125320280747851316944709 106898497552640222121927133)
              ·
                refine ⟨40086936582240083295722675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106898497552640222121927133 40086936582240083295722675)
                ·
                  refine ⟨60130404873360124943584013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40086936582240083295722675 60130404873360124943584013)
                  ·
                    refine ⟨22548901827510046853844005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60130404873360124943584013 22548901827510046853844005)
                    ·
                      refine ⟨4227919092658133785095751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22548901827510046853844005 4227919092658133785095751)
                      ·
                        rfl

theorem cell23_8233843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_8233843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233843 prefixEnd_8233843 := by exact prefixLift 8233843
  have htrace : WordTrace (prefixWord ++ tailWord_8233843) baseStart_8233843 baseEnd_8233843 := by
    simpa [prefixWord, tailWord_8233843, baseEnd_8233843] using wordTrace_append hprefix tailTrace_8233843
  have hstable : (prefixWord ++ tailWord_8233843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233843).length < 2 ^ (prefixWord ++ tailWord_8233843).sum := by decide
  have hdescent : baseEnd_8233843 < baseStart_8233843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233873 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_8233873 : Nat := 118140960795 + 8233873 * 2 ^ 59
def prefixEnd_8233873 : Nat := 4983230072969 + 3 ^ 40 * 8233873 * 2
def baseEnd_8233873 : Nat := 4227934497077768667720613

theorem tailTrace_8233873 : CollatzResearch.WordTrace tailWord_8233873 prefixEnd_8233873 4227934497077768667720613 := by
  unfold tailWord_8233873
  simp only [CollatzResearch.WordTrace]
  refine ⟨300314020099091829397538273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200209346732727886265025515 300314020099091829397538273)
  ·
    refine ⟨225235515074318872048153705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300314020099091829397538273 225235515074318872048153705)
    ·
      refine ⟨168926636305739154036115279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225235515074318872048153705 168926636305739154036115279)
      ·
        refine ⟨253389954458608731054172919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168926636305739154036115279 253389954458608731054172919)
        ·
          refine ⟨380084931687913096581259379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253389954458608731054172919 380084931687913096581259379)
          ·
            refine ⟨570127397531869644871889069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380084931687913096581259379 570127397531869644871889069)
            ·
              refine ⟨213797774074451116826958401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570127397531869644871889069 213797774074451116826958401)
              ·
                refine ⟨160348330555838337620218801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213797774074451116826958401 160348330555838337620218801)
                ·
                  refine ⟨120261247916878753215164101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160348330555838337620218801 120261247916878753215164101)
                  ·
                    refine ⟨22548983984414766227843269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120261247916878753215164101 22548983984414766227843269)
                    ·
                      refine ⟨4227934497077768667720613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22548983984414766227843269 4227934497077768667720613)
                      ·
                        rfl

theorem cell23_8233873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_8233873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233873 prefixEnd_8233873 := by exact prefixLift 8233873
  have htrace : WordTrace (prefixWord ++ tailWord_8233873) baseStart_8233873 baseEnd_8233873 := by
    simpa [prefixWord, tailWord_8233873, baseEnd_8233873] using wordTrace_append hprefix tailTrace_8233873
  have hstable : (prefixWord ++ tailWord_8233873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233873).length < 2 ^ (prefixWord ++ tailWord_8233873).sum := by decide
  have hdescent : baseEnd_8233873 < baseStart_8233873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233877 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_8233877 : Nat := 118140960795 + 8233877 * 2 ^ 59
def prefixEnd_8233877 : Nat := 4983230072969 + 3 ^ 40 * 8233877 * 2
def baseEnd_8233877 : Nat := 4227936551000386652070595

theorem tailTrace_8233877 : CollatzResearch.WordTrace tailWord_8233877 prefixEnd_8233877 4227936551000386652070595 := by
  unfold tailWord_8233877
  simp only [CollatzResearch.WordTrace]
  refine ⟨300314165991077338080683885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200209443994051558720455923 300314165991077338080683885)
  ·
    refine ⟨112617812246654001780256457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300314165991077338080683885 112617812246654001780256457)
    ·
      refine ⟨84463359184990501335192343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112617812246654001780256457 84463359184990501335192343)
      ·
        refine ⟨126695038777485752002788515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84463359184990501335192343 126695038777485752002788515)
        ·
          refine ⟨190042558166228628004182773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126695038777485752002788515 190042558166228628004182773)
          ·
            refine ⟨17816489828083933875392135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190042558166228628004182773 17816489828083933875392135)
            ·
              refine ⟨26724734742125900813088203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17816489828083933875392135 26724734742125900813088203)
              ·
                refine ⟨40087102113188851219632305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26724734742125900813088203 40087102113188851219632305)
                ·
                  refine ⟨30065326584891638414724229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40087102113188851219632305 30065326584891638414724229)
                  ·
                    refine ⟨5637248734667182202760793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30065326584891638414724229 5637248734667182202760793)
                    ·
                      refine ⟨4227936551000386652070595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637248734667182202760793 4227936551000386652070595)
                      ·
                        rfl

theorem cell23_8233877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_8233877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233877 prefixEnd_8233877 := by exact prefixLift 8233877
  have htrace : WordTrace (prefixWord ++ tailWord_8233877) baseStart_8233877 baseEnd_8233877 := by
    simpa [prefixWord, tailWord_8233877, baseEnd_8233877] using wordTrace_append hprefix tailTrace_8233877
  have hstable : (prefixWord ++ tailWord_8233877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233877).length < 2 ^ (prefixWord ++ tailWord_8233877).sum := by decide
  have hdescent : baseEnd_8233877 < baseStart_8233877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233887 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 3, 4]
def baseStart_8233887 : Nat := 118140960795 + 8233887 * 2 ^ 59
def prefixEnd_8233887 : Nat := 4983230072969 + 3 ^ 40 * 8233887 * 2
def baseEnd_8233887 : Nat := 1409313895268977204315183

theorem tailTrace_8233887 : CollatzResearch.WordTrace tailWord_8233887 prefixEnd_8233887 1409313895268977204315183 := by
  unfold tailWord_8233887
  simp only [CollatzResearch.WordTrace]
  refine ⟨300314530721041109788547915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200209687147360739859031943 300314530721041109788547915)
  ·
    refine ⟨450471796081561664682821873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300314530721041109788547915 450471796081561664682821873)
    ·
      refine ⟨337853847061171248512116405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450471796081561664682821873 337853847061171248512116405)
      ·
        refine ⟨31673798161984804548010913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337853847061171248512116405 31673798161984804548010913)
        ·
          refine ⟨23755348621488603411008185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31673798161984804548010913 23755348621488603411008185)
          ·
            refine ⟨17816511466116452558256139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23755348621488603411008185 17816511466116452558256139)
            ·
              refine ⟨26724767199174678837384209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17816511466116452558256139 26724767199174678837384209)
              ·
                refine ⟨20043575399381009128038157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26724767199174678837384209 20043575399381009128038157)
                ·
                  refine ⟨7516340774767878423014309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20043575399381009128038157 7516340774767878423014309)
                  ·
                    refine ⟨1409313895268977204315183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516340774767878423014309 1409313895268977204315183)
                    ·
                      rfl

theorem cell23_8233887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_8233887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233887 prefixEnd_8233887 := by exact prefixLift 8233887
  have htrace : WordTrace (prefixWord ++ tailWord_8233887) baseStart_8233887 baseEnd_8233887 := by
    simpa [prefixWord, tailWord_8233887, baseEnd_8233887] using wordTrace_append hprefix tailTrace_8233887
  have hstable : (prefixWord ++ tailWord_8233887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233887).length < 2 ^ (prefixWord ++ tailWord_8233887).sum := by decide
  have hdescent : baseEnd_8233887 < baseStart_8233887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233923 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_8233923 : Nat := 118140960795 + 8233923 * 2 ^ 59
def prefixEnd_8233923 : Nat := 4983230072969 + 3 ^ 40 * 8233923 * 2
def baseEnd_8233923 : Nat := 4227960171110493472095383

theorem tailTrace_8233923 : CollatzResearch.WordTrace tailWord_8233923 prefixEnd_8233923 4227960171110493472095383 := by
  unfold tailWord_8233923
  simp only [CollatzResearch.WordTrace]
  refine ⟨300315843748910687936858423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200210562499273791957905615 300315843748910687936858423)
  ·
    refine ⟨450473765623366031905287635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300315843748910687936858423 450473765623366031905287635)
    ·
      refine ⟨675710648435049047857931453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450473765623366031905287635 675710648435049047857931453)
      ·
        refine ⟨253391493163143392946724295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675710648435049047857931453 253391493163143392946724295)
        ·
          refine ⟨380087239744715089420086443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253391493163143392946724295 380087239744715089420086443)
          ·
            refine ⟨570130859617072634130129665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380087239744715089420086443 570130859617072634130129665)
            ·
              refine ⟨427598144712804475597597249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570130859617072634130129665 427598144712804475597597249)
              ·
                refine ⟨320698608534603356698197937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427598144712804475597597249 320698608534603356698197937)
                ·
                  refine ⟨240523956400952517523648453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320698608534603356698197937 240523956400952517523648453)
                  ·
                    refine ⟨45098241825178597035684085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240523956400952517523648453 45098241825178597035684085)
                    ·
                      refine ⟨4227960171110493472095383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45098241825178597035684085 4227960171110493472095383)
                      ·
                        rfl

theorem cell23_8233923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_8233923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233923 prefixEnd_8233923 := by exact prefixLift 8233923
  have htrace : WordTrace (prefixWord ++ tailWord_8233923) baseStart_8233923 baseEnd_8233923 := by
    simpa [prefixWord, tailWord_8233923, baseEnd_8233923] using wordTrace_append hprefix tailTrace_8233923
  have hstable : (prefixWord ++ tailWord_8233923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233923).length < 2 ^ (prefixWord ++ tailWord_8233923).sum := by decide
  have hdescent : baseEnd_8233923 < baseStart_8233923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233927 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_8233927 : Nat := 118140960795 + 8233927 * 2 ^ 59
def prefixEnd_8233927 : Nat := 4983230072969 + 3 ^ 40 * 8233927 * 2
def baseEnd_8233927 : Nat := 4227962225033111456445365

theorem tailTrace_8233927 : CollatzResearch.WordTrace tailWord_8233927 prefixEnd_8233927 4227962225033111456445365 := by
  unfold tailWord_8233927
  simp only [CollatzResearch.WordTrace]
  refine ⟨300315989640896196620004035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200210659760597464413336023 300315989640896196620004035)
  ·
    refine ⟨450473984461344294930006053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300315989640896196620004035 450473984461344294930006053)
    ·
      refine ⟨84463872086502055299376135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450473984461344294930006053 84463872086502055299376135)
      ·
        refine ⟨126695808129753082949064203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84463872086502055299376135 126695808129753082949064203)
        ·
          refine ⟨190043712194629624423596305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126695808129753082949064203 190043712194629624423596305)
          ·
            refine ⟨142532784145972218317697229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190043712194629624423596305 142532784145972218317697229)
            ·
              refine ⟨53449794054739581869136461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142532784145972218317697229 53449794054739581869136461)
              ·
                refine ⟨20043672770527343200926173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53449794054739581869136461 20043672770527343200926173)
                ·
                  refine ⟨7516377288947753700347315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20043672770527343200926173 7516377288947753700347315)
                  ·
                    refine ⟨11274565933421630550520973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516377288947753700347315 11274565933421630550520973)
                    ·
                      refine ⟨4227962225033111456445365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11274565933421630550520973 4227962225033111456445365)
                      ·
                        rfl

theorem cell23_8233927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_8233927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233927 prefixEnd_8233927 := by exact prefixLift 8233927
  have htrace : WordTrace (prefixWord ++ tailWord_8233927) baseStart_8233927 baseEnd_8233927 := by
    simpa [prefixWord, tailWord_8233927, baseEnd_8233927] using wordTrace_append hprefix tailTrace_8233927
  have hstable : (prefixWord ++ tailWord_8233927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233927).length < 2 ^ (prefixWord ++ tailWord_8233927).sum := by decide
  have hdescent : baseEnd_8233927 < baseStart_8233927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233960 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_8233960 : Nat := 118140960795 + 8233960 * 2 ^ 59
def prefixEnd_8233960 : Nat := 4983230072969 + 3 ^ 40 * 8233960 * 2
def baseEnd_8233960 : Nat := 1409326389964903275777571

theorem tailTrace_8233960 : CollatzResearch.WordTrace tailWord_8233960 prefixEnd_8233960 1409326389964903275777571 := by
  unfold tailWord_8233960
  simp only [CollatzResearch.WordTrace]
  refine ⟨150158596624888321627977667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200211462166517762170636889 150158596624888321627977667)
  ·
    refine ⟨225237894937332482441966501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150158596624888321627977667 225237894937332482441966501)
    ·
      refine ⟨42232105300749840457868719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225237894937332482441966501 42232105300749840457868719)
      ·
        refine ⟨63348157951124760686803079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42232105300749840457868719 63348157951124760686803079)
        ·
          refine ⟨95022236926687141030204619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63348157951124760686803079 95022236926687141030204619)
          ·
            refine ⟨142533355390030711545306929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95022236926687141030204619 142533355390030711545306929)
            ·
              refine ⟨106900016542523033658980197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142533355390030711545306929 106900016542523033658980197)
              ·
                refine ⟨20043753101723068811058787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106900016542523033658980197 20043753101723068811058787)
                ·
                  refine ⟨30065629652584603216588181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20043753101723068811058787 30065629652584603216588181)
                  ·
                    refine ⟨1409326389964903275777571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30065629652584603216588181 1409326389964903275777571)
                    ·
                      rfl

theorem cell23_8233960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_8233960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233960 prefixEnd_8233960 := by exact prefixLift 8233960
  have htrace : WordTrace (prefixWord ++ tailWord_8233960) baseStart_8233960 baseEnd_8233960 := by
    simpa [prefixWord, tailWord_8233960, baseEnd_8233960] using wordTrace_append hprefix tailTrace_8233960
  have hstable : (prefixWord ++ tailWord_8233960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233960).length < 2 ^ (prefixWord ++ tailWord_8233960).sum := by decide
  have hdescent : baseEnd_8233960 < baseStart_8233960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233967 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_8233967 : Nat := 118140960795 + 8233967 * 2 ^ 59
def prefixEnd_8233967 : Nat := 4983230072969 + 3 ^ 40 * 8233967 * 2
def baseEnd_8233967 : Nat := 4227982764259291299945181

theorem tailTrace_8233967 : CollatzResearch.WordTrace tailWord_8233967 prefixEnd_8233967 4227982764259291299945181 := by
  unfold tailWord_8233967
  simp only [CollatzResearch.WordTrace]
  refine ⟨300317448560751283451460155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200211632373834188967640103 300317448560751283451460155)
  ·
    refine ⟨450476172841126925177190233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300317448560751283451460155 450476172841126925177190233)
    ·
      refine ⟨337857129630845193882892675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450476172841126925177190233 337857129630845193882892675)
      ·
        refine ⟨506785694446267790824339013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337857129630845193882892675 506785694446267790824339013)
        ·
          refine ⟨95022317708675210779563565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506785694446267790824339013 95022317708675210779563565)
          ·
            refine ⟨35633369140753204042336337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95022317708675210779563565 35633369140753204042336337)
            ·
              refine ⟨26725026855564903031752253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35633369140753204042336337 26725026855564903031752253)
              ·
                refine ⟨10021885070836838636907095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26725026855564903031752253 10021885070836838636907095)
                ·
                  refine ⟨15032827606255257955360643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10021885070836838636907095 15032827606255257955360643)
                  ·
                    refine ⟨22549241409382886933040965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15032827606255257955360643 22549241409382886933040965)
                    ·
                      refine ⟨4227982764259291299945181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22549241409382886933040965 4227982764259291299945181)
                      ·
                        rfl

theorem cell23_8233967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_8233967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233967 prefixEnd_8233967 := by exact prefixLift 8233967
  have htrace : WordTrace (prefixWord ++ tailWord_8233967) baseStart_8233967 baseEnd_8233967 := by
    simpa [prefixWord, tailWord_8233967, baseEnd_8233967] using wordTrace_append hprefix tailTrace_8233967
  have hstable : (prefixWord ++ tailWord_8233967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233967).length < 2 ^ (prefixWord ++ tailWord_8233967).sum := by decide
  have hdescent : baseEnd_8233967 < baseStart_8233967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233972 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8233972 : Nat := 118140960795 + 8233972 * 2 ^ 59
def prefixEnd_8233972 : Nat := 4983230072969 + 3 ^ 40 * 8233972 * 2
def baseEnd_8233972 : Nat := 1409328443887521260127553

theorem tailTrace_8233972 : CollatzResearch.WordTrace tailWord_8233972 prefixEnd_8233972 1409328443887521260127553 := by
  unfold tailWord_8233972
  simp only [CollatzResearch.WordTrace]
  refine ⟨150158815462866584652696085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200211753950488779536928113 150158815462866584652696085)
  ·
    refine ⟨7038694474821871155595129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150158815462866584652696085 7038694474821871155595129)
    ·
      refine ⟨5279020856116403366696347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7038694474821871155595129 5279020856116403366696347)
      ·
        refine ⟨7918531284174605050044521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279020856116403366696347 7918531284174605050044521)
        ·
          refine ⟨5938898463130953787533391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7918531284174605050044521 5938898463130953787533391)
          ·
            refine ⟨8908347694696430681300087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938898463130953787533391 8908347694696430681300087)
            ·
              refine ⟨13362521542044646021950131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8908347694696430681300087 13362521542044646021950131)
              ·
                refine ⟨20043782313066969032925197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13362521542044646021950131 20043782313066969032925197)
                ·
                  refine ⟨7516418367400113387346949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20043782313066969032925197 7516418367400113387346949)
                  ·
                    refine ⟨1409328443887521260127553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516418367400113387346949 1409328443887521260127553)
                    ·
                      rfl

theorem cell23_8233972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8233972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233972 prefixEnd_8233972 := by exact prefixLift 8233972
  have htrace : WordTrace (prefixWord ++ tailWord_8233972) baseStart_8233972 baseEnd_8233972 := by
    simpa [prefixWord, tailWord_8233972, baseEnd_8233972] using wordTrace_append hprefix tailTrace_8233972
  have hstable : (prefixWord ++ tailWord_8233972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233972).length < 2 ^ (prefixWord ++ tailWord_8233972).sum := by decide
  have hdescent : baseEnd_8233972 < baseStart_8233972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233977 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_8233977 : Nat := 118140960795 + 8233977 * 2 ^ 59
def prefixEnd_8233977 : Nat := 4983230072969 + 3 ^ 40 * 8233977 * 2
def baseEnd_8233977 : Nat := 1409329299688612086940045

theorem tailTrace_8233977 : CollatzResearch.WordTrace tailWord_8233977 prefixEnd_8233977 1409329299688612086940045 := by
  unfold tailWord_8233977
  simp only [CollatzResearch.WordTrace]
  refine ⟨300317813290715055159324185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200211875527143370106216123 300317813290715055159324185)
  ·
    refine ⟨225238359968036291369493139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300317813290715055159324185 225238359968036291369493139)
    ·
      refine ⟨337857539952054437054239709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225238359968036291369493139 337857539952054437054239709)
      ·
        refine ⟨126696577482020413895339891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337857539952054437054239709 126696577482020413895339891)
        ·
          refine ⟨190044866223030620843009837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126696577482020413895339891 190044866223030620843009837)
          ·
            refine ⟨71266824833636482816128689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190044866223030620843009837 71266824833636482816128689)
            ·
              refine ⟨53450118625227362112096517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71266824833636482816128689 53450118625227362112096517)
              ·
                refine ⟨10021897242230130396018097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53450118625227362112096517 10021897242230130396018097)
                ·
                  refine ⟨7516422931672597797013573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021897242230130396018097 7516422931672597797013573)
                  ·
                    refine ⟨1409329299688612086940045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516422931672597797013573 1409329299688612086940045)
                    ·
                      rfl

theorem cell23_8233977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_8233977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233977 prefixEnd_8233977 := by exact prefixLift 8233977
  have htrace : WordTrace (prefixWord ++ tailWord_8233977) baseStart_8233977 baseEnd_8233977 := by
    simpa [prefixWord, tailWord_8233977, baseEnd_8233977] using wordTrace_append hprefix tailTrace_8233977
  have hstable : (prefixWord ++ tailWord_8233977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233977).length < 2 ^ (prefixWord ++ tailWord_8233977).sum := by decide
  have hdescent : baseEnd_8233977 < baseStart_8233977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233980 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_8233980 : Nat := 118140960795 + 8233980 * 2 ^ 59
def prefixEnd_8233980 : Nat := 4983230072969 + 3 ^ 40 * 8233980 * 2
def baseEnd_8233980 : Nat := 4227989439507799749082621

theorem tailTrace_8233980 : CollatzResearch.WordTrace tailWord_8233980 prefixEnd_8233980 4227989439507799749082621 := by
  unfold tailWord_8233980
  simp only [CollatzResearch.WordTrace]
  refine ⟨150158961354852093335841697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200211948473136124447788929 150158961354852093335841697)
  ·
    refine ⟨112619221016139070001881273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150158961354852093335841697 112619221016139070001881273)
    ·
      refine ⟨84464415762104302501410955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112619221016139070001881273 84464415762104302501410955)
      ·
        refine ⟨126696623643156453752116433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84464415762104302501410955 126696623643156453752116433)
        ·
          refine ⟨95022467732367340314087325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126696623643156453752116433 95022467732367340314087325)
          ·
            refine ⟨35633425399637752617782747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95022467732367340314087325 35633425399637752617782747)
            ·
              refine ⟨53450138099456628926674121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35633425399637752617782747 53450138099456628926674121)
              ·
                refine ⟨40087603574592471695005591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53450138099456628926674121 40087603574592471695005591)
                ·
                  refine ⟨60131405361888707542508387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40087603574592471695005591 60131405361888707542508387)
                  ·
                    refine ⟨90197108042833061313762581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60131405361888707542508387 90197108042833061313762581)
                    ·
                      refine ⟨4227989439507799749082621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90197108042833061313762581 4227989439507799749082621)
                      ·
                        rfl

theorem cell23_8233980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_8233980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233980 prefixEnd_8233980 := by exact prefixLift 8233980
  have htrace : WordTrace (prefixWord ++ tailWord_8233980) baseStart_8233980 baseEnd_8233980 := by
    simpa [prefixWord, tailWord_8233980, baseEnd_8233980] using wordTrace_append hprefix tailTrace_8233980
  have hstable : (prefixWord ++ tailWord_8233980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233980).length < 2 ^ (prefixWord ++ tailWord_8233980).sum := by decide
  have hdescent : baseEnd_8233980 < baseStart_8233980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8233994 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_8233994 : Nat := 118140960795 + 8233994 * 2 ^ 59
def prefixEnd_8233994 : Nat := 4983230072969 + 3 ^ 40 * 8233994 * 2
def baseEnd_8233994 : Nat := 1409332209412320898102519

theorem tailTrace_8233994 : CollatzResearch.WordTrace tailWord_8233994 prefixEnd_8233994 1409332209412320898102519 := by
  unfold tailWord_8233994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75079608332913366765673259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200212288887768978041795357 75079608332913366765673259)
  ·
    refine ⟨112619412499370050148509889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75079608332913366765673259 112619412499370050148509889)
    ·
      refine ⟨84464559374527537611382417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112619412499370050148509889 84464559374527537611382417)
      ·
        refine ⟨63348419530895653208536813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84464559374527537611382417 63348419530895653208536813)
        ·
          refine ⟨23755657324085869953201305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63348419530895653208536813 23755657324085869953201305)
          ·
            refine ⟨17816742993064402464900979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23755657324085869953201305 17816742993064402464900979)
            ·
              refine ⟨26725114489596603697351469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17816742993064402464900979 26725114489596603697351469)
              ·
                refine ⟨10021917933598726386506801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26725114489596603697351469 10021917933598726386506801)
                ·
                  refine ⟨7516438450199044789880101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021917933598726386506801 7516438450199044789880101)
                  ·
                    refine ⟨1409332209412320898102519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516438450199044789880101 1409332209412320898102519)
                    ·
                      rfl

theorem cell23_8233994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_8233994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8233994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8233994 prefixEnd_8233994 := by exact prefixLift 8233994
  have htrace : WordTrace (prefixWord ++ tailWord_8233994) baseStart_8233994 baseEnd_8233994 := by
    simpa [prefixWord, tailWord_8233994, baseEnd_8233994] using wordTrace_append hprefix tailTrace_8233994
  have hstable : (prefixWord ++ tailWord_8233994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8233994).length < 2 ^ (prefixWord ++ tailWord_8233994).sum := by decide
  have hdescent : baseEnd_8233994 < baseStart_8233994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8233994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234017 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_8234017 : Nat := 118140960795 + 8234017 * 2 ^ 59
def prefixEnd_8234017 : Nat := 4983230072969 + 3 ^ 40 * 8234017 * 2
def baseEnd_8234017 : Nat := 4228008438292016104319951

theorem tailTrace_8234017 : CollatzResearch.WordTrace tailWord_8234017 prefixEnd_8234017 4228008438292016104319951 := by
  unfold tailWord_8234017
  simp only [CollatzResearch.WordTrace]
  refine ⟨300319272210570141990780305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200212848140380094660520203 300319272210570141990780305)
  ·
    refine ⟨225239454157927606493085229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300319272210570141990780305 225239454157927606493085229)
    ·
      refine ⟨84464795309222852434906961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225239454157927606493085229 84464795309222852434906961)
      ·
        refine ⟨63348596481917139326180221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84464795309222852434906961 63348596481917139326180221)
        ·
          refine ⟨23755723680718927247317583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63348596481917139326180221 23755723680718927247317583)
          ·
            refine ⟨35633585521078390870976375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23755723680718927247317583 35633585521078390870976375)
            ·
              refine ⟨53450378281617586306464563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35633585521078390870976375 53450378281617586306464563)
              ·
                refine ⟨80175567422426379459696845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53450378281617586306464563 80175567422426379459696845)
                ·
                  refine ⟨30065837783409892297386317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80175567422426379459696845 30065837783409892297386317)
                  ·
                    refine ⟨11274689168778709611519869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30065837783409892297386317 11274689168778709611519869)
                    ·
                      refine ⟨4228008438292016104319951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11274689168778709611519869 4228008438292016104319951)
                      ·
                        rfl

theorem cell23_8234017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_8234017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234017 prefixEnd_8234017 := by exact prefixLift 8234017
  have htrace : WordTrace (prefixWord ++ tailWord_8234017) baseStart_8234017 baseEnd_8234017 := by
    simpa [prefixWord, tailWord_8234017, baseEnd_8234017] using wordTrace_append hprefix tailTrace_8234017
  have hstable : (prefixWord ++ tailWord_8234017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234017).length < 2 ^ (prefixWord ++ tailWord_8234017).sum := by decide
  have hdescent : baseEnd_8234017 < baseStart_8234017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234044 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_8234044 : Nat := 118140960795 + 8234044 * 2 ^ 59
def prefixEnd_8234044 : Nat := 4983230072969 + 3 ^ 40 * 8234044 * 2
def baseEnd_8234044 : Nat := 4228022302269687498682327

theorem tailTrace_8234044 : CollatzResearch.WordTrace tailWord_8234044 prefixEnd_8234044 4228022302269687498682327 := by
  unfold tailWord_8234044
  simp only [CollatzResearch.WordTrace]
  refine ⟨150160128490736162801006593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200213504654314883734675457 150160128490736162801006593)
  ·
    refine ⟨112620096368052122100754945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150160128490736162801006593 112620096368052122100754945)
    ·
      refine ⟨84465072276039091575566209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112620096368052122100754945 84465072276039091575566209)
      ·
        refine ⟨63348804207029318681674657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84465072276039091575566209 63348804207029318681674657)
        ·
          refine ⟨47511603155271989011255993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63348804207029318681674657 47511603155271989011255993)
          ·
            refine ⟨35633702366453991758441995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47511603155271989011255993 35633702366453991758441995)
            ·
              refine ⟨53450553549680987637662993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35633702366453991758441995 53450553549680987637662993)
              ·
                refine ⟨40087915162260740728247245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53450553549680987637662993 40087915162260740728247245)
                ·
                  refine ⟨15032968185847777773092717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40087915162260740728247245 15032968185847777773092717)
                  ·
                    refine ⟨5637363069692916664909769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15032968185847777773092717 5637363069692916664909769)
                    ·
                      refine ⟨4228022302269687498682327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637363069692916664909769 4228022302269687498682327)
                      ·
                        rfl

theorem cell23_8234044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_8234044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234044 prefixEnd_8234044 := by exact prefixLift 8234044
  have htrace : WordTrace (prefixWord ++ tailWord_8234044) baseStart_8234044 baseEnd_8234044 := by
    simpa [prefixWord, tailWord_8234044, baseEnd_8234044] using wordTrace_append hprefix tailTrace_8234044
  have hstable : (prefixWord ++ tailWord_8234044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234044).length < 2 ^ (prefixWord ++ tailWord_8234044).sum := by decide
  have hdescent : baseEnd_8234044 < baseStart_8234044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234061 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_8234061 : Nat := 118140960795 + 8234061 * 2 ^ 59
def prefixEnd_8234061 : Nat := 4983230072969 + 3 ^ 40 * 8234061 * 2
def baseEnd_8234061 : Nat := 4228031031440813932169749

theorem tailTrace_8234061 : CollatzResearch.WordTrace tailWord_8234061 prefixEnd_8234061 4228031031440813932169749 := by
  unfold tailWord_8234061
  simp only [CollatzResearch.WordTrace]
  refine ⟨300320877022410737505382037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200213918014940491670254691 300320877022410737505382037)
  ·
    refine ⟨14077541110425503320564783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300320877022410737505382037 14077541110425503320564783)
    ·
      refine ⟨21116311665638254980847175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14077541110425503320564783 21116311665638254980847175)
      ·
        refine ⟨31674467498457382471270763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21116311665638254980847175 31674467498457382471270763)
        ·
          refine ⟨47511701247686073706906145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31674467498457382471270763 47511701247686073706906145)
          ·
            refine ⟨35633775935764555280179609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47511701247686073706906145 35633775935764555280179609)
            ·
              refine ⟨26725331951823416460134707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35633775935764555280179609 26725331951823416460134707)
              ·
                refine ⟨40087997927735124690202061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26725331951823416460134707 40087997927735124690202061)
                ·
                  refine ⟨15032999222900671758825773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40087997927735124690202061 15032999222900671758825773)
                  ·
                    refine ⟨5637374708587751909559665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15032999222900671758825773 5637374708587751909559665)
                    ·
                      refine ⟨4228031031440813932169749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637374708587751909559665 4228031031440813932169749)
                      ·
                        rfl

theorem cell23_8234061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_8234061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234061 prefixEnd_8234061 := by exact prefixLift 8234061
  have htrace : WordTrace (prefixWord ++ tailWord_8234061) baseStart_8234061 baseEnd_8234061 := by
    simpa [prefixWord, tailWord_8234061, baseEnd_8234061] using wordTrace_append hprefix tailTrace_8234061
  have hstable : (prefixWord ++ tailWord_8234061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234061).length < 2 ^ (prefixWord ++ tailWord_8234061).sum := by decide
  have hdescent : baseEnd_8234061 < baseStart_8234061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234080 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 9]
def baseStart_8234080 : Nat := 118140960795 + 8234080 * 2 ^ 59
def prefixEnd_8234080 : Nat := 4983230072969 + 3 ^ 40 * 8234080 * 2
def baseEnd_8234080 : Nat := 469782309730361039759129

theorem tailTrace_8234080 : CollatzResearch.WordTrace tailWord_8234080 prefixEnd_8234080 469782309730361039759129 := by
  unfold tailWord_8234080
  simp only [CollatzResearch.WordTrace]
  refine ⟨150160785004670951875161847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200214380006227935833549129 150160785004670951875161847)
  ·
    refine ⟨225241177507006427812742771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150160785004670951875161847 225241177507006427812742771)
    ·
      refine ⟨337861766260509641719114157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225241177507006427812742771 337861766260509641719114157)
      ·
        refine ⟨126698162347691115644667809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337861766260509641719114157 126698162347691115644667809)
        ·
          refine ⟨95023621760768336733500857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126698162347691115644667809 95023621760768336733500857)
          ·
            refine ⟨71267716320576252550125643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95023621760768336733500857 71267716320576252550125643)
            ·
              refine ⟨106901574480864378825188465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71267716320576252550125643 106901574480864378825188465)
              ·
                refine ⟨80176180860648284118891349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106901574480864378825188465 80176180860648284118891349)
                ·
                  refine ⟨469782309730361039759129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80176180860648284118891349 469782309730361039759129)
                  ·
                    rfl

theorem cell23_8234080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_8234080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234080 prefixEnd_8234080 := by exact prefixLift 8234080
  have htrace : WordTrace (prefixWord ++ tailWord_8234080) baseStart_8234080 baseEnd_8234080 := by
    simpa [prefixWord, tailWord_8234080, baseEnd_8234080] using wordTrace_append hprefix tailTrace_8234080
  have hstable : (prefixWord ++ tailWord_8234080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234080).length < 2 ^ (prefixWord ++ tailWord_8234080).sum := by decide
  have hdescent : baseEnd_8234080 < baseStart_8234080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234087 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_8234087 : Nat := 118140960795 + 8234087 * 2 ^ 59
def prefixEnd_8234087 : Nat := 4983230072969 + 3 ^ 40 * 8234087 * 2
def baseEnd_8234087 : Nat := 4228044381937830830444629

theorem tailTrace_8234087 : CollatzResearch.WordTrace tailWord_8234087 prefixEnd_8234087 4228044381937830830444629 := by
  unfold tailWord_8234087
  simp only [CollatzResearch.WordTrace]
  refine ⟨300321825320316543945828515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200214550213544362630552343 300321825320316543945828515)
  ·
    refine ⟨450482737980474815918742773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300321825320316543945828515 450482737980474815918742773)
    ·
      refine ⟨42232756685669513992382135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450482737980474815918742773 42232756685669513992382135)
      ·
        refine ⟨63349135028504270988573203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42232756685669513992382135 63349135028504270988573203)
        ·
          refine ⟨95023702542756406482859805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63349135028504270988573203 95023702542756406482859805)
          ·
            refine ⟨35633888453533652431072427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95023702542756406482859805 35633888453533652431072427)
            ·
              refine ⟨53450832680300478646608641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35633888453533652431072427 53450832680300478646608641)
              ·
                refine ⟨40088124510225358984956481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53450832680300478646608641 40088124510225358984956481)
                ·
                  refine ⟨30066093382669019238717361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40088124510225358984956481 30066093382669019238717361)
                  ·
                    refine ⟨22549570037001764429038021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30066093382669019238717361 22549570037001764429038021)
                    ·
                      refine ⟨4228044381937830830444629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22549570037001764429038021 4228044381937830830444629)
                      ·
                        rfl

theorem cell23_8234087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_8234087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234087 prefixEnd_8234087 := by exact prefixLift 8234087
  have htrace : WordTrace (prefixWord ++ tailWord_8234087) baseStart_8234087 baseEnd_8234087 := by
    simpa [prefixWord, tailWord_8234087, baseEnd_8234087] using wordTrace_append hprefix tailTrace_8234087
  have hstable : (prefixWord ++ tailWord_8234087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234087).length < 2 ^ (prefixWord ++ tailWord_8234087).sum := by decide
  have hdescent : baseEnd_8234087 < baseStart_8234087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234108 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_8234108 : Nat := 118140960795 + 8234108 * 2 ^ 59
def prefixEnd_8234108 : Nat := 4983230072969 + 3 ^ 40 * 8234108 * 2
def baseEnd_8234108 : Nat := 4228055165031575248282033

theorem tailTrace_8234108 : CollatzResearch.WordTrace tailWord_8234108 prefixEnd_8234108 4228055165031575248282033 := by
  unfold tailWord_8234108
  simp only [CollatzResearch.WordTrace]
  refine ⟨150161295626620232266171489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200215060835493643021561985 150161295626620232266171489)
  ·
    refine ⟨112620971719965174199628617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150161295626620232266171489 112620971719965174199628617)
    ·
      refine ⟨84465728789973880649721463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112620971719965174199628617 84465728789973880649721463)
      ·
        refine ⟨126698593184960820974582195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84465728789973880649721463 126698593184960820974582195)
        ·
          refine ⟨190047889777441231461873293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126698593184960820974582195 190047889777441231461873293)
          ·
            refine ⟨71267958666540461798202485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190047889777441231461873293 71267958666540461798202485)
            ·
              refine ⟨6681371124988168293581483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71267958666540461798202485 6681371124988168293581483)
              ·
                refine ⟨10022056687482252440372225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681371124988168293581483 10022056687482252440372225)
                ·
                  refine ⟨7516542515611689330279169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10022056687482252440372225 7516542515611689330279169)
                  ·
                    refine ⟨5637406886708766997709377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7516542515611689330279169 5637406886708766997709377)
                    ·
                      refine ⟨4228055165031575248282033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637406886708766997709377 4228055165031575248282033)
                      ·
                        rfl

theorem cell23_8234108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_8234108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234108 prefixEnd_8234108 := by exact prefixLift 8234108
  have htrace : WordTrace (prefixWord ++ tailWord_8234108) baseStart_8234108 baseEnd_8234108 := by
    simpa [prefixWord, tailWord_8234108, baseEnd_8234108] using wordTrace_append hprefix tailTrace_8234108
  have hstable : (prefixWord ++ tailWord_8234108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234108).length < 2 ^ (prefixWord ++ tailWord_8234108).sum := by decide
  have hdescent : baseEnd_8234108 < baseStart_8234108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234154 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8234154 : Nat := 118140960795 + 8234154 * 2 ^ 59
def prefixEnd_8234154 : Nat := 4983230072969 + 3 ^ 40 * 8234154 * 2
def baseEnd_8234154 : Nat := 4228078785141682068306821

theorem tailTrace_8234154 : CollatzResearch.WordTrace tailWord_8234154 prefixEnd_8234154 4228078785141682068306821 := by
  unfold tailWord_8234154
  simp only [CollatzResearch.WordTrace]
  refine ⟨75081067252768453597129379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200216179340715876259011677 75081067252768453597129379)
  ·
    refine ⟨112621600879152680395694069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75081067252768453597129379 112621600879152680395694069)
    ·
      refine ⟨10558275082420563787096319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112621600879152680395694069 10558275082420563787096319)
      ·
        refine ⟨15837412623630845680644479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558275082420563787096319 15837412623630845680644479)
        ·
          refine ⟨23756118935446268520966719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837412623630845680644479 23756118935446268520966719)
          ·
            refine ⟨35634178403169402781450079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23756118935446268520966719 35634178403169402781450079)
            ·
              refine ⟨53451267604754104172175119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35634178403169402781450079 53451267604754104172175119)
              ·
                refine ⟨80176901407131156258262679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53451267604754104172175119 80176901407131156258262679)
                ·
                  refine ⟨120265352110696734387394019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80176901407131156258262679 120265352110696734387394019)
                  ·
                    refine ⟨180398028166045101581091029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120265352110696734387394019 180398028166045101581091029)
                    ·
                      refine ⟨4228078785141682068306821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180398028166045101581091029 4228078785141682068306821)
                      ·
                        rfl

theorem cell23_8234154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8234154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234154 prefixEnd_8234154 := by exact prefixLift 8234154
  have htrace : WordTrace (prefixWord ++ tailWord_8234154) baseStart_8234154 baseEnd_8234154 := by
    simpa [prefixWord, tailWord_8234154, baseEnd_8234154] using wordTrace_append hprefix tailTrace_8234154
  have hstable : (prefixWord ++ tailWord_8234154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234154).length < 2 ^ (prefixWord ++ tailWord_8234154).sum := by decide
  have hdescent : baseEnd_8234154 < baseStart_8234154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234184 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_8234184 : Nat := 118140960795 + 8234184 * 2 ^ 59
def prefixEnd_8234184 : Nat := 4983230072969 + 3 ^ 40 * 8234184 * 2
def baseEnd_8234184 : Nat := 4228094189561316950931683

theorem tailTrace_8234184 : CollatzResearch.WordTrace tailWord_8234184 prefixEnd_8234184 4228094189561316950931683 := by
  unfold tailWord_8234184
  simp only [CollatzResearch.WordTrace]
  refine ⟨150162681600482564756054803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200216908800643419674739737 150162681600482564756054803)
  ·
    refine ⟨225244022400723847134082205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150162681600482564756054803 225244022400723847134082205)
    ·
      refine ⟨84466508400271442675280827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225244022400723847134082205 84466508400271442675280827)
      ·
        refine ⟨126699762600407164012921241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84466508400271442675280827 126699762600407164012921241)
        ·
          refine ⟨95024821950305373009690931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126699762600407164012921241 95024821950305373009690931)
          ·
            refine ⟨142537232925458059514536397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95024821950305373009690931 142537232925458059514536397)
            ·
              refine ⟨53451462347046772317951149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142537232925458059514536397 53451462347046772317951149)
              ·
                refine ⟨20044298380142539619231681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53451462347046772317951149 20044298380142539619231681)
                ·
                  refine ⟨15033223785106904714423761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20044298380142539619231681 15033223785106904714423761)
                  ·
                    refine ⟨11274917838830178535817821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15033223785106904714423761 11274917838830178535817821)
                    ·
                      refine ⟨4228094189561316950931683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11274917838830178535817821 4228094189561316950931683)
                      ·
                        rfl

theorem cell23_8234184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_8234184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234184 prefixEnd_8234184 := by exact prefixLift 8234184
  have htrace : WordTrace (prefixWord ++ tailWord_8234184) baseStart_8234184 baseEnd_8234184 := by
    simpa [prefixWord, tailWord_8234184, baseEnd_8234184] using wordTrace_append hprefix tailTrace_8234184
  have hstable : (prefixWord ++ tailWord_8234184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234184).length < 2 ^ (prefixWord ++ tailWord_8234184).sum := by decide
  have hdescent : baseEnd_8234184 < baseStart_8234184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234208 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 1, 4]
def baseStart_8234208 : Nat := 118140960795 + 8234208 * 2 ^ 59
def prefixEnd_8234208 : Nat := 4983230072969 + 3 ^ 40 * 8234208 * 2
def baseEnd_8234208 : Nat := 1409368837699008285677191

theorem tailTrace_8234208 : CollatzResearch.WordTrace tailWord_8234208 prefixEnd_8234208 1409368837699008285677191 := by
  unfold tailWord_8234208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150163119276439090805491639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200217492368585454407322185 150163119276439090805491639)
  ·
    refine ⟨225244678914658636208237459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150163119276439090805491639 225244678914658636208237459)
    ·
      refine ⟨337867018371987954312356189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225244678914658636208237459 337867018371987954312356189)
      ·
        refine ⟨126700131889495482867133571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337867018371987954312356189 126700131889495482867133571)
        ·
          refine ⟨190050197834243224300700357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126700131889495482867133571 190050197834243224300700357)
          ·
            refine ⟨35634412093920604556381317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190050197834243224300700357 35634412093920604556381317)
            ·
              refine ⟨6681452267610113354321497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35634412093920604556381317 6681452267610113354321497)
              ·
                refine ⟨5011089200707585015741123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681452267610113354321497 5011089200707585015741123)
                ·
                  refine ⟨7516633801061377523611685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011089200707585015741123 7516633801061377523611685)
                  ·
                    refine ⟨1409368837699008285677191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516633801061377523611685 1409368837699008285677191)
                    ·
                      rfl

theorem cell23_8234208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_8234208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234208 prefixEnd_8234208 := by exact prefixLift 8234208
  have htrace : WordTrace (prefixWord ++ tailWord_8234208) baseStart_8234208 baseEnd_8234208 := by
    simpa [prefixWord, tailWord_8234208, baseEnd_8234208] using wordTrace_append hprefix tailTrace_8234208
  have hstable : (prefixWord ++ tailWord_8234208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234208).length < 2 ^ (prefixWord ++ tailWord_8234208).sum := by decide
  have hdescent : baseEnd_8234208 < baseStart_8234208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234234 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_8234234 : Nat := 118140960795 + 8234234 * 2 ^ 59
def prefixEnd_8234234 : Nat := 4983230072969 + 3 ^ 40 * 8234234 * 2
def baseEnd_8234234 : Nat := 1409373287864680585102151

theorem tailTrace_8234234 : CollatzResearch.WordTrace tailWord_8234234 prefixEnd_8234234 1409373287864680585102151 := by
  unfold tailWord_8234234
  simp only [CollatzResearch.WordTrace]
  refine ⟨75081796712695997012857439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200218124567189325367619837 75081796712695997012857439)
  ·
    refine ⟨112622695069043995519286159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75081796712695997012857439 112622695069043995519286159)
    ·
      refine ⟨168934042603565993278929239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112622695069043995519286159 168934042603565993278929239)
      ·
        refine ⟨253401063905348989918393859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168934042603565993278929239 253401063905348989918393859)
        ·
          refine ⟨380101595858023484877590789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253401063905348989918393859 380101595858023484877590789)
          ·
            refine ⟨71269049223379403414548273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380101595858023484877590789 71269049223379403414548273)
            ·
              refine ⟨53451786917534552560911205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71269049223379403414548273 53451786917534552560911205)
              ·
                refine ⟨10022210047037728605170851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53451786917534552560911205 10022210047037728605170851)
                ·
                  refine ⟨15033315070556592907756277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022210047037728605170851 15033315070556592907756277)
                  ·
                    refine ⟨1409373287864680585102151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15033315070556592907756277 1409373287864680585102151)
                    ·
                      rfl

theorem cell23_8234234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_8234234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234234 prefixEnd_8234234 := by exact prefixLift 8234234
  have htrace : WordTrace (prefixWord ++ tailWord_8234234) baseStart_8234234 baseEnd_8234234 := by
    simpa [prefixWord, tailWord_8234234, baseEnd_8234234] using wordTrace_append hprefix tailTrace_8234234
  have hstable : (prefixWord ++ tailWord_8234234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234234).length < 2 ^ (prefixWord ++ tailWord_8234234).sum := by decide
  have hdescent : baseEnd_8234234 < baseStart_8234234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234241 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_8234241 : Nat := 118140960795 + 8234241 * 2 ^ 59
def prefixEnd_8234241 : Nat := 4983230072969 + 3 ^ 40 * 8234241 * 2
def baseEnd_8234241 : Nat := 4228123457958623227918921

theorem tailTrace_8234241 : CollatzResearch.WordTrace tailWord_8234241 prefixEnd_8234241 4228123457958623227918921 := by
  unfold tailWord_8234241
  simp only [CollatzResearch.WordTrace]
  refine ⟨300327442161758628246934577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200218294774505752164623051 300327442161758628246934577)
  ·
    refine ⟨225245581621318971185200933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300327442161758628246934577 225245581621318971185200933)
    ·
      refine ⟨42233546553997307097225175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225245581621318971185200933 42233546553997307097225175)
      ·
        refine ⟨63350319830995960645837763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42233546553997307097225175 63350319830995960645837763)
        ·
          refine ⟨95025479746493940968756645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63350319830995960645837763 95025479746493940968756645)
          ·
            refine ⟨17817277452467613931641871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95025479746493940968756645 17817277452467613931641871)
            ·
              refine ⟨26725916178701420897462807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817277452467613931641871 26725916178701420897462807)
              ·
                refine ⟨40088874268052131346194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26725916178701420897462807 40088874268052131346194211)
                ·
                  refine ⟨60133311402078197019291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40088874268052131346194211 60133311402078197019291317)
                  ·
                    refine ⟨5637497943944830970558561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60133311402078197019291317 5637497943944830970558561)
                    ·
                      refine ⟨4228123457958623227918921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637497943944830970558561 4228123457958623227918921)
                      ·
                        rfl

theorem cell23_8234241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_8234241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234241 prefixEnd_8234241 := by exact prefixLift 8234241
  have htrace : WordTrace (prefixWord ++ tailWord_8234241) baseStart_8234241 baseEnd_8234241 := by
    simpa [prefixWord, tailWord_8234241, baseEnd_8234241] using wordTrace_append hprefix tailTrace_8234241
  have hstable : (prefixWord ++ tailWord_8234241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234241).length < 2 ^ (prefixWord ++ tailWord_8234241).sum := by decide
  have hdescent : baseEnd_8234241 < baseStart_8234241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234251 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 1, 5]
def baseStart_8234251 : Nat := 118140960795 + 8234251 * 2 ^ 59
def prefixEnd_8234251 : Nat := 4983230072969 + 3 ^ 40 * 8234251 * 2
def baseEnd_8234251 : Nat := 1409376197588389396264625

theorem tailTrace_8234251 : CollatzResearch.WordTrace tailWord_8234251 prefixEnd_8234251 1409376197588389396264625 := by
  unfold tailWord_8234251
  simp only [CollatzResearch.WordTrace]
  refine ⟨300327806891722399954798607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200218537927814933303199071 300327806891722399954798607)
  ·
    refine ⟨450491710337583599932197911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300327806891722399954798607 450491710337583599932197911)
    ·
      refine ⟨675737565506375399898296867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450491710337583599932197911 675737565506375399898296867)
      ·
        refine ⟨1013606348259563099847445301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675737565506375399898296867 1013606348259563099847445301)
        ·
          refine ⟨95025595149334040610697997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1013606348259563099847445301 95025595149334040610697997)
          ·
            refine ⟨35634598181000265229011749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95025595149334040610697997 35634598181000265229011749)
            ·
              refine ⟨6681487158937549730439703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35634598181000265229011749 6681487158937549730439703)
              ·
                refine ⟨10022230738406324595659555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681487158937549730439703 10022230738406324595659555)
                ·
                  refine ⟨15033346107609486893489333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022230738406324595659555 15033346107609486893489333)
                  ·
                    refine ⟨1409376197588389396264625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15033346107609486893489333 1409376197588389396264625)
                    ·
                      rfl

theorem cell23_8234251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 5].length) (baseStart_8234251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234251 prefixEnd_8234251 := by exact prefixLift 8234251
  have htrace : WordTrace (prefixWord ++ tailWord_8234251) baseStart_8234251 baseEnd_8234251 := by
    simpa [prefixWord, tailWord_8234251, baseEnd_8234251] using wordTrace_append hprefix tailTrace_8234251
  have hstable : (prefixWord ++ tailWord_8234251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234251).length < 2 ^ (prefixWord ++ tailWord_8234251).sum := by decide
  have hdescent : baseEnd_8234251 < baseStart_8234251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234267 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_8234267 : Nat := 118140960795 + 8234267 * 2 ^ 59
def prefixEnd_8234267 : Nat := 4983230072969 + 3 ^ 40 * 8234267 * 2
def baseEnd_8234267 : Nat := 4228136808455640126193801

theorem tailTrace_8234267 : CollatzResearch.WordTrace tailWord_8234267 prefixEnd_8234267 4228136808455640126193801 := by
  unfold tailWord_8234267
  simp only [CollatzResearch.WordTrace]
  refine ⟨300328390459664434687381055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200218926973109623124920703 300328390459664434687381055)
  ·
    refine ⟨450492585689496652031071583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300328390459664434687381055 450492585689496652031071583)
    ·
      refine ⟨675738878534244978046607375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450492585689496652031071583 675738878534244978046607375)
      ·
        refine ⟨1013608317801367467069911063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675738878534244978046607375 1013608317801367467069911063)
        ·
          refine ⟨1520412476702051200604866595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013608317801367467069911063 1520412476702051200604866595)
          ·
            refine ⟨2280618715053076800907299893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520412476702051200604866595 2280618715053076800907299893)
            ·
              refine ⟨213808004536225950085059365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2280618715053076800907299893 213808004536225950085059365)
              ·
                refine ⟨40089000850542365640948631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213808004536225950085059365 40089000850542365640948631)
                ·
                  refine ⟨60133501275813548461422947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40089000850542365640948631 60133501275813548461422947)
                  ·
                    refine ⟨90200251913720322692134421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60133501275813548461422947 90200251913720322692134421)
                    ·
                      refine ⟨4228136808455640126193801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90200251913720322692134421 4228136808455640126193801)
                      ·
                        rfl

theorem cell23_8234267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_8234267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234267 prefixEnd_8234267 := by exact prefixLift 8234267
  have htrace : WordTrace (prefixWord ++ tailWord_8234267) baseStart_8234267 baseEnd_8234267 := by
    simpa [prefixWord, tailWord_8234267, baseEnd_8234267] using wordTrace_append hprefix tailTrace_8234267
  have hstable : (prefixWord ++ tailWord_8234267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234267).length < 2 ^ (prefixWord ++ tailWord_8234267).sum := by decide
  have hdescent : baseEnd_8234267 < baseStart_8234267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234291 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 3]
def baseStart_8234291 : Nat := 118140960795 + 8234291 * 2 ^ 59
def prefixEnd_8234291 : Nat := 4983230072969 + 3 ^ 40 * 8234291 * 2
def baseEnd_8234291 : Nat := 4228149131991348032293691

theorem tailTrace_8234291 : CollatzResearch.WordTrace tailWord_8234291 prefixEnd_8234291 4228149131991348032293691 := by
  unfold tailWord_8234291
  simp only [CollatzResearch.WordTrace]
  refine ⟨300329265811577486786254727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200219510541051657857503151 300329265811577486786254727)
  ·
    refine ⟨450493898717366230179382091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300329265811577486786254727 450493898717366230179382091)
    ·
      refine ⟨675740848076049345269073137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450493898717366230179382091 675740848076049345269073137)
      ·
        refine ⟨506805636057037008951804853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675740848076049345269073137 506805636057037008951804853)
        ·
          refine ⟨47513028380347219589231705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506805636057037008951804853 47513028380347219589231705)
          ·
            refine ⟨35634771285260414691923779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47513028380347219589231705 35634771285260414691923779)
            ·
              refine ⟨53452156927890622037885669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35634771285260414691923779 53452156927890622037885669)
              ·
                refine ⟨10022279423979491632103563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53452156927890622037885669 10022279423979491632103563)
                ·
                  refine ⟨15033419135969237448155345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022279423979491632103563 15033419135969237448155345)
                  ·
                    refine ⟨11275064351976928086116509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15033419135969237448155345 11275064351976928086116509)
                    ·
                      refine ⟨4228149131991348032293691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275064351976928086116509 4228149131991348032293691)
                      ·
                        rfl

theorem cell23_8234291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_8234291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234291 prefixEnd_8234291 := by exact prefixLift 8234291
  have htrace : WordTrace (prefixWord ++ tailWord_8234291) baseStart_8234291 baseEnd_8234291 := by
    simpa [prefixWord, tailWord_8234291, baseEnd_8234291] using wordTrace_append hprefix tailTrace_8234291
  have hstable : (prefixWord ++ tailWord_8234291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234291).length < 2 ^ (prefixWord ++ tailWord_8234291).sum := by decide
  have hdescent : baseEnd_8234291 < baseStart_8234291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234304 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_8234304 : Nat := 118140960795 + 8234304 * 2 ^ 59
def prefixEnd_8234304 : Nat := 4983230072969 + 3 ^ 40 * 8234304 * 2
def baseEnd_8234304 : Nat := 4228155807239856481431131

theorem tailTrace_8234304 : CollatzResearch.WordTrace tailWord_8234304 prefixEnd_8234304 4228155807239856481431131 := by
  unfold tailWord_8234304
  simp only [CollatzResearch.WordTrace]
  refine ⟨150164869980265195003238983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200219826640353593337651977 150164869980265195003238983)
  ·
    refine ⟨225247304970397792504858475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150164869980265195003238983 225247304970397792504858475)
    ·
      refine ⟨337870957455596688757287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225247304970397792504858475 337870957455596688757287713)
      ·
        refine ⟨253403218091697516567965785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337870957455596688757287713 253403218091697516567965785)
        ·
          refine ⟨190052413568773137425974339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253403218091697516567965785 190052413568773137425974339)
          ·
            refine ⟨285078620353159706138961509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190052413568773137425974339 285078620353159706138961509)
            ·
              refine ⟨53452241316217444901055283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285078620353159706138961509 53452241316217444901055283)
              ·
                refine ⟨80178361974326167351582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53452241316217444901055283 80178361974326167351582925)
                ·
                  refine ⟨30066885740372312756843597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80178361974326167351582925 30066885740372312756843597)
                  ·
                    refine ⟨11275082152639617283816349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30066885740372312756843597 11275082152639617283816349)
                    ·
                      refine ⟨4228155807239856481431131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275082152639617283816349 4228155807239856481431131)
                      ·
                        rfl

theorem cell23_8234304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_8234304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234304 prefixEnd_8234304 := by exact prefixLift 8234304
  have htrace : WordTrace (prefixWord ++ tailWord_8234304) baseStart_8234304 baseEnd_8234304 := by
    simpa [prefixWord, tailWord_8234304, baseEnd_8234304] using wordTrace_append hprefix tailTrace_8234304
  have hstable : (prefixWord ++ tailWord_8234304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234304).length < 2 ^ (prefixWord ++ tailWord_8234304).sum := by decide
  have hdescent : baseEnd_8234304 < baseStart_8234304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234307 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 9]
def baseStart_8234307 : Nat := 118140960795 + 8234307 * 2 ^ 59
def prefixEnd_8234307 : Nat := 4983230072969 + 3 ^ 40 * 8234307 * 2
def baseEnd_8234307 : Nat := 1409385782560606656564539

theorem tailTrace_8234307 : CollatzResearch.WordTrace tailWord_8234307 prefixEnd_8234307 1409385782560606656564539 := by
  unfold tailWord_8234307
  simp only [CollatzResearch.WordTrace]
  refine ⟨300329849379519521518837175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200219899586346347679224783 300329849379519521518837175)
  ·
    refine ⟨450494774069279282278255763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300329849379519521518837175 450494774069279282278255763)
    ·
      refine ⟨675742161103918923417383645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450494774069279282278255763 675742161103918923417383645)
      ·
        refine ⟨253403310413969596281518867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675742161103918923417383645 253403310413969596281518867)
        ·
          refine ⟨380104965620954394422278301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253403310413969596281518867 380104965620954394422278301)
          ·
            refine ⟨142539362107857897908354363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380104965620954394422278301 142539362107857897908354363)
            ·
              refine ⟨213809043161786846862531545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142539362107857897908354363 213809043161786846862531545)
              ·
                refine ⟨160356782371340135146898659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213809043161786846862531545 160356782371340135146898659)
                ·
                  refine ⟨240535173557010202720347989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160356782371340135146898659 240535173557010202720347989)
                  ·
                    refine ⟨1409385782560606656564539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240535173557010202720347989 1409385782560606656564539)
                    ·
                      rfl

theorem cell23_8234307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_8234307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234307 prefixEnd_8234307 := by exact prefixLift 8234307
  have htrace : WordTrace (prefixWord ++ tailWord_8234307) baseStart_8234307 baseEnd_8234307 := by
    simpa [prefixWord, tailWord_8234307, baseEnd_8234307] using wordTrace_append hprefix tailTrace_8234307
  have hstable : (prefixWord ++ tailWord_8234307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234307).length < 2 ^ (prefixWord ++ tailWord_8234307).sum := by decide
  have hdescent : baseEnd_8234307 < baseStart_8234307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234308 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_8234308 : Nat := 118140960795 + 8234308 * 2 ^ 59
def prefixEnd_8234308 : Nat := 4983230072969 + 3 ^ 40 * 8234308 * 2
def baseEnd_8234308 : Nat := 4228157861162474465781113

theorem tailTrace_8234308 : CollatzResearch.WordTrace tailWord_8234308 prefixEnd_8234308 4228157861162474465781113 := by
  unfold tailWord_8234308
  simp only [CollatzResearch.WordTrace]
  refine ⟨150164942926257949344811789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200219923901677265793082385 150164942926257949344811789)
  ·
    refine ⟨56311853597346731004304421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150164942926257949344811789 56311853597346731004304421)
    ·
      refine ⟨10558472549502512063307079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56311853597346731004304421 10558472549502512063307079)
      ·
        refine ⟨15837708824253768094960619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558472549502512063307079 15837708824253768094960619)
        ·
          refine ⟨23756563236380652142440929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837708824253768094960619 23756563236380652142440929)
          ·
            refine ⟨17817422427285489106830697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23756563236380652142440929 17817422427285489106830697)
            ·
              refine ⟨13363066820464116830123023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17817422427285489106830697 13363066820464116830123023)
              ·
                refine ⟨20044600230696175245184535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13363066820464116830123023 20044600230696175245184535)
                ·
                  refine ⟨30066900346044262867776803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20044600230696175245184535 30066900346044262867776803)
                  ·
                    refine ⟨45100350519066394301665205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30066900346044262867776803 45100350519066394301665205)
                    ·
                      refine ⟨4228157861162474465781113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45100350519066394301665205 4228157861162474465781113)
                      ·
                        rfl

theorem cell23_8234308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_8234308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234308 prefixEnd_8234308 := by exact prefixLift 8234308
  have htrace : WordTrace (prefixWord ++ tailWord_8234308) baseStart_8234308 baseEnd_8234308 := by
    simpa [prefixWord, tailWord_8234308, baseEnd_8234308] using wordTrace_append hprefix tailTrace_8234308
  have hstable : (prefixWord ++ tailWord_8234308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234308).length < 2 ^ (prefixWord ++ tailWord_8234308).sum := by decide
  have hdescent : baseEnd_8234308 < baseStart_8234308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234321 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_8234321 : Nat := 118140960795 + 8234321 * 2 ^ 59
def prefixEnd_8234321 : Nat := 4983230072969 + 3 ^ 40 * 8234321 * 2
def baseEnd_8234321 : Nat := 4228164536410982914918553

theorem tailTrace_8234321 : CollatzResearch.WordTrace tailWord_8234321 prefixEnd_8234321 4228164536410982914918553 := by
  unfold tailWord_8234321
  simp only [CollatzResearch.WordTrace]
  refine ⟨300330360001468801909846817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200220240000979201273231211 300330360001468801909846817)
  ·
    refine ⟨225247770001101601432385113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300330360001468801909846817 225247770001101601432385113)
    ·
      refine ⟨168935827500826201074288835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225247770001101601432385113 168935827500826201074288835)
      ·
        refine ⟨253403741251239301611433253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168935827500826201074288835 253403741251239301611433253)
        ·
          refine ⟨47513201484607369052143735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253403741251239301611433253 47513201484607369052143735)
          ·
            refine ⟨71269802226911053578215603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47513201484607369052143735 71269802226911053578215603)
            ·
              refine ⟨106904703340366580367323405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71269802226911053578215603 106904703340366580367323405)
              ·
                refine ⟨40089263752637467637746277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106904703340366580367323405 40089263752637467637746277)
                ·
                  refine ⟨7516736953619525182077427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40089263752637467637746277 7516736953619525182077427)
                  ·
                    refine ⟨11275105430429287773116141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516736953619525182077427 11275105430429287773116141)
                    ·
                      refine ⟨4228164536410982914918553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275105430429287773116141 4228164536410982914918553)
                      ·
                        rfl

theorem cell23_8234321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_8234321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234321 prefixEnd_8234321 := by exact prefixLift 8234321
  have htrace : WordTrace (prefixWord ++ tailWord_8234321) baseStart_8234321 baseEnd_8234321 := by
    simpa [prefixWord, tailWord_8234321, baseEnd_8234321] using wordTrace_append hprefix tailTrace_8234321
  have hstable : (prefixWord ++ tailWord_8234321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234321).length < 2 ^ (prefixWord ++ tailWord_8234321).sum := by decide
  have hdescent : baseEnd_8234321 < baseStart_8234321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234324 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_8234324 : Nat := 118140960795 + 8234324 * 2 ^ 59
def prefixEnd_8234324 : Nat := 4983230072969 + 3 ^ 40 * 8234324 * 2
def baseEnd_8234324 : Nat := 1409388692284315467727013

theorem tailTrace_8234324 : CollatzResearch.WordTrace tailWord_8234324 prefixEnd_8234324 1409388692284315467727013 := by
  unfold tailWord_8234324
  simp only [CollatzResearch.WordTrace]
  refine ⟨150165234710228966711103013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200220312946971955614804017 150165234710228966711103013)
  ·
    refine ⟨28155981508167931258331815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150165234710228966711103013 28155981508167931258331815)
    ·
      refine ⟨42233972262251896887497723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28155981508167931258331815 42233972262251896887497723)
      ·
        refine ⟨63350958393377845331246585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42233972262251896887497723 63350958393377845331246585)
        ·
          refine ⟨47513218795033383998434939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63350958393377845331246585 47513218795033383998434939)
          ·
            refine ⟨71269828192550075997652409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47513218795033383998434939 71269828192550075997652409)
            ·
              refine ⟨53452371144412556998239307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71269828192550075997652409 53452371144412556998239307)
              ·
                refine ⟨80178556716618835497358961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53452371144412556998239307 80178556716618835497358961)
                ·
                  refine ⟨60133917537464126623019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80178556716618835497358961 60133917537464126623019221)
                  ·
                    refine ⟨1409388692284315467727013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60133917537464126623019221 1409388692284315467727013)
                    ·
                      rfl

theorem cell23_8234324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_8234324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234324 prefixEnd_8234324 := by exact prefixLift 8234324
  have htrace : WordTrace (prefixWord ++ tailWord_8234324) baseStart_8234324 baseEnd_8234324 := by
    simpa [prefixWord, tailWord_8234324, baseEnd_8234324] using wordTrace_append hprefix tailTrace_8234324
  have hstable : (prefixWord ++ tailWord_8234324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234324).length < 2 ^ (prefixWord ++ tailWord_8234324).sum := by decide
  have hdescent : baseEnd_8234324 < baseStart_8234324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234348 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_8234348 : Nat := 118140960795 + 8234348 * 2 ^ 59
def prefixEnd_8234348 : Nat := 4983230072969 + 3 ^ 40 * 8234348 * 2
def baseEnd_8234348 : Nat := 4228178400388654309280929

theorem tailTrace_8234348 : CollatzResearch.WordTrace tailWord_8234348 prefixEnd_8234348 4228178400388654309280929 := by
  unfold tailWord_8234348
  simp only [CollatzResearch.WordTrace]
  refine ⟨150165672386185492760539849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200220896514913990347386465 150165672386185492760539849)
  ·
    refine ⟨112624254289639119570404887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150165672386185492760539849 112624254289639119570404887)
    ·
      refine ⟨168936381434458679355607331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112624254289639119570404887 168936381434458679355607331)
      ·
        refine ⟨253404572151688019033410997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168936381434458679355607331 253404572151688019033410997)
        ·
          refine ⟨23756678639220751784382281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253404572151688019033410997 23756678639220751784382281)
          ·
            refine ⟨17817508979415563838286711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23756678639220751784382281 17817508979415563838286711)
            ·
              refine ⟨26726263469123345757430067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817508979415563838286711 26726263469123345757430067)
              ·
                refine ⟨40089395203685018636145101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26726263469123345757430067 40089395203685018636145101)
                ·
                  refine ⟨15033523201381881988554413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40089395203685018636145101 15033523201381881988554413)
                  ·
                    refine ⟨5637571200518205745707905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15033523201381881988554413 5637571200518205745707905)
                    ·
                      refine ⟨4228178400388654309280929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637571200518205745707905 4228178400388654309280929)
                      ·
                        rfl

theorem cell23_8234348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_8234348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234348 prefixEnd_8234348 := by exact prefixLift 8234348
  have htrace : WordTrace (prefixWord ++ tailWord_8234348) baseStart_8234348 baseEnd_8234348 := by
    simpa [prefixWord, tailWord_8234348, baseEnd_8234348] using wordTrace_append hprefix tailTrace_8234348
  have hstable : (prefixWord ++ tailWord_8234348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234348).length < 2 ^ (prefixWord ++ tailWord_8234348).sum := by decide
  have hdescent : baseEnd_8234348 < baseStart_8234348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234361 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 4, 2]
def baseStart_8234361 : Nat := 118140960795 + 8234361 * 2 ^ 59
def prefixEnd_8234361 : Nat := 4983230072969 + 3 ^ 40 * 8234361 * 2
def baseEnd_8234361 : Nat := 4228185075637162758418369

theorem tailTrace_8234361 : CollatzResearch.WordTrace tailWord_8234361 prefixEnd_8234361 4228185075637162758418369 := by
  unfold tailWord_8234361
  simp only [CollatzResearch.WordTrace]
  refine ⟨300331818921323888741302937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200221212614215925827535291 300331818921323888741302937)
  ·
    refine ⟨225248864190992916555977203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300331818921323888741302937 225248864190992916555977203)
    ·
      refine ⟨337873296286489374833965805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225248864190992916555977203 337873296286489374833965805)
      ·
        refine ⟨126702486107433515562737177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337873296286489374833965805 126702486107433515562737177)
        ·
          refine ⟨95026864580575136672052883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126702486107433515562737177 95026864580575136672052883)
          ·
            refine ⟨142540296870862705008079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95026864580575136672052883 142540296870862705008079325)
            ·
              refine ⟨53452611326573514378029747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142540296870862705008079325 53452611326573514378029747)
              ·
                refine ⟨80178916989860271567044621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53452611326573514378029747 80178916989860271567044621)
                ·
                  refine ⟨30067093871197601837641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80178916989860271567044621 30067093871197601837641733)
                  ·
                    refine ⟨5637580100849550344557825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30067093871197601837641733 5637580100849550344557825)
                    ·
                      refine ⟨4228185075637162758418369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637580100849550344557825 4228185075637162758418369)
                      ·
                        rfl

theorem cell23_8234361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_8234361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234361 prefixEnd_8234361 := by exact prefixLift 8234361
  have htrace : WordTrace (prefixWord ++ tailWord_8234361) baseStart_8234361 baseEnd_8234361 := by
    simpa [prefixWord, tailWord_8234361, baseEnd_8234361] using wordTrace_append hprefix tailTrace_8234361
  have hstable : (prefixWord ++ tailWord_8234361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234361).length < 2 ^ (prefixWord ++ tailWord_8234361).sum := by decide
  have hdescent : baseEnd_8234361 < baseStart_8234361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234364 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_8234364 : Nat := 118140960795 + 8234364 * 2 ^ 59
def prefixEnd_8234364 : Nat := 4983230072969 + 3 ^ 40 * 8234364 * 2
def baseEnd_8234364 : Nat := 4228186616079126246680855

theorem tailTrace_8234364 : CollatzResearch.WordTrace tailWord_8234364 prefixEnd_8234364 4228186616079126246680855 := by
  unfold tailWord_8234364
  simp only [CollatzResearch.WordTrace]
  refine ⟨150165964170156510126831073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200221285560208680169108097 150165964170156510126831073)
  ·
    refine ⟨112624473127617382595123305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150165964170156510126831073 112624473127617382595123305)
    ·
      refine ⟨84468354845713036946342479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112624473127617382595123305 84468354845713036946342479)
      ·
        refine ⟨126702532268569555419513719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84468354845713036946342479 126702532268569555419513719)
        ·
          refine ⟨190053798402854333129270579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126702532268569555419513719 190053798402854333129270579)
          ·
            refine ⟨285080697604281499693905869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190053798402854333129270579 285080697604281499693905869)
            ·
              refine ⟨106905261601605562385214701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285080697604281499693905869 106905261601605562385214701)
              ·
                refine ⟨40089473100602085894455513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106905261601605562385214701 40089473100602085894455513)
                ·
                  refine ⟨30067104825451564420841635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40089473100602085894455513 30067104825451564420841635)
                  ·
                    refine ⟨45100657238177346631262453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30067104825451564420841635 45100657238177346631262453)
                    ·
                      refine ⟨4228186616079126246680855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45100657238177346631262453 4228186616079126246680855)
                      ·
                        rfl

theorem cell23_8234364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_8234364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234364 prefixEnd_8234364 := by exact prefixLift 8234364
  have htrace : WordTrace (prefixWord ++ tailWord_8234364) baseStart_8234364 baseEnd_8234364 := by
    simpa [prefixWord, tailWord_8234364, baseEnd_8234364] using wordTrace_append hprefix tailTrace_8234364
  have hstable : (prefixWord ++ tailWord_8234364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234364).length < 2 ^ (prefixWord ++ tailWord_8234364).sum := by decide
  have hdescent : baseEnd_8234364 < baseStart_8234364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234365 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_8234365 : Nat := 118140960795 + 8234365 * 2 ^ 59
def prefixEnd_8234365 : Nat := 4983230072969 + 3 ^ 40 * 8234365 * 2
def baseEnd_8234365 : Nat := 4228187129559780742768351

theorem tailTrace_8234365 : CollatzResearch.WordTrace tailWord_8234365 prefixEnd_8234365 4228187129559780742768351 := by
  unfold tailWord_8234365
  simp only [CollatzResearch.WordTrace]
  refine ⟨300331964813309397424448549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200221309875539598282965699 300331964813309397424448549)
  ·
    refine ⟨56312243402495512017084103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300331964813309397424448549 56312243402495512017084103)
    ·
      refine ⟨84468365103743268025626155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56312243402495512017084103 84468365103743268025626155)
      ·
        refine ⟨126702547655614902038439233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84468365103743268025626155 126702547655614902038439233)
        ·
          refine ⟨95026910741711176528829425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126702547655614902038439233 95026910741711176528829425)
          ·
            refine ⟨71270183056283382396622069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95026910741711176528829425 71270183056283382396622069)
            ·
              refine ⟨6681579661526567099683319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71270183056283382396622069 6681579661526567099683319)
              ·
                refine ⟨10022369492289850649524979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681579661526567099683319 10022369492289850649524979)
                ·
                  refine ⟨15033554238434775974287469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022369492289850649524979 15033554238434775974287469)
                  ·
                    refine ⟨5637582839413040990357801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15033554238434775974287469 5637582839413040990357801)
                    ·
                      refine ⟨4228187129559780742768351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637582839413040990357801 4228187129559780742768351)
                      ·
                        rfl

theorem cell23_8234365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_8234365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234365 prefixEnd_8234365 := by exact prefixLift 8234365
  have htrace : WordTrace (prefixWord ++ tailWord_8234365) baseStart_8234365 baseEnd_8234365 := by
    simpa [prefixWord, tailWord_8234365, baseEnd_8234365] using wordTrace_append hprefix tailTrace_8234365
  have hstable : (prefixWord ++ tailWord_8234365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234365).length < 2 ^ (prefixWord ++ tailWord_8234365).sum := by decide
  have hdescent : baseEnd_8234365 < baseStart_8234365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234424 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_8234424 : Nat := 118140960795 + 8234424 * 2 ^ 59
def prefixEnd_8234424 : Nat := 4983230072969 + 3 ^ 40 * 8234424 * 2
def baseEnd_8234424 : Nat := 4228217424918396011930579

theorem tailTrace_8234424 : CollatzResearch.WordTrace tailWord_8234424 prefixEnd_8234424 4228217424918396011930579 := by
  unfold tailWord_8234424
  simp only [CollatzResearch.WordTrace]
  refine ⟨150167058360047825250423163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200222744480063767000564217 150167058360047825250423163)
  ·
    refine ⟨225250587540071737875634745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150167058360047825250423163 225250587540071737875634745)
    ·
      refine ⟨168937940655053803406726059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225250587540071737875634745 168937940655053803406726059)
      ·
        refine ⟨253406910982580705110089089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168937940655053803406726059 253406910982580705110089089)
        ·
          refine ⟨190055183236935528832566817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253406910982580705110089089 190055183236935528832566817)
          ·
            refine ⟨142541387427701646624425113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190055183236935528832566817 142541387427701646624425113)
            ·
              refine ⟨106906040570776234968318835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142541387427701646624425113 106906040570776234968318835)
              ·
                refine ⟨160359060856164352452478253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106906040570776234968318835 160359060856164352452478253)
                ·
                  refine ⟨60134647821061632169679345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160359060856164352452478253 60134647821061632169679345)
                  ·
                    refine ⟨45100985865796224127259509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60134647821061632169679345 45100985865796224127259509)
                    ·
                      refine ⟨4228217424918396011930579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45100985865796224127259509 4228217424918396011930579)
                      ·
                        rfl

theorem cell23_8234424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_8234424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234424 prefixEnd_8234424 := by exact prefixLift 8234424
  have htrace : WordTrace (prefixWord ++ tailWord_8234424) baseStart_8234424 baseEnd_8234424 := by
    simpa [prefixWord, tailWord_8234424, baseEnd_8234424] using wordTrace_append hprefix tailTrace_8234424
  have hstable : (prefixWord ++ tailWord_8234424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234424).length < 2 ^ (prefixWord ++ tailWord_8234424).sum := by decide
  have hdescent : baseEnd_8234424 < baseStart_8234424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234464 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_8234464 : Nat := 118140960795 + 8234464 * 2 ^ 59
def prefixEnd_8234464 : Nat := 4983230072969 + 3 ^ 40 * 8234464 * 2
def baseEnd_8234464 : Nat := 4228237964144575855430395

theorem tailTrace_8234464 : CollatzResearch.WordTrace tailWord_8234464 prefixEnd_8234464 4228237964144575855430395 := by
  unfold tailWord_8234464
  simp only [CollatzResearch.WordTrace]
  refine ⟨150167787819975368666151223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200223717093300491554868297 150167787819975368666151223)
  ·
    refine ⟨225251681729963052999226835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150167787819975368666151223 225251681729963052999226835)
    ·
      refine ⟨337877522594944579498840253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225251681729963052999226835 337877522594944579498840253)
      ·
        refine ⟨126704070973104217312065095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337877522594944579498840253 126704070973104217312065095)
        ·
          refine ⟨190056106459656325968097643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126704070973104217312065095 190056106459656325968097643)
          ·
            refine ⟨285084159689484488952146465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190056106459656325968097643 285084159689484488952146465)
            ·
              refine ⟨213813119767113366714109849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285084159689484488952146465 213813119767113366714109849)
              ·
                refine ⟨160359839825335025035582387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213813119767113366714109849 160359839825335025035582387)
                ·
                  refine ⟨240539759738002537553373581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160359839825335025035582387 240539759738002537553373581)
                  ·
                    refine ⟨90202409901750951582515093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240539759738002537553373581 90202409901750951582515093)
                    ·
                      refine ⟨4228237964144575855430395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90202409901750951582515093 4228237964144575855430395)
                      ·
                        rfl

theorem cell23_8234464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_8234464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234464 prefixEnd_8234464 := by exact prefixLift 8234464
  have htrace : WordTrace (prefixWord ++ tailWord_8234464) baseStart_8234464 baseEnd_8234464 := by
    simpa [prefixWord, tailWord_8234464, baseEnd_8234464] using wordTrace_append hprefix tailTrace_8234464
  have hstable : (prefixWord ++ tailWord_8234464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234464).length < 2 ^ (prefixWord ++ tailWord_8234464).sum := by decide
  have hdescent : baseEnd_8234464 < baseStart_8234464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234485 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8234485 : Nat := 118140960795 + 8234485 * 2 ^ 59
def prefixEnd_8234485 : Nat := 4983230072969 + 3 ^ 40 * 8234485 * 2
def baseEnd_8234485 : Nat := 4228248747238320273267799

theorem tailTrace_8234485 : CollatzResearch.WordTrace tailWord_8234485 prefixEnd_8234485 4228248747238320273267799 := by
  unfold tailWord_8234485
  simp only [CollatzResearch.WordTrace]
  refine ⟨300336341572874657918816909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200224227715249771945877939 300336341572874657918816909)
  ·
    refine ⟨112626128089827996719556341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300336341572874657918816909 112626128089827996719556341)
    ·
      refine ⟨10558699508421374692458407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112626128089827996719556341 10558699508421374692458407)
      ·
        refine ⟨15838049262632062038687611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558699508421374692458407 15838049262632062038687611)
        ·
          refine ⟨23757073893948093058031417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15838049262632062038687611 23757073893948093058031417)
          ·
            refine ⟨17817805420461069793523563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23757073893948093058031417 17817805420461069793523563)
            ·
              refine ⟨26726708130691604690285345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817805420461069793523563 26726708130691604690285345)
              ·
                refine ⟨20045031098018703517714009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26726708130691604690285345 20045031098018703517714009)
                ·
                  refine ⟨15033773323514027638285507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20045031098018703517714009 15033773323514027638285507)
                  ·
                    refine ⟨22550659985271041457428261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15033773323514027638285507 22550659985271041457428261)
                    ·
                      refine ⟨4228248747238320273267799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22550659985271041457428261 4228248747238320273267799)
                      ·
                        rfl

theorem cell23_8234485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8234485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234485 prefixEnd_8234485 := by exact prefixLift 8234485
  have htrace : WordTrace (prefixWord ++ tailWord_8234485) baseStart_8234485 baseEnd_8234485 := by
    simpa [prefixWord, tailWord_8234485, baseEnd_8234485] using wordTrace_append hprefix tailTrace_8234485
  have hstable : (prefixWord ++ tailWord_8234485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234485).length < 2 ^ (prefixWord ++ tailWord_8234485).sum := by decide
  have hdescent : baseEnd_8234485 < baseStart_8234485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234488 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_8234488 : Nat := 118140960795 + 8234488 * 2 ^ 59
def prefixEnd_8234488 : Nat := 4983230072969 + 3 ^ 40 * 8234488 * 2
def baseEnd_8234488 : Nat := 4228250287680283761530285

theorem tailTrace_8234488 : CollatzResearch.WordTrace tailWord_8234488 prefixEnd_8234488 4228250287680283761530285 := by
  unfold tailWord_8234488
  simp only [CollatzResearch.WordTrace]
  refine ⟨150168225495931894715588059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200224300661242526287450745 150168225495931894715588059)
  ·
    refine ⟨225252338243897842073382089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150168225495931894715588059 225252338243897842073382089)
    ·
      refine ⟨168939253682923381555036567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225252338243897842073382089 168939253682923381555036567)
      ·
        refine ⟨253408880524385072332554851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168939253682923381555036567 253408880524385072332554851)
        ·
          refine ⟨380113320786577608498832277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253408880524385072332554851 380113320786577608498832277)
          ·
            refine ⟨17817811911870825398382763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380113320786577608498832277 17817811911870825398382763)
            ·
              refine ⟨26726717867806238097574145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817811911870825398382763 26726717867806238097574145)
              ·
                refine ⟨20045038400854678573180609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26726717867806238097574145 20045038400854678573180609)
                ·
                  refine ⟨15033778800641008929885457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20045038400854678573180609 15033778800641008929885457)
                  ·
                    refine ⟨11275334100480756697414093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15033778800641008929885457 11275334100480756697414093)
                    ·
                      refine ⟨4228250287680283761530285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275334100480756697414093 4228250287680283761530285)
                      ·
                        rfl

theorem cell23_8234488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_8234488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234488 prefixEnd_8234488 := by exact prefixLift 8234488
  have htrace : WordTrace (prefixWord ++ tailWord_8234488) baseStart_8234488 baseEnd_8234488 := by
    simpa [prefixWord, tailWord_8234488, baseEnd_8234488] using wordTrace_append hprefix tailTrace_8234488
  have hstable : (prefixWord ++ tailWord_8234488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234488).length < 2 ^ (prefixWord ++ tailWord_8234488).sum := by decide
  have hdescent : baseEnd_8234488 < baseStart_8234488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234508 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 6]
def baseStart_8234508 : Nat := 118140960795 + 8234508 * 2 ^ 59
def prefixEnd_8234508 : Nat := 4983230072969 + 3 ^ 40 * 8234508 * 2
def baseEnd_8234508 : Nat := 469806728588152631475577

theorem tailTrace_8234508 : CollatzResearch.WordTrace tailWord_8234508 prefixEnd_8234508 469806728588152631475577 := by
  unfold tailWord_8234508
  simp only [CollatzResearch.WordTrace]
  refine ⟨150168590225895666423452089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200224786967860888564602785 150168590225895666423452089)
  ·
    refine ⟨112626442669421749817589067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150168590225895666423452089 112626442669421749817589067)
    ·
      refine ⟨168939664004132624726383601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112626442669421749817589067 168939664004132624726383601)
      ·
        refine ⟨126704748003099468544787701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168939664004132624726383601 126704748003099468544787701)
        ·
          refine ⟨11878570125290575176073847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126704748003099468544787701 11878570125290575176073847)
          ·
            refine ⟨17817855187935862764110771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11878570125290575176073847 17817855187935862764110771)
            ·
              refine ⟨26726782781903794146166157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817855187935862764110771 26726782781903794146166157)
              ·
                refine ⟨10022543543213922804812309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26726782781903794146166157 10022543543213922804812309)
                ·
                  refine ⟨469806728588152631475577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10022543543213922804812309 469806728588152631475577)
                  ·
                    rfl

theorem cell23_8234508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_8234508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234508 prefixEnd_8234508 := by exact prefixLift 8234508
  have htrace : WordTrace (prefixWord ++ tailWord_8234508) baseStart_8234508 baseEnd_8234508 := by
    simpa [prefixWord, tailWord_8234508, baseEnd_8234508] using wordTrace_append hprefix tailTrace_8234508
  have hstable : (prefixWord ++ tailWord_8234508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234508).length < 2 ^ (prefixWord ++ tailWord_8234508).sum := by decide
  have hdescent : baseEnd_8234508 < baseStart_8234508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234552 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_8234552 : Nat := 118140960795 + 8234552 * 2 ^ 59
def prefixEnd_8234552 : Nat := 4983230072969 + 3 ^ 40 * 8234552 * 2
def baseEnd_8234552 : Nat := 4228283150442171511129991

theorem tailTrace_8234552 : CollatzResearch.WordTrace tailWord_8234552 prefixEnd_8234552 4228283150442171511129991 := by
  unfold tailWord_8234552
  simp only [CollatzResearch.WordTrace]
  refine ⟨150169392631815964180752955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200225856842421285574337273 150169392631815964180752955)
  ·
    refine ⟨225254088947723946271129433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150169392631815964180752955 225254088947723946271129433)
    ·
      refine ⟨168940566710792959703347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225254088947723946271129433 168940566710792959703347075)
      ·
        refine ⟨253410850066189439555020613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168940566710792959703347075 253410850066189439555020613)
        ·
          refine ⟨47514534387410519916566365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253410850066189439555020613 47514534387410519916566365)
          ·
            refine ⟨17817950395278944968712387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47514534387410519916566365 17817950395278944968712387)
            ·
              refine ⟨26726925592918417453068581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817950395278944968712387 26726925592918417453068581)
              ·
                refine ⟨5011298548672203272450359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26726925592918417453068581 5011298548672203272450359)
                ·
                  refine ⟨7516947823008304908675539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011298548672203272450359 7516947823008304908675539)
                  ·
                    refine ⟨11275421734512457363013309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516947823008304908675539 11275421734512457363013309)
                    ·
                      refine ⟨4228283150442171511129991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275421734512457363013309 4228283150442171511129991)
                      ·
                        rfl

theorem cell23_8234552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_8234552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234552 prefixEnd_8234552 := by exact prefixLift 8234552
  have htrace : WordTrace (prefixWord ++ tailWord_8234552) baseStart_8234552 baseEnd_8234552 := by
    simpa [prefixWord, tailWord_8234552, baseEnd_8234552] using wordTrace_append hprefix tailTrace_8234552
  have hstable : (prefixWord ++ tailWord_8234552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234552).length < 2 ^ (prefixWord ++ tailWord_8234552).sum := by decide
  have hdescent : baseEnd_8234552 < baseStart_8234552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234595 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 3]
def baseStart_8234595 : Nat := 118140960795 + 8234595 * 2 ^ 59
def prefixEnd_8234595 : Nat := 4983230072969 + 3 ^ 40 * 8234595 * 2
def baseEnd_8234595 : Nat := 4228305230110314842892293

theorem tailTrace_8234595 : CollatzResearch.WordTrace tailWord_8234595 prefixEnd_8234595 4228305230110314842892293 := by
  unfold tailWord_8234595
  simp only [CollatzResearch.WordTrace]
  refine ⟨300340353602476146705321239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200226902401650764470214159 300340353602476146705321239)
  ·
    refine ⟨450510530403714220057981859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300340353602476146705321239 450510530403714220057981859)
    ·
      refine ⟨675765795605571330086972789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450510530403714220057981859 675765795605571330086972789)
      ·
        refine ⟨63353043338022312195653699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 675765795605571330086972789 63353043338022312195653699)
        ·
          refine ⟨95029565007033468293480549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63353043338022312195653699 95029565007033468293480549)
          ·
            refine ⟨17818043438818775305027603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95029565007033468293480549 17818043438818775305027603)
            ·
              refine ⟨26727065158228162957541405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17818043438818775305027603 26727065158228162957541405)
              ·
                refine ⟨10022649434335561109078027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26727065158228162957541405 10022649434335561109078027)
                ·
                  refine ⟨15033974151503341663617041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022649434335561109078027 15033974151503341663617041)
                  ·
                    refine ⟨11275480613627506247712781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15033974151503341663617041 11275480613627506247712781)
                    ·
                      refine ⟨4228305230110314842892293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275480613627506247712781 4228305230110314842892293)
                      ·
                        rfl

theorem cell23_8234595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_8234595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234595 prefixEnd_8234595 := by exact prefixLift 8234595
  have htrace : WordTrace (prefixWord ++ tailWord_8234595) baseStart_8234595 baseEnd_8234595 := by
    simpa [prefixWord, tailWord_8234595, baseEnd_8234595] using wordTrace_append hprefix tailTrace_8234595
  have hstable : (prefixWord ++ tailWord_8234595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234595).length < 2 ^ (prefixWord ++ tailWord_8234595).sum := by decide
  have hdescent : baseEnd_8234595 < baseStart_8234595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234602 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_8234602 : Nat := 118140960795 + 8234602 * 2 ^ 59
def prefixEnd_8234602 : Nat := 4983230072969 + 3 ^ 40 * 8234602 * 2
def baseEnd_8234602 : Nat := 1409436274824965438501587

theorem tailTrace_8234602 : CollatzResearch.WordTrace tailWord_8234602 prefixEnd_8234602 1409436274824965438501587 := by
  unfold tailWord_8234602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085152228362696725206515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200227072608967191267217373 75085152228362696725206515)
  ·
    refine ⟨112627728342544045087809773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085152228362696725206515 112627728342544045087809773)
    ·
      refine ⟨42235398128454016907928665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112627728342544045087809773 42235398128454016907928665)
      ·
        refine ⟨31676548596340512680946499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42235398128454016907928665 31676548596340512680946499)
        ·
          refine ⟨47514822894510769021419749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31676548596340512680946499 47514822894510769021419749)
          ·
            refine ⟨8909029292720769191516203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47514822894510769021419749 8909029292720769191516203)
            ·
              refine ⟨13363543939081153787274305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909029292720769191516203 13363543939081153787274305)
              ·
                refine ⟨10022657954310865340455729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13363543939081153787274305 10022657954310865340455729)
                ·
                  refine ⟨7516993465733149005341797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10022657954310865340455729 7516993465733149005341797)
                  ·
                    refine ⟨1409436274824965438501587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7516993465733149005341797 1409436274824965438501587)
                    ·
                      rfl

theorem cell23_8234602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_8234602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234602 prefixEnd_8234602 := by exact prefixLift 8234602
  have htrace : WordTrace (prefixWord ++ tailWord_8234602) baseStart_8234602 baseEnd_8234602 := by
    simpa [prefixWord, tailWord_8234602, baseEnd_8234602] using wordTrace_append hprefix tailTrace_8234602
  have hstable : (prefixWord ++ tailWord_8234602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234602).length < 2 ^ (prefixWord ++ tailWord_8234602).sum := by decide
  have hdescent : baseEnd_8234602 < baseStart_8234602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234618 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_8234618 : Nat := 118140960795 + 8234618 * 2 ^ 59
def prefixEnd_8234618 : Nat := 4983230072969 + 3 ^ 40 * 8234618 * 2
def baseEnd_8234618 : Nat := 4228317040165368252904687

theorem tailTrace_8234618 : CollatzResearch.WordTrace tailWord_8234618 prefixEnd_8234618 4228317040165368252904687 := by
  unfold tailWord_8234618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085298120348205408352127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200227461654261881088939005 75085298120348205408352127)
  ·
    refine ⟨112627947180522308112528191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085298120348205408352127 112627947180522308112528191)
    ·
      refine ⟨168941920770783462168792287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112627947180522308112528191 168941920770783462168792287)
      ·
        refine ⟨253412881156175193253188431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168941920770783462168792287 253412881156175193253188431)
        ·
          refine ⟨380119321734262789879782647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253412881156175193253188431 380119321734262789879782647)
          ·
            refine ⟨570178982601394184819673971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380119321734262789879782647 570178982601394184819673971)
            ·
              refine ⟨855268473902091277229510957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570178982601394184819673971 855268473902091277229510957)
              ·
                refine ⟨320725677713284228961066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855268473902091277229510957 320725677713284228961066609)
                ·
                  refine ⟨240544258284963171720799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320725677713284228961066609 240544258284963171720799957)
                  ·
                    refine ⟨5637756053553824337206249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240544258284963171720799957 5637756053553824337206249)
                    ·
                      refine ⟨4228317040165368252904687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637756053553824337206249 4228317040165368252904687)
                      ·
                        rfl

theorem cell23_8234618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_8234618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234618 prefixEnd_8234618 := by exact prefixLift 8234618
  have htrace : WordTrace (prefixWord ++ tailWord_8234618) baseStart_8234618 baseEnd_8234618 := by
    simpa [prefixWord, tailWord_8234618, baseEnd_8234618] using wordTrace_append hprefix tailTrace_8234618
  have hstable : (prefixWord ++ tailWord_8234618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234618).length < 2 ^ (prefixWord ++ tailWord_8234618).sum := by decide
  have hdescent : baseEnd_8234618 < baseStart_8234618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234625 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_8234625 : Nat := 118140960795 + 8234625 * 2 ^ 59
def prefixEnd_8234625 : Nat := 4983230072969 + 3 ^ 40 * 8234625 * 2
def baseEnd_8234625 : Nat := 4228320634529949725517155

theorem tailTrace_8234625 : CollatzResearch.WordTrace tailWord_8234625 prefixEnd_8234625 4228320634529949725517155 := by
  unfold tailWord_8234625
  simp only [CollatzResearch.WordTrace]
  refine ⟨300341447792367461828913329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200227631861578307885942219 300341447792367461828913329)
  ·
    refine ⟨225256085844275596371684997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300341447792367461828913329 225256085844275596371684997)
    ·
      refine ⟨42235516095801674319690937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225256085844275596371684997 42235516095801674319690937)
      ·
        refine ⟨31676637071851255739768203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42235516095801674319690937 31676637071851255739768203)
        ·
          refine ⟨47514955607776883609652305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31676637071851255739768203 47514955607776883609652305)
          ·
            refine ⟨35636216705832662707239229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47514955607776883609652305 35636216705832662707239229)
            ·
              refine ⟨13363581264687248515214711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35636216705832662707239229 13363581264687248515214711)
              ·
                refine ⟨20045371897030872772822067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13363581264687248515214711 20045371897030872772822067)
                ·
                  refine ⟨30068057845546309159233101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20045371897030872772822067 30068057845546309159233101)
                  ·
                    refine ⟨11275521692079865934712413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30068057845546309159233101 11275521692079865934712413)
                    ·
                      refine ⟨4228320634529949725517155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275521692079865934712413 4228320634529949725517155)
                      ·
                        rfl

theorem cell23_8234625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_8234625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234625 prefixEnd_8234625 := by exact prefixLift 8234625
  have htrace : WordTrace (prefixWord ++ tailWord_8234625) baseStart_8234625 baseEnd_8234625 := by
    simpa [prefixWord, tailWord_8234625, baseEnd_8234625] using wordTrace_append hprefix tailTrace_8234625
  have hstable : (prefixWord ++ tailWord_8234625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234625).length < 2 ^ (prefixWord ++ tailWord_8234625).sum := by decide
  have hdescent : baseEnd_8234625 < baseStart_8234625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234632 : List Nat := [2, 1, 3, 5, 1, 2, 2, 7]
def baseStart_8234632 : Nat := 118140960795 + 8234632 * 2 ^ 59
def prefixEnd_8234632 : Nat := 4983230072969 + 3 ^ 40 * 8234632 * 2
def baseEnd_8234632 : Nat := 156604601070167822152949

theorem tailTrace_8234632 : CollatzResearch.WordTrace tailWord_8234632 prefixEnd_8234632 156604601070167822152949 := by
  unfold tailWord_8234632
  simp only [CollatzResearch.WordTrace]
  refine ⟨150170851551671051012209075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200227802068894734682945433 150170851551671051012209075)
  ·
    refine ⟨225256277327506576518313613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150170851551671051012209075 225256277327506576518313613)
    ·
      refine ⟨84471103997814966194367605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225256277327506576518313613 84471103997814966194367605)
      ·
        refine ⟨7919165999795153080721963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84471103997814966194367605 7919165999795153080721963)
        ·
          refine ⟨11878748999692729621082945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919165999795153080721963 11878748999692729621082945)
          ·
            refine ⟨8909061749769547215812209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878748999692729621082945 8909061749769547215812209)
            ·
              refine ⟨6681796312327160411859157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909061749769547215812209 6681796312327160411859157)
              ·
                refine ⟨156604601070167822152949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6681796312327160411859157 156604601070167822152949)
                ·
                  rfl

theorem cell23_8234632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 7].length) (baseStart_8234632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234632 prefixEnd_8234632 := by exact prefixLift 8234632
  have htrace : WordTrace (prefixWord ++ tailWord_8234632) baseStart_8234632 baseEnd_8234632 := by
    simpa [prefixWord, tailWord_8234632, baseEnd_8234632] using wordTrace_append hprefix tailTrace_8234632
  have hstable : (prefixWord ++ tailWord_8234632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234632).length < 2 ^ (prefixWord ++ tailWord_8234632).sum := by decide
  have hdescent : baseEnd_8234632 < baseStart_8234632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234638 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8234638 : Nat := 118140960795 + 8234638 * 2 ^ 59
def prefixEnd_8234638 : Nat := 4983230072969 + 3 ^ 40 * 8234638 * 2
def baseEnd_8234638 : Nat := 4228327309778458174654595

theorem tailTrace_8234638 : CollatzResearch.WordTrace tailWord_8234638 prefixEnd_8234638 4228327309778458174654595 := by
  unfold tailWord_8234638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37542740242665045631142071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200227947960880243366091045 37542740242665045631142071)
  ·
    refine ⟨56314110363997568446713107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37542740242665045631142071 56314110363997568446713107)
    ·
      refine ⟨84471165545996352670069661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56314110363997568446713107 84471165545996352670069661)
      ·
        refine ⟨31676687079748632251276123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84471165545996352670069661 31676687079748632251276123)
        ·
          refine ⟨47515030619622948376914185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31676687079748632251276123 47515030619622948376914185)
          ·
            refine ⟨35636272964717211282685639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47515030619622948376914185 35636272964717211282685639)
            ·
              refine ⟨53454409447075816924028459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35636272964717211282685639 53454409447075816924028459)
              ·
                refine ⟨80181614170613725386042689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53454409447075816924028459 80181614170613725386042689)
                ·
                  refine ⟨60136210627960294039532017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80181614170613725386042689 60136210627960294039532017)
                  ·
                    refine ⟨45102157970970220529649013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60136210627960294039532017 45102157970970220529649013)
                    ·
                      refine ⟨4228327309778458174654595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45102157970970220529649013 4228327309778458174654595)
                      ·
                        rfl

theorem cell23_8234638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8234638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234638 prefixEnd_8234638 := by exact prefixLift 8234638
  have htrace : WordTrace (prefixWord ++ tailWord_8234638) baseStart_8234638 baseEnd_8234638 := by
    simpa [prefixWord, tailWord_8234638, baseEnd_8234638] using wordTrace_append hprefix tailTrace_8234638
  have hstable : (prefixWord ++ tailWord_8234638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234638).length < 2 ^ (prefixWord ++ tailWord_8234638).sum := by decide
  have hdescent : baseEnd_8234638 < baseStart_8234638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_8234641 : Nat := 118140960795 + 8234641 * 2 ^ 59
def prefixEnd_8234641 : Nat := 4983230072969 + 3 ^ 40 * 8234641 * 2
def baseEnd_8234641 : Nat := 1409442950073473887639027

theorem tailTrace_8234641 : CollatzResearch.WordTrace tailWord_8234641 prefixEnd_8234641 1409442950073473887639027 := by
  unfold tailWord_8234641
  simp only [CollatzResearch.WordTrace]
  refine ⟨300342031360309496561495777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200228020906872997707663851 300342031360309496561495777)
  ·
    refine ⟨225256523520232122421121833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300342031360309496561495777 225256523520232122421121833)
    ·
      refine ⟨168942392640174091815841375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225256523520232122421121833 168942392640174091815841375)
      ·
        refine ⟨253413588960261137723762063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168942392640174091815841375 253413588960261137723762063)
        ·
          refine ⟨380120383440391706585643095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253413588960261137723762063 380120383440391706585643095)
          ·
            refine ⟨570180575160587559878464643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380120383440391706585643095 570180575160587559878464643)
            ·
              refine ⟨855270862740881339817696965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570180575160587559878464643 855270862740881339817696965)
              ·
                refine ⟨160363286763915251215818181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 855270862740881339817696965 160363286763915251215818181)
                ·
                  refine ⟨30068116268234109602965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160363286763915251215818181 30068116268234109602965909)
                  ·
                    refine ⟨1409442950073473887639027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30068116268234109602965909 1409442950073473887639027)
                    ·
                      rfl

theorem cell23_8234641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_8234641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234641 prefixEnd_8234641 := by exact prefixLift 8234641
  have htrace : WordTrace (prefixWord ++ tailWord_8234641) baseStart_8234641 baseEnd_8234641 := by
    simpa [prefixWord, tailWord_8234641, baseEnd_8234641] using wordTrace_append hprefix tailTrace_8234641
  have hstable : (prefixWord ++ tailWord_8234641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234641).length < 2 ^ (prefixWord ++ tailWord_8234641).sum := by decide
  have hdescent : baseEnd_8234641 < baseStart_8234641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234665 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 8, 2, 2]
def baseStart_8234665 : Nat := 118140960795 + 8234665 * 2 ^ 59
def prefixEnd_8234665 : Nat := 4983230072969 + 3 ^ 40 * 8234665 * 2
def baseEnd_8234665 : Nat := 4228341173756129569016971

theorem tailTrace_8234665 : CollatzResearch.WordTrace tailWord_8234665 prefixEnd_8234665 4228341173756129569016971 := by
  unfold tailWord_8234665
  simp only [CollatzResearch.WordTrace]
  refine ⟨300342906712222548660369449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200228604474815032440246299 300342906712222548660369449)
  ·
    refine ⟨225257180034166911495277087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300342906712222548660369449 225257180034166911495277087)
    ·
      refine ⟨337885770051250367242915631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225257180034166911495277087 337885770051250367242915631)
      ·
        refine ⟨506828655076875550864373447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337885770051250367242915631 506828655076875550864373447)
        ·
          refine ⟨760242982615313326296560171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506828655076875550864373447 760242982615313326296560171)
          ·
            refine ⟨1140364473922969989444840257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760242982615313326296560171 1140364473922969989444840257)
            ·
              refine ⟨855273355442227492083630193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140364473922969989444840257 855273355442227492083630193)
              ·
                refine ⟨641455016581670619062722645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855273355442227492083630193 641455016581670619062722645)
                ·
                  refine ⟨7517050975566452567141281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 641455016581670619062722645 7517050975566452567141281)
                  ·
                    refine ⟨5637788231674839425355961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517050975566452567141281 5637788231674839425355961)
                    ·
                      refine ⟨4228341173756129569016971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637788231674839425355961 4228341173756129569016971)
                      ·
                        rfl

theorem cell23_8234665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2, 2].length) (baseStart_8234665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234665 prefixEnd_8234665 := by exact prefixLift 8234665
  have htrace : WordTrace (prefixWord ++ tailWord_8234665) baseStart_8234665 baseEnd_8234665 := by
    simpa [prefixWord, tailWord_8234665, baseEnd_8234665] using wordTrace_append hprefix tailTrace_8234665
  have hstable : (prefixWord ++ tailWord_8234665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234665).length < 2 ^ (prefixWord ++ tailWord_8234665).sum := by decide
  have hdescent : baseEnd_8234665 < baseStart_8234665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_8234691 : Nat := 118140960795 + 8234691 * 2 ^ 59
def prefixEnd_8234691 : Nat := 4983230072969 + 3 ^ 40 * 8234691 * 2
def baseEnd_8234691 : Nat := 4228354524253146467291851

theorem tailTrace_8234691 : CollatzResearch.WordTrace tailWord_8234691 prefixEnd_8234691 4228354524253146467291851 := by
  unfold tailWord_8234691
  simp only [CollatzResearch.WordTrace]
  refine ⟨300343855010128355100815927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200229236673418903400543951 300343855010128355100815927)
  ·
    refine ⟨450515782515192532651223891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300343855010128355100815927 450515782515192532651223891)
    ·
      refine ⟨675773673772788798976835837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450515782515192532651223891 675773673772788798976835837)
      ·
        refine ⟨253415127664795799616313439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675773673772788798976835837 253415127664795799616313439)
        ·
          refine ⟨380122691497193699424470159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253415127664795799616313439 380122691497193699424470159)
          ·
            refine ⟨570184037245790549136705239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380122691497193699424470159 570184037245790549136705239)
            ·
              refine ⟨855276055868685823705057859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570184037245790549136705239 855276055868685823705057859)
              ·
                refine ⟨1282914083803028735557586789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855276055868685823705057859 1282914083803028735557586789)
                ·
                  refine ⟨240546390713067887917047523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282914083803028735557586789 240546390713067887917047523)
                  ·
                    refine ⟨360819586069601831875571285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240546390713067887917047523 360819586069601831875571285)
                    ·
                      refine ⟨4228354524253146467291851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 360819586069601831875571285 4228354524253146467291851)
                      ·
                        rfl

theorem cell23_8234691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_8234691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234691 prefixEnd_8234691 := by exact prefixLift 8234691
  have htrace : WordTrace (prefixWord ++ tailWord_8234691) baseStart_8234691 baseEnd_8234691 := by
    simpa [prefixWord, tailWord_8234691, baseEnd_8234691] using wordTrace_append hprefix tailTrace_8234691
  have hstable : (prefixWord ++ tailWord_8234691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234691).length < 2 ^ (prefixWord ++ tailWord_8234691).sum := by decide
  have hdescent : baseEnd_8234691 < baseStart_8234691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234725 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_8234725 : Nat := 118140960795 + 8234725 * 2 ^ 59
def prefixEnd_8234725 : Nat := 4983230072969 + 3 ^ 40 * 8234725 * 2
def baseEnd_8234725 : Nat := 4228371982595399334266695

theorem tailTrace_8234725 : CollatzResearch.WordTrace tailWord_8234725 prefixEnd_8234725 4228371982595399334266695 := by
  unfold tailWord_8234725
  simp only [CollatzResearch.WordTrace]
  refine ⟨300345095092005178907553629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200230063394670119271702419 300345095092005178907553629)
  ·
    refine ⟨112629410659501942090332611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300345095092005178907553629 112629410659501942090332611)
    ·
      refine ⟨168944115989252913135498917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112629410659501942090332611 168944115989252913135498917)
      ·
        refine ⟨31677021747984921212906047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168944115989252913135498917 31677021747984921212906047)
        ·
          refine ⟨47515532621977381819359071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31677021747984921212906047 47515532621977381819359071)
          ·
            refine ⟨71273298932966072729038607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47515532621977381819359071 71273298932966072729038607)
            ·
              refine ⟨106909948399449109093557911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71273298932966072729038607 106909948399449109093557911)
              ·
                refine ⟨160364922599173663640336867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106909948399449109093557911 160364922599173663640336867)
                ·
                  refine ⟨240547383898760495460505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160364922599173663640336867 240547383898760495460505301)
                  ·
                    refine ⟨5637829310127199112355593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240547383898760495460505301 5637829310127199112355593)
                    ·
                      refine ⟨4228371982595399334266695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637829310127199112355593 4228371982595399334266695)
                      ·
                        rfl

theorem cell23_8234725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_8234725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234725 prefixEnd_8234725 := by exact prefixLift 8234725
  have htrace : WordTrace (prefixWord ++ tailWord_8234725) baseStart_8234725 baseEnd_8234725 := by
    simpa [prefixWord, tailWord_8234725, baseEnd_8234725] using wordTrace_append hprefix tailTrace_8234725
  have hstable : (prefixWord ++ tailWord_8234725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234725).length < 2 ^ (prefixWord ++ tailWord_8234725).sum := by decide
  have hdescent : baseEnd_8234725 < baseStart_8234725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234755 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4]
def baseStart_8234755 : Nat := 118140960795 + 8234755 * 2 ^ 59
def prefixEnd_8234755 : Nat := 4983230072969 + 3 ^ 40 * 8234755 * 2
def baseEnd_8234755 : Nat := 4228387387015034216891557

theorem tailTrace_8234755 : CollatzResearch.WordTrace tailWord_8234755 prefixEnd_8234755 4228387387015034216891557 := by
  unfold tailWord_8234755
  simp only [CollatzResearch.WordTrace]
  refine ⟨300346189281896494031145719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200230792854597662687430479 300346189281896494031145719)
  ·
    refine ⟨450519283922844741046718579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300346189281896494031145719 450519283922844741046718579)
    ·
      refine ⟨675778925884267111570077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450519283922844741046718579 675778925884267111570077869)
      ·
        refine ⟨253417097206600166838779201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675778925884267111570077869 253417097206600166838779201)
        ·
          refine ⟨190062822904950125129084401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253417097206600166838779201 190062822904950125129084401)
          ·
            refine ⟨142547117178712593846813301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190062822904950125129084401 142547117178712593846813301)
            ·
              refine ⟨13363792235504305673138747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142547117178712593846813301 13363792235504305673138747)
              ·
                refine ⟨20045688353256458509708121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13363792235504305673138747 20045688353256458509708121)
                ·
                  refine ⟨15034266264942343882281091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20045688353256458509708121 15034266264942343882281091)
                  ·
                    refine ⟨22551399397413515823421637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15034266264942343882281091 22551399397413515823421637)
                    ·
                      refine ⟨4228387387015034216891557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22551399397413515823421637 4228387387015034216891557)
                      ·
                        rfl

theorem cell23_8234755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_8234755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234755 prefixEnd_8234755 := by exact prefixLift 8234755
  have htrace : WordTrace (prefixWord ++ tailWord_8234755) baseStart_8234755 baseEnd_8234755 := by
    simpa [prefixWord, tailWord_8234755, baseEnd_8234755] using wordTrace_append hprefix tailTrace_8234755
  have hstable : (prefixWord ++ tailWord_8234755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234755).length < 2 ^ (prefixWord ++ tailWord_8234755).sum := by decide
  have hdescent : baseEnd_8234755 < baseStart_8234755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234825 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_8234825 : Nat := 118140960795 + 8234825 * 2 ^ 59
def prefixEnd_8234825 : Nat := 4983230072969 + 3 ^ 40 * 8234825 * 2
def baseEnd_8234825 : Nat := 1409474443553616314338745

theorem tailTrace_8234825 : CollatzResearch.WordTrace tailWord_8234825 prefixEnd_8234825 1409474443553616314338745 := by
  unfold tailWord_8234825
  simp only [CollatzResearch.WordTrace]
  refine ⟨300348742391642895986193929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200232494927761930657462619 300348742391642895986193929)
  ·
    refine ⟨225261556793732171989645447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300348742391642895986193929 225261556793732171989645447)
    ·
      refine ⟨337892335190598257984468171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225261556793732171989645447 337892335190598257984468171)
      ·
        refine ⟨506838502785897386976702257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337892335190598257984468171 506838502785897386976702257)
        ·
          refine ⟨380128877089423040232526693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506838502785897386976702257 380128877089423040232526693)
          ·
            refine ⟨71274164454266820043598755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380128877089423040232526693 71274164454266820043598755)
            ·
              refine ⟨106911246681400230065398133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71274164454266820043598755 106911246681400230065398133)
              ·
                refine ⟨10022929376381271568631075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106911246681400230065398133 10022929376381271568631075)
                ·
                  refine ⟨15034394064571907352946613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022929376381271568631075 15034394064571907352946613)
                  ·
                    refine ⟨1409474443553616314338745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15034394064571907352946613 1409474443553616314338745)
                    ·
                      rfl

theorem cell23_8234825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_8234825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234825 prefixEnd_8234825 := by exact prefixLift 8234825
  have htrace : WordTrace (prefixWord ++ tailWord_8234825) baseStart_8234825 baseEnd_8234825 := by
    simpa [prefixWord, tailWord_8234825, baseEnd_8234825] using wordTrace_append hprefix tailTrace_8234825
  have hstable : (prefixWord ++ tailWord_8234825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234825).length < 2 ^ (prefixWord ++ tailWord_8234825).sum := by decide
  have hdescent : baseEnd_8234825 < baseStart_8234825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234855 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 6]
def baseStart_8234855 : Nat := 118140960795 + 8234855 * 2 ^ 59
def prefixEnd_8234855 : Nat := 4983230072969 + 3 ^ 40 * 8234855 * 2
def baseEnd_8234855 : Nat := 1409479578360161275213699

theorem tailTrace_8234855 : CollatzResearch.WordTrace tailWord_8234855 prefixEnd_8234855 1409479578360161275213699 := by
  unfold tailWord_8234855
  simp only [CollatzResearch.WordTrace]
  refine ⟨300349836581534211109786019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200233224387689474073190679 300349836581534211109786019)
  ·
    refine ⟨450524754872301316664679029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300349836581534211109786019 450524754872301316664679029)
    ·
      refine ⟨42236695769278248437313659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450524754872301316664679029 42236695769278248437313659)
      ·
        refine ⟨63355043653917372655970489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42236695769278248437313659 63355043653917372655970489)
        ·
          refine ⟨47516282740438029491977867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63355043653917372655970489 47516282740438029491977867)
          ·
            refine ⟨71274424110657044237966801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47516282740438029491977867 71274424110657044237966801)
            ·
              refine ⟨53455818082992783178475101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71274424110657044237966801 53455818082992783178475101)
              ·
                refine ⟨20045931781122293691928163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53455818082992783178475101 20045931781122293691928163)
                ·
                  refine ⟨30068897671683440537892245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20045931781122293691928163 30068897671683440537892245)
                  ·
                    refine ⟨1409479578360161275213699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30068897671683440537892245 1409479578360161275213699)
                    ·
                      rfl

theorem cell23_8234855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_8234855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234855 prefixEnd_8234855 := by exact prefixLift 8234855
  have htrace : WordTrace (prefixWord ++ tailWord_8234855) baseStart_8234855 baseEnd_8234855 := by
    simpa [prefixWord, tailWord_8234855, baseEnd_8234855] using wordTrace_append hprefix tailTrace_8234855
  have hstable : (prefixWord ++ tailWord_8234855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234855).length < 2 ^ (prefixWord ++ tailWord_8234855).sum := by decide
  have hdescent : baseEnd_8234855 < baseStart_8234855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234890 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_8234890 : Nat := 118140960795 + 8234890 * 2 ^ 59
def prefixEnd_8234890 : Nat := 4983230072969 + 3 ^ 40 * 8234890 * 2
def baseEnd_8234890 : Nat := 4228456706903391188703437

theorem tailTrace_8234890 : CollatzResearch.WordTrace tailWord_8234890 prefixEnd_8234890 4228456706903391188703437 := by
  unfold tailWord_8234890
  simp only [CollatzResearch.WordTrace]
  refine ⟨75087778284101853021827531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200234075424271608058206749 75087778284101853021827531)
  ·
    refine ⟨112631667426152779532741297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75087778284101853021827531 112631667426152779532741297)
    ·
      refine ⟨84473750569614584649555973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112631667426152779532741297 84473750569614584649555973)
      ·
        refine ⟨15838828231802734621791745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84473750569614584649555973 15838828231802734621791745)
        ·
          refine ⟨11879121173852050966343809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15838828231802734621791745 11879121173852050966343809)
          ·
            refine ⟨8909340880389038224757857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11879121173852050966343809 8909340880389038224757857)
            ·
              refine ⟨6682005660291778668568393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909340880389038224757857 6682005660291778668568393)
              ·
                refine ⟨5011504245218834001426295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682005660291778668568393 5011504245218834001426295)
                ·
                  refine ⟨7517256367828251002139443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011504245218834001426295 7517256367828251002139443)
                  ·
                    refine ⟨11275884551742376503209165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517256367828251002139443 11275884551742376503209165)
                    ·
                      refine ⟨4228456706903391188703437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275884551742376503209165 4228456706903391188703437)
                      ·
                        rfl

theorem cell23_8234890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_8234890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234890 prefixEnd_8234890 := by exact prefixLift 8234890
  have htrace : WordTrace (prefixWord ++ tailWord_8234890) baseStart_8234890 baseEnd_8234890 := by
    simpa [prefixWord, tailWord_8234890, baseEnd_8234890] using wordTrace_append hprefix tailTrace_8234890
  have hstable : (prefixWord ++ tailWord_8234890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234890).length < 2 ^ (prefixWord ++ tailWord_8234890).sum := by decide
  have hdescent : baseEnd_8234890 < baseStart_8234890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234912 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_8234912 : Nat := 118140960795 + 8234912 * 2 ^ 59
def prefixEnd_8234912 : Nat := 4983230072969 + 3 ^ 40 * 8234912 * 2
def baseEnd_8234912 : Nat := 4228468003477790102628335

theorem tailTrace_8234912 : CollatzResearch.WordTrace tailWord_8234912 prefixEnd_8234912 4228468003477790102628335 := by
  unfold tailWord_8234912
  simp only [CollatzResearch.WordTrace]
  refine ⟨150175957771163854922305495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200234610361551806563073993 150175957771163854922305495)
  ·
    refine ⟨225263936656745782383458243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150175957771163854922305495 225263936656745782383458243)
    ·
      refine ⟨337895904985118673575187365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225263936656745782383458243 337895904985118673575187365)
      ·
        refine ⟨63355482184709751295347631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337895904985118673575187365 63355482184709751295347631)
        ·
          refine ⟨95033223277064626943021447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63355482184709751295347631 95033223277064626943021447)
          ·
            refine ⟨142549834915596940414532171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95033223277064626943021447 142549834915596940414532171)
            ·
              refine ⟨213824752373395410621798257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142549834915596940414532171 213824752373395410621798257)
              ·
                refine ⟨160368564280046557966348693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213824752373395410621798257 160368564280046557966348693)
                ·
                  refine ⟨7517276450627182404672595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160368564280046557966348693 7517276450627182404672595)
                  ·
                    refine ⟨11275914675940773607008893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517276450627182404672595 11275914675940773607008893)
                    ·
                      refine ⟨4228468003477790102628335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11275914675940773607008893 4228468003477790102628335)
                      ·
                        rfl

theorem cell23_8234912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_8234912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234912 prefixEnd_8234912 := by exact prefixLift 8234912
  have htrace : WordTrace (prefixWord ++ tailWord_8234912) baseStart_8234912 baseEnd_8234912 := by
    simpa [prefixWord, tailWord_8234912, baseEnd_8234912] using wordTrace_append hprefix tailTrace_8234912
  have hstable : (prefixWord ++ tailWord_8234912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234912).length < 2 ^ (prefixWord ++ tailWord_8234912).sum := by decide
  have hdescent : baseEnd_8234912 < baseStart_8234912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8234973 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_8234973 : Nat := 118140960795 + 8234973 * 2 ^ 59
def prefixEnd_8234973 : Nat := 4983230072969 + 3 ^ 40 * 8234973 * 2
def baseEnd_8234973 : Nat := 4228499325797714363965555

theorem tailTrace_8234973 : CollatzResearch.WordTrace tailWord_8234973 prefixEnd_8234973 4228499325797714363965555 := by
  unfold tailWord_8234973
  simp only [CollatzResearch.WordTrace]
  refine ⟨300354140395106717262581573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200236093596737811508387715 300354140395106717262581573)
  ·
    refine ⟨56316401324082509486734045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300354140395106717262581573 56316401324082509486734045)
    ·
      refine ⟨21118650496530941057525267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56316401324082509486734045 21118650496530941057525267)
      ·
        refine ⟨31677975744796411586287901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21118650496530941057525267 31677975744796411586287901)
        ·
          refine ⟨11879240904298654344857963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31677975744796411586287901 11879240904298654344857963)
          ·
            refine ⟨17818861356447981517286945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879240904298654344857963 17818861356447981517286945)
            ·
              refine ⟨13364146017335986137965209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17818861356447981517286945 13364146017335986137965209)
              ·
                refine ⟨10023109513001989603473907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13364146017335986137965209 10023109513001989603473907)
                ·
                  refine ⟨15034664269502984405210861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10023109513001989603473907 15034664269502984405210861)
                  ·
                    refine ⟨5637999101063619151954073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15034664269502984405210861 5637999101063619151954073)
                    ·
                      refine ⟨4228499325797714363965555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5637999101063619151954073 4228499325797714363965555)
                      ·
                        rfl

theorem cell23_8234973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_8234973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8234973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8234973 prefixEnd_8234973 := by exact prefixLift 8234973
  have htrace : WordTrace (prefixWord ++ tailWord_8234973) baseStart_8234973 baseEnd_8234973 := by
    simpa [prefixWord, tailWord_8234973, baseEnd_8234973] using wordTrace_append hprefix tailTrace_8234973
  have hstable : (prefixWord ++ tailWord_8234973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8234973).length < 2 ^ (prefixWord ++ tailWord_8234973).sum := by decide
  have hdescent : baseEnd_8234973 < baseStart_8234973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8234973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235022 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_8235022 : Nat := 118140960795 + 8235022 * 2 ^ 59
def prefixEnd_8235022 : Nat := 4983230072969 + 3 ^ 40 * 8235022 * 2
def baseEnd_8235022 : Nat := 1409508162116594890750943

theorem tailTrace_8235022 : CollatzResearch.WordTrace tailWord_8235022 prefixEnd_8235022 1409508162116594890750943 := by
  unfold tailWord_8235022
  simp only [CollatzResearch.WordTrace]
  refine ⟨37544490946491149828889415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200237285047952799087410213 37544490946491149828889415)
  ·
    refine ⟨56316736419736724743334123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37544490946491149828889415 56316736419736724743334123)
    ·
      refine ⟨84475104629605087115001185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56316736419736724743334123 84475104629605087115001185)
      ·
        refine ⟨63356328472203815336250889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84475104629605087115001185 63356328472203815336250889)
        ·
          refine ⟨47517246354152861502188167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63356328472203815336250889 47517246354152861502188167)
          ·
            refine ⟨71275869531229292253282251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47517246354152861502188167 71275869531229292253282251)
            ·
              refine ⟨106913804296843938379923377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71275869531229292253282251 106913804296843938379923377)
              ·
                refine ⟨80185353222632953784942533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106913804296843938379923377 80185353222632953784942533)
                ·
                  refine ⟨15034753729243678834676725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80185353222632953784942533 15034753729243678834676725)
                  ·
                    refine ⟨1409508162116594890750943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15034753729243678834676725 1409508162116594890750943)
                    ·
                      rfl

theorem cell23_8235022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_8235022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235022 prefixEnd_8235022 := by exact prefixLift 8235022
  have htrace : WordTrace (prefixWord ++ tailWord_8235022) baseStart_8235022 baseEnd_8235022 := by
    simpa [prefixWord, tailWord_8235022, baseEnd_8235022] using wordTrace_append hprefix tailTrace_8235022
  have hstable : (prefixWord ++ tailWord_8235022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235022).length < 2 ^ (prefixWord ++ tailWord_8235022).sum := by decide
  have hdescent : baseEnd_8235022 < baseStart_8235022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235052 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_8235052 : Nat := 118140960795 + 8235052 * 2 ^ 59
def prefixEnd_8235052 : Nat := 4983230072969 + 3 ^ 40 * 8235052 * 2
def baseEnd_8235052 : Nat := 1409513296923139851625897

theorem tailTrace_8235052 : CollatzResearch.WordTrace tailWord_8235052 prefixEnd_8235052 1409513296923139851625897 := by
  unfold tailWord_8235052
  simp only [CollatzResearch.WordTrace]
  refine ⟨150178510880910256877353705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200238014507880342503138273 150178510880910256877353705)
  ·
    refine ⟨112633883160682692658015279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150178510880910256877353705 112633883160682692658015279)
    ·
      refine ⟨168950824741024038987022919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112633883160682692658015279 168950824741024038987022919)
      ·
        refine ⟨253426237111536058480534379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168950824741024038987022919 253426237111536058480534379)
        ·
          refine ⟨380139355667304087720801569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253426237111536058480534379 380139355667304087720801569)
          ·
            refine ⟨285104516750478065790601177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380139355667304087720801569 285104516750478065790601177)
            ·
              refine ⟨213828387562858549342950883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285104516750478065790601177 213828387562858549342950883)
              ·
                refine ⟨320742581344287824014426325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213828387562858549342950883 320742581344287824014426325)
                ·
                  refine ⟨7517404250256745875338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320742581344287824014426325 7517404250256745875338117)
                  ·
                    refine ⟨1409513296923139851625897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517404250256745875338117 1409513296923139851625897)
                    ·
                      rfl

theorem cell23_8235052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_8235052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235052 prefixEnd_8235052 := by exact prefixLift 8235052
  have htrace : WordTrace (prefixWord ++ tailWord_8235052) baseStart_8235052 baseEnd_8235052 := by
    simpa [prefixWord, tailWord_8235052, baseEnd_8235052] using wordTrace_append hprefix tailTrace_8235052
  have hstable : (prefixWord ++ tailWord_8235052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235052).length < 2 ^ (prefixWord ++ tailWord_8235052).sum := by decide
  have hdescent : baseEnd_8235052 < baseStart_8235052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235060 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 5]
def baseStart_8235060 : Nat := 118140960795 + 8235060 * 2 ^ 59
def prefixEnd_8235060 : Nat := 4983230072969 + 3 ^ 40 * 8235060 * 2
def baseEnd_8235060 : Nat := 469838222068295058175295

theorem tailTrace_8235060 : CollatzResearch.WordTrace tailWord_8235060 prefixEnd_8235060 469838222068295058175295 := by
  unfold tailWord_8235060
  simp only [CollatzResearch.WordTrace]
  refine ⟨150178656772895765560499317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200238209030527687413999089 150178656772895765560499317)
  ·
    refine ⟨14079249072458978021296811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150178656772895765560499317 14079249072458978021296811)
    ·
      refine ⟨21118873608688467031945217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14079249072458978021296811 21118873608688467031945217)
      ·
        refine ⟨15839155206516350273958913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21118873608688467031945217 15839155206516350273958913)
        ·
          refine ⟨11879366404887262705469185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15839155206516350273958913 11879366404887262705469185)
          ·
            refine ⟨8909524803665447029101889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11879366404887262705469185 8909524803665447029101889)
            ·
              refine ⟨6682143602749085271826417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909524803665447029101889 6682143602749085271826417)
              ·
                refine ⟨5011607702061813953869813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682143602749085271826417 5011607702061813953869813)
                ·
                  refine ⟨469838222068295058175295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011607702061813953869813 469838222068295058175295)
                  ·
                    rfl

theorem cell23_8235060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_8235060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235060 prefixEnd_8235060 := by exact prefixLift 8235060
  have htrace : WordTrace (prefixWord ++ tailWord_8235060) baseStart_8235060 baseEnd_8235060 := by
    simpa [prefixWord, tailWord_8235060, baseEnd_8235060] using wordTrace_append hprefix tailTrace_8235060
  have hstable : (prefixWord ++ tailWord_8235060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235060).length < 2 ^ (prefixWord ++ tailWord_8235060).sum := by decide
  have hdescent : baseEnd_8235060 < baseStart_8235060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235069 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_8235069 : Nat := 118140960795 + 8235069 * 2 ^ 59
def prefixEnd_8235069 : Nat := 4983230072969 + 3 ^ 40 * 8235069 * 2
def baseEnd_8235069 : Nat := 1409516206646848662788371

theorem tailTrace_8235069 : CollatzResearch.WordTrace tailWord_8235069 prefixEnd_8235069 1409516206646848662788371 := by
  unfold tailWord_8235069
  simp only [CollatzResearch.WordTrace]
  refine ⟨300357641802758925658076261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200238427868505950438717507 300357641802758925658076261)
  ·
    refine ⟨56317057838017298560889299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300357641802758925658076261 56317057838017298560889299)
    ·
      refine ⟨84475586757025947841333949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56317057838017298560889299 84475586757025947841333949)
      ·
        refine ⟨31678345033884730440500231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84475586757025947841333949 31678345033884730440500231)
        ·
          refine ⟨47517517550827095660750347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31678345033884730440500231 47517517550827095660750347)
          ·
            refine ⟨71276276326240643491125521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47517517550827095660750347 71276276326240643491125521)
            ·
              refine ⟨53457207244680482618344141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71276276326240643491125521 53457207244680482618344141)
              ·
                refine ⟨20046452716755180981879053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53457207244680482618344141 20046452716755180981879053)
                ·
                  refine ⟨7517419768783192868204645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20046452716755180981879053 7517419768783192868204645)
                  ·
                    refine ⟨1409516206646848662788371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517419768783192868204645 1409516206646848662788371)
                    ·
                      rfl

theorem cell23_8235069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_8235069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235069 prefixEnd_8235069 := by exact prefixLift 8235069
  have htrace : WordTrace (prefixWord ++ tailWord_8235069) baseStart_8235069 baseEnd_8235069 := by
    simpa [prefixWord, tailWord_8235069, baseEnd_8235069] using wordTrace_append hprefix tailTrace_8235069
  have hstable : (prefixWord ++ tailWord_8235069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235069).length < 2 ^ (prefixWord ++ tailWord_8235069).sum := by decide
  have hdescent : baseEnd_8235069 < baseStart_8235069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235096 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_8235096 : Nat := 118140960795 + 8235096 * 2 ^ 59
def prefixEnd_8235096 : Nat := 4983230072969 + 3 ^ 40 * 8235096 * 2
def baseEnd_8235096 : Nat := 4228562483918217382727489

theorem tailTrace_8235096 : CollatzResearch.WordTrace tailWord_8235096 prefixEnd_8235096 4228562483918217382727489 := by
  unfold tailWord_8235096
  simp only [CollatzResearch.WordTrace]
  refine ⟨150179313286830554634654571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200239084382440739512872761 150179313286830554634654571)
  ·
    refine ⟨225268969930245831951981857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150179313286830554634654571 225268969930245831951981857)
    ·
      refine ⟨168951727447684373963986393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225268969930245831951981857 168951727447684373963986393)
      ·
        refine ⟨126713795585763280472989795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168951727447684373963986393 126713795585763280472989795)
        ·
          refine ⟨190070693378644920709484693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126713795585763280472989795 190070693378644920709484693)
          ·
            refine ⟨8909563752123980658257095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190070693378644920709484693 8909563752123980658257095)
            ·
              refine ⟨13364345628185970987385643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909563752123980658257095 13364345628185970987385643)
              ·
                refine ⟨20046518442278956481078465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13364345628185970987385643 20046518442278956481078465)
                ·
                  refine ⟨15034888831709217360808849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20046518442278956481078465 15034888831709217360808849)
                  ·
                    refine ⟨11276166623781913020606637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15034888831709217360808849 11276166623781913020606637)
                    ·
                      refine ⟨4228562483918217382727489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11276166623781913020606637 4228562483918217382727489)
                      ·
                        rfl

theorem cell23_8235096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_8235096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235096 prefixEnd_8235096 := by exact prefixLift 8235096
  have htrace : WordTrace (prefixWord ++ tailWord_8235096) baseStart_8235096 baseEnd_8235096 := by
    simpa [prefixWord, tailWord_8235096, baseEnd_8235096] using wordTrace_append hprefix tailTrace_8235096
  have hstable : (prefixWord ++ tailWord_8235096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235096).length < 2 ^ (prefixWord ++ tailWord_8235096).sum := by decide
  have hdescent : baseEnd_8235096 < baseStart_8235096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235146 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_8235146 : Nat := 118140960795 + 8235146 * 2 ^ 59
def prefixEnd_8235146 : Nat := 4983230072969 + 3 ^ 40 * 8235146 * 2
def baseEnd_8235146 : Nat := 1409529385983647395700753

theorem tailTrace_8235146 : CollatzResearch.WordTrace tailWord_8235146 prefixEnd_8235146 1409529385983647395700753 := by
  unfold tailWord_8235146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75090112555869991952157323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200240300148986645205752861 75090112555869991952157323)
  ·
    refine ⟨112635168833804987928235985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75090112555869991952157323 112635168833804987928235985)
    ·
      refine ⟨84476376625353740946176989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112635168833804987928235985 84476376625353740946176989)
      ·
        refine ⟨31678641234507652854816371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84476376625353740946176989 31678641234507652854816371)
        ·
          refine ⟨47517961851761479282224557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31678641234507652854816371 47517961851761479282224557)
          ·
            refine ⟨17819235694410554730834209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47517961851761479282224557 17819235694410554730834209)
            ·
              refine ⟨13364426770807916048125657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17819235694410554730834209 13364426770807916048125657)
              ·
                refine ⟨10023320078105937036094243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13364426770807916048125657 10023320078105937036094243)
                ·
                  refine ⟨15034980117158905554141365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10023320078105937036094243 15034980117158905554141365)
                  ·
                    refine ⟨1409529385983647395700753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15034980117158905554141365 1409529385983647395700753)
                    ·
                      rfl

theorem cell23_8235146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_8235146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235146 prefixEnd_8235146 := by exact prefixLift 8235146
  have htrace : WordTrace (prefixWord ++ tailWord_8235146) baseStart_8235146 baseEnd_8235146 := by
    simpa [prefixWord, tailWord_8235146, baseEnd_8235146] using wordTrace_append hprefix tailTrace_8235146
  have hstable : (prefixWord ++ tailWord_8235146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235146).length < 2 ^ (prefixWord ++ tailWord_8235146).sum := by decide
  have hdescent : baseEnd_8235146 < baseStart_8235146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235152 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_8235152 : Nat := 118140960795 + 8235152 * 2 ^ 59
def prefixEnd_8235152 : Nat := 4983230072969 + 3 ^ 40 * 8235152 * 2
def baseEnd_8235152 : Nat := 4228591238834869163627231

theorem tailTrace_8235152 : CollatzResearch.WordTrace tailWord_8235152 prefixEnd_8235152 4228591238834869163627231 := by
  unfold tailWord_8235152
  simp only [CollatzResearch.WordTrace]
  refine ⟨150180334530729115416673855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200240446040972153888898473 150180334530729115416673855)
  ·
    refine ⟨225270501796093673125010783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150180334530729115416673855 225270501796093673125010783)
    ·
      refine ⟨337905752694140509687516175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225270501796093673125010783 337905752694140509687516175)
      ·
        refine ⟨506858629041210764531274263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337905752694140509687516175 506858629041210764531274263)
        ·
          refine ⟨760287943561816146796911395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506858629041210764531274263 760287943561816146796911395)
          ·
            refine ⟨1140431915342724220195367093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760287943561816146796911395 1140431915342724220195367093)
            ·
              refine ⟨106915492063380395643315665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1140431915342724220195367093 106915492063380395643315665)
              ·
                refine ⟨80186619047535296732486749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106915492063380395643315665 80186619047535296732486749)
                ·
                  refine ⟨30069982142825736274682531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80186619047535296732486749 30069982142825736274682531)
                  ·
                    refine ⟨45104973214238604412023797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30069982142825736274682531 45104973214238604412023797)
                    ·
                      refine ⟨4228591238834869163627231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45104973214238604412023797 4228591238834869163627231)
                      ·
                        rfl

theorem cell23_8235152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_8235152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235152 prefixEnd_8235152 := by exact prefixLift 8235152
  have htrace : WordTrace (prefixWord ++ tailWord_8235152) baseStart_8235152 baseEnd_8235152 := by
    simpa [prefixWord, tailWord_8235152, baseEnd_8235152] using wordTrace_append hprefix tailTrace_8235152
  have hstable : (prefixWord ++ tailWord_8235152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235152).length < 2 ^ (prefixWord ++ tailWord_8235152).sum := by decide
  have hdescent : baseEnd_8235152 < baseStart_8235152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235169 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_8235169 : Nat := 118140960795 + 8235169 * 2 ^ 59
def prefixEnd_8235169 : Nat := 4983230072969 + 3 ^ 40 * 8235169 * 2
def baseEnd_8235169 : Nat := 4228599968005995597114653

theorem tailTrace_8235169 : CollatzResearch.WordTrace tailWord_8235169 prefixEnd_8235169 4228599968005995597114653 := by
  unfold tailWord_8235169
  simp only [CollatzResearch.WordTrace]
  refine ⟨300361289102396642736716561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200240859401597761824477707 300361289102396642736716561)
  ·
    refine ⟨225270966826797482052537421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300361289102396642736716561 225270966826797482052537421)
    ·
      refine ⟨84476612560049055769701533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225270966826797482052537421 84476612560049055769701533)
      ·
        refine ⟨31678729710018395913638075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84476612560049055769701533 31678729710018395913638075)
        ·
          refine ⟨47518094565027593870457113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31678729710018395913638075 47518094565027593870457113)
          ·
            refine ⟨35638570923770695402842835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47518094565027593870457113 35638570923770695402842835)
            ·
              refine ⟨53457856385656043104264253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35638570923770695402842835 53457856385656043104264253)
              ·
                refine ⟨20046696144621016164099095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53457856385656043104264253 20046696144621016164099095)
                ·
                  refine ⟨30070044216931524246148643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20046696144621016164099095 30070044216931524246148643)
                  ·
                    refine ⟨45105066325397286369222965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30070044216931524246148643 45105066325397286369222965)
                    ·
                      refine ⟨4228599968005995597114653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45105066325397286369222965 4228599968005995597114653)
                      ·
                        rfl

theorem cell23_8235169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_8235169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235169 prefixEnd_8235169 := by exact prefixLift 8235169
  have htrace : WordTrace (prefixWord ++ tailWord_8235169) baseStart_8235169 baseEnd_8235169 := by
    simpa [prefixWord, tailWord_8235169, baseEnd_8235169] using wordTrace_append hprefix tailTrace_8235169
  have hstable : (prefixWord ++ tailWord_8235169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235169).length < 2 ^ (prefixWord ++ tailWord_8235169).sum := by decide
  have hdescent : baseEnd_8235169 < baseStart_8235169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235192 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_8235192 : Nat := 118140960795 + 8235192 * 2 ^ 59
def prefixEnd_8235192 : Nat := 4983230072969 + 3 ^ 40 * 8235192 * 2
def baseEnd_8235192 : Nat := 4228611778061049007127047

theorem tailTrace_8235192 : CollatzResearch.WordTrace tailWord_8235192 prefixEnd_8235192 4228611778061049007127047 := by
  unfold tailWord_8235192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150181063990656658832401915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200241418654208878443202553 150181063990656658832401915)
  ·
    refine ⟨225271595985984988248602873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150181063990656658832401915 225271595985984988248602873)
    ·
      refine ⟨168953696989488741186452155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225271595985984988248602873 168953696989488741186452155)
      ·
        refine ⟨253430545484233111779678233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168953696989488741186452155 253430545484233111779678233)
        ·
          refine ⟨190072909113174833834758675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253430545484233111779678233 190072909113174833834758675)
          ·
            refine ⟨285109363669762250752138013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190072909113174833834758675 285109363669762250752138013)
            ·
              refine ⟨106916011376160844032051755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285109363669762250752138013 106916011376160844032051755)
              ·
                refine ⟨160374017064241266048077633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106916011376160844032051755 160374017064241266048077633)
                ·
                  refine ⟨120280512798180949536058225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160374017064241266048077633 120280512798180949536058225)
                  ·
                    refine ⟨90210384598635712152043669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120280512798180949536058225 90210384598635712152043669)
                    ·
                      refine ⟨4228611778061049007127047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90210384598635712152043669 4228611778061049007127047)
                      ·
                        rfl

theorem cell23_8235192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_8235192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235192 prefixEnd_8235192 := by exact prefixLift 8235192
  have htrace : WordTrace (prefixWord ++ tailWord_8235192) baseStart_8235192 baseEnd_8235192 := by
    simpa [prefixWord, tailWord_8235192, baseEnd_8235192] using wordTrace_append hprefix tailTrace_8235192
  have hstable : (prefixWord ++ tailWord_8235192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235192).length < 2 ^ (prefixWord ++ tailWord_8235192).sum := by decide
  have hdescent : baseEnd_8235192 < baseStart_8235192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235199 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_8235199 : Nat := 118140960795 + 8235199 * 2 ^ 59
def prefixEnd_8235199 : Nat := 4983230072969 + 3 ^ 40 * 8235199 * 2
def baseEnd_8235199 : Nat := 4228615372425630479739515

theorem tailTrace_8235199 : CollatzResearch.WordTrace tailWord_8235199 prefixEnd_8235199 4228615372425630479739515 := by
  unfold tailWord_8235199
  simp only [CollatzResearch.WordTrace]
  refine ⟨300362383292287957860308651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200241588861525305240205767 300362383292287957860308651)
  ·
    refine ⟨450543574938431936790462977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300362383292287957860308651 450543574938431936790462977)
    ·
      refine ⟨337907681203823952592847233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450543574938431936790462977 337907681203823952592847233)
      ·
        refine ⟨253430760902867964444635425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337907681203823952592847233 253430760902867964444635425)
        ·
          refine ⟨190073070677150973333476569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253430760902867964444635425 190073070677150973333476569)
          ·
            refine ⟨142554803007863230000107427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190073070677150973333476569 142554803007863230000107427)
            ·
              refine ⟨213832204511794845000161141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142554803007863230000107427 213832204511794845000161141)
              ·
                refine ⟨20046769172980766718765107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213832204511794845000161141 20046769172980766718765107)
                ·
                  refine ⟨30070153759471150078147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20046769172980766718765107 30070153759471150078147661)
                  ·
                    refine ⟨11276307659801681279305373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30070153759471150078147661 11276307659801681279305373)
                    ·
                      refine ⟨4228615372425630479739515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11276307659801681279305373 4228615372425630479739515)
                      ·
                        rfl

theorem cell23_8235199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_8235199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235199 prefixEnd_8235199 := by exact prefixLift 8235199
  have htrace : WordTrace (prefixWord ++ tailWord_8235199) baseStart_8235199 baseEnd_8235199 := by
    simpa [prefixWord, tailWord_8235199, baseEnd_8235199] using wordTrace_append hprefix tailTrace_8235199
  have hstable : (prefixWord ++ tailWord_8235199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235199).length < 2 ^ (prefixWord ++ tailWord_8235199).sum := by decide
  have hdescent : baseEnd_8235199 < baseStart_8235199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235233 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_8235233 : Nat := 118140960795 + 8235233 * 2 ^ 59
def prefixEnd_8235233 : Nat := 4983230072969 + 3 ^ 40 * 8235233 * 2
def baseEnd_8235233 : Nat := 4228632830767883346714359

theorem tailTrace_8235233 : CollatzResearch.WordTrace tailWord_8235233 prefixEnd_8235233 4228632830767883346714359 := by
  unfold tailWord_8235233
  simp only [CollatzResearch.WordTrace]
  refine ⟨300363623374164781667046353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200242415582776521111364235 300363623374164781667046353)
  ·
    refine ⟨225272717530623586250284765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300363623374164781667046353 225272717530623586250284765)
    ·
      refine ⟨84477269073983844843856787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225272717530623586250284765 84477269073983844843856787)
      ·
        refine ⟨126715903610975767265785181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84477269073983844843856787 126715903610975767265785181)
        ·
          refine ⟨47518463854115912724669443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126715903610975767265785181 47518463854115912724669443)
          ·
            refine ⟨71277695781173869087004165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47518463854115912724669443 71277695781173869087004165)
            ·
              refine ⟨13364567958970100453813281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71277695781173869087004165 13364567958970100453813281)
              ·
                refine ⟨10023425969227575340359961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13364567958970100453813281 10023425969227575340359961)
                ·
                  refine ⟨7517569476920681505269971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10023425969227575340359961 7517569476920681505269971)
                  ·
                    refine ⟨11276354215381022257904957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517569476920681505269971 11276354215381022257904957)
                    ·
                      refine ⟨4228632830767883346714359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11276354215381022257904957 4228632830767883346714359)
                      ·
                        rfl

theorem cell23_8235233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_8235233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235233 prefixEnd_8235233 := by exact prefixLift 8235233
  have htrace : WordTrace (prefixWord ++ tailWord_8235233) baseStart_8235233 baseEnd_8235233 := by
    simpa [prefixWord, tailWord_8235233, baseEnd_8235233] using wordTrace_append hprefix tailTrace_8235233
  have hstable : (prefixWord ++ tailWord_8235233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235233).length < 2 ^ (prefixWord ++ tailWord_8235233).sum := by decide
  have hdescent : baseEnd_8235233 < baseStart_8235233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235290 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_8235290 : Nat := 118140960795 + 8235290 * 2 ^ 59
def prefixEnd_8235290 : Nat := 4983230072969 + 3 ^ 40 * 8235290 * 2
def baseEnd_8235290 : Nat := 4228662099165189623701597

theorem tailTrace_8235290 : CollatzResearch.WordTrace tailWord_8235290 prefixEnd_8235290 4228662099165189623701597 := by
  unfold tailWord_8235290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091425583739570100467831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200243801556638853601247549 75091425583739570100467831)
  ·
    refine ⟨112637138375609355150701747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75091425583739570100467831 112637138375609355150701747)
    ·
      refine ⟨168955707563414032726052621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112637138375609355150701747 168955707563414032726052621)
      ·
        refine ⟨63358390336280262272269733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168955707563414032726052621 63358390336280262272269733)
        ·
          refine ⟨11879698188052549176050575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63358390336280262272269733 11879698188052549176050575)
          ·
            refine ⟨17819547282078823764075863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879698188052549176050575 17819547282078823764075863)
            ·
              refine ⟨26729320923118235646113795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819547282078823764075863 26729320923118235646113795)
              ·
                refine ⟨40093981384677353469170693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26729320923118235646113795 40093981384677353469170693)
                ·
                  refine ⟨7517621509627003775469505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40093981384677353469170693 7517621509627003775469505)
                  ·
                    refine ⟨5638216132220252831602129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517621509627003775469505 5638216132220252831602129)
                    ·
                      refine ⟨4228662099165189623701597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638216132220252831602129 4228662099165189623701597)
                      ·
                        rfl

theorem cell23_8235290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_8235290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235290 prefixEnd_8235290 := by exact prefixLift 8235290
  have htrace : WordTrace (prefixWord ++ tailWord_8235290) baseStart_8235290 baseEnd_8235290 := by
    simpa [prefixWord, tailWord_8235290, baseEnd_8235290] using wordTrace_append hprefix tailTrace_8235290
  have hstable : (prefixWord ++ tailWord_8235290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235290).length < 2 ^ (prefixWord ++ tailWord_8235290).sum := by decide
  have hdescent : baseEnd_8235290 < baseStart_8235290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235296 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 7]
def baseStart_8235296 : Nat := 118140960795 + 8235296 * 2 ^ 59
def prefixEnd_8235296 : Nat := 4983230072969 + 3 ^ 40 * 8235296 * 2
def baseEnd_8235296 : Nat := 469851686672124066691841

theorem tailTrace_8235296 : CollatzResearch.WordTrace tailWord_8235296 prefixEnd_8235296 469851686672124066691841 := by
  unfold tailWord_8235296
  simp only [CollatzResearch.WordTrace]
  refine ⟨150182960586468271713294871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200243947448624362284393161 150182960586468271713294871)
  ·
    refine ⟨225274440879702407569942307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150182960586468271713294871 225274440879702407569942307)
    ·
      refine ⟨337911661319553611354913461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225274440879702407569942307 337911661319553611354913461)
      ·
        refine ⟨31679218248708151064523137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337911661319553611354913461 31679218248708151064523137)
        ·
          refine ⟨23759413686531113298392353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31679218248708151064523137 23759413686531113298392353)
          ·
            refine ⟨17819560264898334973794265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23759413686531113298392353 17819560264898334973794265)
            ·
              refine ⟨13364670198673751230345699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17819560264898334973794265 13364670198673751230345699)
              ·
                refine ⟨20047005298010626845518549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13364670198673751230345699 20047005298010626845518549)
                ·
                  refine ⟨469851686672124066691841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20047005298010626845518549 469851686672124066691841)
                  ·
                    rfl

theorem cell23_8235296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_8235296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235296 prefixEnd_8235296 := by exact prefixLift 8235296
  have htrace : WordTrace (prefixWord ++ tailWord_8235296) baseStart_8235296 baseEnd_8235296 := by
    simpa [prefixWord, tailWord_8235296, baseEnd_8235296] using wordTrace_append hprefix tailTrace_8235296
  have hstable : (prefixWord ++ tailWord_8235296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235296).length < 2 ^ (prefixWord ++ tailWord_8235296).sum := by decide
  have hdescent : baseEnd_8235296 < baseStart_8235296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235326 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_8235326 : Nat := 118140960795 + 8235326 * 2 ^ 59
def prefixEnd_8235326 : Nat := 4983230072969 + 3 ^ 40 * 8235326 * 2
def baseEnd_8235326 : Nat := 1409560194822917160950477

theorem tailTrace_8235326 : CollatzResearch.WordTrace tailWord_8235326 prefixEnd_8235326 1409560194822917160950477 := by
  unfold tailWord_8235326
  simp only [CollatzResearch.WordTrace]
  refine ⟨37545876920353482318772729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200244676908551905700121221 37545876920353482318772729)
  ·
    refine ⟨28159407690265111739079547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37545876920353482318772729 28159407690265111739079547)
    ·
      refine ⟨42239111535397667608619321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28159407690265111739079547 42239111535397667608619321)
      ·
        refine ⟨31679333651548250706464491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42239111535397667608619321 31679333651548250706464491)
        ·
          refine ⟨47519000477322376059696737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679333651548250706464491 47519000477322376059696737)
          ·
            refine ⟨35639250357991782044772553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47519000477322376059696737 35639250357991782044772553)
            ·
              refine ⟨26729437768493836533579415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35639250357991782044772553 26729437768493836533579415)
              ·
                refine ⟨40094156652740754800369123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26729437768493836533579415 40094156652740754800369123)
                ·
                  refine ⟨60141234979111132200553685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40094156652740754800369123 60141234979111132200553685)
                  ·
                    refine ⟨1409560194822917160950477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60141234979111132200553685 1409560194822917160950477)
                    ·
                      rfl

theorem cell23_8235326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_8235326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235326 prefixEnd_8235326 := by exact prefixLift 8235326
  have htrace : WordTrace (prefixWord ++ tailWord_8235326) baseStart_8235326 baseEnd_8235326 := by
    simpa [prefixWord, tailWord_8235326, baseEnd_8235326] using wordTrace_append hprefix tailTrace_8235326
  have hstable : (prefixWord ++ tailWord_8235326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235326).length < 2 ^ (prefixWord ++ tailWord_8235326).sum := by decide
  have hdescent : baseEnd_8235326 < baseStart_8235326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235346 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_8235346 : Nat := 118140960795 + 8235346 * 2 ^ 59
def prefixEnd_8235346 : Nat := 4983230072969 + 3 ^ 40 * 8235346 * 2
def baseEnd_8235346 : Nat := 4228690854081841404601339

theorem tailTrace_8235346 : CollatzResearch.WordTrace tailWord_8235346 prefixEnd_8235346 4228690854081841404601339 := by
  unfold tailWord_8235346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091936205688850491477473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200245163215170267977273261 75091936205688850491477473)
  ·
    refine ⟨56318952154266637868608105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75091936205688850491477473 56318952154266637868608105)
    ·
      refine ⟨42239214115699978401456079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56318952154266637868608105 42239214115699978401456079)
      ·
        refine ⟨63358821173549967602184119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42239214115699978401456079 63358821173549967602184119)
        ·
          refine ⟨95038231760324951403276179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63358821173549967602184119 95038231760324951403276179)
          ·
            refine ⟨142557347640487427104914269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95038231760324951403276179 142557347640487427104914269)
            ·
              refine ⟨53459005365182785164342851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142557347640487427104914269 53459005365182785164342851)
              ·
                refine ⟨80188508047774177746514277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53459005365182785164342851 80188508047774177746514277)
                ·
                  refine ⟨15035345258957658327471427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80188508047774177746514277 15035345258957658327471427)
                  ·
                    refine ⟨22553017888436487491207141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15035345258957658327471427 22553017888436487491207141)
                    ·
                      refine ⟨4228690854081841404601339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22553017888436487491207141 4228690854081841404601339)
                      ·
                        rfl

theorem cell23_8235346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_8235346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235346 prefixEnd_8235346 := by exact prefixLift 8235346
  have htrace : WordTrace (prefixWord ++ tailWord_8235346) baseStart_8235346 baseEnd_8235346 := by
    simpa [prefixWord, tailWord_8235346, baseEnd_8235346] using wordTrace_append hprefix tailTrace_8235346
  have hstable : (prefixWord ++ tailWord_8235346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235346).length < 2 ^ (prefixWord ++ tailWord_8235346).sum := by decide
  have hdescent : baseEnd_8235346 < baseStart_8235346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235358 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_8235358 : Nat := 118140960795 + 8235358 * 2 ^ 59
def prefixEnd_8235358 : Nat := 4983230072969 + 3 ^ 40 * 8235358 * 2
def baseEnd_8235358 : Nat := 4228697015849695357651285

theorem tailTrace_8235358 : CollatzResearch.WordTrace tailWord_8235358 prefixEnd_8235358 4228697015849695357651285 := by
  unfold tailWord_8235358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37546022812338991001918341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200245454999141285343564485 37546022812338991001918341)
  ·
    refine ⟨7039879277313560812859689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37546022812338991001918341 7039879277313560812859689)
    ·
      refine ⟨5279909457985170609644767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7039879277313560812859689 5279909457985170609644767)
      ·
        refine ⟨7919864186977755914467151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279909457985170609644767 7919864186977755914467151)
        ·
          refine ⟨11879796280466633871700727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919864186977755914467151 11879796280466633871700727)
          ·
            refine ⟨17819694420699950807551091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879796280466633871700727 17819694420699950807551091)
            ·
              refine ⟨26729541631049926211326637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819694420699950807551091 26729541631049926211326637)
              ·
                refine ⟨10023578111643722329247489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26729541631049926211326637 10023578111643722329247489)
                ·
                  refine ⟨7517683583732791746935617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10023578111643722329247489 7517683583732791746935617)
                  ·
                    refine ⟨5638262687799593810201713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517683583732791746935617 5638262687799593810201713)
                    ·
                      refine ⟨4228697015849695357651285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638262687799593810201713 4228697015849695357651285)
                      ·
                        rfl

theorem cell23_8235358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_8235358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235358 prefixEnd_8235358 := by exact prefixLift 8235358
  have htrace : WordTrace (prefixWord ++ tailWord_8235358) baseStart_8235358 baseEnd_8235358 := by
    simpa [prefixWord, tailWord_8235358, baseEnd_8235358] using wordTrace_append hprefix tailTrace_8235358
  have hstable : (prefixWord ++ tailWord_8235358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235358).length < 2 ^ (prefixWord ++ tailWord_8235358).sum := by decide
  have hdescent : baseEnd_8235358 < baseStart_8235358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235359 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_8235359 : Nat := 118140960795 + 8235359 * 2 ^ 59
def prefixEnd_8235359 : Nat := 4983230072969 + 3 ^ 40 * 8235359 * 2
def baseEnd_8235359 : Nat := 4228697529330349853738779

theorem tailTrace_8235359 : CollatzResearch.WordTrace tailWord_8235359 prefixEnd_8235359 4228697529330349853738779 := by
  unfold tailWord_8235359
  simp only [CollatzResearch.WordTrace]
  refine ⟨300368218971708305186133131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200245479314472203457422087 300368218971708305186133131)
  ·
    refine ⟨450552328457562457779199697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300368218971708305186133131 450552328457562457779199697)
    ·
      refine ⟨337914246343171843334399773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450552328457562457779199697 337914246343171843334399773)
      ·
        refine ⟨126717842378689441250399915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337914246343171843334399773 126717842378689441250399915)
        ·
          refine ⟨190076763568034161875599873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126717842378689441250399915 190076763568034161875599873)
          ·
            refine ⟨142557572676025621406699905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190076763568034161875599873 142557572676025621406699905)
            ·
              refine ⟨106918179507019216055024929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142557572676025621406699905 106918179507019216055024929)
              ·
                refine ⟨80188634630264412041268697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106918179507019216055024929 80188634630264412041268697)
                ·
                  refine ⟨60141475972698309030951523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80188634630264412041268697 60141475972698309030951523)
                  ·
                    refine ⟨90212213959047463546427285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60141475972698309030951523 90212213959047463546427285)
                    ·
                      refine ⟨4228697529330349853738779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90212213959047463546427285 4228697529330349853738779)
                      ·
                        rfl

theorem cell23_8235359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_8235359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235359 prefixEnd_8235359 := by exact prefixLift 8235359
  have htrace : WordTrace (prefixWord ++ tailWord_8235359) baseStart_8235359 baseEnd_8235359 := by
    simpa [prefixWord, tailWord_8235359, baseEnd_8235359] using wordTrace_append hprefix tailTrace_8235359
  have hstable : (prefixWord ++ tailWord_8235359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235359).length < 2 ^ (prefixWord ++ tailWord_8235359).sum := by decide
  have hdescent : baseEnd_8235359 < baseStart_8235359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235409 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_8235409 : Nat := 118140960795 + 8235409 * 2 ^ 59
def prefixEnd_8235409 : Nat := 4983230072969 + 3 ^ 40 * 8235409 * 2
def baseEnd_8235409 : Nat := 4228723203363074658113549

theorem tailTrace_8235409 : CollatzResearch.WordTrace tailWord_8235409 prefixEnd_8235409 4228723203363074658113549 := by
  unfold tailWord_8235409
  simp only [CollatzResearch.WordTrace]
  refine ⟨300370042621527163725453281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200246695081018109150302187 300370042621527163725453281)
  ·
    refine ⟨225277531966145372794089961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300370042621527163725453281 225277531966145372794089961)
    ·
      refine ⟨168958148974609029595567471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225277531966145372794089961 168958148974609029595567471)
      ·
        refine ⟨253437223461913544393351207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168958148974609029595567471 253437223461913544393351207)
        ·
          refine ⟨380155835192870316590026811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253437223461913544393351207 380155835192870316590026811)
          ·
            refine ⟨570233752789305474885040217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380155835192870316590026811 570233752789305474885040217)
            ·
              refine ⟨427675314591979106163780163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570233752789305474885040217 427675314591979106163780163)
              ·
                refine ⟨641512971887968659245670245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427675314591979106163780163 641512971887968659245670245)
                ·
                  refine ⟨120283682228994123608563171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641512971887968659245670245 120283682228994123608563171)
                  ·
                    refine ⟨180425523343491185412844757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120283682228994123608563171 180425523343491185412844757)
                    ·
                      refine ⟨4228723203363074658113549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180425523343491185412844757 4228723203363074658113549)
                      ·
                        rfl

theorem cell23_8235409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_8235409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235409 prefixEnd_8235409 := by exact prefixLift 8235409
  have htrace : WordTrace (prefixWord ++ tailWord_8235409) baseStart_8235409 baseEnd_8235409 := by
    simpa [prefixWord, tailWord_8235409, baseEnd_8235409] using wordTrace_append hprefix tailTrace_8235409
  have hstable : (prefixWord ++ tailWord_8235409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235409).length < 2 ^ (prefixWord ++ tailWord_8235409).sum := by decide
  have hdescent : baseEnd_8235409 < baseStart_8235409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235413 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_8235413 : Nat := 118140960795 + 8235413 * 2 ^ 59
def prefixEnd_8235413 : Nat := 4983230072969 + 3 ^ 40 * 8235413 * 2
def baseEnd_8235413 : Nat := 4228725257285692642463531

theorem tailTrace_8235413 : CollatzResearch.WordTrace tailWord_8235413 prefixEnd_8235413 4228725257285692642463531 := by
  unfold tailWord_8235413
  simp only [CollatzResearch.WordTrace]
  refine ⟨300370188513512672408598893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200246792342341781605732595 300370188513512672408598893)
  ·
    refine ⟨112638820692567252153224585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300370188513512672408598893 112638820692567252153224585)
    ·
      refine ⟨84479115519425439114918439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112638820692567252153224585 84479115519425439114918439)
      ·
        refine ⟨126718673279138158672377659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84479115519425439114918439 126718673279138158672377659)
        ·
          refine ⟨190078009918707238008566489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126718673279138158672377659 190078009918707238008566489)
          ·
            refine ⟨142558507439030428506424867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190078009918707238008566489 142558507439030428506424867)
            ·
              refine ⟨213837761158545642759637301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142558507439030428506424867 213837761158545642759637301)
              ·
                refine ⟨20047290108613654008715997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213837761158545642759637301 20047290108613654008715997)
                ·
                  refine ⟨7517733790730120253268499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20047290108613654008715997 7517733790730120253268499)
                  ·
                    refine ⟨11276600686095180379902749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517733790730120253268499 11276600686095180379902749)
                    ·
                      refine ⟨4228725257285692642463531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11276600686095180379902749 4228725257285692642463531)
                      ·
                        rfl

theorem cell23_8235413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_8235413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235413 prefixEnd_8235413 := by exact prefixLift 8235413
  have htrace : WordTrace (prefixWord ++ tailWord_8235413) baseStart_8235413 baseEnd_8235413 := by
    simpa [prefixWord, tailWord_8235413, baseEnd_8235413] using wordTrace_append hprefix tailTrace_8235413
  have hstable : (prefixWord ++ tailWord_8235413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235413).length < 2 ^ (prefixWord ++ tailWord_8235413).sum := by decide
  have hdescent : baseEnd_8235413 < baseStart_8235413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235423 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 5, 2]
def baseStart_8235423 : Nat := 118140960795 + 8235423 * 2 ^ 59
def prefixEnd_8235423 : Nat := 4983230072969 + 3 ^ 40 * 8235423 * 2
def baseEnd_8235423 : Nat := 4228730392092237603338485

theorem tailTrace_8235423 : CollatzResearch.WordTrace tailWord_8235423 prefixEnd_8235423 4228730392092237603338485 := by
  unfold tailWord_8235423
  simp only [CollatzResearch.WordTrace]
  refine ⟨300370553243476444116462923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200247035495650962744308615 300370553243476444116462923)
  ·
    refine ⟨450555829865214666174694385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300370553243476444116462923 450555829865214666174694385)
    ·
      refine ⟨337916872398910999631020789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450555829865214666174694385 337916872398910999631020789)
      ·
        refine ⟨31679706787397906215408199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337916872398910999631020789 31679706787397906215408199)
        ·
          refine ⟨47519560181096859323112299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679706787397906215408199 47519560181096859323112299)
          ·
            refine ⟨71279340271645288984668449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47519560181096859323112299 71279340271645288984668449)
            ·
              refine ⟨53459505203733966738501337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71279340271645288984668449 53459505203733966738501337)
              ·
                refine ⟨40094628902800475053876003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53459505203733966738501337 40094628902800475053876003)
                ·
                  refine ⟨60141943354200712580814005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40094628902800475053876003 60141943354200712580814005)
                  ·
                    refine ⟨5638307189456316804451313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60141943354200712580814005 5638307189456316804451313)
                    ·
                      refine ⟨4228730392092237603338485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638307189456316804451313 4228730392092237603338485)
                      ·
                        rfl

theorem cell23_8235423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_8235423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235423 prefixEnd_8235423 := by exact prefixLift 8235423
  have htrace : WordTrace (prefixWord ++ tailWord_8235423) baseStart_8235423 baseEnd_8235423 := by
    simpa [prefixWord, tailWord_8235423, baseEnd_8235423] using wordTrace_append hprefix tailTrace_8235423
  have hstable : (prefixWord ++ tailWord_8235423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235423).length < 2 ^ (prefixWord ++ tailWord_8235423).sum := by decide
  have hdescent : baseEnd_8235423 < baseStart_8235423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235426 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_8235426 : Nat := 118140960795 + 8235426 * 2 ^ 59
def prefixEnd_8235426 : Nat := 4983230072969 + 3 ^ 40 * 8235426 * 2
def baseEnd_8235426 : Nat := 4228731932534201091600971

theorem tailTrace_8235426 : CollatzResearch.WordTrace tailWord_8235426 prefixEnd_8235426 4228731932534201091600971 := by
  unfold tailWord_8235426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75092665665616393907205533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200247108441643717085881421 75092665665616393907205533)
  ·
    refine ⟨28159749624606147715202075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75092665665616393907205533 28159749624606147715202075)
    ·
      refine ⟨42239624436909221572803113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28159749624606147715202075 42239624436909221572803113)
      ·
        refine ⟨31679718327681916179602335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42239624436909221572803113 31679718327681916179602335)
        ·
          refine ⟨47519577491522874269403503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679718327681916179602335 47519577491522874269403503)
          ·
            refine ⟨71279366237284311404105255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47519577491522874269403503 71279366237284311404105255)
            ·
              refine ⟨106919049355926467106157883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71279366237284311404105255 106919049355926467106157883)
              ·
                refine ⟨160378574033889700659236825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106919049355926467106157883 160378574033889700659236825)
                ·
                  refine ⟨120283930525417275494427619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160378574033889700659236825 120283930525417275494427619)
                  ·
                    refine ⟨180425895788125913241641429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120283930525417275494427619 180425895788125913241641429)
                    ·
                      refine ⟨4228731932534201091600971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180425895788125913241641429 4228731932534201091600971)
                      ·
                        rfl

theorem cell23_8235426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_8235426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235426 prefixEnd_8235426 := by exact prefixLift 8235426
  have htrace : WordTrace (prefixWord ++ tailWord_8235426) baseStart_8235426 baseEnd_8235426 := by
    simpa [prefixWord, tailWord_8235426, baseEnd_8235426] using wordTrace_append hprefix tailTrace_8235426
  have hstable : (prefixWord ++ tailWord_8235426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235426).length < 2 ^ (prefixWord ++ tailWord_8235426).sum := by decide
  have hdescent : baseEnd_8235426 < baseStart_8235426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235447 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_8235447 : Nat := 118140960795 + 8235447 * 2 ^ 59
def prefixEnd_8235447 : Nat := 4983230072969 + 3 ^ 40 * 8235447 * 2
def baseEnd_8235447 : Nat := 4228742715627945509438375

theorem tailTrace_8235447 : CollatzResearch.WordTrace tailWord_8235447 prefixEnd_8235447 4228742715627945509438375 := by
  unfold tailWord_8235447
  simp only [CollatzResearch.WordTrace]
  refine ⟨300371428595389496215336595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200247619063592997476891063 300371428595389496215336595)
  ·
    refine ⟨450557142893084244323004893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300371428595389496215336595 450557142893084244323004893)
    ·
      refine ⟨168958928584906591621126835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450557142893084244323004893 168958928584906591621126835)
      ·
        refine ⟨253438392877359887431690253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168958928584906591621126835 253438392877359887431690253)
        ·
          refine ⟨95039397329009957786883845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253438392877359887431690253 95039397329009957786883845)
          ·
            refine ⟨17819886999189367085040721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95039397329009957786883845 17819886999189367085040721)
            ·
              refine ⟨13364915249392025313780541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17819886999189367085040721 13364915249392025313780541)
              ·
                refine ⟨5011843218522009492667703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13364915249392025313780541 5011843218522009492667703)
                ·
                  refine ⟨7517764827783014239001555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011843218522009492667703 7517764827783014239001555)
                  ·
                    refine ⟨11276647241674521358502333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517764827783014239001555 11276647241674521358502333)
                    ·
                      refine ⟨4228742715627945509438375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11276647241674521358502333 4228742715627945509438375)
                      ·
                        rfl

theorem cell23_8235447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_8235447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235447 prefixEnd_8235447 := by exact prefixLift 8235447
  have htrace : WordTrace (prefixWord ++ tailWord_8235447) baseStart_8235447 baseEnd_8235447 := by
    simpa [prefixWord, tailWord_8235447, baseEnd_8235447] using wordTrace_append hprefix tailTrace_8235447
  have hstable : (prefixWord ++ tailWord_8235447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235447).length < 2 ^ (prefixWord ++ tailWord_8235447).sum := by decide
  have hdescent : baseEnd_8235447 < baseStart_8235447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235456 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_8235456 : Nat := 118140960795 + 8235456 * 2 ^ 59
def prefixEnd_8235456 : Nat := 4983230072969 + 3 ^ 40 * 8235456 * 2
def baseEnd_8235456 : Nat := 4228747336953835974225833

theorem tailTrace_8235456 : CollatzResearch.WordTrace tailWord_8235456 prefixEnd_8235456 4228747336953835974225833 := by
  unfold tailWord_8235456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150185878426178445376207111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200247837901571260501609481 150185878426178445376207111)
  ·
    refine ⟨225278817639267668064310667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150185878426178445376207111 225278817639267668064310667)
    ·
      refine ⟨337918226458901502096466001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225278817639267668064310667 337918226458901502096466001)
      ·
        refine ⟨253438669844176126572349501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337918226458901502096466001 253438669844176126572349501)
        ·
          refine ⟨95039501191566047464631063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253438669844176126572349501 95039501191566047464631063)
          ·
            refine ⟨142559251787349071196946595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95039501191566047464631063 142559251787349071196946595)
            ·
              refine ⟨213838877681023606795419893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142559251787349071196946595 213838877681023606795419893)
              ·
                refine ⟨20047394782595963137070615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213838877681023606795419893 20047394782595963137070615)
                ·
                  refine ⟨30071092173893944705605923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20047394782595963137070615 30071092173893944705605923)
                  ·
                    refine ⟨45106638260840917058408885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30071092173893944705605923 45106638260840917058408885)
                    ·
                      refine ⟨4228747336953835974225833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45106638260840917058408885 4228747336953835974225833)
                      ·
                        rfl

theorem cell23_8235456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_8235456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235456 prefixEnd_8235456 := by exact prefixLift 8235456
  have htrace : WordTrace (prefixWord ++ tailWord_8235456) baseStart_8235456 baseEnd_8235456 := by
    simpa [prefixWord, tailWord_8235456, baseEnd_8235456] using wordTrace_append hprefix tailTrace_8235456
  have hstable : (prefixWord ++ tailWord_8235456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235456).length < 2 ^ (prefixWord ++ tailWord_8235456).sum := by decide
  have hdescent : baseEnd_8235456 < baseStart_8235456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235463 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 4, 4]
def baseStart_8235463 : Nat := 118140960795 + 8235463 * 2 ^ 59
def prefixEnd_8235463 : Nat := 4983230072969 + 3 ^ 40 * 8235463 * 2
def baseEnd_8235463 : Nat := 1409583643772805815612767

theorem tailTrace_8235463 : CollatzResearch.WordTrace tailWord_8235463 prefixEnd_8235463 1409583643772805815612767 := by
  unfold tailWord_8235463
  simp only [CollatzResearch.WordTrace]
  refine ⟨300372012163331530947919043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200248008108887687298612695 300372012163331530947919043)
  ·
    refine ⟨450558018244997296421878565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300372012163331530947919043 450558018244997296421878565)
    ·
      refine ⟨84479628420936993079102231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450558018244997296421878565 84479628420936993079102231)
      ·
        refine ⟨126719442631405489618653347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84479628420936993079102231 126719442631405489618653347)
        ·
          refine ⟨190079163947108234427980021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126719442631405489618653347 190079163947108234427980021)
          ·
            refine ⟨17819921620041396977623127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190079163947108234427980021 17819921620041396977623127)
            ·
              refine ⟨26729882430062095466434691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819921620041396977623127 26729882430062095466434691)
              ·
                refine ⟨40094823645093143199652037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26729882430062095466434691 40094823645093143199652037)
                ·
                  refine ⟨7517779433454964349934757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40094823645093143199652037 7517779433454964349934757)
                  ·
                    refine ⟨1409583643772805815612767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517779433454964349934757 1409583643772805815612767)
                    ·
                      rfl

theorem cell23_8235463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_8235463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235463 prefixEnd_8235463 := by exact prefixLift 8235463
  have htrace : WordTrace (prefixWord ++ tailWord_8235463) baseStart_8235463 baseEnd_8235463 := by
    simpa [prefixWord, tailWord_8235463, baseEnd_8235463] using wordTrace_append hprefix tailTrace_8235463
  have hstable : (prefixWord ++ tailWord_8235463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235463).length < 2 ^ (prefixWord ++ tailWord_8235463).sum := by decide
  have hdescent : baseEnd_8235463 < baseStart_8235463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235466 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_8235466 : Nat := 118140960795 + 8235466 * 2 ^ 59
def prefixEnd_8235466 : Nat := 4983230072969 + 3 ^ 40 * 8235466 * 2
def baseEnd_8235466 : Nat := 4228752471760380935100787

theorem tailTrace_8235466 : CollatzResearch.WordTrace tailWord_8235466 prefixEnd_8235466 4228752471760380935100787 := by
  unfold tailWord_8235466
  simp only [CollatzResearch.WordTrace]
  refine ⟨75093030395580165615069563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200248081054880441640185501 75093030395580165615069563)
  ·
    refine ⟨112639545593370248422604345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75093030395580165615069563 112639545593370248422604345)
    ·
      refine ⟨84479659195027686316953259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112639545593370248422604345 84479659195027686316953259)
      ·
        refine ⟨126719488792541529475429889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84479659195027686316953259 126719488792541529475429889)
        ·
          refine ⟨95039616594406147106572417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126719488792541529475429889 95039616594406147106572417)
          ·
            refine ⟨71279712445804610329929313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95039616594406147106572417 71279712445804610329929313)
            ·
              refine ⟨53459784334353457747446985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71279712445804610329929313 53459784334353457747446985)
              ·
                refine ⟨40094838250765093310585239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53459784334353457747446985 40094838250765093310585239)
                ·
                  refine ⟨60142257376147639965877859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40094838250765093310585239 60142257376147639965877859)
                  ·
                    refine ⟨90213386064221459948816789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60142257376147639965877859 90213386064221459948816789)
                    ·
                      refine ⟨4228752471760380935100787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90213386064221459948816789 4228752471760380935100787)
                      ·
                        rfl

theorem cell23_8235466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_8235466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235466 prefixEnd_8235466 := by exact prefixLift 8235466
  have htrace : WordTrace (prefixWord ++ tailWord_8235466) baseStart_8235466 baseEnd_8235466 := by
    simpa [prefixWord, tailWord_8235466, baseEnd_8235466] using wordTrace_append hprefix tailTrace_8235466
  have hstable : (prefixWord ++ tailWord_8235466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235466).length < 2 ^ (prefixWord ++ tailWord_8235466).sum := by decide
  have hdescent : baseEnd_8235466 < baseStart_8235466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235493 : List Nat := [1, 3, 1, 5, 2, 1, 1, 9]
def baseStart_8235493 : Nat := 118140960795 + 8235493 * 2 ^ 59
def prefixEnd_8235493 : Nat := 4983230072969 + 3 ^ 40 * 8235493 * 2
def baseEnd_8235493 : Nat := 156620975397705641831969

theorem tailTrace_8235493 : CollatzResearch.WordTrace tailWord_8235493 prefixEnd_8235493 156620975397705641831969 := by
  unfold tailWord_8235493
  simp only [CollatzResearch.WordTrace]
  refine ⟨300373106353222846071511133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200248737568815230714340755 300373106353222846071511133)
  ·
    refine ⟨112639914882458567276816675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300373106353222846071511133 112639914882458567276816675)
    ·
      refine ⟨168959872323687850915225013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112639914882458567276816675 168959872323687850915225013)
      ·
        refine ⟨15839988030345736023302345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168959872323687850915225013 15839988030345736023302345)
        ·
          refine ⟨11879991022759302017476759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15839988030345736023302345 11879991022759302017476759)
          ·
            refine ⟨17819986534138953026215139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879991022759302017476759 17819986534138953026215139)
            ·
              refine ⟨26729979801208429539322709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819986534138953026215139 26729979801208429539322709)
              ·
                refine ⟨156620975397705641831969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26729979801208429539322709 156620975397705641831969)
                ·
                  rfl

theorem cell23_8235493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 9].length) (baseStart_8235493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235493 prefixEnd_8235493 := by exact prefixLift 8235493
  have htrace : WordTrace (prefixWord ++ tailWord_8235493) baseStart_8235493 baseEnd_8235493 := by
    simpa [prefixWord, tailWord_8235493, baseEnd_8235493] using wordTrace_append hprefix tailTrace_8235493
  have hstable : (prefixWord ++ tailWord_8235493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235493).length < 2 ^ (prefixWord ++ tailWord_8235493).sum := by decide
  have hdescent : baseEnd_8235493 < baseStart_8235493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235516 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_8235516 : Nat := 118140960795 + 8235516 * 2 ^ 59
def prefixEnd_8235516 : Nat := 4983230072969 + 3 ^ 40 * 8235516 * 2
def baseEnd_8235516 : Nat := 4228778145793105739475557

theorem tailTrace_8235516 : CollatzResearch.WordTrace tailWord_8235516 prefixEnd_8235516 4228778145793105739475557 := by
  unfold tailWord_8235516
  simp only [CollatzResearch.WordTrace]
  refine ⟨150186972616069760499799201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200249296821426347333065601 150186972616069760499799201)
  ·
    refine ⟨112640229462052320374849401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150186972616069760499799201 112640229462052320374849401)
    ·
      refine ⟨84480172096539240281137051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112640229462052320374849401 84480172096539240281137051)
      ·
        refine ⟨126720258144808860421705577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84480172096539240281137051 126720258144808860421705577)
        ·
          refine ⟨95040193608606645316279183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126720258144808860421705577 95040193608606645316279183)
          ·
            refine ⟨142560290412909967974418775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95040193608606645316279183 142560290412909967974418775)
            ·
              refine ⟨213840435619364951961628163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142560290412909967974418775 213840435619364951961628163)
              ·
                refine ⟨320760653429047427942442245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213840435619364951961628163 320760653429047427942442245)
                ·
                  refine ⟨60142622517946392739207921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320760653429047427942442245 60142622517946392739207921)
                  ·
                    refine ⟨45106966888459794554405941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60142622517946392739207921 45106966888459794554405941)
                    ·
                      refine ⟨4228778145793105739475557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45106966888459794554405941 4228778145793105739475557)
                      ·
                        rfl

theorem cell23_8235516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_8235516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235516 prefixEnd_8235516 := by exact prefixLift 8235516
  have htrace : WordTrace (prefixWord ++ tailWord_8235516) baseStart_8235516 baseEnd_8235516 := by
    simpa [prefixWord, tailWord_8235516, baseEnd_8235516] using wordTrace_append hprefix tailTrace_8235516
  have hstable : (prefixWord ++ tailWord_8235516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235516).length < 2 ^ (prefixWord ++ tailWord_8235516).sum := by decide
  have hdescent : baseEnd_8235516 < baseStart_8235516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235521 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_8235521 : Nat := 118140960795 + 8235521 * 2 ^ 59
def prefixEnd_8235521 : Nat := 4983230072969 + 3 ^ 40 * 8235521 * 2
def baseEnd_8235521 : Nat := 4228780713196378219913035

theorem tailTrace_8235521 : CollatzResearch.WordTrace tailWord_8235521 prefixEnd_8235521 4228780713196378219913035 := by
  unfold tailWord_8235521
  simp only [CollatzResearch.WordTrace]
  refine ⟨300374127597121406853530417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200249418398080937902353611 300374127597121406853530417)
  ·
    refine ⟨225280595697841055140147813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300374127597121406853530417 225280595697841055140147813)
    ·
      refine ⟨42240111693345197838777715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225280595697841055140147813 42240111693345197838777715)
      ·
        refine ⟨63360167540017796758166573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42240111693345197838777715 63360167540017796758166573)
        ·
          refine ⟨23760062827506673784312465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63360167540017796758166573 23760062827506673784312465)
          ·
            refine ⟨17820047120630005338234349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23760062827506673784312465 17820047120630005338234349)
            ·
              refine ⟨6682517670236252001837881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17820047120630005338234349 6682517670236252001837881)
              ·
                refine ⟨5011888252677189001378411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682517670236252001837881 5011888252677189001378411)
                ·
                  refine ⟨7517832379015783502067617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011888252677189001378411 7517832379015783502067617)
                  ·
                    refine ⟨5638374284261837626550713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517832379015783502067617 5638374284261837626550713)
                    ·
                      refine ⟨4228780713196378219913035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638374284261837626550713 4228780713196378219913035)
                      ·
                        rfl

theorem cell23_8235521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_8235521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235521 prefixEnd_8235521 := by exact prefixLift 8235521
  have htrace : WordTrace (prefixWord ++ tailWord_8235521) baseStart_8235521 baseEnd_8235521 := by
    simpa [prefixWord, tailWord_8235521, baseEnd_8235521] using wordTrace_append hprefix tailTrace_8235521
  have hstable : (prefixWord ++ tailWord_8235521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235521).length < 2 ^ (prefixWord ++ tailWord_8235521).sum := by decide
  have hdescent : baseEnd_8235521 < baseStart_8235521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235530 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_8235530 : Nat := 118140960795 + 8235530 * 2 ^ 59
def prefixEnd_8235530 : Nat := 4983230072969 + 3 ^ 40 * 8235530 * 2
def baseEnd_8235530 : Nat := 4228785334522268684700493

theorem tailTrace_8235530 : CollatzResearch.WordTrace tailWord_8235530 prefixEnd_8235530 4228785334522268684700493 := by
  unfold tailWord_8235530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75093613963522200347652011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200249637236059200927072029 75093613963522200347652011)
  ·
    refine ⟨112640420945283300521478017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75093613963522200347652011 112640420945283300521478017)
    ·
      refine ⟨84480315708962475391108513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112640420945283300521478017 84480315708962475391108513)
      ·
        refine ⟨63360236781721856543331385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84480315708962475391108513 63360236781721856543331385)
        ·
          refine ⟨47520177586291392407498539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63360236781721856543331385 47520177586291392407498539)
          ·
            refine ⟨71280266379437088611247809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47520177586291392407498539 71280266379437088611247809)
            ·
              refine ⟨53460199784577816458435857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71280266379437088611247809 53460199784577816458435857)
              ·
                refine ⟨40095149838433362343826893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53460199784577816458435857 40095149838433362343826893)
                ·
                  refine ⟨15035681189412510878935085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40095149838433362343826893 15035681189412510878935085)
                  ·
                    refine ⟨5638380446029691579600657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15035681189412510878935085 5638380446029691579600657)
                    ·
                      refine ⟨4228785334522268684700493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638380446029691579600657 4228785334522268684700493)
                      ·
                        rfl

theorem cell23_8235530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_8235530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235530 prefixEnd_8235530 := by exact prefixLift 8235530
  have htrace : WordTrace (prefixWord ++ tailWord_8235530) baseStart_8235530 baseEnd_8235530 := by
    simpa [prefixWord, tailWord_8235530, baseEnd_8235530] using wordTrace_append hprefix tailTrace_8235530
  have hstable : (prefixWord ++ tailWord_8235530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235530).length < 2 ^ (prefixWord ++ tailWord_8235530).sum := by decide
  have hdescent : baseEnd_8235530 < baseStart_8235530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235572 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_8235572 : Nat := 118140960795 + 8235572 * 2 ^ 59
def prefixEnd_8235572 : Nat := 4983230072969 + 3 ^ 40 * 8235572 * 2
def baseEnd_8235572 : Nat := 4228806900709757520375301

theorem tailTrace_8235572 : CollatzResearch.WordTrace tailWord_8235572 prefixEnd_8235572 4228806900709757520375301 := by
  unfold tailWord_8235572
  simp only [CollatzResearch.WordTrace]
  refine ⟨150187993859968321281818485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200250658479957761709091313 150187993859968321281818485)
  ·
    refine ⟨14080124424372030120170483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150187993859968321281818485 14080124424372030120170483)
    ·
      refine ⟨21120186636558045180255725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14080124424372030120170483 21120186636558045180255725)
      ·
        refine ⟨7920069988709266942595897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21120186636558045180255725 7920069988709266942595897)
        ·
          refine ⟨5940052491531950206946923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7920069988709266942595897 5940052491531950206946923)
          ·
            refine ⟨8910078737297925310420385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940052491531950206946923 8910078737297925310420385)
            ·
              refine ⟨6682559052973443982815289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910078737297925310420385 6682559052973443982815289)
              ·
                refine ⟨5011919289730082987111467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682559052973443982815289 5011919289730082987111467)
                ·
                  refine ⟨7517878934595124480667201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011919289730082987111467 7517878934595124480667201)
                  ·
                    refine ⟨5638409200946343360500401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517878934595124480667201 5638409200946343360500401)
                    ·
                      refine ⟨4228806900709757520375301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638409200946343360500401 4228806900709757520375301)
                      ·
                        rfl

theorem cell23_8235572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_8235572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235572 prefixEnd_8235572 := by exact prefixLift 8235572
  have htrace : WordTrace (prefixWord ++ tailWord_8235572) baseStart_8235572 baseEnd_8235572 := by
    simpa [prefixWord, tailWord_8235572, baseEnd_8235572] using wordTrace_append hprefix tailTrace_8235572
  have hstable : (prefixWord ++ tailWord_8235572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235572).length < 2 ^ (prefixWord ++ tailWord_8235572).sum := by decide
  have hdescent : baseEnd_8235572 < baseStart_8235572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235573 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_8235573 : Nat := 118140960795 + 8235573 * 2 ^ 59
def prefixEnd_8235573 : Nat := 4983230072969 + 3 ^ 40 * 8235573 * 2
def baseEnd_8235573 : Nat := 4228807414190412016462795

theorem tailTrace_8235573 : CollatzResearch.WordTrace tailWord_8235573 prefixEnd_8235573 4228807414190412016462795 := by
  unfold tailWord_8235573
  simp only [CollatzResearch.WordTrace]
  refine ⟨300376024192933019734423373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200250682795288679822948915 300376024192933019734423373)
  ·
    refine ⟨112641009072349882400408765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300376024192933019734423373 112641009072349882400408765)
    ·
      refine ⟨42240378402131205900153287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112641009072349882400408765 42240378402131205900153287)
      ·
        refine ⟨63360567603196808850229931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42240378402131205900153287 63360567603196808850229931)
        ·
          refine ⟨95040851404795213275344897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63360567603196808850229931 95040851404795213275344897)
          ·
            refine ⟨71280638553596409956508673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95040851404795213275344897 71280638553596409956508673)
            ·
              refine ⟨53460478915197307467381505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71280638553596409956508673 53460478915197307467381505)
              ·
                refine ⟨40095359186397980600536129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53460478915197307467381505 40095359186397980600536129)
                ·
                  refine ⟨30071519389798485450402097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40095359186397980600536129 30071519389798485450402097)
                  ·
                    refine ⟨22553639542348864087801573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30071519389798485450402097 22553639542348864087801573)
                    ·
                      refine ⟨4228807414190412016462795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22553639542348864087801573 4228807414190412016462795)
                      ·
                        rfl

theorem cell23_8235573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_8235573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235573 prefixEnd_8235573 := by exact prefixLift 8235573
  have htrace : WordTrace (prefixWord ++ tailWord_8235573) baseStart_8235573 baseEnd_8235573 := by
    simpa [prefixWord, tailWord_8235573, baseEnd_8235573] using wordTrace_append hprefix tailTrace_8235573
  have hstable : (prefixWord ++ tailWord_8235573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235573).length < 2 ^ (prefixWord ++ tailWord_8235573).sum := by decide
  have hdescent : baseEnd_8235573 < baseStart_8235573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235694 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_8235694 : Nat := 118140960795 + 8235694 * 2 ^ 59
def prefixEnd_8235694 : Nat := 4983230072969 + 3 ^ 40 * 8235694 * 2
def baseEnd_8235694 : Nat := 1409623181783202014349913

theorem tailTrace_8235694 : CollatzResearch.WordTrace tailWord_8235694 prefixEnd_8235694 1409623181783202014349913 := by
  unfold tailWord_8235694
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547554678186832174947267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200253624950329771599718757 37547554678186832174947267)
  ·
    refine ⟨56321332017280248262420901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37547554678186832174947267 56321332017280248262420901)
    ·
      refine ⟨10560249753240046549203919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56321332017280248262420901 10560249753240046549203919)
      ·
        refine ⟨15840374629860069823805879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560249753240046549203919 15840374629860069823805879)
        ·
          refine ⟨23760561944790104735708819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840374629860069823805879 23760561944790104735708819)
          ·
            refine ⟨35640842917185157103563229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23760561944790104735708819 35640842917185157103563229)
            ·
              refine ⟨13365316093944433913836211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35640842917185157103563229 13365316093944433913836211)
              ·
                refine ⟨20047974140916650870754317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13365316093944433913836211 20047974140916650870754317)
                ·
                  refine ⟨7517990302843744076532869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20047974140916650870754317 7517990302843744076532869)
                  ·
                    refine ⟨1409623181783202014349913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7517990302843744076532869 1409623181783202014349913)
                    ·
                      rfl

theorem cell23_8235694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_8235694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235694 prefixEnd_8235694 := by exact prefixLift 8235694
  have htrace : WordTrace (prefixWord ++ tailWord_8235694) baseStart_8235694 baseEnd_8235694 := by
    simpa [prefixWord, tailWord_8235694, baseEnd_8235694] using wordTrace_append hprefix tailTrace_8235694
  have hstable : (prefixWord ++ tailWord_8235694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235694).length < 2 ^ (prefixWord ++ tailWord_8235694).sum := by decide
  have hdescent : baseEnd_8235694 < baseStart_8235694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235720 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_8235720 : Nat := 118140960795 + 8235720 * 2 ^ 59
def prefixEnd_8235720 : Nat := 4983230072969 + 3 ^ 40 * 8235720 * 2
def baseEnd_8235720 : Nat := 1409627631948874313774873

theorem tailTrace_8235720 : CollatzResearch.WordTrace tailWord_8235720 prefixEnd_8235720 1409627631948874313774873 := by
  unfold tailWord_8235720
  simp only [CollatzResearch.WordTrace]
  refine ⟨150190692861700231920012307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200254257148933642560016409 150190692861700231920012307)
  ·
    refine ⟨225286039292550347880018461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150190692861700231920012307 225286039292550347880018461)
    ·
      refine ⟨84482264734706380455006923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225286039292550347880018461 84482264734706380455006923)
      ·
        refine ⟨126723397102059570682510385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84482264734706380455006923 126723397102059570682510385)
        ·
          refine ⟨95042547826544678011882789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126723397102059570682510385 95042547826544678011882789)
          ·
            refine ⟨17820477717477127127228023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95042547826544678011882789 17820477717477127127228023)
            ·
              refine ⟨26730716576215690690842035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17820477717477127127228023 26730716576215690690842035)
              ·
                refine ⟨40096074864323536036263053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26730716576215690690842035 40096074864323536036263053)
                ·
                  refine ⟨15036028074121326013598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40096074864323536036263053 15036028074121326013598645)
                  ·
                    refine ⟨1409627631948874313774873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15036028074121326013598645 1409627631948874313774873)
                    ·
                      rfl

theorem cell23_8235720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_8235720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235720 prefixEnd_8235720 := by exact prefixLift 8235720
  have htrace : WordTrace (prefixWord ++ tailWord_8235720) baseStart_8235720 baseEnd_8235720 := by
    simpa [prefixWord, tailWord_8235720, baseEnd_8235720] using wordTrace_append hprefix tailTrace_8235720
  have hstable : (prefixWord ++ tailWord_8235720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235720).length < 2 ^ (prefixWord ++ tailWord_8235720).sum := by decide
  have hdescent : baseEnd_8235720 < baseStart_8235720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235737 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_8235737 : Nat := 118140960795 + 8235737 * 2 ^ 59
def prefixEnd_8235737 : Nat := 4983230072969 + 3 ^ 40 * 8235737 * 2
def baseEnd_8235737 : Nat := 1409630541672583124937347

theorem tailTrace_8235737 : CollatzResearch.WordTrace tailWord_8235737 prefixEnd_8235737 1409630541672583124937347 := by
  unfold tailWord_8235737
  simp only [CollatzResearch.WordTrace]
  refine ⟨300382005764338875743393465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200254670509559250495595643 300382005764338875743393465)
  ·
    refine ⟨225286504323254156807545099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300382005764338875743393465 225286504323254156807545099)
    ·
      refine ⟨337929756484881235211317649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225286504323254156807545099 337929756484881235211317649)
      ·
        refine ⟨253447317363660926408488237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337929756484881235211317649 253447317363660926408488237)
        ·
          refine ⟨95042744011372847403183089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253447317363660926408488237 95042744011372847403183089)
          ·
            refine ⟨71282058008529635552387317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95042744011372847403183089 71282058008529635552387317)
            ·
              refine ⟨6682692938299653333036311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71282058008529635552387317 6682692938299653333036311)
              ·
                refine ⟨10024039407449479999554467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682692938299653333036311 10024039407449479999554467)
                ·
                  refine ⟨15036059111174219999331701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024039407449479999554467 15036059111174219999331701)
                  ·
                    refine ⟨1409630541672583124937347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15036059111174219999331701 1409630541672583124937347)
                    ·
                      rfl

theorem cell23_8235737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_8235737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235737 prefixEnd_8235737 := by exact prefixLift 8235737
  have htrace : WordTrace (prefixWord ++ tailWord_8235737) baseStart_8235737 baseEnd_8235737 := by
    simpa [prefixWord, tailWord_8235737, baseEnd_8235737] using wordTrace_append hprefix tailTrace_8235737
  have hstable : (prefixWord ++ tailWord_8235737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235737).length < 2 ^ (prefixWord ++ tailWord_8235737).sum := by decide
  have hdescent : baseEnd_8235737 < baseStart_8235737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235753 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_8235753 : Nat := 118140960795 + 8235753 * 2 ^ 59
def prefixEnd_8235753 : Nat := 4983230072969 + 3 ^ 40 * 8235753 * 2
def baseEnd_8235753 : Nat := 4228899840708221312211967

theorem tailTrace_8235753 : CollatzResearch.WordTrace tailWord_8235753 prefixEnd_8235753 4228899840708221312211967 := by
  unfold tailWord_8235753
  simp only [CollatzResearch.WordTrace]
  refine ⟨300382589332280910475975913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200255059554853940317317275 300382589332280910475975913)
  ·
    refine ⟨225286941999210682856981935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300382589332280910475975913 225286941999210682856981935)
    ·
      refine ⟨337930412998816024285472903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225286941999210682856981935 337930412998816024285472903)
      ·
        refine ⟨506895619498224036428209355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337930412998816024285472903 506895619498224036428209355)
        ·
          refine ⟨760343429247336054642314033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506895619498224036428209355 760343429247336054642314033)
          ·
            refine ⟨570257571935502040981735525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760343429247336054642314033 570257571935502040981735525)
            ·
              refine ⟨106923294737906632684075411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570257571935502040981735525 106923294737906632684075411)
              ·
                refine ⟨160384942106859949026113117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106923294737906632684075411 160384942106859949026113117)
                ·
                  refine ⟨60144353290072480884792419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160384942106859949026113117 60144353290072480884792419)
                  ·
                    refine ⟨90216529935108721327188629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60144353290072480884792419 90216529935108721327188629)
                    ·
                      refine ⟨4228899840708221312211967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90216529935108721327188629 4228899840708221312211967)
                      ·
                        rfl

theorem cell23_8235753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_8235753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235753 prefixEnd_8235753 := by exact prefixLift 8235753
  have htrace : WordTrace (prefixWord ++ tailWord_8235753) baseStart_8235753 baseEnd_8235753 := by
    simpa [prefixWord, tailWord_8235753, baseEnd_8235753] using wordTrace_append hprefix tailTrace_8235753
  have hstable : (prefixWord ++ tailWord_8235753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235753).length < 2 ^ (prefixWord ++ tailWord_8235753).sum := by decide
  have hdescent : baseEnd_8235753 < baseStart_8235753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235760 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_8235760 : Nat := 118140960795 + 8235760 * 2 ^ 59
def prefixEnd_8235760 : Nat := 4983230072969 + 3 ^ 40 * 8235760 * 2
def baseEnd_8235760 : Nat := 4228903435072802784824435

theorem tailTrace_8235760 : CollatzResearch.WordTrace tailWord_8235760 prefixEnd_8235760 4228903435072802784824435 := by
  unfold tailWord_8235760
  simp only [CollatzResearch.WordTrace]
  refine ⟨150191422321627775335740367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200255229762170367114320489 150191422321627775335740367)
  ·
    refine ⟨225287133482441663003610551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150191422321627775335740367 225287133482441663003610551)
    ·
      refine ⟨337930700223662494505415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225287133482441663003610551 337930700223662494505415827)
      ·
        refine ⟨506896050335493741758123741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337930700223662494505415827 506896050335493741758123741)
        ·
          refine ⟨190086018875810153159296403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506896050335493741758123741 190086018875810153159296403)
          ·
            refine ⟨285129028313715229738944605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190086018875810153159296403 285129028313715229738944605)
            ·
              refine ⟨106923385617643211152104227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285129028313715229738944605 106923385617643211152104227)
              ·
                refine ⟨160385078426464816728156341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106923385617643211152104227 160385078426464816728156341)
                ·
                  refine ⟨15036101102481076568264657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160385078426464816728156341 15036101102481076568264657)
                  ·
                    refine ⟨11277075826860807426198493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15036101102481076568264657 11277075826860807426198493)
                    ·
                      refine ⟨4228903435072802784824435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11277075826860807426198493 4228903435072802784824435)
                      ·
                        rfl

theorem cell23_8235760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_8235760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235760 prefixEnd_8235760 := by exact prefixLift 8235760
  have htrace : WordTrace (prefixWord ++ tailWord_8235760) baseStart_8235760 baseEnd_8235760 := by
    simpa [prefixWord, tailWord_8235760, baseEnd_8235760] using wordTrace_append hprefix tailTrace_8235760
  have hstable : (prefixWord ++ tailWord_8235760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235760).length < 2 ^ (prefixWord ++ tailWord_8235760).sum := by decide
  have hdescent : baseEnd_8235760 < baseStart_8235760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235770 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_8235770 : Nat := 118140960795 + 8235770 * 2 ^ 59
def prefixEnd_8235770 : Nat := 4983230072969 + 3 ^ 40 * 8235770 * 2
def baseEnd_8235770 : Nat := 4228908569879347745699389

theorem tailTrace_8235770 : CollatzResearch.WordTrace tailWord_8235770 prefixEnd_8235770 4228908569879347745699389 := by
  unfold tailWord_8235770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75095802343304830594836191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200255472915479548252896509 75095802343304830594836191)
  ·
    refine ⟨112643703514957245892254287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75095802343304830594836191 112643703514957245892254287)
    ·
      refine ⟨168965555272435868838381431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112643703514957245892254287 168965555272435868838381431)
      ·
        refine ⟨253448332908653803257572147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168965555272435868838381431 253448332908653803257572147)
        ·
          refine ⟨380172499362980704886358221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253448332908653803257572147 380172499362980704886358221)
          ·
            refine ⟨142564687261117764332384333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380172499362980704886358221 142564687261117764332384333)
            ·
              refine ⟨53461757722919161624644125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142564687261117764332384333 53461757722919161624644125)
              ·
                refine ⟨20048159146094685609241547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53461757722919161624644125 20048159146094685609241547)
                ·
                  refine ⟨30072238719142028413862321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20048159146094685609241547 30072238719142028413862321)
                  ·
                    refine ⟨22554179039356521310396741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30072238719142028413862321 22554179039356521310396741)
                    ·
                      refine ⟨4228908569879347745699389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22554179039356521310396741 4228908569879347745699389)
                      ·
                        rfl

theorem cell23_8235770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_8235770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235770 prefixEnd_8235770 := by exact prefixLift 8235770
  have htrace : WordTrace (prefixWord ++ tailWord_8235770) baseStart_8235770 baseEnd_8235770 := by
    simpa [prefixWord, tailWord_8235770, baseEnd_8235770] using wordTrace_append hprefix tailTrace_8235770
  have hstable : (prefixWord ++ tailWord_8235770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235770).length < 2 ^ (prefixWord ++ tailWord_8235770).sum := by decide
  have hdescent : baseEnd_8235770 < baseStart_8235770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235777 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_8235777 : Nat := 118140960795 + 8235777 * 2 ^ 59
def prefixEnd_8235777 : Nat := 4983230072969 + 3 ^ 40 * 8235777 * 2
def baseEnd_8235777 : Nat := 4228912164243929218311857

theorem tailTrace_8235777 : CollatzResearch.WordTrace tailWord_8235777 prefixEnd_8235777 4228912164243929218311857 := by
  unfold tailWord_8235777
  simp only [CollatzResearch.WordTrace]
  refine ⟨300383464684193962574849585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200255643122795975049899723 300383464684193962574849585)
  ·
    refine ⟨225287598513145471931137189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300383464684193962574849585 225287598513145471931137189)
    ·
      refine ⟨42241424721214775987088223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225287598513145471931137189 42241424721214775987088223)
      ·
        refine ⟨63362137081822163980632335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42241424721214775987088223 63362137081822163980632335)
        ·
          refine ⟨95043205622733245970948503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63362137081822163980632335 95043205622733245970948503)
          ·
            refine ⟨142564808434099868956422755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95043205622733245970948503 142564808434099868956422755)
            ·
              refine ⟨213847212651149803434634133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142564808434099868956422755 213847212651149803434634133)
              ·
                refine ⟨10024088093022647035998475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213847212651149803434634133 10024088093022647035998475)
                ·
                  refine ⟨15036132139533970553997713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024088093022647035998475 15036132139533970553997713)
                  ·
                    refine ⟨11277099104650477915498285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15036132139533970553997713 11277099104650477915498285)
                    ·
                      refine ⟨4228912164243929218311857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11277099104650477915498285 4228912164243929218311857)
                      ·
                        rfl

theorem cell23_8235777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_8235777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235777 prefixEnd_8235777 := by exact prefixLift 8235777
  have htrace : WordTrace (prefixWord ++ tailWord_8235777) baseStart_8235777 baseEnd_8235777 := by
    simpa [prefixWord, tailWord_8235777, baseEnd_8235777] using wordTrace_append hprefix tailTrace_8235777
  have hstable : (prefixWord ++ tailWord_8235777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235777).length < 2 ^ (prefixWord ++ tailWord_8235777).sum := by decide
  have hdescent : baseEnd_8235777 < baseStart_8235777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235791 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 1, 2, 2]
def baseStart_8235791 : Nat := 118140960795 + 8235791 * 2 ^ 59
def prefixEnd_8235791 : Nat := 4983230072969 + 3 ^ 40 * 8235791 * 2
def baseEnd_8235791 : Nat := 4228919352973092163536793

theorem tailTrace_8235791 : CollatzResearch.WordTrace tailWord_8235791 prefixEnd_8235791 4228919352973092163536793 := by
  unfold tailWord_8235791
  simp only [CollatzResearch.WordTrace]
  refine ⟨300383975306143242965859227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200255983537428828643906151 300383975306143242965859227)
  ·
    refine ⟨450575962959214864448788841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300383975306143242965859227 450575962959214864448788841)
    ·
      refine ⟨337931972219411148336591631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450575962959214864448788841 337931972219411148336591631)
      ·
        refine ⟨506897958329116722504887447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337931972219411148336591631 506897958329116722504887447)
        ·
          refine ⟨760346937493675083757331171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506897958329116722504887447 760346937493675083757331171)
          ·
            refine ⟨1140520406240512625635996757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760346937493675083757331171 1140520406240512625635996757)
            ·
              refine ⟨13365473510631007331671837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1140520406240512625635996757 13365473510631007331671837)
              ·
                refine ⟨5012052566486627749376939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13365473510631007331671837 5012052566486627749376939)
                ·
                  refine ⟨7518078849729941624065409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012052566486627749376939 7518078849729941624065409)
                  ·
                    refine ⟨5638559137297456218049057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518078849729941624065409 5638559137297456218049057)
                    ·
                      refine ⟨4228919352973092163536793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638559137297456218049057 4228919352973092163536793)
                      ·
                        rfl

theorem cell23_8235791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 2, 2].length) (baseStart_8235791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235791 prefixEnd_8235791 := by exact prefixLift 8235791
  have htrace : WordTrace (prefixWord ++ tailWord_8235791) baseStart_8235791 baseEnd_8235791 := by
    simpa [prefixWord, tailWord_8235791, baseEnd_8235791] using wordTrace_append hprefix tailTrace_8235791
  have hstable : (prefixWord ++ tailWord_8235791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235791).length < 2 ^ (prefixWord ++ tailWord_8235791).sum := by decide
  have hdescent : baseEnd_8235791 < baseStart_8235791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235803 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_8235803 : Nat := 118140960795 + 8235803 * 2 ^ 59
def prefixEnd_8235803 : Nat := 4983230072969 + 3 ^ 40 * 8235803 * 2
def baseEnd_8235803 : Nat := 4228925514740946116586737

theorem tailTrace_8235803 : CollatzResearch.WordTrace tailWord_8235803 prefixEnd_8235803 4228925514740946116586737 := by
  unfold tailWord_8235803
  simp only [CollatzResearch.WordTrace]
  refine ⟨300384412982099769015296063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200256275321399846010197375 300384412982099769015296063)
  ·
    refine ⟨450576619473149653522944095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300384412982099769015296063 450576619473149653522944095)
    ·
      refine ⟨675864929209724480284416143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450576619473149653522944095 675864929209724480284416143)
      ·
        refine ⟨1013797393814586720426624215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675864929209724480284416143 1013797393814586720426624215)
        ·
          refine ⟨1520696090721880080639936323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013797393814586720426624215 1520696090721880080639936323)
          ·
            refine ⟨2281044136082820120959904485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520696090721880080639936323 2281044136082820120959904485)
            ·
              refine ⟨427695775515528772679982091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2281044136082820120959904485 427695775515528772679982091)
              ·
                refine ⟨641543663273293159019973137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427695775515528772679982091 641543663273293159019973137)
                ·
                  refine ⟨481157747454969869264979853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641543663273293159019973137 481157747454969869264979853)
                  ·
                    refine ⟨180434155295613700974367445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481157747454969869264979853 180434155295613700974367445)
                    ·
                      refine ⟨4228925514740946116586737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180434155295613700974367445 4228925514740946116586737)
                      ·
                        rfl

theorem cell23_8235803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_8235803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235803 prefixEnd_8235803 := by exact prefixLift 8235803
  have htrace : WordTrace (prefixWord ++ tailWord_8235803) baseStart_8235803 baseEnd_8235803 := by
    simpa [prefixWord, tailWord_8235803, baseEnd_8235803] using wordTrace_append hprefix tailTrace_8235803
  have hstable : (prefixWord ++ tailWord_8235803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235803).length < 2 ^ (prefixWord ++ tailWord_8235803).sum := by decide
  have hdescent : baseEnd_8235803 < baseStart_8235803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235818 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_8235818 : Nat := 118140960795 + 8235818 * 2 ^ 59
def prefixEnd_8235818 : Nat := 4983230072969 + 3 ^ 40 * 8235818 * 2
def baseEnd_8235818 : Nat := 1409644405650254519299723

theorem tailTrace_8235818 : CollatzResearch.WordTrace tailWord_8235818 prefixEnd_8235818 1409644405650254519299723 := by
  unfold tailWord_8235818
  simp only [CollatzResearch.WordTrace]
  refine ⟨75096240019261356644273027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200256640051363617718061405 75096240019261356644273027)
  ·
    refine ⟨112644360028892034966409541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75096240019261356644273027 112644360028892034966409541)
    ·
      refine ⟨21120817505417256556201789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112644360028892034966409541 21120817505417256556201789)
      ·
        refine ⟨7920306564531471208575671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21120817505417256556201789 7920306564531471208575671)
        ·
          refine ⟨11880459846797206812863507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920306564531471208575671 11880459846797206812863507)
          ·
            refine ⟨17820689770195810219295261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11880459846797206812863507 17820689770195810219295261)
            ·
              refine ⟨6682758663823428832235723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17820689770195810219295261 6682758663823428832235723)
              ·
                refine ⟨10024137995735143248353585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682758663823428832235723 10024137995735143248353585)
                ·
                  refine ⟨7518103496801357436265189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10024137995735143248353585 7518103496801357436265189)
                  ·
                    refine ⟨1409644405650254519299723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7518103496801357436265189 1409644405650254519299723)
                    ·
                      rfl

theorem cell23_8235818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_8235818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235818 prefixEnd_8235818 := by exact prefixLift 8235818
  have htrace : WordTrace (prefixWord ++ tailWord_8235818) baseStart_8235818 baseEnd_8235818 := by
    simpa [prefixWord, tailWord_8235818, baseEnd_8235818] using wordTrace_append hprefix tailTrace_8235818
  have hstable : (prefixWord ++ tailWord_8235818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235818).length < 2 ^ (prefixWord ++ tailWord_8235818).sum := by decide
  have hdescent : baseEnd_8235818 < baseStart_8235818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235847 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_8235847 : Nat := 118140960795 + 8235847 * 2 ^ 59
def prefixEnd_8235847 : Nat := 4983230072969 + 3 ^ 40 * 8235847 * 2
def baseEnd_8235847 : Nat := 4228948107889743944436535

theorem tailTrace_8235847 : CollatzResearch.WordTrace tailWord_8235847 prefixEnd_8235847 4228948107889743944436535 := by
  unfold tailWord_8235847
  simp only [CollatzResearch.WordTrace]
  refine ⟨300386017793940364529897795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200257345195960243019931863 300386017793940364529897795)
  ·
    refine ⟨450579026690910546794846693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300386017793940364529897795 450579026690910546794846693)
    ·
      refine ⟨84483567504545727524033755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450579026690910546794846693 84483567504545727524033755)
      ·
        refine ⟨126725351256818591286050633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84483567504545727524033755 126725351256818591286050633)
        ·
          refine ⟨95044013442613943464537975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126725351256818591286050633 95044013442613943464537975)
          ·
            refine ⟨142566020163920915196806963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95044013442613943464537975 142566020163920915196806963)
            ·
              refine ⟨213849030245881372795210445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142566020163920915196806963 213849030245881372795210445)
              ·
                refine ⟨80193386342205514798203917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213849030245881372795210445 80193386342205514798203917)
                ·
                  refine ⟨30072519878327068049326469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80193386342205514798203917 30072519878327068049326469)
                  ·
                    refine ⟨5638597477186325259248713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30072519878327068049326469 5638597477186325259248713)
                    ·
                      refine ⟨4228948107889743944436535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638597477186325259248713 4228948107889743944436535)
                      ·
                        rfl

theorem cell23_8235847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_8235847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235847 prefixEnd_8235847 := by exact prefixLift 8235847
  have htrace : WordTrace (prefixWord ++ tailWord_8235847) baseStart_8235847 baseEnd_8235847 := by
    simpa [prefixWord, tailWord_8235847, baseEnd_8235847] using wordTrace_append hprefix tailTrace_8235847
  have hstable : (prefixWord ++ tailWord_8235847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235847).length < 2 ^ (prefixWord ++ tailWord_8235847).sum := by decide
  have hdescent : baseEnd_8235847 < baseStart_8235847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235900 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_8235900 : Nat := 118140960795 + 8235900 * 2 ^ 59
def prefixEnd_8235900 : Nat := 4983230072969 + 3 ^ 40 * 8235900 * 2
def baseEnd_8235900 : Nat := 1409658440788144079024597

theorem tailTrace_8235900 : CollatzResearch.WordTrace tailWord_8235900 prefixEnd_8235900 1409658440788144079024597 := by
  unfold tailWord_8235900
  simp only [CollatzResearch.WordTrace]
  refine ⟨150193975431374177290788577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200258633908498903054384769 150193975431374177290788577)
  ·
    refine ⟨112645481573530632968091433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150193975431374177290788577 112645481573530632968091433)
    ·
      refine ⟨84484111180147974726068575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112645481573530632968091433 84484111180147974726068575)
      ·
        refine ⟨126726166770221962089102863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84484111180147974726068575 126726166770221962089102863)
        ·
          refine ⟨190089250155332943133654295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126726166770221962089102863 190089250155332943133654295)
          ·
            refine ⟨285133875232999414700481443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190089250155332943133654295 285133875232999414700481443)
            ·
              refine ⟨427700812849499122050722165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285133875232999414700481443 427700812849499122050722165)
              ·
                refine ⟨40096951204640542692255203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427700812849499122050722165 40096951204640542692255203)
                ·
                  refine ⟨60145426806960814038382805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40096951204640542692255203 60145426806960814038382805)
                  ·
                    refine ⟨1409658440788144079024597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60145426806960814038382805 1409658440788144079024597)
                    ·
                      rfl

theorem cell23_8235900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_8235900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235900 prefixEnd_8235900 := by exact prefixLift 8235900
  have htrace : WordTrace (prefixWord ++ tailWord_8235900) baseStart_8235900 baseEnd_8235900 := by
    simpa [prefixWord, tailWord_8235900, baseEnd_8235900] using wordTrace_append hprefix tailTrace_8235900
  have hstable : (prefixWord ++ tailWord_8235900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235900).length < 2 ^ (prefixWord ++ tailWord_8235900).sum := by decide
  have hdescent : baseEnd_8235900 < baseStart_8235900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235924 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_8235924 : Nat := 118140960795 + 8235924 * 2 ^ 59
def prefixEnd_8235924 : Nat := 4983230072969 + 3 ^ 40 * 8235924 * 2
def baseEnd_8235924 : Nat := 4228987645900140143173681

theorem tailTrace_8235924 : CollatzResearch.WordTrace tailWord_8235924 prefixEnd_8235924 4228987645900140143173681 := by
  unfold tailWord_8235924
  simp only [CollatzResearch.WordTrace]
  refine ⟨150194413107330703340225413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200259217476440937786967217 150194413107330703340225413)
  ·
    refine ⟨28161452457624506876292265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150194413107330703340225413 28161452457624506876292265)
    ·
      refine ⟨21121089343218380157219199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28161452457624506876292265 21121089343218380157219199)
      ·
        refine ⟨31681634014827570235828799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121089343218380157219199 31681634014827570235828799)
        ·
          refine ⟨47522451022241355353743199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31681634014827570235828799 47522451022241355353743199)
          ·
            refine ⟨71283676533362033030614799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47522451022241355353743199 71283676533362033030614799)
            ·
              refine ⟨106925514800043049545922199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71283676533362033030614799 106925514800043049545922199)
              ·
                refine ⟨160388272200064574318883299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106925514800043049545922199 160388272200064574318883299)
                ·
                  refine ⟨240582408300096861478324949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160388272200064574318883299 240582408300096861478324949)
                  ·
                    refine ⟨5638650194533520190898241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240582408300096861478324949 5638650194533520190898241)
                    ·
                      refine ⟨4228987645900140143173681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638650194533520190898241 4228987645900140143173681)
                      ·
                        rfl

theorem cell23_8235924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_8235924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235924 prefixEnd_8235924 := by exact prefixLift 8235924
  have htrace : WordTrace (prefixWord ++ tailWord_8235924) baseStart_8235924 baseEnd_8235924 := by
    simpa [prefixWord, tailWord_8235924, baseEnd_8235924] using wordTrace_append hprefix tailTrace_8235924
  have hstable : (prefixWord ++ tailWord_8235924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235924).length < 2 ^ (prefixWord ++ tailWord_8235924).sum := by decide
  have hdescent : baseEnd_8235924 < baseStart_8235924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8235947 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 3, 4]
def baseStart_8235947 : Nat := 118140960795 + 8235947 * 2 ^ 59
def prefixEnd_8235947 : Nat := 4983230072969 + 3 ^ 40 * 8235947 * 2
def baseEnd_8235947 : Nat := 1409666485318397851062025

theorem tailTrace_8235947 : CollatzResearch.WordTrace tailWord_8235947 prefixEnd_8235947 1409666485318397851062025 := by
  unfold tailWord_8235947
  simp only [CollatzResearch.WordTrace]
  refine ⟨300389665093578081608538095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200259776729052054405692063 300389665093578081608538095)
  ·
    refine ⟨450584497640367122412807143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300389665093578081608538095 450584497640367122412807143)
    ·
      refine ⟨675876746460550683619210715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450584497640367122412807143 675876746460550683619210715)
      ·
        refine ⟨1013815119690826025428816073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675876746460550683619210715 1013815119690826025428816073)
        ·
          refine ⟨760361339768119519071612055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013815119690826025428816073 760361339768119519071612055)
          ·
            refine ⟨1140542009652179278607418083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760361339768119519071612055 1140542009652179278607418083)
            ·
              refine ⟨1710813014478268917911127125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140542009652179278607418083 1710813014478268917911127125)
              ·
                refine ⟨20048590013417213881771021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1710813014478268917911127125 20048590013417213881771021)
                ·
                  refine ⟨7518221255031455205664133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20048590013417213881771021 7518221255031455205664133)
                  ·
                    refine ⟨1409666485318397851062025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7518221255031455205664133 1409666485318397851062025)
                    ·
                      rfl

theorem cell23_8235947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 4].length) (baseStart_8235947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8235947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8235947 prefixEnd_8235947 := by exact prefixLift 8235947
  have htrace : WordTrace (prefixWord ++ tailWord_8235947) baseStart_8235947 baseEnd_8235947 := by
    simpa [prefixWord, tailWord_8235947, baseEnd_8235947] using wordTrace_append hprefix tailTrace_8235947
  have hstable : (prefixWord ++ tailWord_8235947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8235947).length < 2 ^ (prefixWord ++ tailWord_8235947).sum := by decide
  have hdescent : baseEnd_8235947 < baseStart_8235947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8235947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236004 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_8236004 : Nat := 118140960795 + 8236004 * 2 ^ 59
def prefixEnd_8236004 : Nat := 4983230072969 + 3 ^ 40 * 8236004 * 2
def baseEnd_8236004 : Nat := 4229028724352499830173313

theorem tailTrace_8236004 : CollatzResearch.WordTrace tailWord_8236004 prefixEnd_8236004 4229028724352499830173313 := by
  unfold tailWord_8236004
  simp only [CollatzResearch.WordTrace]
  refine ⟨150195872027185790171681533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200261162702914386895575377 150195872027185790171681533)
  ·
    refine ⟨56323452010194671314380575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150195872027185790171681533 56323452010194671314380575)
    ·
      refine ⟨84485178015292006971570863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56323452010194671314380575 84485178015292006971570863)
      ·
        refine ⟨126727767022938010457356295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84485178015292006971570863 126727767022938010457356295)
        ·
          refine ⟨190091650534407015686034443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126727767022938010457356295 190091650534407015686034443)
          ·
            refine ⟨285137475801610523529051665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190091650534407015686034443 285137475801610523529051665)
            ·
              refine ⟨213853106851207892646788749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285137475801610523529051665 213853106851207892646788749)
              ·
                refine ⟨80194915069202959742545781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213853106851207892646788749 80194915069202959742545781)
                ·
                  refine ⟨7518273287737777475863667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80194915069202959742545781 7518273287737777475863667)
                  ·
                    refine ⟨11277409931606666213795501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7518273287737777475863667 11277409931606666213795501)
                    ·
                      refine ⟨4229028724352499830173313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11277409931606666213795501 4229028724352499830173313)
                      ·
                        rfl

theorem cell23_8236004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_8236004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236004 prefixEnd_8236004 := by exact prefixLift 8236004
  have htrace : WordTrace (prefixWord ++ tailWord_8236004) baseStart_8236004 baseEnd_8236004 := by
    simpa [prefixWord, tailWord_8236004, baseEnd_8236004] using wordTrace_append hprefix tailTrace_8236004
  have hstable : (prefixWord ++ tailWord_8236004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236004).length < 2 ^ (prefixWord ++ tailWord_8236004).sum := by decide
  have hdescent : baseEnd_8236004 < baseStart_8236004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236027 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4]
def baseStart_8236027 : Nat := 118140960795 + 8236027 * 2 ^ 59
def prefixEnd_8236027 : Nat := 4983230072969 + 3 ^ 40 * 8236027 * 2
def baseEnd_8236027 : Nat := 4229040534407553240185707

theorem tailTrace_8236027 : CollatzResearch.WordTrace tailWord_8236027 prefixEnd_8236027 4229040534407553240185707 := by
  unfold tailWord_8236027
  simp only [CollatzResearch.WordTrace]
  refine ⟨300392582933288255271450335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200261721955525503514300223 300392582933288255271450335)
  ·
    refine ⟨450588874399932382907175503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300392582933288255271450335 450588874399932382907175503)
    ·
      refine ⟨675883311599898574360763255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450588874399932382907175503 675883311599898574360763255)
      ·
        refine ⟨1013824967399847861541144883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675883311599898574360763255 1013824967399847861541144883)
        ·
          refine ⟨1520737451099771792311717325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013824967399847861541144883 1520737451099771792311717325)
          ·
            refine ⟨570276544162414422116893997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1520737451099771792311717325 570276544162414422116893997)
            ·
              refine ⟨213853704060905408293835249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570276544162414422116893997 213853704060905408293835249)
              ·
                refine ⟨160390278045679056220376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213853704060905408293835249 160390278045679056220376437)
                ·
                  refine ⟨15036588566782411520660291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160390278045679056220376437 15036588566782411520660291)
                  ·
                    refine ⟨22554882850173617280990437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15036588566782411520660291 22554882850173617280990437)
                    ·
                      refine ⟨4229040534407553240185707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22554882850173617280990437 4229040534407553240185707)
                      ·
                        rfl

theorem cell23_8236027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_8236027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236027 prefixEnd_8236027 := by exact prefixLift 8236027
  have htrace : WordTrace (prefixWord ++ tailWord_8236027) baseStart_8236027 baseEnd_8236027 := by
    simpa [prefixWord, tailWord_8236027, baseEnd_8236027] using wordTrace_append hprefix tailTrace_8236027
  have hstable : (prefixWord ++ tailWord_8236027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236027).length < 2 ^ (prefixWord ++ tailWord_8236027).sum := by decide
  have hdescent : baseEnd_8236027 < baseStart_8236027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236057 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_8236057 : Nat := 118140960795 + 8236057 * 2 ^ 59
def prefixEnd_8236057 : Nat := 4983230072969 + 3 ^ 40 * 8236057 * 2
def baseEnd_8236057 : Nat := 4229055938827188122810569

theorem tailTrace_8236057 : CollatzResearch.WordTrace tailWord_8236057 prefixEnd_8236057 4229055938827188122810569 := by
  unfold tailWord_8236057
  simp only [CollatzResearch.WordTrace]
  refine ⟨300393677123179570395042425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200262451415453046930028283 300393677123179570395042425)
  ·
    refine ⟨225295257842384677796281819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300393677123179570395042425 225295257842384677796281819)
    ·
      refine ⟨337942886763577016694422729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225295257842384677796281819 337942886763577016694422729)
      ·
        refine ⟨253457165072682762520817047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337942886763577016694422729 253457165072682762520817047)
        ·
          refine ⟨380185747609024143781225571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253457165072682762520817047 380185747609024143781225571)
          ·
            refine ⟨570278621413536215671838357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380185747609024143781225571 570278621413536215671838357)
            ·
              refine ⟨26731810378759510109617423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 570278621413536215671838357 26731810378759510109617423)
              ·
                refine ⟨40097715568139265164426135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26731810378759510109617423 40097715568139265164426135)
                ·
                  refine ⟨60146573352208897746639203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40097715568139265164426135 60146573352208897746639203)
                  ·
                    refine ⟨90219860028313346619958805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60146573352208897746639203 90219860028313346619958805)
                    ·
                      refine ⟨4229055938827188122810569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90219860028313346619958805 4229055938827188122810569)
                      ·
                        rfl

theorem cell23_8236057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_8236057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236057 prefixEnd_8236057 := by exact prefixLift 8236057
  have htrace : WordTrace (prefixWord ++ tailWord_8236057) baseStart_8236057 baseEnd_8236057 := by
    simpa [prefixWord, tailWord_8236057, baseEnd_8236057] using wordTrace_append hprefix tailTrace_8236057
  have hstable : (prefixWord ++ tailWord_8236057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236057).length < 2 ^ (prefixWord ++ tailWord_8236057).sum := by decide
  have hdescent : baseEnd_8236057 < baseStart_8236057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236061 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_8236061 : Nat := 118140960795 + 8236061 * 2 ^ 59
def prefixEnd_8236061 : Nat := 4983230072969 + 3 ^ 40 * 8236061 * 2
def baseEnd_8236061 : Nat := 4229057992749806107160551

theorem tailTrace_8236061 : CollatzResearch.WordTrace tailWord_8236061 prefixEnd_8236061 4229057992749806107160551 := by
  unfold tailWord_8236061
  simp only [CollatzResearch.WordTrace]
  refine ⟨300393823015165079078188037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200262548676776719385458691 300393823015165079078188037)
  ·
    refine ⟨56323841815343452327160257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300393823015165079078188037 56323841815343452327160257)
    ·
      refine ⟨42242881361507589245370193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56323841815343452327160257 42242881361507589245370193)
      ·
        refine ⟨31682161021130691934027645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42242881361507589245370193 31682161021130691934027645)
        ·
          refine ⟨11880810382924009475260367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31682161021130691934027645 11880810382924009475260367)
          ·
            refine ⟨17821215574386014212890551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11880810382924009475260367 17821215574386014212890551)
            ·
              refine ⟨26731823361579021319335827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17821215574386014212890551 26731823361579021319335827)
              ·
                refine ⟨40097735042368531979003741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26731823361579021319335827 40097735042368531979003741)
                ·
                  refine ⟨15036650640888199492126403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40097735042368531979003741 15036650640888199492126403)
                  ·
                    refine ⟨22554975961332299238189605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15036650640888199492126403 22554975961332299238189605)
                    ·
                      refine ⟨4229057992749806107160551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22554975961332299238189605 4229057992749806107160551)
                      ·
                        rfl

theorem cell23_8236061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_8236061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236061 prefixEnd_8236061 := by exact prefixLift 8236061
  have htrace : WordTrace (prefixWord ++ tailWord_8236061) baseStart_8236061 baseEnd_8236061 := by
    simpa [prefixWord, tailWord_8236061, baseEnd_8236061] using wordTrace_append hprefix tailTrace_8236061
  have hstable : (prefixWord ++ tailWord_8236061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236061).length < 2 ^ (prefixWord ++ tailWord_8236061).sum := by decide
  have hdescent : baseEnd_8236061 < baseStart_8236061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236067 : List Nat := [1, 1, 1, 4, 3, 2, 2, 9]
def baseStart_8236067 : Nat := 118140960795 + 8236067 * 2 ^ 59
def prefixEnd_8236067 : Nat := 4983230072969 + 3 ^ 40 * 8236067 * 2
def baseEnd_8236067 : Nat := 156631891616064188284649

theorem tailTrace_8236067 : CollatzResearch.WordTrace tailWord_8236067 prefixEnd_8236067 156631891616064188284649 := by
  unfold tailWord_8236067
  simp only [CollatzResearch.WordTrace]
  refine ⟨300394041853143342102906455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200262694568762228068604303 300394041853143342102906455)
  ·
    refine ⟨450591062779715013154359683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300394041853143342102906455 450591062779715013154359683)
    ·
      refine ⟨675886594169572519731539525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450591062779715013154359683 675886594169572519731539525)
      ·
        refine ⟨126728736406794847449663661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675886594169572519731539525 126728736406794847449663661)
        ·
          refine ⟨47523276152548067793623873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126728736406794847449663661 47523276152548067793623873)
          ·
            refine ⟨35642457114411050845217905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47523276152548067793623873 35642457114411050845217905)
            ·
              refine ⟨26731842835808288133913429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35642457114411050845217905 26731842835808288133913429)
              ·
                refine ⟨156631891616064188284649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26731842835808288133913429 156631891616064188284649)
                ·
                  rfl

theorem cell23_8236067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 9].length) (baseStart_8236067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236067 prefixEnd_8236067 := by exact prefixLift 8236067
  have htrace : WordTrace (prefixWord ++ tailWord_8236067) baseStart_8236067 baseEnd_8236067 := by
    simpa [prefixWord, tailWord_8236067, baseEnd_8236067] using wordTrace_append hprefix tailTrace_8236067
  have hstable : (prefixWord ++ tailWord_8236067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236067).length < 2 ^ (prefixWord ++ tailWord_8236067).sum := by decide
  have hdescent : baseEnd_8236067 < baseStart_8236067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236071 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 6]
def baseStart_8236071 : Nat := 118140960795 + 8236071 * 2 ^ 59
def prefixEnd_8236071 : Nat := 4983230072969 + 3 ^ 40 * 8236071 * 2
def baseEnd_8236071 : Nat := 1409687709185450356011835

theorem tailTrace_8236071 : CollatzResearch.WordTrace tailWord_8236071 prefixEnd_8236071 1409687709185450356011835 := by
  unfold tailWord_8236071
  simp only [CollatzResearch.WordTrace]
  refine ⟨300394187745128850786052067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200262791830085900524034711 300394187745128850786052067)
  ·
    refine ⟨450591281617693276179078101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300394187745128850786052067 450591281617693276179078101)
    ·
      refine ⟨10560733162914686160447143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 450591281617693276179078101 10560733162914686160447143)
      ·
        refine ⟨15841099744372029240670715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560733162914686160447143 15841099744372029240670715)
        ·
          refine ⟨23761649616558043861006073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15841099744372029240670715 23761649616558043861006073)
          ·
            refine ⟨17821237212418532895754555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23761649616558043861006073 17821237212418532895754555)
            ·
              refine ⟨26731855818627799343631833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17821237212418532895754555 26731855818627799343631833)
              ·
                refine ⟨20048891863970849507723875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26731855818627799343631833 20048891863970849507723875)
                ·
                  refine ⟨30073337795956274261585813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20048891863970849507723875 30073337795956274261585813)
                  ·
                    refine ⟨1409687709185450356011835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30073337795956274261585813 1409687709185450356011835)
                    ·
                      rfl

theorem cell23_8236071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_8236071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236071 prefixEnd_8236071 := by exact prefixLift 8236071
  have htrace : WordTrace (prefixWord ++ tailWord_8236071) baseStart_8236071 baseEnd_8236071 := by
    simpa [prefixWord, tailWord_8236071, baseEnd_8236071] using wordTrace_append hprefix tailTrace_8236071
  have hstable : (prefixWord ++ tailWord_8236071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236071).length < 2 ^ (prefixWord ++ tailWord_8236071).sum := by decide
  have hdescent : baseEnd_8236071 < baseStart_8236071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236078 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_8236078 : Nat := 118140960795 + 8236078 * 2 ^ 59
def prefixEnd_8236078 : Nat := 4983230072969 + 3 ^ 40 * 8236078 * 2
def baseEnd_8236078 : Nat := 4229066721920932540647973

theorem tailTrace_8236078 : CollatzResearch.WordTrace tailWord_8236078 prefixEnd_8236078 4229066721920932540647973 := by
  unfold tailWord_8236078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37549305382012936372694611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200262962037402327321037925 37549305382012936372694611)
  ·
    refine ⟨56323958073019404559041917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37549305382012936372694611 56323958073019404559041917)
    ·
      refine ⟨21121484277382276709640719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56323958073019404559041917 21121484277382276709640719)
      ·
        refine ⟨31682226416073415064461079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121484277382276709640719 31682226416073415064461079)
        ·
          refine ⟨47523339624110122596691619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31682226416073415064461079 47523339624110122596691619)
          ·
            refine ⟨71285009436165183895037429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47523339624110122596691619 71285009436165183895037429)
            ·
              refine ⟨6682969634640485990159759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71285009436165183895037429 6682969634640485990159759)
              ·
                refine ⟨10024454451960728985239639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682969634640485990159759 10024454451960728985239639)
                ·
                  refine ⟨15036681677941093477859459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024454451960728985239639 15036681677941093477859459)
                  ·
                    refine ⟨22555022516911640216789189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15036681677941093477859459 22555022516911640216789189)
                    ·
                      refine ⟨4229066721920932540647973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22555022516911640216789189 4229066721920932540647973)
                      ·
                        rfl

theorem cell23_8236078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_8236078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236078 prefixEnd_8236078 := by exact prefixLift 8236078
  have htrace : WordTrace (prefixWord ++ tailWord_8236078) baseStart_8236078 baseEnd_8236078 := by
    simpa [prefixWord, tailWord_8236078, baseEnd_8236078] using wordTrace_append hprefix tailTrace_8236078
  have hstable : (prefixWord ++ tailWord_8236078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236078).length < 2 ^ (prefixWord ++ tailWord_8236078).sum := by decide
  have hdescent : baseEnd_8236078 < baseStart_8236078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236084 : List Nat := [2, 5, 1, 2, 1, 12]
def baseStart_8236084 : Nat := 118140960795 + 8236084 * 2 ^ 59
def prefixEnd_8236084 : Nat := 4983230072969 + 3 ^ 40 * 8236084 * 2
def baseEnd_8236084 : Nat := 17403579435410944515115

theorem tailTrace_8236084 : CollatzResearch.WordTrace tailWord_8236084 prefixEnd_8236084 17403579435410944515115 := by
  unfold tailWord_8236084
  simp only [CollatzResearch.WordTrace]
  refine ⟨150197330947040877003137653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200263107929387836004183537 150197330947040877003137653)
  ·
    refine ⟨14080999776285082219044155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150197330947040877003137653 14080999776285082219044155)
    ·
      refine ⟨21121499664427623328566233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14080999776285082219044155 21121499664427623328566233)
      ·
        refine ⟨15841124748320717496424675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21121499664427623328566233 15841124748320717496424675)
        ·
          refine ⟨23761687122481076244637013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15841124748320717496424675 23761687122481076244637013)
          ·
            refine ⟨17403579435410944515115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23761687122481076244637013 17403579435410944515115)
            ·
              rfl

theorem cell23_8236084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 12].length) (baseStart_8236084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236084 prefixEnd_8236084 := by exact prefixLift 8236084
  have htrace : WordTrace (prefixWord ++ tailWord_8236084) baseStart_8236084 baseEnd_8236084 := by
    simpa [prefixWord, tailWord_8236084, baseEnd_8236084] using wordTrace_append hprefix tailTrace_8236084
  have hstable : (prefixWord ++ tailWord_8236084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236084).length < 2 ^ (prefixWord ++ tailWord_8236084).sum := by decide
  have hdescent : baseEnd_8236084 < baseStart_8236084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236124 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_8236124 : Nat := 118140960795 + 8236124 * 2 ^ 59
def prefixEnd_8236124 : Nat := 4983230072969 + 3 ^ 40 * 8236124 * 2
def baseEnd_8236124 : Nat := 4229090342031039360672761

theorem tailTrace_8236124 : CollatzResearch.WordTrace tailWord_8236124 prefixEnd_8236124 4229090342031039360672761 := by
  unfold tailWord_8236124
  simp only [CollatzResearch.WordTrace]
  refine ⟨150198060406968420418865713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200264080542624560558487617 150198060406968420418865713)
  ·
    refine ⟨112648545305226315314149285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150198060406968420418865713 112648545305226315314149285)
    ·
      refine ⟨21121602244729934121402991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112648545305226315314149285 21121602244729934121402991)
      ·
        refine ⟨31682403367094901182104487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121602244729934121402991 31682403367094901182104487)
        ·
          refine ⟨47523605050642351773156731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31682403367094901182104487 47523605050642351773156731)
          ·
            refine ⟨71285407575963527659735097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47523605050642351773156731 71285407575963527659735097)
            ·
              refine ⟨53464055681972645744801323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71285407575963527659735097 53464055681972645744801323)
              ·
                refine ⟨80196083522958968617201985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53464055681972645744801323 80196083522958968617201985)
                ·
                  refine ⟨60147062642219226462901489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80196083522958968617201985 60147062642219226462901489)
                  ·
                    refine ⟨45110296981664419847176117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60147062642219226462901489 45110296981664419847176117)
                    ·
                      refine ⟨4229090342031039360672761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45110296981664419847176117 4229090342031039360672761)
                      ·
                        rfl

theorem cell23_8236124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_8236124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236124 prefixEnd_8236124 := by exact prefixLift 8236124
  have htrace : WordTrace (prefixWord ++ tailWord_8236124) baseStart_8236124 baseEnd_8236124 := by
    simpa [prefixWord, tailWord_8236124, baseEnd_8236124] using wordTrace_append hprefix tailTrace_8236124
  have hstable : (prefixWord ++ tailWord_8236124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236124).length < 2 ^ (prefixWord ++ tailWord_8236124).sum := by decide
  have hdescent : baseEnd_8236124 < baseStart_8236124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236127 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 8]
def baseStart_8236127 : Nat := 118140960795 + 8236127 * 2 ^ 59
def prefixEnd_8236127 : Nat := 4983230072969 + 3 ^ 40 * 8236127 * 2
def baseEnd_8236127 : Nat := 1409697294157667616311749

theorem tailTrace_8236127 : CollatzResearch.WordTrace tailWord_8236127 prefixEnd_8236127 1409697294157667616311749 := by
  unfold tailWord_8236127
  simp only [CollatzResearch.WordTrace]
  refine ⟨300396230232925972350090635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200264153488617314900060423 300396230232925972350090635)
  ·
    refine ⟨450594345349388958525135953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300396230232925972350090635 450594345349388958525135953)
    ·
      refine ⟨337945759012041718893851965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450594345349388958525135953 337945759012041718893851965)
      ·
        refine ⟨126729659629515644585194487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337945759012041718893851965 126729659629515644585194487)
        ·
          refine ⟨190094489444273466877791731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126729659629515644585194487 190094489444273466877791731)
          ·
            refine ⟨285141734166410200316687597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190094489444273466877791731 285141734166410200316687597)
            ·
              refine ⟨106928150312403825118757849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285141734166410200316687597 106928150312403825118757849)
              ·
                refine ⟨80196112734302868839068387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106928150312403825118757849 80196112734302868839068387)
                ·
                  refine ⟨120294169101454303258602581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80196112734302868839068387 120294169101454303258602581)
                  ·
                    refine ⟨1409697294157667616311749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120294169101454303258602581 1409697294157667616311749)
                    ·
                      rfl

theorem cell23_8236127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_8236127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236127 prefixEnd_8236127 := by exact prefixLift 8236127
  have htrace : WordTrace (prefixWord ++ tailWord_8236127) baseStart_8236127 baseEnd_8236127 := by
    simpa [prefixWord, tailWord_8236127, baseEnd_8236127] using wordTrace_append hprefix tailTrace_8236127
  have hstable : (prefixWord ++ tailWord_8236127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236127).length < 2 ^ (prefixWord ++ tailWord_8236127).sum := by decide
  have hdescent : baseEnd_8236127 < baseStart_8236127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236238 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_8236238 : Nat := 118140960795 + 8236238 * 2 ^ 59
def prefixEnd_8236238 : Nat := 4983230072969 + 3 ^ 40 * 8236238 * 2
def baseEnd_8236238 : Nat := 1409716292941883971549079

theorem tailTrace_8236238 : CollatzResearch.WordTrace tailWord_8236238 prefixEnd_8236238 1409716292941883971549079 := by
  unfold tailWord_8236238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550034841940479788422671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200266852490349225538254245 37550034841940479788422671)
  ·
    refine ⟨56325052262910719682634007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37550034841940479788422671 56325052262910719682634007)
    ·
      refine ⟨84487578394366079523951011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56325052262910719682634007 84487578394366079523951011)
      ·
        refine ⟨126731367591549119285926517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84487578394366079523951011 126731367591549119285926517)
        ·
          refine ⟨11881065711707729933055611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126731367591549119285926517 11881065711707729933055611)
          ·
            refine ⟨17821598567561594899583417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881065711707729933055611 17821598567561594899583417)
            ·
              refine ⟨13366198925671196174687563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17821598567561594899583417 13366198925671196174687563)
              ·
                refine ⟨20049298388506794262031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366198925671196174687563 20049298388506794262031345)
                ·
                  refine ⟨15036973791380095696523509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20049298388506794262031345 15036973791380095696523509)
                  ·
                    refine ⟨1409716292941883971549079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15036973791380095696523509 1409716292941883971549079)
                    ·
                      rfl

theorem cell23_8236238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_8236238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236238 prefixEnd_8236238 := by exact prefixLift 8236238
  have htrace : WordTrace (prefixWord ++ tailWord_8236238) baseStart_8236238 baseEnd_8236238 := by
    simpa [prefixWord, tailWord_8236238, baseEnd_8236238] using wordTrace_append hprefix tailTrace_8236238
  have hstable : (prefixWord ++ tailWord_8236238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236238).length < 2 ^ (prefixWord ++ tailWord_8236238).sum := by decide
  have hdescent : baseEnd_8236238 < baseStart_8236238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236241 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_8236241 : Nat := 118140960795 + 8236241 * 2 ^ 59
def prefixEnd_8236241 : Nat := 4983230072969 + 3 ^ 40 * 8236241 * 2
def baseEnd_8236241 : Nat := 4229150419267615402909723

theorem tailTrace_8236241 : CollatzResearch.WordTrace tailWord_8236241 prefixEnd_8236241 4229150419267615402909723 := by
  unfold tailWord_8236241
  simp only [CollatzResearch.WordTrace]
  refine ⟨300400388154512969819740577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200266925436341979879827051 300400388154512969819740577)
  ·
    refine ⟨225300291115884727364805433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300400388154512969819740577 225300291115884727364805433)
    ·
      refine ⟨168975218336913545523604075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225300291115884727364805433 168975218336913545523604075)
      ·
        refine ⟨253462827505370318285406113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168975218336913545523604075 253462827505370318285406113)
        ·
          refine ⟨190097120629027738714054585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253462827505370318285406113 190097120629027738714054585)
          ·
            refine ⟨142572840471770804035540939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190097120629027738714054585 142572840471770804035540939)
            ·
              refine ⟨213859260707656206053311409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142572840471770804035540939 213859260707656206053311409)
              ·
                refine ⟨160394445530742154539983557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213859260707656206053311409 160394445530742154539983557)
                ·
                  refine ⟨30073958537014153976246917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160394445530742154539983557 30073958537014153976246917)
                  ·
                    refine ⟨5638867225690153870546297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30073958537014153976246917 5638867225690153870546297)
                    ·
                      refine ⟨4229150419267615402909723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5638867225690153870546297 4229150419267615402909723)
                      ·
                        rfl

theorem cell23_8236241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_8236241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236241 prefixEnd_8236241 := by exact prefixLift 8236241
  have htrace : WordTrace (prefixWord ++ tailWord_8236241) baseStart_8236241 baseEnd_8236241 := by
    simpa [prefixWord, tailWord_8236241, baseEnd_8236241] using wordTrace_append hprefix tailTrace_8236241
  have hstable : (prefixWord ++ tailWord_8236241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236241).length < 2 ^ (prefixWord ++ tailWord_8236241).sum := by decide
  have hdescent : baseEnd_8236241 < baseStart_8236241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236325 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_8236325 : Nat := 118140960795 + 8236325 * 2 ^ 59
def prefixEnd_8236325 : Nat := 4983230072969 + 3 ^ 40 * 8236325 * 2
def baseEnd_8236325 : Nat := 4229193551642593074259337

theorem tailTrace_8236325 : CollatzResearch.WordTrace tailWord_8236325 prefixEnd_8236325 4229193551642593074259337 := by
  unfold tailWord_8236325
  simp only [CollatzResearch.WordTrace]
  refine ⟨300403451886208652165798429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200268967924139101443865619 300403451886208652165798429)
  ·
    refine ⟨112651294457328244562174411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300403451886208652165798429 112651294457328244562174411)
    ·
      refine ⟨168976941685992366843261617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112651294457328244562174411 168976941685992366843261617)
      ·
        refine ⟨126732706264494275132446213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168976941685992366843261617 126732706264494275132446213)
        ·
          refine ⟨23762382424592676587333665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126732706264494275132446213 23762382424592676587333665)
          ·
            refine ⟨17821786818444507440500249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23762382424592676587333665 17821786818444507440500249)
            ·
              refine ⟨13366340113833380580375187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17821786818444507440500249 13366340113833380580375187)
              ·
                refine ⟨20049510170750070870562781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366340113833380580375187 20049510170750070870562781)
                ·
                  refine ⟨7518566314031276576461043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20049510170750070870562781 7518566314031276576461043)
                  ·
                    refine ⟨11277849471046914864691565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7518566314031276576461043 11277849471046914864691565)
                    ·
                      refine ⟨4229193551642593074259337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11277849471046914864691565 4229193551642593074259337)
                      ·
                        rfl

theorem cell23_8236325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_8236325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236325 prefixEnd_8236325 := by exact prefixLift 8236325
  have htrace : WordTrace (prefixWord ++ tailWord_8236325) baseStart_8236325 baseEnd_8236325 := by
    simpa [prefixWord, tailWord_8236325, baseEnd_8236325] using wordTrace_append hprefix tailTrace_8236325
  have hstable : (prefixWord ++ tailWord_8236325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236325).length < 2 ^ (prefixWord ++ tailWord_8236325).sum := by decide
  have hdescent : baseEnd_8236325 < baseStart_8236325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236345 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_8236345 : Nat := 118140960795 + 8236345 * 2 ^ 59
def prefixEnd_8236345 : Nat := 4983230072969 + 3 ^ 40 * 8236345 * 2
def baseEnd_8236345 : Nat := 1409734607085227665336415

theorem tailTrace_8236345 : CollatzResearch.WordTrace tailWord_8236345 prefixEnd_8236345 1409734607085227665336415 := by
  unfold tailWord_8236345
  simp only [CollatzResearch.WordTrace]
  refine ⟨300404181346136195581526489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200269454230757463721017659 300404181346136195581526489)
  ·
    refine ⟨225303136009602146686144867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300404181346136195581526489 225303136009602146686144867)
    ·
      refine ⟨337954704014403220029217301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225303136009602146686144867 337954704014403220029217301)
      ·
        refine ⟨15841626750675150938869561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 337954704014403220029217301 15841626750675150938869561)
        ·
          refine ⟨11881220063006363204152171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15841626750675150938869561 11881220063006363204152171)
          ·
            refine ⟨17821830094509544806228257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881220063006363204152171 17821830094509544806228257)
            ·
              refine ⟨13366372570882158604671193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17821830094509544806228257 13366372570882158604671193)
              ·
                refine ⟨10024779428161618953503395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13366372570882158604671193 10024779428161618953503395)
                ·
                  refine ⟨15037169142242428430255093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024779428161618953503395 15037169142242428430255093)
                  ·
                    refine ⟨1409734607085227665336415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15037169142242428430255093 1409734607085227665336415)
                    ·
                      rfl

theorem cell23_8236345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_8236345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236345 prefixEnd_8236345 := by exact prefixLift 8236345
  have htrace : WordTrace (prefixWord ++ tailWord_8236345) baseStart_8236345 baseEnd_8236345 := by
    simpa [prefixWord, tailWord_8236345, baseEnd_8236345] using wordTrace_append hprefix tailTrace_8236345
  have hstable : (prefixWord ++ tailWord_8236345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236345).length < 2 ^ (prefixWord ++ tailWord_8236345).sum := by decide
  have hdescent : baseEnd_8236345 < baseStart_8236345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236348 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_8236348 : Nat := 118140960795 + 8236348 * 2 ^ 59
def prefixEnd_8236348 : Nat := 4983230072969 + 3 ^ 40 * 8236348 * 2
def baseEnd_8236348 : Nat := 4229205361697646484271731

theorem tailTrace_8236348 : CollatzResearch.WordTrace tailWord_8236348 prefixEnd_8236348 4229205361697646484271731 := by
  unfold tailWord_8236348
  simp only [CollatzResearch.WordTrace]
  refine ⟨150202145382562663546942849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200269527176750218062590465 150202145382562663546942849)
  ·
    refine ⟨112651609036921997660207137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150202145382562663546942849 112651609036921997660207137)
    ·
      refine ⟨84488706777691498245155353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112651609036921997660207137 84488706777691498245155353)
      ·
        refine ⟨63366530083268623683866515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84488706777691498245155353 63366530083268623683866515)
        ·
          refine ⟨95049795124902935525799773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63366530083268623683866515 95049795124902935525799773)
          ·
            refine ⟨35643673171838600822174915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95049795124902935525799773 35643673171838600822174915)
            ·
              refine ⟨53465509757757901233262373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35643673171838600822174915 53465509757757901233262373)
              ·
                refine ⟨10024783079579606481236695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53465509757757901233262373 10024783079579606481236695)
                ·
                  refine ⟨15037174619369409721855043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024783079579606481236695 15037174619369409721855043)
                  ·
                    refine ⟨22555761929054114582782565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15037174619369409721855043 22555761929054114582782565)
                    ·
                      refine ⟨4229205361697646484271731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22555761929054114582782565 4229205361697646484271731)
                      ·
                        rfl

theorem cell23_8236348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_8236348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236348 prefixEnd_8236348 := by exact prefixLift 8236348
  have htrace : WordTrace (prefixWord ++ tailWord_8236348) baseStart_8236348 baseEnd_8236348 := by
    simpa [prefixWord, tailWord_8236348, baseEnd_8236348] using wordTrace_append hprefix tailTrace_8236348
  have hstable : (prefixWord ++ tailWord_8236348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236348).length < 2 ^ (prefixWord ++ tailWord_8236348).sum := by decide
  have hdescent : baseEnd_8236348 < baseStart_8236348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236361 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_8236361 : Nat := 118140960795 + 8236361 * 2 ^ 59
def prefixEnd_8236361 : Nat := 4983230072969 + 3 ^ 40 * 8236361 * 2
def baseEnd_8236361 : Nat := 4229212036946154933409171

theorem tailTrace_8236361 : CollatzResearch.WordTrace tailWord_8236361 prefixEnd_8236361 4229212036946154933409171 := by
  unfold tailWord_8236361
  simp only [CollatzResearch.WordTrace]
  refine ⟨300404764914078230314108937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200269843276052153542739291 300404764914078230314108937)
  ·
    refine ⟨225303573685558672735581703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300404764914078230314108937 225303573685558672735581703)
    ·
      refine ⟨337955360528338009103372555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225303573685558672735581703 337955360528338009103372555)
      ·
        refine ⟨506933040792507013655058833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337955360528338009103372555 506933040792507013655058833)
        ·
          refine ⟨380199780594380260241294125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506933040792507013655058833 380199780594380260241294125)
          ·
            refine ⟨142574917722892597590485297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380199780594380260241294125 142574917722892597590485297)
            ·
              refine ⟨106931188292169448192863973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142574917722892597590485297 106931188292169448192863973)
              ·
                refine ⟨20049597804781771536161995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106931188292169448192863973 20049597804781771536161995)
                ·
                  refine ⟨30074396707172657304242993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20049597804781771536161995 30074396707172657304242993)
                  ·
                    refine ⟨22555797530379492978182245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30074396707172657304242993 22555797530379492978182245)
                    ·
                      refine ⟨4229212036946154933409171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22555797530379492978182245 4229212036946154933409171)
                      ·
                        rfl

theorem cell23_8236361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_8236361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236361 prefixEnd_8236361 := by exact prefixLift 8236361
  have htrace : WordTrace (prefixWord ++ tailWord_8236361) baseStart_8236361 baseEnd_8236361 := by
    simpa [prefixWord, tailWord_8236361, baseEnd_8236361] using wordTrace_append hprefix tailTrace_8236361
  have hstable : (prefixWord ++ tailWord_8236361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236361).length < 2 ^ (prefixWord ++ tailWord_8236361).sum := by decide
  have hdescent : baseEnd_8236361 < baseStart_8236361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236368 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_8236368 : Nat := 118140960795 + 8236368 * 2 ^ 59
def prefixEnd_8236368 : Nat := 4983230072969 + 3 ^ 40 * 8236368 * 2
def baseEnd_8236368 : Nat := 4229215631310736406021639

theorem tailTrace_8236368 : CollatzResearch.WordTrace tailWord_8236368 prefixEnd_8236368 4229215631310736406021639 := by
  unfold tailWord_8236368
  simp only [CollatzResearch.WordTrace]
  refine ⟨150202510112526435254806879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200270013483368580339742505 150202510112526435254806879)
  ·
    refine ⟨225303765168789652882210319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150202510112526435254806879 225303765168789652882210319)
    ·
      refine ⟨337955647753184479323315479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225303765168789652882210319 337955647753184479323315479)
      ·
        refine ⟨506933471629776718984973219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337955647753184479323315479 506933471629776718984973219)
        ·
          refine ⟨760400207444665078477459829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506933471629776718984973219 760400207444665078477459829)
          ·
            refine ⟨71287519447937351107261859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 760400207444665078477459829 71287519447937351107261859)
            ·
              refine ⟨106931279171906026660892789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71287519447937351107261859 106931279171906026660892789)
              ·
                refine ⟨10024807422366189999458699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106931279171906026660892789 10024807422366189999458699)
                ·
                  refine ⟨15037211133549284999188049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024807422366189999458699 15037211133549284999188049)
                  ·
                    refine ⟨11277908350161963749391037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15037211133549284999188049 11277908350161963749391037)
                    ·
                      refine ⟨4229215631310736406021639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11277908350161963749391037 4229215631310736406021639)
                      ·
                        rfl

theorem cell23_8236368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_8236368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236368 prefixEnd_8236368 := by exact prefixLift 8236368
  have htrace : WordTrace (prefixWord ++ tailWord_8236368) baseStart_8236368 baseEnd_8236368 := by
    simpa [prefixWord, tailWord_8236368, baseEnd_8236368] using wordTrace_append hprefix tailTrace_8236368
  have hstable : (prefixWord ++ tailWord_8236368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236368).length < 2 ^ (prefixWord ++ tailWord_8236368).sum := by decide
  have hdescent : baseEnd_8236368 < baseStart_8236368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236476 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_8236476 : Nat := 118140960795 + 8236476 * 2 ^ 59
def prefixEnd_8236476 : Nat := 4983230072969 + 3 ^ 40 * 8236476 * 2
def baseEnd_8236476 : Nat := 4229271087221421983471143

theorem tailTrace_8236476 : CollatzResearch.WordTrace tailWord_8236476 prefixEnd_8236476 4229271087221421983471143 := by
  unfold tailWord_8236476
  simp only [CollatzResearch.WordTrace]
  refine ⟨150204479654330802477272641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200272639539107736636363521 150204479654330802477272641)
  ·
    refine ⟨112653359740748101857954481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150204479654330802477272641 112653359740748101857954481)
    ·
      refine ⟨84490019805561076393465861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112653359740748101857954481 84490019805561076393465861)
      ·
        refine ⟨15841878713542701823774849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84490019805561076393465861 15841878713542701823774849)
        ·
          refine ⟨11881409035157026367831137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15841878713542701823774849 11881409035157026367831137)
          ·
            refine ⟨8911056776367769775873353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11881409035157026367831137 8911056776367769775873353)
            ·
              refine ⟨6683292582275827331905015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911056776367769775873353 6683292582275827331905015)
              ·
                refine ⟨10024938873413740997857523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683292582275827331905015 10024938873413740997857523)
                ·
                  refine ⟨15037408310120611496786285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10024938873413740997857523 15037408310120611496786285)
                  ·
                    refine ⟨5639028116295229311294857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15037408310120611496786285 5639028116295229311294857)
                    ·
                      refine ⟨4229271087221421983471143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639028116295229311294857 4229271087221421983471143)
                      ·
                        rfl

theorem cell23_8236476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_8236476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236476 prefixEnd_8236476 := by exact prefixLift 8236476
  have htrace : WordTrace (prefixWord ++ tailWord_8236476) baseStart_8236476 baseEnd_8236476 := by
    simpa [prefixWord, tailWord_8236476, baseEnd_8236476] using wordTrace_append hprefix tailTrace_8236476
  have hstable : (prefixWord ++ tailWord_8236476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236476).length < 2 ^ (prefixWord ++ tailWord_8236476).sum := by decide
  have hdescent : baseEnd_8236476 < baseStart_8236476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236488 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_8236488 : Nat := 118140960795 + 8236488 * 2 ^ 59
def prefixEnd_8236488 : Nat := 4983230072969 + 3 ^ 40 * 8236488 * 2
def baseEnd_8236488 : Nat := 4229277248989275936521087

theorem tailTrace_8236488 : CollatzResearch.WordTrace tailWord_8236488 prefixEnd_8236488 4229277248989275936521087 := by
  unfold tailWord_8236488
  simp only [CollatzResearch.WordTrace]
  refine ⟨150204698492309065501991059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200272931323078754002654745 150204698492309065501991059)
  ·
    refine ⟨225307047738463598252986589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150204698492309065501991059 225307047738463598252986589)
    ·
      refine ⟨84490142901923849344869971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225307047738463598252986589 84490142901923849344869971)
      ·
        refine ⟨126735214352885774017304957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84490142901923849344869971 126735214352885774017304957)
        ·
          refine ⟨47525705382332165256489359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126735214352885774017304957 47525705382332165256489359)
          ·
            refine ⟨71288558073498247884734039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47525705382332165256489359 71288558073498247884734039)
            ·
              refine ⟨106932837110247371827101059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71288558073498247884734039 106932837110247371827101059)
              ·
                refine ⟨160399255665371057740651589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106932837110247371827101059 160399255665371057740651589)
                ·
                  refine ⟨30074860437257073326372173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160399255665371057740651589 30074860437257073326372173)
                  ·
                    refine ⟨11278072663971402497389565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30074860437257073326372173 11278072663971402497389565)
                    ·
                      refine ⟨4229277248989275936521087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11278072663971402497389565 4229277248989275936521087)
                      ·
                        rfl

theorem cell23_8236488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_8236488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236488 prefixEnd_8236488 := by exact prefixLift 8236488
  have htrace : WordTrace (prefixWord ++ tailWord_8236488) baseStart_8236488 baseEnd_8236488 := by
    simpa [prefixWord, tailWord_8236488, baseEnd_8236488] using wordTrace_append hprefix tailTrace_8236488
  have hstable : (prefixWord ++ tailWord_8236488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236488).length < 2 ^ (prefixWord ++ tailWord_8236488).sum := by decide
  have hdescent : baseEnd_8236488 < baseStart_8236488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236528 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_8236528 : Nat := 118140960795 + 8236528 * 2 ^ 59
def prefixEnd_8236528 : Nat := 4983230072969 + 3 ^ 40 * 8236528 * 2
def baseEnd_8236528 : Nat := 4229297788215455780020903

theorem tailTrace_8236528 : CollatzResearch.WordTrace tailWord_8236528 prefixEnd_8236528 4229297788215455780020903 := by
  unfold tailWord_8236528
  simp only [CollatzResearch.WordTrace]
  refine ⟨150205427952236608917719119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200273903936315478556958825 150205427952236608917719119)
  ·
    refine ⟨225308141928354913376578679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150205427952236608917719119 225308141928354913376578679)
    ·
      refine ⟨337962212892532370064868019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225308141928354913376578679 337962212892532370064868019)
      ·
        refine ⟨506943319338798555097302029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337962212892532370064868019 506943319338798555097302029)
        ·
          refine ⟨190103744752049458161488261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506943319338798555097302029 190103744752049458161488261)
          ·
            refine ⟨35644452141009273405279049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190103744752049458161488261 35644452141009273405279049)
            ·
              refine ⟨26733339105756955053959287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35644452141009273405279049 26733339105756955053959287)
              ·
                refine ⟨40100008658635432580938931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26733339105756955053959287 40100008658635432580938931)
                ·
                  refine ⟨60150012987953148871408397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40100008658635432580938931 60150012987953148871408397)
                  ·
                    refine ⟨22556254870482430826778149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60150012987953148871408397 22556254870482430826778149)
                    ·
                      refine ⟨4229297788215455780020903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22556254870482430826778149 4229297788215455780020903)
                      ·
                        rfl

theorem cell23_8236528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_8236528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236528 prefixEnd_8236528 := by exact prefixLift 8236528
  have htrace : WordTrace (prefixWord ++ tailWord_8236528) baseStart_8236528 baseEnd_8236528 := by
    simpa [prefixWord, tailWord_8236528, baseEnd_8236528] using wordTrace_append hprefix tailTrace_8236528
  have hstable : (prefixWord ++ tailWord_8236528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236528).length < 2 ^ (prefixWord ++ tailWord_8236528).sum := by decide
  have hdescent : baseEnd_8236528 < baseStart_8236528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236557 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8236557 : Nat := 118140960795 + 8236557 * 2 ^ 59
def prefixEnd_8236557 : Nat := 4983230072969 + 3 ^ 40 * 8236557 * 2
def baseEnd_8236557 : Nat := 4229312679154436166558271

theorem tailTrace_8236557 : CollatzResearch.WordTrace tailWord_8236557 prefixEnd_8236557 4229312679154436166558271 := by
  unfold tailWord_8236557
  simp only [CollatzResearch.WordTrace]
  refine ⟨300411913621368155788243925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200274609080912103858829283 300411913621368155788243925)
  ·
    refine ⟨7040904225500816151286967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 300411913621368155788243925 7040904225500816151286967)
    ·
      refine ⟨10561356338251224226930451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040904225500816151286967 10561356338251224226930451)
      ·
        refine ⟨15842034507376836340395677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561356338251224226930451 15842034507376836340395677)
        ·
          refine ⟨5940762940266313627648379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15842034507376836340395677 5940762940266313627648379)
          ·
            refine ⟨8911144410399470441472569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940762940266313627648379 8911144410399470441472569)
            ·
              refine ⟨6683358307799602831104427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8911144410399470441472569 6683358307799602831104427)
              ·
                refine ⟨10025037461699404246656641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683358307799602831104427 10025037461699404246656641)
                ·
                  refine ⟨7518778096274553184992481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10025037461699404246656641 7518778096274553184992481)
                  ·
                    refine ⟨5639083572205914888744361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518778096274553184992481 5639083572205914888744361)
                    ·
                      refine ⟨4229312679154436166558271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639083572205914888744361 4229312679154436166558271)
                      ·
                        rfl

theorem cell23_8236557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8236557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236557 prefixEnd_8236557 := by exact prefixLift 8236557
  have htrace : WordTrace (prefixWord ++ tailWord_8236557) baseStart_8236557 baseEnd_8236557 := by
    simpa [prefixWord, tailWord_8236557, baseEnd_8236557] using wordTrace_append hprefix tailTrace_8236557
  have hstable : (prefixWord ++ tailWord_8236557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236557).length < 2 ^ (prefixWord ++ tailWord_8236557).sum := by decide
  have hdescent : baseEnd_8236557 < baseStart_8236557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236645 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_8236645 : Nat := 118140960795 + 8236645 * 2 ^ 59
def prefixEnd_8236645 : Nat := 4983230072969 + 3 ^ 40 * 8236645 * 2
def baseEnd_8236645 : Nat := 1409785955150677274085955

theorem tailTrace_8236645 : CollatzResearch.WordTrace tailWord_8236645 prefixEnd_8236645 1409785955150677274085955 := by
  unfold tailWord_8236645
  simp only [CollatzResearch.WordTrace]
  refine ⟨300415123245049346817447389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200276748830032897878298259 300415123245049346817447389)
  ·
    refine ⟨112655671216893505056542771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300415123245049346817447389 112655671216893505056542771)
    ·
      refine ⟨168983506825340257584814157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112655671216893505056542771 168983506825340257584814157)
      ·
        refine ⟨63368815059502596594305309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168983506825340257584814157 63368815059502596594305309)
        ·
          refine ⟨23763305647313473722864491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63368815059502596594305309 23763305647313473722864491)
          ·
            refine ⟨35644958470970210584296737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23763305647313473722864491 35644958470970210584296737)
            ·
              refine ⟨26733718853227657938222553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35644958470970210584296737 26733718853227657938222553)
              ·
                refine ⟨20050289139920743453666915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26733718853227657938222553 20050289139920743453666915)
                ·
                  refine ⟨30075433709881115180500373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20050289139920743453666915 30075433709881115180500373)
                  ·
                    refine ⟨1409785955150677274085955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30075433709881115180500373 1409785955150677274085955)
                    ·
                      rfl

theorem cell23_8236645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_8236645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236645 prefixEnd_8236645 := by exact prefixLift 8236645
  have htrace : WordTrace (prefixWord ++ tailWord_8236645) baseStart_8236645 baseEnd_8236645 := by
    simpa [prefixWord, tailWord_8236645, baseEnd_8236645] using wordTrace_append hprefix tailTrace_8236645
  have hstable : (prefixWord ++ tailWord_8236645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236645).length < 2 ^ (prefixWord ++ tailWord_8236645).sum := by decide
  have hdescent : baseEnd_8236645 < baseStart_8236645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236652 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_8236652 : Nat := 118140960795 + 8236652 * 2 ^ 59
def prefixEnd_8236652 : Nat := 4983230072969 + 3 ^ 40 * 8236652 * 2
def baseEnd_8236652 : Nat := 4229361459816613294870333

theorem tailTrace_8236652 : CollatzResearch.WordTrace tailWord_8236652 prefixEnd_8236652 4229361459816613294870333 := by
  unfold tailWord_8236652
  simp only [CollatzResearch.WordTrace]
  refine ⟨150207689278011993506476105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200276919037349324675301473 150207689278011993506476105)
  ·
    refine ⟨112655766958508995129857079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150207689278011993506476105 112655766958508995129857079)
    ·
      refine ⟨168983650437763492694785619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112655766958508995129857079 168983650437763492694785619)
      ·
        refine ⟨253475475656645239042178429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168983650437763492694785619 253475475656645239042178429)
        ·
          refine ⟨95053303371241964640816911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253475475656645239042178429 95053303371241964640816911)
          ·
            refine ⟨142579955056862946961225367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95053303371241964640816911 142579955056862946961225367)
            ·
              refine ⟨213869932585294420441838051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142579955056862946961225367 213869932585294420441838051)
              ·
                refine ⟨320804898877941630662757077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213869932585294420441838051 320804898877941630662757077)
                ·
                  refine ⟨7518864817451756968658369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320804898877941630662757077 7518864817451756968658369)
                  ·
                    refine ⟨5639148613088817726493777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518864817451756968658369 5639148613088817726493777)
                    ·
                      refine ⟨4229361459816613294870333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639148613088817726493777 4229361459816613294870333)
                      ·
                        rfl

theorem cell23_8236652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_8236652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236652 prefixEnd_8236652 := by exact prefixLift 8236652
  have htrace : WordTrace (prefixWord ++ tailWord_8236652) baseStart_8236652 baseEnd_8236652 := by
    simpa [prefixWord, tailWord_8236652, baseEnd_8236652] using wordTrace_append hprefix tailTrace_8236652
  have hstable : (prefixWord ++ tailWord_8236652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236652).length < 2 ^ (prefixWord ++ tailWord_8236652).sum := by decide
  have hdescent : baseEnd_8236652 < baseStart_8236652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236668 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_8236668 : Nat := 118140960795 + 8236668 * 2 ^ 59
def prefixEnd_8236668 : Nat := 4983230072969 + 3 ^ 40 * 8236668 * 2
def baseEnd_8236668 : Nat := 4229369675507085232270259

theorem tailTrace_8236668 : CollatzResearch.WordTrace tailWord_8236668 prefixEnd_8236668 4229369675507085232270259 := by
  unfold tailWord_8236668
  simp only [CollatzResearch.WordTrace]
  refine ⟨150207981061983010872767329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200277308082644014497023105 150207981061983010872767329)
  ·
    refine ⟨112655985796487258154575497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150207981061983010872767329 112655985796487258154575497)
    ·
      refine ⟨84491989347365443615931623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112655985796487258154575497 84491989347365443615931623)
      ·
        refine ⟨126737984021048165423897435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84491989347365443615931623 126737984021048165423897435)
        ·
          refine ⟨190106976031572248135846153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126737984021048165423897435 190106976031572248135846153)
          ·
            refine ⟨142580232023679186101884615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190106976031572248135846153 142580232023679186101884615)
            ·
              refine ⟨213870348035518779152826923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142580232023679186101884615 213870348035518779152826923)
              ·
                refine ⟨320805522053278168729240385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213870348035518779152826923 320805522053278168729240385)
                ·
                  refine ⟨240604141539958626546930289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320805522053278168729240385 240604141539958626546930289)
                  ·
                    refine ⟨180453106154968969910197717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240604141539958626546930289 180453106154968969910197717)
                    ·
                      refine ⟨4229369675507085232270259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180453106154968969910197717 4229369675507085232270259)
                      ·
                        rfl

theorem cell23_8236668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_8236668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236668 prefixEnd_8236668 := by exact prefixLift 8236668
  have htrace : WordTrace (prefixWord ++ tailWord_8236668) baseStart_8236668 baseEnd_8236668 := by
    simpa [prefixWord, tailWord_8236668, baseEnd_8236668] using wordTrace_append hprefix tailTrace_8236668
  have hstable : (prefixWord ++ tailWord_8236668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236668).length < 2 ^ (prefixWord ++ tailWord_8236668).sum := by decide
  have hdescent : baseEnd_8236668 < baseStart_8236668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236669 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_8236669 : Nat := 118140960795 + 8236669 * 2 ^ 59
def prefixEnd_8236669 : Nat := 4983230072969 + 3 ^ 40 * 8236669 * 2
def baseEnd_8236669 : Nat := 4229370188987739728357755

theorem tailTrace_8236669 : CollatzResearch.WordTrace tailWord_8236669 prefixEnd_8236669 4229370188987739728357755 := by
  unfold tailWord_8236669
  simp only [CollatzResearch.WordTrace]
  refine ⟨300415998596962398916321061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200277332397974932610880707 300415998596962398916321061)
  ·
    refine ⟨56327999736930449796810199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300415998596962398916321061 56327999736930449796810199)
    ·
      refine ⟨84491999605395674695215299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56327999736930449796810199 84491999605395674695215299)
      ·
        refine ⟨126737999408093512042822949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84491999605395674695215299 126737999408093512042822949)
        ·
          refine ⟨23763374889017533508029303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126737999408093512042822949 23763374889017533508029303)
          ·
            refine ⟨35645062333526300262043955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23763374889017533508029303 35645062333526300262043955)
            ·
              refine ⟨53467593500289450393065933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35645062333526300262043955 53467593500289450393065933)
              ·
                refine ⟨20050347562608543897399725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53467593500289450393065933 20050347562608543897399725)
                ·
                  refine ⟨7518880335978203961524897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20050347562608543897399725 7518880335978203961524897)
                  ·
                    refine ⟨5639160251983652971143673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518880335978203961524897 5639160251983652971143673)
                    ·
                      refine ⟨4229370188987739728357755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639160251983652971143673 4229370188987739728357755)
                      ·
                        rfl

theorem cell23_8236669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_8236669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236669 prefixEnd_8236669 := by exact prefixLift 8236669
  have htrace : WordTrace (prefixWord ++ tailWord_8236669) baseStart_8236669 baseEnd_8236669 := by
    simpa [prefixWord, tailWord_8236669, baseEnd_8236669] using wordTrace_append hprefix tailTrace_8236669
  have hstable : (prefixWord ++ tailWord_8236669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236669).length < 2 ^ (prefixWord ++ tailWord_8236669).sum := by decide
  have hdescent : baseEnd_8236669 < baseStart_8236669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236679 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 2, 4]
def baseStart_8236679 : Nat := 118140960795 + 8236679 * 2 ^ 59
def prefixEnd_8236679 : Nat := 4983230072969 + 3 ^ 40 * 8236679 * 2
def baseEnd_8236679 : Nat := 1409791774598094896410903

theorem tailTrace_8236679 : CollatzResearch.WordTrace tailWord_8236679 prefixEnd_8236679 1409791774598094896410903 := by
  unfold tailWord_8236679
  simp only [CollatzResearch.WordTrace]
  refine ⟨300416363326926170624185091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200277575551284113749456727 300416363326926170624185091)
  ·
    refine ⟨450624544990389255936277637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300416363326926170624185091 450624544990389255936277637)
    ·
      refine ⟨84492102185697985488052057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450624544990389255936277637 84492102185697985488052057)
      ·
        refine ⟨63369076639273489116039043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84492102185697985488052057 63369076639273489116039043)
        ·
          refine ⟨95053614958910233674058565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63369076639273489116039043 95053614958910233674058565)
          ·
            refine ⟨17822552804795668813885981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95053614958910233674058565 17822552804795668813885981)
            ·
              refine ⟨6683457301798375805207243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17822552804795668813885981 6683457301798375805207243)
              ·
                refine ⟨10025185952697563707810865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683457301798375805207243 10025185952697563707810865)
                ·
                  refine ⟨7518889464523172780858149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10025185952697563707810865 7518889464523172780858149)
                  ·
                    refine ⟨1409791774598094896410903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7518889464523172780858149 1409791774598094896410903)
                    ·
                      rfl

theorem cell23_8236679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_8236679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236679 prefixEnd_8236679 := by exact prefixLift 8236679
  have htrace : WordTrace (prefixWord ++ tailWord_8236679) baseStart_8236679 baseEnd_8236679 := by
    simpa [prefixWord, tailWord_8236679, baseEnd_8236679] using wordTrace_append hprefix tailTrace_8236679
  have hstable : (prefixWord ++ tailWord_8236679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236679).length < 2 ^ (prefixWord ++ tailWord_8236679).sum := by decide
  have hdescent : baseEnd_8236679 < baseStart_8236679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236682 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_8236682 : Nat := 118140960795 + 8236682 * 2 ^ 59
def prefixEnd_8236682 : Nat := 4983230072969 + 3 ^ 40 * 8236682 * 2
def baseEnd_8236682 : Nat := 4229376864236248177495195

theorem tailTrace_8236682 : CollatzResearch.WordTrace tailWord_8236682 prefixEnd_8236682 4229376864236248177495195 := by
  unfold tailWord_8236682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75104118186478825534136075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200277648497276868091029533 75104118186478825534136075)
  ·
    refine ⟨112656177279718238301204113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75104118186478825534136075 112656177279718238301204113)
    ·
      refine ⟨84492132959788678725903085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112656177279718238301204113 84492132959788678725903085)
      ·
        refine ⟨31684549859920754522213657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84492132959788678725903085 31684549859920754522213657)
        ·
          refine ⟨23763412394940565891660243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31684549859920754522213657 23763412394940565891660243)
          ·
            refine ⟨35645118592410848837490365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23763412394940565891660243 35645118592410848837490365)
            ·
              refine ⟨13366919472154068314058887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35645118592410848837490365 13366919472154068314058887)
              ·
                refine ⟨20050379208231102471088331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366919472154068314058887 20050379208231102471088331)
                ·
                  refine ⟨30075568812346653706632497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20050379208231102471088331 30075568812346653706632497)
                  ·
                    refine ⟨22556676609259990279974373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30075568812346653706632497 22556676609259990279974373)
                    ·
                      refine ⟨4229376864236248177495195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22556676609259990279974373 4229376864236248177495195)
                      ·
                        rfl

theorem cell23_8236682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_8236682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236682 prefixEnd_8236682 := by exact prefixLift 8236682
  have htrace : WordTrace (prefixWord ++ tailWord_8236682) baseStart_8236682 baseEnd_8236682 := by
    simpa [prefixWord, tailWord_8236682, baseEnd_8236682] using wordTrace_append hprefix tailTrace_8236682
  have hstable : (prefixWord ++ tailWord_8236682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236682).length < 2 ^ (prefixWord ++ tailWord_8236682).sum := by decide
  have hdescent : baseEnd_8236682 < baseStart_8236682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236688 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_8236688 : Nat := 118140960795 + 8236688 * 2 ^ 59
def prefixEnd_8236688 : Nat := 4983230072969 + 3 ^ 40 * 8236688 * 2
def baseEnd_8236688 : Nat := 1409793315040058384673389

theorem tailTrace_8236688 : CollatzResearch.WordTrace tailWord_8236688 prefixEnd_8236688 1409793315040058384673389 := by
  unfold tailWord_8236688
  simp only [CollatzResearch.WordTrace]
  refine ⟨150208345791946782580631359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200277794389262376774175145 150208345791946782580631359)
  ·
    refine ⟨225312518687920173870947039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150208345791946782580631359 225312518687920173870947039)
    ·
      refine ⟨337968778031880260806420559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225312518687920173870947039 337968778031880260806420559)
      ·
        refine ⟨506953167047820391209630839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337968778031880260806420559 506953167047820391209630839)
        ·
          refine ⟨760429750571730586814446259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506953167047820391209630839 760429750571730586814446259)
          ·
            refine ⟨1140644625857595880221669389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760429750571730586814446259 1140644625857595880221669389)
            ·
              refine ⟨427741734696598455083126021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140644625857595880221669389 427741734696598455083126021)
              ·
                refine ⟨80201575255612210328086129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427741734696598455083126021 80201575255612210328086129)
                ·
                  refine ⟨60151181441709157746064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80201575255612210328086129 60151181441709157746064597)
                  ·
                    refine ⟨1409793315040058384673389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60151181441709157746064597 1409793315040058384673389)
                    ·
                      rfl

theorem cell23_8236688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_8236688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236688 prefixEnd_8236688 := by exact prefixLift 8236688
  have htrace : WordTrace (prefixWord ++ tailWord_8236688) baseStart_8236688 baseEnd_8236688 := by
    simpa [prefixWord, tailWord_8236688, baseEnd_8236688] using wordTrace_append hprefix tailTrace_8236688
  have hstable : (prefixWord ++ tailWord_8236688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236688).length < 2 ^ (prefixWord ++ tailWord_8236688).sum := by decide
  have hdescent : baseEnd_8236688 < baseStart_8236688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236692 : List Nat := [2, 4, 2, 2, 2, 1, 1, 9]
def baseStart_8236692 : Nat := 118140960795 + 8236692 * 2 ^ 59
def prefixEnd_8236692 : Nat := 4983230072969 + 3 ^ 40 * 8236692 * 2
def baseEnd_8236692 : Nat := 156643777742325671791487

theorem tailTrace_8236692 : CollatzResearch.WordTrace tailWord_8236692 prefixEnd_8236692 156643777742325671791487 := by
  unfold tailWord_8236692
  simp only [CollatzResearch.WordTrace]
  refine ⟨150208418737939536922204165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200277891650586049229605553 150208418737939536922204165)
  ·
    refine ⟨28164078513363663172913281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150208418737939536922204165 28164078513363663172913281)
    ·
      refine ⟨21123058885022747379684961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28164078513363663172913281 21123058885022747379684961)
      ·
        refine ⟨15842294163767060534763721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21123058885022747379684961 15842294163767060534763721)
        ·
          refine ⟨11881720622825295401072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15842294163767060534763721 11881720622825295401072791)
          ·
            refine ⟨17822580934237943101609187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881720622825295401072791 17822580934237943101609187)
            ·
              refine ⟨26733871401356914652413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17822580934237943101609187 26733871401356914652413781)
              ·
                refine ⟨156643777742325671791487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26733871401356914652413781 156643777742325671791487)
                ·
                  rfl

theorem cell23_8236692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 9].length) (baseStart_8236692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236692 prefixEnd_8236692 := by exact prefixLift 8236692
  have htrace : WordTrace (prefixWord ++ tailWord_8236692) baseStart_8236692 baseEnd_8236692 := by
    simpa [prefixWord, tailWord_8236692, baseEnd_8236692] using wordTrace_append hprefix tailTrace_8236692
  have hstable : (prefixWord ++ tailWord_8236692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236692).length < 2 ^ (prefixWord ++ tailWord_8236692).sum := by decide
  have hdescent : baseEnd_8236692 < baseStart_8236692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236776 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_8236776 : Nat := 118140960795 + 8236776 * 2 ^ 59
def prefixEnd_8236776 : Nat := 4983230072969 + 3 ^ 40 * 8236776 * 2
def baseEnd_8236776 : Nat := 4229425131417770809719763

theorem tailTrace_8236776 : CollatzResearch.WordTrace tailWord_8236776 prefixEnd_8236776 4229425131417770809719763 := by
  unfold tailWord_8236776
  simp only [CollatzResearch.WordTrace]
  refine ⟨150209950603787378095233091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200279934138383170793644121 150209950603787378095233091)
  ·
    refine ⟨225314925905681067142849637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150209950603787378095233091 225314925905681067142849637)
    ·
      refine ⟨42246548607315200089284307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225314925905681067142849637 42246548607315200089284307)
      ·
        refine ⟨63369822910972800133926461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42246548607315200089284307 63369822910972800133926461)
        ·
          refine ⟨23763683591614800050222423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63369822910972800133926461 23763683591614800050222423)
          ·
            refine ⟨35645525387422200075333635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23763683591614800050222423 35645525387422200075333635)
            ·
              refine ⟨53468288081133300113000453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35645525387422200075333635 53468288081133300113000453)
              ·
                refine ⟨10025304015212493771187585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53468288081133300113000453 10025304015212493771187585)
                ·
                  refine ⟨7518978011409370328390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10025304015212493771187585 7518978011409370328390689)
                  ·
                    refine ⟨5639233508557027746293017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518978011409370328390689 5639233508557027746293017)
                    ·
                      refine ⟨4229425131417770809719763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639233508557027746293017 4229425131417770809719763)
                      ·
                        rfl

theorem cell23_8236776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_8236776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236776 prefixEnd_8236776 := by exact prefixLift 8236776
  have htrace : WordTrace (prefixWord ++ tailWord_8236776) baseStart_8236776 baseEnd_8236776 := by
    simpa [prefixWord, tailWord_8236776, baseEnd_8236776] using wordTrace_append hprefix tailTrace_8236776
  have hstable : (prefixWord ++ tailWord_8236776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236776).length < 2 ^ (prefixWord ++ tailWord_8236776).sum := by decide
  have hdescent : baseEnd_8236776 < baseStart_8236776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236812 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_8236812 : Nat := 118140960795 + 8236812 * 2 ^ 59
def prefixEnd_8236812 : Nat := 4983230072969 + 3 ^ 40 * 8236812 * 2
def baseEnd_8236812 : Nat := 1409814538907110889623199

theorem tailTrace_8236812 : CollatzResearch.WordTrace tailWord_8236812 prefixEnd_8236812 1409814538907110889623199 := by
  unfold tailWord_8236812
  simp only [CollatzResearch.WordTrace]
  refine ⟨150210607117722167169388345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200280809490296222892517793 150210607117722167169388345)
  ·
    refine ⟨112657955338291625377041259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150210607117722167169388345 112657955338291625377041259)
    ·
      refine ⟨168986933007437438065561889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112657955338291625377041259 168986933007437438065561889)
      ·
        refine ⟨126740199755578078549171417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168986933007437438065561889 126740199755578078549171417)
        ·
          refine ⟨95055149816683558911878563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126740199755578078549171417 95055149816683558911878563)
          ·
            refine ⟨142582724725025338367817845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95055149816683558911878563 142582724725025338367817845)
            ·
              refine ⟨13367130442971125471982923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142582724725025338367817845 13367130442971125471982923)
              ·
                refine ⟨20050695664456688207974385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13367130442971125471982923 20050695664456688207974385)
                ·
                  refine ⟨15038021748342516155980789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20050695664456688207974385 15038021748342516155980789)
                  ·
                    refine ⟨1409814538907110889623199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15038021748342516155980789 1409814538907110889623199)
                    ·
                      rfl

theorem cell23_8236812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_8236812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236812 prefixEnd_8236812 := by exact prefixLift 8236812
  have htrace : WordTrace (prefixWord ++ tailWord_8236812) baseStart_8236812 baseEnd_8236812 := by
    simpa [prefixWord, tailWord_8236812, baseEnd_8236812] using wordTrace_append hprefix tailTrace_8236812
  have hstable : (prefixWord ++ tailWord_8236812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236812).length < 2 ^ (prefixWord ++ tailWord_8236812).sum := by decide
  have hdescent : baseEnd_8236812 < baseStart_8236812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236832 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_8236832 : Nat := 118140960795 + 8236832 * 2 ^ 59
def prefixEnd_8236832 : Nat := 4983230072969 + 3 ^ 40 * 8236832 * 2
def baseEnd_8236832 : Nat := 4229453886334422590619505

theorem tailTrace_8236832 : CollatzResearch.WordTrace tailWord_8236832 prefixEnd_8236832 4229453886334422590619505 := by
  unfold tailWord_8236832
  simp only [CollatzResearch.WordTrace]
  refine ⟨150210971847685938877252375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200281295796914585169669833 150210971847685938877252375)
  ·
    refine ⟨225316457771528908315878563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150210971847685938877252375 225316457771528908315878563)
    ·
      refine ⟨337974686657293362473817845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225316457771528908315878563 337974686657293362473817845)
      ·
        refine ⟨31685126874121252731920423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337974686657293362473817845 31685126874121252731920423)
        ·
          refine ⟨47527690311181879097880635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31685126874121252731920423 47527690311181879097880635)
          ·
            refine ⟨71291535466772818646820953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47527690311181879097880635 71291535466772818646820953)
            ·
              refine ⟨53468651600079613985115715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71291535466772818646820953 53468651600079613985115715)
              ·
                refine ⟨80202977400119420977673573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53468651600079613985115715 80202977400119420977673573)
                ·
                  refine ⟨15038058262522391433313795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80202977400119420977673573 15038058262522391433313795)
                  ·
                    refine ⟨22557087393783587149970693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15038058262522391433313795 22557087393783587149970693)
                    ·
                      refine ⟨4229453886334422590619505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22557087393783587149970693 4229453886334422590619505)
                      ·
                        rfl

theorem cell23_8236832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_8236832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236832 prefixEnd_8236832 := by exact prefixLift 8236832
  have htrace : WordTrace (prefixWord ++ tailWord_8236832) baseStart_8236832 baseEnd_8236832 := by
    simpa [prefixWord, tailWord_8236832, baseEnd_8236832] using wordTrace_append hprefix tailTrace_8236832
  have hstable : (prefixWord ++ tailWord_8236832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236832).length < 2 ^ (prefixWord ++ tailWord_8236832).sum := by decide
  have hdescent : baseEnd_8236832 < baseStart_8236832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236835 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_8236835 : Nat := 118140960795 + 8236835 * 2 ^ 59
def prefixEnd_8236835 : Nat := 4983230072969 + 3 ^ 40 * 8236835 * 2
def baseEnd_8236835 : Nat := 4229455426776386078881991

theorem tailTrace_8236835 : CollatzResearch.WordTrace tailWord_8236835 prefixEnd_8236835 4229455426776386078881991 := by
  unfold tailWord_8236835
  simp only [CollatzResearch.WordTrace]
  refine ⟨300422053114361009266863959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200281368742907339511242639 300422053114361009266863959)
  ·
    refine ⟨450633079671541513900295939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300422053114361009266863959 450633079671541513900295939)
    ·
      refine ⟨675949619507312270850443909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450633079671541513900295939 675949619507312270850443909)
      ·
        refine ⟨126740553657621050784458233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675949619507312270850443909 126740553657621050784458233)
        ·
          refine ⟨95055415243215788088343675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126740553657621050784458233 95055415243215788088343675)
          ·
            refine ⟨142583122864823682132515513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95055415243215788088343675 142583122864823682132515513)
            ·
              refine ⟨106937342148617761599386635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142583122864823682132515513 106937342148617761599386635)
              ·
                refine ⟨160406013222926642399079953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106937342148617761599386635 160406013222926642399079953)
                ·
                  refine ⟨120304509917194981799309965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160406013222926642399079953 120304509917194981799309965)
                  ·
                    refine ⟨45114191218948118174741237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120304509917194981799309965 45114191218948118174741237)
                    ·
                      refine ⟨4229455426776386078881991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45114191218948118174741237 4229455426776386078881991)
                      ·
                        rfl

theorem cell23_8236835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_8236835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236835 prefixEnd_8236835 := by exact prefixLift 8236835
  have htrace : WordTrace (prefixWord ++ tailWord_8236835) baseStart_8236835 baseEnd_8236835 := by
    simpa [prefixWord, tailWord_8236835, baseEnd_8236835] using wordTrace_append hprefix tailTrace_8236835
  have hstable : (prefixWord ++ tailWord_8236835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236835).length < 2 ^ (prefixWord ++ tailWord_8236835).sum := by decide
  have hdescent : baseEnd_8236835 < baseStart_8236835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236849 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_8236849 : Nat := 118140960795 + 8236849 * 2 ^ 59
def prefixEnd_8236849 : Nat := 4983230072969 + 3 ^ 40 * 8236849 * 2
def baseEnd_8236849 : Nat := 4229462615505549024106927

theorem tailTrace_8236849 : CollatzResearch.WordTrace tailWord_8236849 prefixEnd_8236849 4229462615505549024106927 := by
  unfold tailWord_8236849
  simp only [CollatzResearch.WordTrace]
  refine ⟨300422563736310289657873601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200281709157540193105249067 300422563736310289657873601)
  ·
    refine ⟨225316922802232717243405201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300422563736310289657873601 225316922802232717243405201)
    ·
      refine ⟨168987692101674537932553901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225316922802232717243405201 168987692101674537932553901)
      ·
        refine ⟨63370384538127951724707713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168987692101674537932553901 63370384538127951724707713)
        ·
          refine ⟨47527788403595963793530785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63370384538127951724707713 47527788403595963793530785)
          ·
            refine ⟨35645841302696972845148089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47527788403595963793530785 35645841302696972845148089)
            ·
              refine ⟨26734380977022729633861067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35645841302696972845148089 26734380977022729633861067)
              ·
                refine ⟨40101571465534094450791601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26734380977022729633861067 40101571465534094450791601)
                ·
                  refine ⟨30076178599150570838093701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40101571465534094450791601 30076178599150570838093701)
                  ·
                    refine ⟨5639283487340732032142569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30076178599150570838093701 5639283487340732032142569)
                    ·
                      refine ⟨4229462615505549024106927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639283487340732032142569 4229462615505549024106927)
                      ·
                        rfl

theorem cell23_8236849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_8236849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236849 prefixEnd_8236849 := by exact prefixLift 8236849
  have htrace : WordTrace (prefixWord ++ tailWord_8236849) baseStart_8236849 baseEnd_8236849 := by
    simpa [prefixWord, tailWord_8236849, baseEnd_8236849] using wordTrace_append hprefix tailTrace_8236849
  have hstable : (prefixWord ++ tailWord_8236849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236849).length < 2 ^ (prefixWord ++ tailWord_8236849).sum := by decide
  have hdescent : baseEnd_8236849 < baseStart_8236849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236906 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_8236906 : Nat := 118140960795 + 8236906 * 2 ^ 59
def prefixEnd_8236906 : Nat := 4983230072969 + 3 ^ 40 * 8236906 * 2
def baseEnd_8236906 : Nat := 469943542655872811232685

theorem tailTrace_8236906 : CollatzResearch.WordTrace tailWord_8236906 prefixEnd_8236906 469943542655872811232685 := by
  unfold tailWord_8236906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75106160674275947098174643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200283095131402525595132381 75106160674275947098174643)
  ·
    refine ⟨112659241011413920647261965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75106160674275947098174643 112659241011413920647261965)
    ·
      refine ⟨42247215379280220242723237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112659241011413920647261965 42247215379280220242723237)
      ·
        refine ⟨7921352883615041295510607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42247215379280220242723237 7921352883615041295510607)
        ·
          refine ⟨11882029325422561943265911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7921352883615041295510607 11882029325422561943265911)
          ·
            refine ⟨17823043988133842914898867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882029325422561943265911 17823043988133842914898867)
            ·
              refine ⟨26734565982200764372348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823043988133842914898867 26734565982200764372348301)
              ·
                refine ⟨10025462243325286639630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26734565982200764372348301 10025462243325286639630613)
                ·
                  refine ⟨469943542655872811232685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10025462243325286639630613 469943542655872811232685)
                  ·
                    rfl

theorem cell23_8236906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_8236906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236906 prefixEnd_8236906 := by exact prefixLift 8236906
  have htrace : WordTrace (prefixWord ++ tailWord_8236906) baseStart_8236906 baseEnd_8236906 := by
    simpa [prefixWord, tailWord_8236906, baseEnd_8236906] using wordTrace_append hprefix tailTrace_8236906
  have hstable : (prefixWord ++ tailWord_8236906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236906).length < 2 ^ (prefixWord ++ tailWord_8236906).sum := by decide
  have hdescent : baseEnd_8236906 < baseStart_8236906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236909 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_8236909 : Nat := 118140960795 + 8236909 * 2 ^ 59
def prefixEnd_8236909 : Nat := 4983230072969 + 3 ^ 40 * 8236909 * 2
def baseEnd_8236909 : Nat := 4229493424344818789356651

theorem tailTrace_8236909 : CollatzResearch.WordTrace tailWord_8236909 prefixEnd_8236909 4229493424344818789356651 := by
  unfold tailWord_8236909
  simp only [CollatzResearch.WordTrace]
  refine ⟨300424752116092919905057781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200283168077395279936705187 300424752116092919905057781)
  ·
    refine ⟨28164820510883711241099167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300424752116092919905057781 28164820510883711241099167)
    ·
      refine ⟨42247230766325566861648751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28164820510883711241099167 42247230766325566861648751)
      ·
        refine ⟨63370846149488350292473127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42247230766325566861648751 63370846149488350292473127)
        ·
          refine ⟨95056269224232525438709691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63370846149488350292473127 95056269224232525438709691)
          ·
            refine ⟨142584403836348788158064537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95056269224232525438709691 142584403836348788158064537)
            ·
              refine ⟨106938302877261591118548403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142584403836348788158064537 106938302877261591118548403)
              ·
                refine ⟨160407454315892386677822605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106938302877261591118548403 160407454315892386677822605)
                ·
                  refine ⟨60152795368459645004183477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160407454315892386677822605 60152795368459645004183477)
                  ·
                    refine ⟨5639324565793091719142201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60152795368459645004183477 5639324565793091719142201)
                    ·
                      refine ⟨4229493424344818789356651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639324565793091719142201 4229493424344818789356651)
                      ·
                        rfl

theorem cell23_8236909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_8236909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236909 prefixEnd_8236909 := by exact prefixLift 8236909
  have htrace : WordTrace (prefixWord ++ tailWord_8236909) baseStart_8236909 baseEnd_8236909 := by
    simpa [prefixWord, tailWord_8236909, baseEnd_8236909] using wordTrace_append hprefix tailTrace_8236909
  have hstable : (prefixWord ++ tailWord_8236909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236909).length < 2 ^ (prefixWord ++ tailWord_8236909).sum := by decide
  have hdescent : baseEnd_8236909 < baseStart_8236909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236932 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_8236932 : Nat := 118140960795 + 8236932 * 2 ^ 59
def prefixEnd_8236932 : Nat := 4983230072969 + 3 ^ 40 * 8236932 * 2
def baseEnd_8236932 : Nat := 1409835078133290733123015

theorem tailTrace_8236932 : CollatzResearch.WordTrace tailWord_8236932 prefixEnd_8236932 1409835078133290733123015 := by
  unfold tailWord_8236932
  simp only [CollatzResearch.WordTrace]
  refine ⟨150212795497504797416572525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200283727330006396555430033 150212795497504797416572525)
  ·
    refine ⟨56329798311564299031214697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150212795497504797416572525 56329798311564299031214697)
    ·
      refine ⟨42247348733673224273411023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56329798311564299031214697 42247348733673224273411023)
      ·
        refine ⟨63371023100509836410116535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42247348733673224273411023 63371023100509836410116535)
        ·
          refine ⟨95056534650764754615174803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63371023100509836410116535 95056534650764754615174803)
          ·
            refine ⟨142584801976147131922762205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95056534650764754615174803 142584801976147131922762205)
            ·
              refine ⟨53469300741055174471035827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142584801976147131922762205 53469300741055174471035827)
              ·
                refine ⟨80203951111582761706553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53469300741055174471035827 80203951111582761706553741)
                ·
                  refine ⟨30076481666843535639957653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80203951111582761706553741 30076481666843535639957653)
                  ·
                    refine ⟨1409835078133290733123015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30076481666843535639957653 1409835078133290733123015)
                    ·
                      rfl

theorem cell23_8236932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_8236932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236932 prefixEnd_8236932 := by exact prefixLift 8236932
  have htrace : WordTrace (prefixWord ++ tailWord_8236932) baseStart_8236932 baseEnd_8236932 := by
    simpa [prefixWord, tailWord_8236932, baseEnd_8236932] using wordTrace_append hprefix tailTrace_8236932
  have hstable : (prefixWord ++ tailWord_8236932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236932).length < 2 ^ (prefixWord ++ tailWord_8236932).sum := by decide
  have hdescent : baseEnd_8236932 < baseStart_8236932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236990 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_8236990 : Nat := 118140960795 + 8236990 * 2 ^ 59
def prefixEnd_8236990 : Nat := 4983230072969 + 3 ^ 40 * 8236990 * 2
def baseEnd_8236990 : Nat := 4229535016277832972443779

theorem tailTrace_8236990 : CollatzResearch.WordTrace tailWord_8236990 prefixEnd_8236990 4229535016277832972443779 := by
  unfold tailWord_8236990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37553463303599933842344553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200285137619199647159170949 37553463303599933842344553)
  ·
    refine ⟨28165097477699950381758415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37553463303599933842344553 28165097477699950381758415)
    ·
      refine ⟨42247646216549925572637623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28165097477699950381758415 42247646216549925572637623)
      ·
        refine ⟨63371469324824888358956435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42247646216549925572637623 63371469324824888358956435)
        ·
          refine ⟨95057203987237332538434653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63371469324824888358956435 95057203987237332538434653)
          ·
            refine ⟨35646451495213999701912995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95057203987237332538434653 35646451495213999701912995)
            ·
              refine ⟨53469677242820999552869493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35646451495213999701912995 53469677242820999552869493)
              ·
                refine ⟨5012782241514468708081515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53469677242820999552869493 5012782241514468708081515)
                ·
                  refine ⟨7519173362271703062122273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012782241514468708081515 7519173362271703062122273)
                  ·
                    refine ⟨5639380021703777296591705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7519173362271703062122273 5639380021703777296591705)
                    ·
                      refine ⟨4229535016277832972443779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639380021703777296591705 4229535016277832972443779)
                      ·
                        rfl

theorem cell23_8236990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_8236990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236990 prefixEnd_8236990 := by exact prefixLift 8236990
  have htrace : WordTrace (prefixWord ++ tailWord_8236990) baseStart_8236990 baseEnd_8236990 := by
    simpa [prefixWord, tailWord_8236990, baseEnd_8236990] using wordTrace_append hprefix tailTrace_8236990
  have hstable : (prefixWord ++ tailWord_8236990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236990).length < 2 ^ (prefixWord ++ tailWord_8236990).sum := by decide
  have hdescent : baseEnd_8236990 < baseStart_8236990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237006 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_8237006 : Nat := 118140960795 + 8237006 * 2 ^ 59
def prefixEnd_8237006 : Nat := 4983230072969 + 3 ^ 40 * 8237006 * 2
def baseEnd_8237006 : Nat := 4229543231968304909843705

theorem tailTrace_8237006 : CollatzResearch.WordTrace tailWord_8237006 prefixEnd_8237006 4229543231968304909843705 := by
  unfold tailWord_8237006
  simp only [CollatzResearch.WordTrace]
  refine ⟨37553536249592688183917359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200285526664494336980892581 37553536249592688183917359)
  ·
    refine ⟨56330304374389032275876039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37553536249592688183917359 56330304374389032275876039)
    ·
      refine ⟨84495456561583548413814059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56330304374389032275876039 84495456561583548413814059)
      ·
        refine ⟨126743184842375322620721089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84495456561583548413814059 126743184842375322620721089)
        ·
          refine ⟨95057388631781491965540817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126743184842375322620721089 95057388631781491965540817)
          ·
            refine ⟨71293041473836118974155613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95057388631781491965540817 71293041473836118974155613)
            ·
              refine ⟨26734890552688544615308355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71293041473836118974155613 26734890552688544615308355)
              ·
                refine ⟨40102335829032816922962533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26734890552688544615308355 40102335829032816922962533)
                ·
                  refine ⟨7519187967943653173055475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40102335829032816922962533 7519187967943653173055475)
                  ·
                    refine ⟨11278781951915479759583213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7519187967943653173055475 11278781951915479759583213)
                    ·
                      refine ⟨4229543231968304909843705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11278781951915479759583213 4229543231968304909843705)
                      ·
                        rfl

theorem cell23_8237006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_8237006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237006 prefixEnd_8237006 := by exact prefixLift 8237006
  have htrace : WordTrace (prefixWord ++ tailWord_8237006) baseStart_8237006 baseEnd_8237006 := by
    simpa [prefixWord, tailWord_8237006, baseEnd_8237006] using wordTrace_append hprefix tailTrace_8237006
  have hstable : (prefixWord ++ tailWord_8237006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237006).length < 2 ^ (prefixWord ++ tailWord_8237006).sum := by decide
  have hdescent : baseEnd_8237006 < baseStart_8237006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237049 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_8237049 : Nat := 118140960795 + 8237049 * 2 ^ 59
def prefixEnd_8237049 : Nat := 4983230072969 + 3 ^ 40 * 8237049 * 2
def baseEnd_8237049 : Nat := 4229565311636448241606007

theorem tailTrace_8237049 : CollatzResearch.WordTrace tailWord_8237049 prefixEnd_8237049 4229565311636448241606007 := by
  unfold tailWord_8237049
  simp only [CollatzResearch.WordTrace]
  refine ⟨300429858335585723815154201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200286572223723815876769467 300429858335585723815154201)
  ·
    refine ⟨225322393751689292861365651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300429858335585723815154201 225322393751689292861365651)
    ·
      refine ⟨337983590627533939292048477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225322393751689292861365651 337983590627533939292048477)
      ·
        refine ⟨126743846485325227234518179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337983590627533939292048477 126743846485325227234518179)
        ·
          refine ⟨190115769727987840851777269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126743846485325227234518179 190115769727987840851777269)
          ·
            refine ⟨17823353411998860079854119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190115769727987840851777269 17823353411998860079854119)
            ·
              refine ⟨26735030117998290119781179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823353411998860079854119 26735030117998290119781179)
              ·
                refine ⟨40102545176997435179671769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735030117998290119781179 40102545176997435179671769)
                ·
                  refine ⟨30076908882748076384753827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40102545176997435179671769 30076908882748076384753827)
                  ·
                    refine ⟨45115363324122114577130741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30076908882748076384753827 45115363324122114577130741)
                    ·
                      refine ⟨4229565311636448241606007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45115363324122114577130741 4229565311636448241606007)
                      ·
                        rfl

theorem cell23_8237049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_8237049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237049 prefixEnd_8237049 := by exact prefixLift 8237049
  have htrace : WordTrace (prefixWord ++ tailWord_8237049) baseStart_8237049 baseEnd_8237049 := by
    simpa [prefixWord, tailWord_8237049, baseEnd_8237049] using wordTrace_append hprefix tailTrace_8237049
  have hstable : (prefixWord ++ tailWord_8237049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237049).length < 2 ^ (prefixWord ++ tailWord_8237049).sum := by decide
  have hdescent : baseEnd_8237049 < baseStart_8237049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237063 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_8237063 : Nat := 118140960795 + 8237063 * 2 ^ 59
def prefixEnd_8237063 : Nat := 4983230072969 + 3 ^ 40 * 8237063 * 2
def baseEnd_8237063 : Nat := 4229572500365611186830943

theorem tailTrace_8237063 : CollatzResearch.WordTrace tailWord_8237063 prefixEnd_8237063 4229572500365611186830943 := by
  unfold tailWord_8237063
  simp only [CollatzResearch.WordTrace]
  refine ⟨300430368957535004206163843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200286912638356669470775895 300430368957535004206163843)
  ·
    refine ⟨450645553436302506309245765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300430368957535004206163843 450645553436302506309245765)
    ·
      refine ⟨84496041269306719932983581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450645553436302506309245765 84496041269306719932983581)
      ·
        refine ⟨31686015475990019974868843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84496041269306719932983581 31686015475990019974868843)
        ·
          refine ⟨47529023213985029962303265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686015475990019974868843 47529023213985029962303265)
          ·
            refine ⟨35646767410488772471727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47529023213985029962303265 35646767410488772471727449)
            ·
              refine ⟨26735075557866579353795587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35646767410488772471727449 26735075557866579353795587)
              ·
                refine ⟨40102613336799869030693381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735075557866579353795587 40102613336799869030693381)
                ·
                  refine ⟨7519240000649975443255009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40102613336799869030693381 7519240000649975443255009)
                  ·
                    refine ⟨5639430000487481582441257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7519240000649975443255009 5639430000487481582441257)
                    ·
                      refine ⟨4229572500365611186830943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639430000487481582441257 4229572500365611186830943)
                      ·
                        rfl

theorem cell23_8237063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_8237063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237063 prefixEnd_8237063 := by exact prefixLift 8237063
  have htrace : WordTrace (prefixWord ++ tailWord_8237063) baseStart_8237063 baseEnd_8237063 := by
    simpa [prefixWord, tailWord_8237063, baseEnd_8237063] using wordTrace_append hprefix tailTrace_8237063
  have hstable : (prefixWord ++ tailWord_8237063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237063).length < 2 ^ (prefixWord ++ tailWord_8237063).sum := by decide
  have hdescent : baseEnd_8237063 < baseStart_8237063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237109 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_8237109 : Nat := 118140960795 + 8237109 * 2 ^ 59
def prefixEnd_8237109 : Nat := 4983230072969 + 3 ^ 40 * 8237109 * 2
def baseEnd_8237109 : Nat := 4229596120475718006855731

theorem tailTrace_8237109 : CollatzResearch.WordTrace tailWord_8237109 prefixEnd_8237109 4229596120475718006855731 := by
  unfold tailWord_8237109
  simp only [CollatzResearch.WordTrace]
  refine ⟨300432046715368354062338381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200288031143578902708225587 300432046715368354062338381)
  ·
    refine ⟨112662017518263132773376893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300432046715368354062338381 112662017518263132773376893)
    ·
      refine ⟨42248256569348674790016335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112662017518263132773376893 42248256569348674790016335)
      ·
        refine ⟨63372384854023012185024503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42248256569348674790016335 63372384854023012185024503)
        ·
          refine ⟨95058577281034518277536755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63372384854023012185024503 95058577281034518277536755)
          ·
            refine ⟨142587865921551777416305133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95058577281034518277536755 142587865921551777416305133)
            ·
              refine ⟨53470449720581916531114425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142587865921551777416305133 53470449720581916531114425)
              ·
                refine ⟨40102837290436437398335819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53470449720581916531114425 40102837290436437398335819)
                ·
                  refine ⟨60154255935654656097503729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40102837290436437398335819 60154255935654656097503729)
                  ·
                    refine ⟨45115691951740992073127797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60154255935654656097503729 45115691951740992073127797)
                    ·
                      refine ⟨4229596120475718006855731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45115691951740992073127797 4229596120475718006855731)
                      ·
                        rfl

theorem cell23_8237109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_8237109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237109 prefixEnd_8237109 := by exact prefixLift 8237109
  have htrace : WordTrace (prefixWord ++ tailWord_8237109) baseStart_8237109 baseEnd_8237109 := by
    simpa [prefixWord, tailWord_8237109, baseEnd_8237109] using wordTrace_append hprefix tailTrace_8237109
  have hstable : (prefixWord ++ tailWord_8237109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237109).length < 2 ^ (prefixWord ++ tailWord_8237109).sum := by decide
  have hdescent : baseEnd_8237109 < baseStart_8237109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237146 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_8237146 : Nat := 118140960795 + 8237146 * 2 ^ 59
def prefixEnd_8237146 : Nat := 4983230072969 + 3 ^ 40 * 8237146 * 2
def baseEnd_8237146 : Nat := 1409871706419978120697687

theorem tailTrace_8237146 : CollatzResearch.WordTrace tailWord_8237146 prefixEnd_8237146 1409871706419978120697687 := by
  unfold tailWord_8237146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75108349054058577345358823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200288930810822872920956861 75108349054058577345358823)
  ·
    refine ⟨112662523581087866018038235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75108349054058577345358823 112662523581087866018038235)
    ·
      refine ⟨168993785371631799027057353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112662523581087866018038235 168993785371631799027057353)
      ·
        refine ⟨126745339028723849270293015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168993785371631799027057353 126745339028723849270293015)
        ·
          refine ⟨190118008543085773905439523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126745339028723849270293015 190118008543085773905439523)
          ·
            refine ⟨285177012814628660858159285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190118008543085773905439523 285177012814628660858159285)
            ·
              refine ⟨26735344951371436955452433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285177012814628660858159285 26735344951371436955452433)
              ·
                refine ⟨20051508713528577716589325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26735344951371436955452433 20051508713528577716589325)
                ·
                  refine ⟨7519315767573216643720997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20051508713528577716589325 7519315767573216643720997)
                  ·
                    refine ⟨1409871706419978120697687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519315767573216643720997 1409871706419978120697687)
                    ·
                      rfl

theorem cell23_8237146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_8237146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237146 prefixEnd_8237146 := by exact prefixLift 8237146
  have htrace : WordTrace (prefixWord ++ tailWord_8237146) baseStart_8237146 baseEnd_8237146 := by
    simpa [prefixWord, tailWord_8237146, baseEnd_8237146] using wordTrace_append hprefix tailTrace_8237146
  have hstable : (prefixWord ++ tailWord_8237146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237146).length < 2 ^ (prefixWord ++ tailWord_8237146).sum := by decide
  have hdescent : baseEnd_8237146 < baseStart_8237146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237150 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_8237150 : Nat := 118140960795 + 8237150 * 2 ^ 59
def prefixEnd_8237150 : Nat := 4983230072969 + 3 ^ 40 * 8237150 * 2
def baseEnd_8237150 : Nat := 1409872391060850782147681

theorem tailTrace_8237150 : CollatzResearch.WordTrace tailWord_8237150 prefixEnd_8237150 1409872391060850782147681 := by
  unfold tailWord_8237150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37554192763527477258072613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200289028072146545376387269 37554192763527477258072613)
  ·
    refine ⟨7041411143161401985888615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37554192763527477258072613 7041411143161401985888615)
    ·
      refine ⟨10562116714742102978832923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7041411143161401985888615 10562116714742102978832923)
      ·
        refine ⟨15843175072113154468249385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10562116714742102978832923 15843175072113154468249385)
        ·
          refine ⟨11882381304084865851187039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15843175072113154468249385 11882381304084865851187039)
          ·
            refine ⟨17823571956127298776780559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882381304084865851187039 17823571956127298776780559)
            ·
              refine ⟨26735357934190948165170839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823571956127298776780559 26735357934190948165170839)
              ·
                refine ⟨40103036901286422247756259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735357934190948165170839 40103036901286422247756259)
                ·
                  refine ⟨60154555351929633371634389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40103036901286422247756259 60154555351929633371634389)
                  ·
                    refine ⟨1409872391060850782147681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60154555351929633371634389 1409872391060850782147681)
                    ·
                      rfl

theorem cell23_8237150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_8237150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237150 prefixEnd_8237150 := by exact prefixLift 8237150
  have htrace : WordTrace (prefixWord ++ tailWord_8237150) baseStart_8237150 baseEnd_8237150 := by
    simpa [prefixWord, tailWord_8237150, baseEnd_8237150] using wordTrace_append hprefix tailTrace_8237150
  have hstable : (prefixWord ++ tailWord_8237150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237150).length < 2 ^ (prefixWord ++ tailWord_8237150).sum := by decide
  have hdescent : baseEnd_8237150 < baseStart_8237150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237159 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 8]
def baseStart_8237159 : Nat := 118140960795 + 8237159 * 2 ^ 59
def prefixEnd_8237159 : Nat := 4983230072969 + 3 ^ 40 * 8237159 * 2
def baseEnd_8237159 : Nat := 469957977167604756803389

theorem tailTrace_8237159 : CollatzResearch.WordTrace tailWord_8237159 prefixEnd_8237159 469957977167604756803389 := by
  unfold tailWord_8237159
  simp only [CollatzResearch.WordTrace]
  refine ⟨300433870365187212601658531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200289246910124808401105687 300433870365187212601658531)
  ·
    refine ⟨450650805547780818902487797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300433870365187212601658531 450650805547780818902487797)
    ·
      refine ⟨42248513020104451772108231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450650805547780818902487797 42248513020104451772108231)
      ·
        refine ⟨63372769530156677658162347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42248513020104451772108231 63372769530156677658162347)
        ·
          refine ⟨95059154295235016487243521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63372769530156677658162347 95059154295235016487243521)
          ·
            refine ⟨71294365721426262365432641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95059154295235016487243521 71294365721426262365432641)
            ·
              refine ⟨53470774291069696774074481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71294365721426262365432641 53470774291069696774074481)
              ·
                refine ⟨40103080718302272580555861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53470774291069696774074481 40103080718302272580555861)
                ·
                  refine ⟨469957977167604756803389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40103080718302272580555861 469957977167604756803389)
                  ·
                    rfl

theorem cell23_8237159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 8].length) (baseStart_8237159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237159 prefixEnd_8237159 := by exact prefixLift 8237159
  have htrace : WordTrace (prefixWord ++ tailWord_8237159) baseStart_8237159 baseEnd_8237159 := by
    simpa [prefixWord, tailWord_8237159, baseEnd_8237159] using wordTrace_append hprefix tailTrace_8237159
  have hstable : (prefixWord ++ tailWord_8237159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237159).length < 2 ^ (prefixWord ++ tailWord_8237159).sum := by decide
  have hdescent : baseEnd_8237159 < baseStart_8237159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237209 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_8237209 : Nat := 118140960795 + 8237209 * 2 ^ 59
def prefixEnd_8237209 : Nat := 4983230072969 + 3 ^ 40 * 8237209 * 2
def baseEnd_8237209 : Nat := 4229647468541167615605271

theorem tailTrace_8237209 : CollatzResearch.WordTrace tailWord_8237209 prefixEnd_8237209 4229647468541167615605271 := by
  unfold tailWord_8237209
  simp only [CollatzResearch.WordTrace]
  refine ⟨300435694015006071140978681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200290462676670714093985787 300435694015006071140978681)
  ·
    refine ⟨225326770511254553355734011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300435694015006071140978681 225326770511254553355734011)
    ·
      refine ⟨337990155766881830033601017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225326770511254553355734011 337990155766881830033601017)
      ·
        refine ⟨253492616825161372525200763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337990155766881830033601017 253492616825161372525200763)
        ·
          refine ⟨380238925237742058787801145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253492616825161372525200763 380238925237742058787801145)
          ·
            refine ⟨285179193928306544090850859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380238925237742058787801145 285179193928306544090850859)
            ·
              refine ⟨427768790892459816136276289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285179193928306544090850859 427768790892459816136276289)
              ·
                refine ⟨320826593169344862102207217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427768790892459816136276289 320826593169344862102207217)
                ·
                  refine ⟨240619944877008646576655413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320826593169344862102207217 240619944877008646576655413)
                  ·
                    refine ⟨22558119832219560616561445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240619944877008646576655413 22558119832219560616561445)
                    ·
                      refine ⟨4229647468541167615605271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22558119832219560616561445 4229647468541167615605271)
                      ·
                        rfl

theorem cell23_8237209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_8237209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237209 prefixEnd_8237209 := by exact prefixLift 8237209
  have htrace : WordTrace (prefixWord ++ tailWord_8237209) baseStart_8237209 baseEnd_8237209 := by
    simpa [prefixWord, tailWord_8237209, baseEnd_8237209] using wordTrace_append hprefix tailTrace_8237209
  have hstable : (prefixWord ++ tailWord_8237209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237209).length < 2 ^ (prefixWord ++ tailWord_8237209).sum := by decide
  have hdescent : baseEnd_8237209 < baseStart_8237209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237213 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_8237213 : Nat := 118140960795 + 8237213 * 2 ^ 59
def prefixEnd_8237213 : Nat := 4983230072969 + 3 ^ 40 * 8237213 * 2
def baseEnd_8237213 : Nat := 4229649522463785599955253

theorem tailTrace_8237213 : CollatzResearch.WordTrace tailWord_8237213 prefixEnd_8237213 4229649522463785599955253 := by
  unfold tailWord_8237213
  simp only [CollatzResearch.WordTrace]
  refine ⟨300435839906991579824124293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200290559937994386549416195 300435839906991579824124293)
  ·
    refine ⟨56331719982560921217023305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300435839906991579824124293 56331719982560921217023305)
    ·
      refine ⟨42248789986920690912767479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56331719982560921217023305 42248789986920690912767479)
      ·
        refine ⟨63373184980381036369151219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42248789986920690912767479 63373184980381036369151219)
        ·
          refine ⟨95059777470571554553726829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63373184980381036369151219 95059777470571554553726829)
          ·
            refine ⟨35647416551464332957647561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95059777470571554553726829 35647416551464332957647561)
            ·
              refine ⟨26735562413598249718235671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35647416551464332957647561 26735562413598249718235671)
              ·
                refine ⟨40103343620397374577353507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735562413598249718235671 40103343620397374577353507)
                ·
                  refine ⟨60155015430596061866030261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40103343620397374577353507 60155015430596061866030261)
                  ·
                    refine ⟨5639532696618380799940337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60155015430596061866030261 5639532696618380799940337)
                    ·
                      refine ⟨4229649522463785599955253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639532696618380799940337 4229649522463785599955253)
                      ·
                        rfl

theorem cell23_8237213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_8237213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237213 prefixEnd_8237213 := by exact prefixLift 8237213
  have htrace : WordTrace (prefixWord ++ tailWord_8237213) baseStart_8237213 baseEnd_8237213 := by
    simpa [prefixWord, tailWord_8237213, baseEnd_8237213] using wordTrace_append hprefix tailTrace_8237213
  have hstable : (prefixWord ++ tailWord_8237213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237213).length < 2 ^ (prefixWord ++ tailWord_8237213).sum := by decide
  have hdescent : baseEnd_8237213 < baseStart_8237213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237214 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_8237214 : Nat := 118140960795 + 8237214 * 2 ^ 59
def prefixEnd_8237214 : Nat := 4983230072969 + 3 ^ 40 * 8237214 * 2
def baseEnd_8237214 : Nat := 1409883345314813365347583

theorem tailTrace_8237214 : CollatzResearch.WordTrace tailWord_8237214 prefixEnd_8237214 1409883345314813365347583 := by
  unfold tailWord_8237214
  simp only [CollatzResearch.WordTrace]
  refine ⟨37554484547498494624363837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200290584253325304663273797 37554484547498494624363837)
  ·
    refine ⟨14082931705311935484136439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37554484547498494624363837 14082931705311935484136439)
    ·
      refine ⟨21124397557967903226204659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14082931705311935484136439 21124397557967903226204659)
      ·
        refine ⟨31686596336951854839306989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124397557967903226204659 31686596336951854839306989)
        ·
          refine ⟨11882473626356945564740121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31686596336951854839306989 11882473626356945564740121)
          ·
            refine ⟨8911855219767709173555091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11882473626356945564740121 8911855219767709173555091)
            ·
              refine ⟨13367782829651563760332637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911855219767709173555091 13367782829651563760332637)
              ·
                refine ⟨5012918561119336410124739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13367782829651563760332637 5012918561119336410124739)
                ·
                  refine ⟨7519377841679004615187109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012918561119336410124739 7519377841679004615187109)
                  ·
                    refine ⟨1409883345314813365347583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519377841679004615187109 1409883345314813365347583)
                    ·
                      rfl

theorem cell23_8237214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_8237214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237214 prefixEnd_8237214 := by exact prefixLift 8237214
  have htrace : WordTrace (prefixWord ++ tailWord_8237214) baseStart_8237214 baseEnd_8237214 := by
    simpa [prefixWord, tailWord_8237214, baseEnd_8237214] using wordTrace_append hprefix tailTrace_8237214
  have hstable : (prefixWord ++ tailWord_8237214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237214).length < 2 ^ (prefixWord ++ tailWord_8237214).sum := by decide
  have hdescent : baseEnd_8237214 < baseStart_8237214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237256 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_8237256 : Nat := 118140960795 + 8237256 * 2 ^ 59
def prefixEnd_8237256 : Nat := 4983230072969 + 3 ^ 40 * 8237256 * 2
def baseEnd_8237256 : Nat := 4229671602131928931717555

theorem tailTrace_8237256 : CollatzResearch.WordTrace tailWord_8237256 prefixEnd_8237256 4229671602131928931717555 := by
  unfold tailWord_8237256
  simp only [CollatzResearch.WordTrace]
  refine ⟨150218704122917899083969811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200291605497223865445293081 150218704122917899083969811)
  ·
    refine ⟨225328056184376848625954717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150218704122917899083969811 225328056184376848625954717)
    ·
      refine ⟨84498021069141318234733019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225328056184376848625954717 84498021069141318234733019)
      ·
        refine ⟨126747031603711977352099529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84498021069141318234733019 126747031603711977352099529)
        ·
          refine ⟨95060273702783983014074647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126747031603711977352099529 95060273702783983014074647)
          ·
            refine ⟨142590410554175974521111971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95060273702783983014074647 142590410554175974521111971)
            ·
              refine ⟨213885615831263961781667957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142590410554175974521111971 213885615831263961781667957)
              ·
                refine ⟨20051776484180996417031371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213885615831263961781667957 20051776484180996417031371)
                ·
                  refine ⟨30077664726271494625547057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20051776484180996417031371 30077664726271494625547057)
                  ·
                    refine ⟨22558248544703620969160293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30077664726271494625547057 22558248544703620969160293)
                    ·
                      refine ⟨4229671602131928931717555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22558248544703620969160293 4229671602131928931717555)
                      ·
                        rfl

theorem cell23_8237256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_8237256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237256 prefixEnd_8237256 := by exact prefixLift 8237256
  have htrace : WordTrace (prefixWord ++ tailWord_8237256) baseStart_8237256 baseEnd_8237256 := by
    simpa [prefixWord, tailWord_8237256, baseEnd_8237256] using wordTrace_append hprefix tailTrace_8237256
  have hstable : (prefixWord ++ tailWord_8237256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237256).length < 2 ^ (prefixWord ++ tailWord_8237256).sum := by decide
  have hdescent : baseEnd_8237256 < baseStart_8237256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237260 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_8237260 : Nat := 118140960795 + 8237260 * 2 ^ 59
def prefixEnd_8237260 : Nat := 4983230072969 + 3 ^ 40 * 8237260 * 2
def baseEnd_8237260 : Nat := 4229673656054546916067537

theorem tailTrace_8237260 : CollatzResearch.WordTrace tailWord_8237260 prefixEnd_8237260 4229673656054546916067537 := by
  unfold tailWord_8237260
  simp only [CollatzResearch.WordTrace]
  refine ⟨150218777068910653425542617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200291702758547537900723489 150218777068910653425542617)
  ·
    refine ⟨112664082801682990069156963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150218777068910653425542617 112664082801682990069156963)
    ·
      refine ⟨168996124202524485103735445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112664082801682990069156963 168996124202524485103735445)
      ·
        refine ⟨7921693321993335239237599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168996124202524485103735445 7921693321993335239237599)
        ·
          refine ⟨11882539982990002858856399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7921693321993335239237599 11882539982990002858856399)
          ·
            refine ⟨17823809974485004288284599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882539982990002858856399 17823809974485004288284599)
            ·
              refine ⟨26735714961727506432426899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823809974485004288284599 26735714961727506432426899)
              ·
                refine ⟨40103572442591259648640349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735714961727506432426899 40103572442591259648640349)
                ·
                  refine ⟨15038839665971722368240131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40103572442591259648640349 15038839665971722368240131)
                  ·
                    refine ⟨22558259498957583552360197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15038839665971722368240131 22558259498957583552360197)
                    ·
                      refine ⟨4229673656054546916067537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22558259498957583552360197 4229673656054546916067537)
                      ·
                        rfl

theorem cell23_8237260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_8237260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237260 prefixEnd_8237260 := by exact prefixLift 8237260
  have htrace : WordTrace (prefixWord ++ tailWord_8237260) baseStart_8237260 baseEnd_8237260 := by
    simpa [prefixWord, tailWord_8237260, baseEnd_8237260] using wordTrace_append hprefix tailTrace_8237260
  have hstable : (prefixWord ++ tailWord_8237260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237260).length < 2 ^ (prefixWord ++ tailWord_8237260).sum := by decide
  have hdescent : baseEnd_8237260 < baseStart_8237260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237266 : List Nat := [3, 2, 2, 2, 1, 2, 2, 9]
def baseStart_8237266 : Nat := 118140960795 + 8237266 * 2 ^ 59
def prefixEnd_8237266 : Nat := 4983230072969 + 3 ^ 40 * 8237266 * 2
def baseEnd_8237266 : Nat := 156654693960684218244167

theorem tailTrace_8237266 : CollatzResearch.WordTrace tailWord_8237266 prefixEnd_8237266 156654693960684218244167 := by
  unfold tailWord_8237266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75109443243949892468950913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200291848650533046583869101 75109443243949892468950913)
  ·
    refine ⟨56332082432962419351713185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75109443243949892468950913 56332082432962419351713185)
    ·
      refine ⟨42249061824721814513784889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56332082432962419351713185 42249061824721814513784889)
      ·
        refine ⟨31686796368541360885338667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42249061824721814513784889 31686796368541360885338667)
        ·
          refine ⟨47530194552812041328008001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686796368541360885338667 47530194552812041328008001)
          ·
            refine ⟨35647645914609030996006001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47530194552812041328008001 35647645914609030996006001)
            ·
              refine ⟨26735734435956773247004501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35647645914609030996006001 26735734435956773247004501)
              ·
                refine ⟨156654693960684218244167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26735734435956773247004501 156654693960684218244167)
                ·
                  rfl

theorem cell23_8237266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_8237266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237266 prefixEnd_8237266 := by exact prefixLift 8237266
  have htrace : WordTrace (prefixWord ++ tailWord_8237266) baseStart_8237266 baseEnd_8237266 := by
    simpa [prefixWord, tailWord_8237266, baseEnd_8237266] using wordTrace_append hprefix tailTrace_8237266
  have hstable : (prefixWord ++ tailWord_8237266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237266).length < 2 ^ (prefixWord ++ tailWord_8237266).sum := by decide
  have hdescent : baseEnd_8237266 < baseStart_8237266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237270 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_8237270 : Nat := 118140960795 + 8237270 * 2 ^ 59
def prefixEnd_8237270 : Nat := 4983230072969 + 3 ^ 40 * 8237270 * 2
def baseEnd_8237270 : Nat := 1409892930287030625647497

theorem tailTrace_8237270 : CollatzResearch.WordTrace tailWord_8237270 prefixEnd_8237270 1409892930287030625647497 := by
  unfold tailWord_8237270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777369929236567409934329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200291945911856719039299509 18777369929236567409934329)
  ·
    refine ⟨14083027446927425557450747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18777369929236567409934329 14083027446927425557450747)
    ·
      refine ⟨21124541170391138336176121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14083027446927425557450747 21124541170391138336176121)
      ·
        refine ⟨15843405877793353752132091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21124541170391138336176121 15843405877793353752132091)
        ·
          refine ⟨23765108816690030628198137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15843405877793353752132091 23765108816690030628198137)
          ·
            refine ⟨17823831612517522971148603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23765108816690030628198137 17823831612517522971148603)
            ·
              refine ⟨26735747418776284456722905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17823831612517522971148603 26735747418776284456722905)
              ·
                refine ⟨20051810564082213342542179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26735747418776284456722905 20051810564082213342542179)
                ·
                  refine ⟨30077715846123320013813269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20051810564082213342542179 30077715846123320013813269)
                  ·
                    refine ⟨1409892930287030625647497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30077715846123320013813269 1409892930287030625647497)
                    ·
                      rfl

theorem cell23_8237270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_8237270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237270 prefixEnd_8237270 := by exact prefixLift 8237270
  have htrace : WordTrace (prefixWord ++ tailWord_8237270) baseStart_8237270 baseEnd_8237270 := by
    simpa [prefixWord, tailWord_8237270, baseEnd_8237270] using wordTrace_append hprefix tailTrace_8237270
  have hstable : (prefixWord ++ tailWord_8237270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237270).length < 2 ^ (prefixWord ++ tailWord_8237270).sum := by decide
  have hdescent : baseEnd_8237270 < baseStart_8237270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237277 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_8237277 : Nat := 118140960795 + 8237277 * 2 ^ 59
def prefixEnd_8237277 : Nat := 4983230072969 + 3 ^ 40 * 8237277 * 2
def baseEnd_8237277 : Nat := 4229682385225673349554959

theorem tailTrace_8237277 : CollatzResearch.WordTrace tailWord_8237277 prefixEnd_8237277 4229682385225673349554959 := by
  unfold tailWord_8237277
  simp only [CollatzResearch.WordTrace]
  refine ⟨300438174178759718754454085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200292116119173145836302723 300438174178759718754454085)
  ·
    refine ⟨56332157658517447266460141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300438174178759718754454085 56332157658517447266460141)
    ·
      refine ⟨21124559121944042724922553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56332157658517447266460141 21124559121944042724922553)
      ·
        refine ⟨15843419341458032043691915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21124559121944042724922553 15843419341458032043691915)
        ·
          refine ⟨23765129012187048065537873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15843419341458032043691915 23765129012187048065537873)
          ·
            refine ⟨17823846759140286049153405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23765129012187048065537873 17823846759140286049153405)
            ·
              refine ⟨6683942534677607268432527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17823846759140286049153405 6683942534677607268432527)
              ·
                refine ⟨10025913802016410902648791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683942534677607268432527 10025913802016410902648791)
                ·
                  refine ⟨15038870703024616353973187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10025913802016410902648791 15038870703024616353973187)
                  ·
                    refine ⟨22558306054536924530959781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15038870703024616353973187 22558306054536924530959781)
                    ·
                      refine ⟨4229682385225673349554959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22558306054536924530959781 4229682385225673349554959)
                      ·
                        rfl

theorem cell23_8237277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_8237277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237277 prefixEnd_8237277 := by exact prefixLift 8237277
  have htrace : WordTrace (prefixWord ++ tailWord_8237277) baseStart_8237277 baseEnd_8237277 := by
    simpa [prefixWord, tailWord_8237277, baseEnd_8237277] using wordTrace_append hprefix tailTrace_8237277
  have hstable : (prefixWord ++ tailWord_8237277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237277).length < 2 ^ (prefixWord ++ tailWord_8237277).sum := by decide
  have hdescent : baseEnd_8237277 < baseStart_8237277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237280 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3]
def baseStart_8237280 : Nat := 118140960795 + 8237280 * 2 ^ 59
def prefixEnd_8237280 : Nat := 4983230072969 + 3 ^ 40 * 8237280 * 2
def baseEnd_8237280 : Nat := 4229683925667636837817445

theorem tailTrace_8237280 : CollatzResearch.WordTrace tailWord_8237280 prefixEnd_8237280 4229683925667636837817445 := by
  unfold tailWord_8237280
  simp only [CollatzResearch.WordTrace]
  refine ⟨150219141798874425133406647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200292189065165900177875529 150219141798874425133406647)
  ·
    refine ⟨225328712698311637700109971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150219141798874425133406647 225328712698311637700109971)
    ·
      refine ⟨337993069047467456550164957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225328712698311637700109971 337993069047467456550164957)
      ·
        refine ⟨126747400892800296206311859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337993069047467456550164957 126747400892800296206311859)
        ·
          refine ⟨190121101339200444309467789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126747400892800296206311859 190121101339200444309467789)
          ·
            refine ⟨71295413002200166616050421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190121101339200444309467789 71295413002200166616050421)
            ·
              refine ⟨6683944968956265620254727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71295413002200166616050421 6683944968956265620254727)
              ·
                refine ⟨10025917453434398430382091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683944968956265620254727 10025917453434398430382091)
                ·
                  refine ⟨15038876180151597645573137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10025917453434398430382091 15038876180151597645573137)
                  ·
                    refine ⟨11279157135113698234179853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15038876180151597645573137 11279157135113698234179853)
                    ·
                      refine ⟨4229683925667636837817445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279157135113698234179853 4229683925667636837817445)
                      ·
                        rfl

theorem cell23_8237280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_8237280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237280 prefixEnd_8237280 := by exact prefixLift 8237280
  have htrace : WordTrace (prefixWord ++ tailWord_8237280) baseStart_8237280 baseEnd_8237280 := by
    simpa [prefixWord, tailWord_8237280, baseEnd_8237280] using wordTrace_append hprefix tailTrace_8237280
  have hstable : (prefixWord ++ tailWord_8237280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237280).length < 2 ^ (prefixWord ++ tailWord_8237280).sum := by decide
  have hdescent : baseEnd_8237280 < baseStart_8237280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237283 : List Nat := [1, 1, 1, 8, 2, 10]
def baseStart_8237283 : Nat := 118140960795 + 8237283 * 2 ^ 59
def prefixEnd_8237283 : Nat := 4983230072969 + 3 ^ 40 * 8237283 * 2
def baseEnd_8237283 : Nat := 17406113029257614510617

theorem tailTrace_8237283 : CollatzResearch.WordTrace tailWord_8237283 prefixEnd_8237283 17406113029257614510617 := by
  unfold tailWord_8237283
  simp only [CollatzResearch.WordTrace]
  refine ⟨300438393016737981779172503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200292262011158654519448335 300438393016737981779172503)
  ·
    refine ⟨450657589525106972668758755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300438393016737981779172503 450657589525106972668758755)
    ·
      refine ⟨675986384287660459003138133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450657589525106972668758755 675986384287660459003138133)
      ·
        refine ⟨7921715440871021003943025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 675986384287660459003138133 7921715440871021003943025)
        ·
          refine ⟨5941286580653265752957269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921715440871021003943025 5941286580653265752957269)
          ·
            refine ⟨17406113029257614510617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5941286580653265752957269 17406113029257614510617)
            ·
              rfl

theorem cell23_8237283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 10].length) (baseStart_8237283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237283 prefixEnd_8237283 := by exact prefixLift 8237283
  have htrace : WordTrace (prefixWord ++ tailWord_8237283) baseStart_8237283 baseEnd_8237283 := by
    simpa [prefixWord, tailWord_8237283, baseEnd_8237283] using wordTrace_append hprefix tailTrace_8237283
  have hstable : (prefixWord ++ tailWord_8237283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237283).length < 2 ^ (prefixWord ++ tailWord_8237283).sum := by decide
  have hdescent : baseEnd_8237283 < baseStart_8237283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237310 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_8237310 : Nat := 118140960795 + 8237310 * 2 ^ 59
def prefixEnd_8237310 : Nat := 4983230072969 + 3 ^ 40 * 8237310 * 2
def baseEnd_8237310 : Nat := 4229699330087271720442307

theorem tailTrace_8237310 : CollatzResearch.WordTrace tailWord_8237310 prefixEnd_8237310 4229699330087271720442307 := by
  unfold tailWord_8237310
  simp only [CollatzResearch.WordTrace]
  refine ⟨37554922223455020673800673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200292918525093443593603589 37554922223455020673800673)
  ·
    refine ⟨28166191667591265505350505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37554922223455020673800673 28166191667591265505350505)
    ·
      refine ⟨21124643750693449129012879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28166191667591265505350505 21124643750693449129012879)
      ·
        refine ⟨31686965626040173693519319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124643750693449129012879 31686965626040173693519319)
        ·
          refine ⟨47530448439060260540278979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686965626040173693519319 47530448439060260540278979)
          ·
            refine ⟨71295672658590390810418469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47530448439060260540278979 71295672658590390810418469)
            ·
              refine ⟨13367938623485698276953463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71295672658590390810418469 13367938623485698276953463)
              ·
                refine ⟨20051907935228547415430195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13367938623485698276953463 20051907935228547415430195)
                ·
                  refine ⟨30077861902842821123145293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20051907935228547415430195 30077861902842821123145293)
                  ·
                    refine ⟨11279198213566057921179485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30077861902842821123145293 11279198213566057921179485)
                    ·
                      refine ⟨4229699330087271720442307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279198213566057921179485 4229699330087271720442307)
                      ·
                        rfl

theorem cell23_8237310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_8237310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237310 prefixEnd_8237310 := by exact prefixLift 8237310
  have htrace : WordTrace (prefixWord ++ tailWord_8237310) baseStart_8237310 baseEnd_8237310 := by
    simpa [prefixWord, tailWord_8237310, baseEnd_8237310] using wordTrace_append hprefix tailTrace_8237310
  have hstable : (prefixWord ++ tailWord_8237310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237310).length < 2 ^ (prefixWord ++ tailWord_8237310).sum := by decide
  have hdescent : baseEnd_8237310 < baseStart_8237310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237320 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_8237320 : Nat := 118140960795 + 8237320 * 2 ^ 59
def prefixEnd_8237320 : Nat := 4983230072969 + 3 ^ 40 * 8237320 * 2
def baseEnd_8237320 : Nat := 4229704464893816681317261

theorem tailTrace_8237320 : CollatzResearch.WordTrace tailWord_8237320 prefixEnd_8237320 4229704464893816681317261 := by
  unfold tailWord_8237320
  simp only [CollatzResearch.WordTrace]
  refine ⟨150219871258801968549134707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200293161678402624732179609 150219871258801968549134707)
  ·
    refine ⟨225329806888202952823702061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150219871258801968549134707 225329806888202952823702061)
    ·
      refine ⟨84498677583076107308888273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225329806888202952823702061 84498677583076107308888273)
      ·
        refine ⟨63374008187307080481666205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84498677583076107308888273 63374008187307080481666205)
        ·
          refine ⟨23765253070240155180624827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63374008187307080481666205 23765253070240155180624827)
          ·
            refine ⟨35647879605360232770937241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23765253070240155180624827 35647879605360232770937241)
            ·
              refine ⟨26735909704020174578202931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35647879605360232770937241 26735909704020174578202931)
              ·
                refine ⟨40103864556030261867304397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26735909704020174578202931 40103864556030261867304397)
                ·
                  refine ⟨15038949208511348200239149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40103864556030261867304397 15038949208511348200239149)
                  ·
                    refine ⟨5639605953191755575089681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15038949208511348200239149 5639605953191755575089681)
                    ·
                      refine ⟨4229704464893816681317261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639605953191755575089681 4229704464893816681317261)
                      ·
                        rfl

theorem cell23_8237320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_8237320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237320 prefixEnd_8237320 := by exact prefixLift 8237320
  have htrace : WordTrace (prefixWord ++ tailWord_8237320) baseStart_8237320 baseEnd_8237320 := by
    simpa [prefixWord, tailWord_8237320, baseEnd_8237320] using wordTrace_append hprefix tailTrace_8237320
  have hstable : (prefixWord ++ tailWord_8237320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237320).length < 2 ^ (prefixWord ++ tailWord_8237320).sum := by decide
  have hdescent : baseEnd_8237320 < baseStart_8237320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237326 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_8237326 : Nat := 118140960795 + 8237326 * 2 ^ 59
def prefixEnd_8237326 : Nat := 4983230072969 + 3 ^ 40 * 8237326 * 2
def baseEnd_8237326 : Nat := 1409902515259247885947411

theorem tailTrace_8237326 : CollatzResearch.WordTrace tailWord_8237326 prefixEnd_8237326 1409902515259247885947411 := by
  unfold tailWord_8237326
  simp only [CollatzResearch.WordTrace]
  refine ⟨37554995169447775015373479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200293307570388133415325221 37554995169447775015373479)
  ·
    refine ⟨56332492754171662523060219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37554995169447775015373479 56332492754171662523060219)
    ·
      refine ⟨84498739131257493784590329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56332492754171662523060219 84498739131257493784590329)
      ·
        refine ⟨63374054348443120338442747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84498739131257493784590329 63374054348443120338442747)
        ·
          refine ⟨95061081522664680507664121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63374054348443120338442747 95061081522664680507664121)
          ·
            refine ⟨71295811141998510380748091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95061081522664680507664121 71295811141998510380748091)
            ·
              refine ⟨106943716712997765571122137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71295811141998510380748091 106943716712997765571122137)
              ·
                refine ⟨80207787534748324178341603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106943716712997765571122137 80207787534748324178341603)
                ·
                  refine ⟨120311681302122486267512405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80207787534748324178341603 120311681302122486267512405)
                  ·
                    refine ⟨1409902515259247885947411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120311681302122486267512405 1409902515259247885947411)
                    ·
                      rfl

theorem cell23_8237326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_8237326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237326 prefixEnd_8237326 := by exact prefixLift 8237326
  have htrace : WordTrace (prefixWord ++ tailWord_8237326) baseStart_8237326 baseEnd_8237326 := by
    simpa [prefixWord, tailWord_8237326, baseEnd_8237326] using wordTrace_append hprefix tailTrace_8237326
  have hstable : (prefixWord ++ tailWord_8237326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237326).length < 2 ^ (prefixWord ++ tailWord_8237326).sum := by decide
  have hdescent : baseEnd_8237326 < baseStart_8237326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237336 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_8237336 : Nat := 118140960795 + 8237336 * 2 ^ 59
def prefixEnd_8237336 : Nat := 4983230072969 + 3 ^ 40 * 8237336 * 2
def baseEnd_8237336 : Nat := 4229712680584288618717187

theorem tailTrace_8237336 : CollatzResearch.WordTrace tailWord_8237336 prefixEnd_8237336 4229712680584288618717187 := by
  unfold tailWord_8237336
  simp only [CollatzResearch.WordTrace]
  refine ⟨150220163042772985915425931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200293550723697314553901241 150220163042772985915425931)
  ·
    refine ⟨225330244564159478873138897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150220163042772985915425931 225330244564159478873138897)
    ·
      refine ⟨168997683423119609154854173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225330244564159478873138897 168997683423119609154854173)
      ·
        refine ⟨63374131283669853433070315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168997683423119609154854173 63374131283669853433070315)
        ·
          refine ⟨95061196925504780149605473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63374131283669853433070315 95061196925504780149605473)
          ·
            refine ⟨71295897694128585112204105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95061196925504780149605473 71295897694128585112204105)
            ·
              refine ⟨53471923270596438834153079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71295897694128585112204105 53471923270596438834153079)
              ·
                refine ⟨80207884905894658251229619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53471923270596438834153079 80207884905894658251229619)
                ·
                  refine ⟨120311827358841987376844429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80207884905894658251229619 120311827358841987376844429)
                  ·
                    refine ⟨45116935259565745266316661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120311827358841987376844429 45116935259565745266316661)
                    ·
                      refine ⟨4229712680584288618717187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45116935259565745266316661 4229712680584288618717187)
                      ·
                        rfl

theorem cell23_8237336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_8237336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237336 prefixEnd_8237336 := by exact prefixLift 8237336
  have htrace : WordTrace (prefixWord ++ tailWord_8237336) baseStart_8237336 baseEnd_8237336 := by
    simpa [prefixWord, tailWord_8237336, baseEnd_8237336] using wordTrace_append hprefix tailTrace_8237336
  have hstable : (prefixWord ++ tailWord_8237336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237336).length < 2 ^ (prefixWord ++ tailWord_8237336).sum := by decide
  have hdescent : baseEnd_8237336 < baseStart_8237336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237356 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 7]
def baseStart_8237356 : Nat := 118140960795 + 8237356 * 2 ^ 59
def prefixEnd_8237356 : Nat := 4983230072969 + 3 ^ 40 * 8237356 * 2
def baseEnd_8237356 : Nat := 469969216688597615607455

theorem tailTrace_8237356 : CollatzResearch.WordTrace tailWord_8237356 prefixEnd_8237356 469969216688597615607455 := by
  unfold tailWord_8237356
  simp only [CollatzResearch.WordTrace]
  refine ⟨150220527772736757623289961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200294037030315676831053281 150220527772736757623289961)
  ·
    refine ⟨112665395829552568217467471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150220527772736757623289961 112665395829552568217467471)
    ·
      refine ⟨168998093744328852326201207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112665395829552568217467471 168998093744328852326201207)
      ·
        refine ⟨253497140616493278489301811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168998093744328852326201207 253497140616493278489301811)
        ·
          refine ⟨380245710924739917733952717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253497140616493278489301811 380245710924739917733952717)
          ·
            refine ⟨142592141596777469150232269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380245710924739917733952717 142592141596777469150232269)
            ·
              refine ⟨53472053098791550931337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142592141596777469150232269 53472053098791550931337101)
              ·
                refine ⟨20052019912046831599251413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53472053098791550931337101 20052019912046831599251413)
                ·
                  refine ⟨469969216688597615607455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20052019912046831599251413 469969216688597615607455)
                  ·
                    rfl

theorem cell23_8237356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_8237356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237356 prefixEnd_8237356 := by exact prefixLift 8237356
  have htrace : WordTrace (prefixWord ++ tailWord_8237356) baseStart_8237356 baseEnd_8237356 := by
    simpa [prefixWord, tailWord_8237356, baseEnd_8237356] using wordTrace_append hprefix tailTrace_8237356
  have hstable : (prefixWord ++ tailWord_8237356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237356).length < 2 ^ (prefixWord ++ tailWord_8237356).sum := by decide
  have hdescent : baseEnd_8237356 < baseStart_8237356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237413 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_8237413 : Nat := 118140960795 + 8237413 * 2 ^ 59
def prefixEnd_8237413 : Nat := 4983230072969 + 3 ^ 40 * 8237413 * 2
def baseEnd_8237413 : Nat := 4229752218594684817454333

theorem tailTrace_8237413 : CollatzResearch.WordTrace tailWord_8237413 prefixEnd_8237413 4229752218594684817454333 := by
  unfold tailWord_8237413
  simp only [CollatzResearch.WordTrace]
  refine ⟨300443134506267013981404893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200295423004178009320936595 300443134506267013981404893)
  ·
    refine ⟨112666175439850130243026835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300443134506267013981404893 112666175439850130243026835)
    ·
      refine ⟨168999263159775195364540253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112666175439850130243026835 168999263159775195364540253)
      ·
        refine ⟨63374723684915698261702595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168999263159775195364540253 63374723684915698261702595)
        ·
          refine ⟨95062085527373547392553893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63374723684915698261702595 95062085527373547392553893)
          ·
            refine ⟨17824141036382540136103855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95062085527373547392553893 17824141036382540136103855)
            ·
              refine ⟨26736211554573810204155783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824141036382540136103855 26736211554573810204155783)
              ·
                refine ⟨40104317331860715306233675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26736211554573810204155783 40104317331860715306233675)
                ·
                  refine ⟨60156475997791072959350513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40104317331860715306233675 60156475997791072959350513)
                  ·
                    refine ⟨45117356998343304719512885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60156475997791072959350513 45117356998343304719512885)
                    ·
                      refine ⟨4229752218594684817454333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45117356998343304719512885 4229752218594684817454333)
                      ·
                        rfl

theorem cell23_8237413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_8237413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237413 prefixEnd_8237413 := by exact prefixLift 8237413
  have htrace : WordTrace (prefixWord ++ tailWord_8237413) baseStart_8237413 baseEnd_8237413 := by
    simpa [prefixWord, tailWord_8237413, baseEnd_8237413] using wordTrace_append hprefix tailTrace_8237413
  have hstable : (prefixWord ++ tailWord_8237413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237413).length < 2 ^ (prefixWord ++ tailWord_8237413).sum := by decide
  have hdescent : baseEnd_8237413 < baseStart_8237413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237433 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_8237433 : Nat := 118140960795 + 8237433 * 2 ^ 59
def prefixEnd_8237433 : Nat := 4983230072969 + 3 ^ 40 * 8237433 * 2
def baseEnd_8237433 : Nat := 1409920829402591579734747

theorem tailTrace_8237433 : CollatzResearch.WordTrace tailWord_8237433 prefixEnd_8237433 1409920829402591579734747 := by
  unfold tailWord_8237433
  simp only [CollatzResearch.WordTrace]
  refine ⟨300443863966194557397132953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200295909310796371598088635 300443863966194557397132953)
  ·
    refine ⟨225332897974645918047849715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300443863966194557397132953 225332897974645918047849715)
    ·
      refine ⟨337999346961968877071774573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225332897974645918047849715 337999346961968877071774573)
      ·
        refine ⟨126749755110738328901915465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337999346961968877071774573 126749755110738328901915465)
        ·
          refine ⟨95062316333053746676436599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126749755110738328901915465 95062316333053746676436599)
          ·
            refine ⟨142593474499580620014654899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95062316333053746676436599 142593474499580620014654899)
            ·
              refine ⟨213890211749370930021982349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142593474499580620014654899 213890211749370930021982349)
              ·
                refine ⟨80208829406014098758243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213890211749370930021982349 80208829406014098758243381)
                ·
                  refine ⟨7519577756813821758585317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80208829406014098758243381 7519577756813821758585317)
                  ·
                    refine ⟨1409920829402591579734747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519577756813821758585317 1409920829402591579734747)
                    ·
                      rfl

theorem cell23_8237433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_8237433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237433 prefixEnd_8237433 := by exact prefixLift 8237433
  have htrace : WordTrace (prefixWord ++ tailWord_8237433) baseStart_8237433 baseEnd_8237433 := by
    simpa [prefixWord, tailWord_8237433, baseEnd_8237433] using wordTrace_append hprefix tailTrace_8237433
  have hstable : (prefixWord ++ tailWord_8237433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237433).length < 2 ^ (prefixWord ++ tailWord_8237433).sum := by decide
  have hdescent : baseEnd_8237433 < baseStart_8237433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237456 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_8237456 : Nat := 118140960795 + 8237456 * 2 ^ 59
def prefixEnd_8237456 : Nat := 4983230072969 + 3 ^ 40 * 8237456 * 2
def baseEnd_8237456 : Nat := 4229774298262828149216635

theorem tailTrace_8237456 : CollatzResearch.WordTrace tailWord_8237456 prefixEnd_8237456 4229774298262828149216635 := by
  unfold tailWord_8237456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150222351422555616162610111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200296468563407488216813481 150222351422555616162610111)
  ·
    refine ⟨225333527133833424243915167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150222351422555616162610111 225333527133833424243915167)
    ·
      refine ⟨338000290700750136365872751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225333527133833424243915167 338000290700750136365872751)
      ·
        refine ⟨507000436051125204548809127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338000290700750136365872751 507000436051125204548809127)
        ·
          refine ⟨760500654076687806823213691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507000436051125204548809127 760500654076687806823213691)
          ·
            refine ⟨1140750981115031710234820537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760500654076687806823213691 1140750981115031710234820537)
            ·
              refine ⟨855563235836273782676115403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140750981115031710234820537 855563235836273782676115403)
              ·
                refine ⟨1283344853754410674014173105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855563235836273782676115403 1283344853754410674014173105)
                ·
                  refine ⟨962508640315808005510629829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1283344853754410674014173105 962508640315808005510629829)
                  ·
                    refine ⟨180470370059214001033243093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962508640315808005510629829 180470370059214001033243093)
                    ·
                      refine ⟨4229774298262828149216635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180470370059214001033243093 4229774298262828149216635)
                      ·
                        rfl

theorem cell23_8237456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_8237456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237456 prefixEnd_8237456 := by exact prefixLift 8237456
  have htrace : WordTrace (prefixWord ++ tailWord_8237456) baseStart_8237456 baseEnd_8237456 := by
    simpa [prefixWord, tailWord_8237456, baseEnd_8237456] using wordTrace_append hprefix tailTrace_8237456
  have hstable : (prefixWord ++ tailWord_8237456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237456).length < 2 ^ (prefixWord ++ tailWord_8237456).sum := by decide
  have hdescent : baseEnd_8237456 < baseStart_8237456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237463 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 6]
def baseStart_8237463 : Nat := 118140960795 + 8237463 * 2 ^ 59
def prefixEnd_8237463 : Nat := 4983230072969 + 3 ^ 40 * 8237463 * 2
def baseEnd_8237463 : Nat := 469975321403045513536567

theorem tailTrace_8237463 : CollatzResearch.WordTrace tailWord_8237463 prefixEnd_8237463 469975321403045513536567 := by
  unfold tailWord_8237463
  simp only [CollatzResearch.WordTrace]
  refine ⟨300444958156085872520725043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200296638770723915013816695 300444958156085872520725043)
  ·
    refine ⟨450667437234128808781087565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300444958156085872520725043 450667437234128808781087565)
    ·
      refine ⟨169000288962798303292907837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450667437234128808781087565 169000288962798303292907837)
      ·
        refine ⟨63375108361049363734840439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169000288962798303292907837 63375108361049363734840439)
        ·
          refine ⟨95062662541574045602260659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63375108361049363734840439 95062662541574045602260659)
          ·
            refine ⟨142593993812361068403390989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95062662541574045602260659 142593993812361068403390989)
            ·
              refine ⟨53472747679635400651271621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142593993812361068403390989 53472747679635400651271621)
              ·
                refine ⟨10026140189931637622113429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53472747679635400651271621 10026140189931637622113429)
                ·
                  refine ⟨469975321403045513536567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10026140189931637622113429 469975321403045513536567)
                  ·
                    rfl

theorem cell23_8237463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 6].length) (baseStart_8237463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237463 prefixEnd_8237463 := by exact prefixLift 8237463
  have htrace : WordTrace (prefixWord ++ tailWord_8237463) baseStart_8237463 baseEnd_8237463 := by
    simpa [prefixWord, tailWord_8237463, baseEnd_8237463] using wordTrace_append hprefix tailTrace_8237463
  have hstable : (prefixWord ++ tailWord_8237463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237463).length < 2 ^ (prefixWord ++ tailWord_8237463).sum := by decide
  have hdescent : baseEnd_8237463 < baseStart_8237463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237524 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_8237524 : Nat := 118140960795 + 8237524 * 2 ^ 59
def prefixEnd_8237524 : Nat := 4983230072969 + 3 ^ 40 * 8237524 * 2
def baseEnd_8237524 : Nat := 4229809214947333883166323

theorem tailTrace_8237524 : CollatzResearch.WordTrace tailWord_8237524 prefixEnd_8237524 4229809214947333883166323 := by
  unfold tailWord_8237524
  simp only [CollatzResearch.WordTrace]
  refine ⟨150223591504432439969347813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200298122005909919959130417 150223591504432439969347813)
  ·
    refine ⟨28166923407081082494252715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150223591504432439969347813 28166923407081082494252715)
    ·
      refine ⟨42250385110621623741379073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28166923407081082494252715 42250385110621623741379073)
      ·
        refine ⟨31687788832966217806034305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42250385110621623741379073 31687788832966217806034305)
        ·
          refine ⟨23765841624724663354525729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31687788832966217806034305 23765841624724663354525729)
          ·
            refine ⟨17824381218543497515894297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23765841624724663354525729 17824381218543497515894297)
            ·
              refine ⟨13368285913907623136920723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17824381218543497515894297 13368285913907623136920723)
              ·
                refine ⟨20052428870861434705381085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13368285913907623136920723 20052428870861434705381085)
                ·
                  refine ⟨7519660826573038014517907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20052428870861434705381085 7519660826573038014517907)
                  ·
                    refine ⟨11279491239859557021776861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7519660826573038014517907 11279491239859557021776861)
                    ·
                      refine ⟨4229809214947333883166323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279491239859557021776861 4229809214947333883166323)
                      ·
                        rfl

theorem cell23_8237524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_8237524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237524 prefixEnd_8237524 := by exact prefixLift 8237524
  have htrace : WordTrace (prefixWord ++ tailWord_8237524) baseStart_8237524 baseEnd_8237524 := by
    simpa [prefixWord, tailWord_8237524, baseEnd_8237524] using wordTrace_append hprefix tailTrace_8237524
  have hstable : (prefixWord ++ tailWord_8237524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237524).length < 2 ^ (prefixWord ++ tailWord_8237524).sum := by decide
  have hdescent : baseEnd_8237524 < baseStart_8237524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237547 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 3, 2, 2]
def baseStart_8237547 : Nat := 118140960795 + 8237547 * 2 ^ 59
def prefixEnd_8237547 : Nat := 4983230072969 + 3 ^ 40 * 8237547 * 2
def baseEnd_8237547 : Nat := 4229821025002387293178717

theorem tailTrace_8237547 : CollatzResearch.WordTrace tailWord_8237547 prefixEnd_8237547 4229821025002387293178717 := by
  unfold tailWord_8237547
  simp only [CollatzResearch.WordTrace]
  refine ⟨300448021887781554866782895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200298681258521036577855263 300448021887781554866782895)
  ·
    refine ⟨450672032831672332300174343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300448021887781554866782895 450672032831672332300174343)
    ·
      refine ⟨676008049247508498450261515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450672032831672332300174343 676008049247508498450261515)
      ·
        refine ⟨1014012073871262747675392273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676008049247508498450261515 1014012073871262747675392273)
        ·
          refine ⟨760509055403447060756544205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014012073871262747675392273 760509055403447060756544205)
          ·
            refine ⟨285190895776292647783704077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760509055403447060756544205 285190895776292647783704077)
            ·
              refine ⟨106946585916109742918889029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285190895776292647783704077 106946585916109742918889029)
              ·
                refine ⟨20052484859270576797291693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106946585916109742918889029 20052484859270576797291693)
                ·
                  refine ⟨7519681822226466298984385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20052484859270576797291693 7519681822226466298984385)
                  ·
                    refine ⟨5639761366669849724238289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7519681822226466298984385 5639761366669849724238289)
                    ·
                      refine ⟨4229821025002387293178717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639761366669849724238289 4229821025002387293178717)
                      ·
                        rfl

theorem cell23_8237547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2, 2].length) (baseStart_8237547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237547 prefixEnd_8237547 := by exact prefixLift 8237547
  have htrace : WordTrace (prefixWord ++ tailWord_8237547) baseStart_8237547 baseEnd_8237547 := by
    simpa [prefixWord, tailWord_8237547, baseEnd_8237547] using wordTrace_append hprefix tailTrace_8237547
  have hstable : (prefixWord ++ tailWord_8237547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237547).length < 2 ^ (prefixWord ++ tailWord_8237547).sum := by decide
  have hdescent : baseEnd_8237547 < baseStart_8237547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237553 : List Nat := [1, 2, 2, 2, 3, 1, 3, 9]
def baseStart_8237553 : Nat := 118140960795 + 8237553 * 2 ^ 59
def prefixEnd_8237553 : Nat := 4983230072969 + 3 ^ 40 * 8237553 * 2
def baseEnd_8237553 : Nat := 156660152069863491470507

theorem tailTrace_8237553 : CollatzResearch.WordTrace tailWord_8237553 prefixEnd_8237553 156660152069863491470507 := by
  unfold tailWord_8237553
  simp only [CollatzResearch.WordTrace]
  refine ⟨300448240725759817891501313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200298827150506545261000875 300448240725759817891501313)
  ·
    refine ⟨225336180544319863418625985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300448240725759817891501313 225336180544319863418625985)
    ·
      refine ⟨169002135408239897563969489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225336180544319863418625985 169002135408239897563969489)
      ·
        refine ⟨126751601556179923172977117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169002135408239897563969489 126751601556179923172977117)
        ·
          refine ⟨47531850583567471189866419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126751601556179923172977117 47531850583567471189866419)
          ·
            refine ⟨71297775875351206784799629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47531850583567471189866419 71297775875351206784799629)
            ·
              refine ⟨26736665953256702544299861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71297775875351206784799629 26736665953256702544299861)
              ·
                refine ⟨156660152069863491470507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26736665953256702544299861 156660152069863491470507)
                ·
                  rfl

theorem cell23_8237553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 9].length) (baseStart_8237553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237553 prefixEnd_8237553 := by exact prefixLift 8237553
  have htrace : WordTrace (prefixWord ++ tailWord_8237553) baseStart_8237553 baseEnd_8237553 := by
    simpa [prefixWord, tailWord_8237553, baseEnd_8237553] using wordTrace_append hprefix tailTrace_8237553
  have hstable : (prefixWord ++ tailWord_8237553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237553).length < 2 ^ (prefixWord ++ tailWord_8237553).sum := by decide
  have hdescent : baseEnd_8237553 < baseStart_8237553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237593 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_8237593 : Nat := 118140960795 + 8237593 * 2 ^ 59
def prefixEnd_8237593 : Nat := 4983230072969 + 3 ^ 40 * 8237593 * 2
def baseEnd_8237593 : Nat := 4229844645112494113203505

theorem tailTrace_8237593 : CollatzResearch.WordTrace tailWord_8237593 prefixEnd_8237593 4229844645112494113203505 := by
  unfold tailWord_8237593
  simp only [CollatzResearch.WordTrace]
  refine ⟨300449699645614904722957433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200299799763743269815304955 300449699645614904722957433)
  ·
    refine ⟨225337274734211178542218075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300449699645614904722957433 225337274734211178542218075)
    ·
      refine ⟨338005912101316767813327113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225337274734211178542218075 338005912101316767813327113)
      ·
        refine ⟨253504434075987575859995335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338005912101316767813327113 253504434075987575859995335)
        ·
          refine ⟨380256651113981363789993003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253504434075987575859995335 380256651113981363789993003)
          ·
            refine ⟨570384976670972045684989505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380256651113981363789993003 570384976670972045684989505)
            ·
              refine ⟨427788732503229034263742129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570384976670972045684989505 427788732503229034263742129)
              ·
                refine ⟨320841549377421775697806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427788732503229034263742129 320841549377421775697806597)
                ·
                  refine ⟨60157790508266582943338737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320841549377421775697806597 60157790508266582943338737)
                  ·
                    refine ⟨45118342881199937207504053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60157790508266582943338737 45118342881199937207504053)
                    ·
                      refine ⟨4229844645112494113203505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45118342881199937207504053 4229844645112494113203505)
                      ·
                        rfl

theorem cell23_8237593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_8237593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237593 prefixEnd_8237593 := by exact prefixLift 8237593
  have htrace : WordTrace (prefixWord ++ tailWord_8237593) baseStart_8237593 baseEnd_8237593 := by
    simpa [prefixWord, tailWord_8237593, baseEnd_8237593] using wordTrace_append hprefix tailTrace_8237593
  have hstable : (prefixWord ++ tailWord_8237593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237593).length < 2 ^ (prefixWord ++ tailWord_8237593).sum := by decide
  have hdescent : baseEnd_8237593 < baseStart_8237593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237614 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_8237614 : Nat := 118140960795 + 8237614 * 2 ^ 59
def prefixEnd_8237614 : Nat := 4983230072969 + 3 ^ 40 * 8237614 * 2
def baseEnd_8237614 : Nat := 4229855428206238531040909

theorem tailTrace_8237614 : CollatzResearch.WordTrace tailWord_8237614 prefixEnd_8237614 4229855428206238531040909 := by
  unfold tailWord_8237614
  simp only [CollatzResearch.WordTrace]
  refine ⟨37556308197317353163683987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200300310385692550206314597 37556308197317353163683987)
  ·
    refine ⟨56334462295976029745525981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37556308197317353163683987 56334462295976029745525981)
    ·
      refine ⟨21125423360991011154572243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56334462295976029745525981 21125423360991011154572243)
      ·
        refine ⟨31688135041486516731858365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21125423360991011154572243 31688135041486516731858365)
        ·
          refine ⟨11883050640557443774446887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31688135041486516731858365 11883050640557443774446887)
          ·
            refine ⟨17824575960836165661670331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11883050640557443774446887 17824575960836165661670331)
            ·
              refine ⟨26736863941254248492505497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824575960836165661670331 26736863941254248492505497)
              ·
                refine ⟨20052647955940686369379123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26736863941254248492505497 20052647955940686369379123)
                ·
                  refine ⟨30078971933911029554068685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20052647955940686369379123 30078971933911029554068685)
                  ·
                    refine ⟨11279614475216636082775757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30078971933911029554068685 11279614475216636082775757)
                    ·
                      refine ⟨4229855428206238531040909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279614475216636082775757 4229855428206238531040909)
                      ·
                        rfl

theorem cell23_8237614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_8237614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237614 prefixEnd_8237614 := by exact prefixLift 8237614
  have htrace : WordTrace (prefixWord ++ tailWord_8237614) baseStart_8237614 baseEnd_8237614 := by
    simpa [prefixWord, tailWord_8237614, baseEnd_8237614] using wordTrace_append hprefix tailTrace_8237614
  have hstable : (prefixWord ++ tailWord_8237614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237614).length < 2 ^ (prefixWord ++ tailWord_8237614).sum := by decide
  have hdescent : baseEnd_8237614 < baseStart_8237614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237720 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_8237720 : Nat := 118140960795 + 8237720 * 2 ^ 59
def prefixEnd_8237720 : Nat := 4983230072969 + 3 ^ 40 * 8237720 * 2
def baseEnd_8237720 : Nat := 1409969952385205038771807

theorem tailTrace_8237720 : CollatzResearch.WordTrace tailWord_8237720 prefixEnd_8237720 1409969952385205038771807 := by
  unfold tailWord_8237720
  simp only [CollatzResearch.WordTrace]
  refine ⟨150227165858077402706415307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200302887810769870275220409 150227165858077402706415307)
  ·
    refine ⟨225340748787116104059622961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150227165858077402706415307 225340748787116104059622961)
    ·
      refine ⟨169005561590337078044717221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225340748787116104059622961 169005561590337078044717221)
      ·
        refine ⟨31688542798188202133384479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169005561590337078044717221 31688542798188202133384479)
        ·
          refine ⟨47532814197282303200076719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31688542798188202133384479 47532814197282303200076719)
          ·
            refine ⟨71299221295923454800115079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47532814197282303200076719 71299221295923454800115079)
            ·
              refine ⟨106948831943885182200172619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71299221295923454800115079 106948831943885182200172619)
              ·
                refine ⟨160423247915827773300258929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106948831943885182200172619 160423247915827773300258929)
                ·
                  refine ⟨120317435936870829975194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160423247915827773300258929 120317435936870829975194197)
                  ·
                    refine ⟨1409969952385205038771807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120317435936870829975194197 1409969952385205038771807)
                    ·
                      rfl

theorem cell23_8237720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_8237720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237720 prefixEnd_8237720 := by exact prefixLift 8237720
  have htrace : WordTrace (prefixWord ++ tailWord_8237720) baseStart_8237720 baseEnd_8237720 := by
    simpa [prefixWord, tailWord_8237720, baseEnd_8237720] using wordTrace_append hprefix tailTrace_8237720
  have hstable : (prefixWord ++ tailWord_8237720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237720).length < 2 ^ (prefixWord ++ tailWord_8237720).sum := by decide
  have hdescent : baseEnd_8237720 < baseStart_8237720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237747 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3]
def baseStart_8237747 : Nat := 118140960795 + 8237747 * 2 ^ 59
def prefixEnd_8237747 : Nat := 4983230072969 + 3 ^ 40 * 8237747 * 2
def baseEnd_8237747 : Nat := 4229923721133286510677797

theorem tailTrace_8237747 : CollatzResearch.WordTrace tailWord_8237747 prefixEnd_8237747 4229923721133286510677797 := by
  unfold tailWord_8237747
  simp only [CollatzResearch.WordTrace]
  refine ⟨300455316487056989024063495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200303544324704659349375663 300455316487056989024063495)
  ·
    refine ⟨450682974730585483536095243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300455316487056989024063495 450682974730585483536095243)
    ·
      refine ⟨676024462095878225304142865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450682974730585483536095243 676024462095878225304142865)
      ·
        refine ⟨507018346571908668978107149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676024462095878225304142865 507018346571908668978107149)
        ·
          refine ⟨190131879964465750866790181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507018346571908668978107149 190131879964465750866790181)
          ·
            refine ⟨35649727493337328287523159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190131879964465750866790181 35649727493337328287523159)
            ·
              refine ⟨53474591240005992431284739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35649727493337328287523159 53474591240005992431284739)
              ·
                refine ⟨80211886860008988646927109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53474591240005992431284739 80211886860008988646927109)
                ·
                  refine ⟨15039728786251685371298833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80211886860008988646927109 15039728786251685371298833)
                  ·
                    refine ⟨11279796589688764028474125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15039728786251685371298833 11279796589688764028474125)
                    ·
                      refine ⟨4229923721133286510677797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279796589688764028474125 4229923721133286510677797)
                      ·
                        rfl

theorem cell23_8237747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_8237747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237747 prefixEnd_8237747 := by exact prefixLift 8237747
  have htrace : WordTrace (prefixWord ++ tailWord_8237747) baseStart_8237747 baseEnd_8237747 := by
    simpa [prefixWord, tailWord_8237747, baseEnd_8237747] using wordTrace_append hprefix tailTrace_8237747
  have hstable : (prefixWord ++ tailWord_8237747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237747).length < 2 ^ (prefixWord ++ tailWord_8237747).sum := by decide
  have hdescent : baseEnd_8237747 < baseStart_8237747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237827 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 6, 4]
def baseStart_8237827 : Nat := 118140960795 + 8237827 * 2 ^ 59
def prefixEnd_8237827 : Nat := 4983230072969 + 3 ^ 40 * 8237827 * 2
def baseEnd_8237827 : Nat := 1409988266528548732559143

theorem tailTrace_8237827 : CollatzResearch.WordTrace tailWord_8237827 prefixEnd_8237827 1409988266528548732559143 := by
  unfold tailWord_8237827
  simp only [CollatzResearch.WordTrace]
  refine ⟨300458234326767162686975735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200305489551178108457983823 300458234326767162686975735)
  ·
    refine ⟨450687351490150744030463603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300458234326767162686975735 450687351490150744030463603)
    ·
      refine ⟨676031027235226116045695405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450687351490150744030463603 676031027235226116045695405)
      ·
        refine ⟨253511635213209793517135777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676031027235226116045695405 253511635213209793517135777)
        ·
          refine ⟨190133726409907345137851833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253511635213209793517135777 190133726409907345137851833)
          ·
            refine ⟨142600294807430508853388875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190133726409907345137851833 142600294807430508853388875)
            ·
              refine ⟨213900442211145763280083313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142600294807430508853388875 213900442211145763280083313)
              ·
                refine ⟨160425331658359322460062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213900442211145763280083313 160425331658359322460062485)
                ·
                  refine ⟨7519937421485593240315429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160425331658359322460062485 7519937421485593240315429)
                  ·
                    refine ⟨1409988266528548732559143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7519937421485593240315429 1409988266528548732559143)
                    ·
                      rfl

theorem cell23_8237827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 4].length) (baseStart_8237827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237827 prefixEnd_8237827 := by exact prefixLift 8237827
  have htrace : WordTrace (prefixWord ++ tailWord_8237827) baseStart_8237827 baseEnd_8237827 := by
    simpa [prefixWord, tailWord_8237827, baseEnd_8237827] using wordTrace_append hprefix tailTrace_8237827
  have hstable : (prefixWord ++ tailWord_8237827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237827).length < 2 ^ (prefixWord ++ tailWord_8237827).sum := by decide
  have hdescent : baseEnd_8237827 < baseStart_8237827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237834 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_8237834 : Nat := 118140960795 + 8237834 * 2 ^ 59
def prefixEnd_8237834 : Nat := 4983230072969 + 3 ^ 40 * 8237834 * 2
def baseEnd_8237834 : Nat := 4229968393950227670289897

theorem tailTrace_8237834 : CollatzResearch.WordTrace tailWord_8237834 prefixEnd_8237834 4229968393950227670289897 := by
  unfold tailWord_8237834
  simp only [CollatzResearch.WordTrace]
  refine ⟨75114622409435450720620139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200305659758494535254987037 75114622409435450720620139)
  ·
    refine ⟨112671933614153176080930209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75114622409435450720620139 112671933614153176080930209)
    ·
      refine ⟨84503950210614882060697657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112671933614153176080930209 84503950210614882060697657)
      ·
        refine ⟨63377962657961161545523243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84503950210614882060697657 63377962657961161545523243)
        ·
          refine ⟨95066943986941742318284865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63377962657961161545523243 95066943986941742318284865)
          ·
            refine ⟨71300207990206306738713649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95066943986941742318284865 71300207990206306738713649)
            ·
              refine ⟨53475155992654730054035237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71300207990206306738713649 53475155992654730054035237)
              ·
                refine ⟨10026591748622761885131607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53475155992654730054035237 10026591748622761885131607)
                ·
                  refine ⟨15039887622934142827697411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10026591748622761885131607 15039887622934142827697411)
                  ·
                    refine ⟨22559831434401214241546117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15039887622934142827697411 22559831434401214241546117)
                    ·
                      refine ⟨4229968393950227670289897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22559831434401214241546117 4229968393950227670289897)
                      ·
                        rfl

theorem cell23_8237834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_8237834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237834 prefixEnd_8237834 := by exact prefixLift 8237834
  have htrace : WordTrace (prefixWord ++ tailWord_8237834) baseStart_8237834 baseEnd_8237834 := by
    simpa [prefixWord, tailWord_8237834, baseEnd_8237834] using wordTrace_append hprefix tailTrace_8237834
  have hstable : (prefixWord ++ tailWord_8237834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237834).length < 2 ^ (prefixWord ++ tailWord_8237834).sum := by decide
  have hdescent : baseEnd_8237834 < baseStart_8237834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3]
def baseStart_8237867 : Nat := 118140960795 + 8237867 * 2 ^ 59
def prefixEnd_8237867 : Nat := 4983230072969 + 3 ^ 40 * 8237867 * 2
def baseEnd_8237867 : Nat := 4229985338811826041177245

theorem tailTrace_8237867 : CollatzResearch.WordTrace tailWord_8237867 prefixEnd_8237867 4229985338811826041177245 := by
  unfold tailWord_8237867
  simp only [CollatzResearch.WordTrace]
  refine ⟨300459693246622249518431855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200306462164414833012287903 300459693246622249518431855)
  ·
    refine ⟨450689539869933374277647783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300459693246622249518431855 450689539869933374277647783)
    ·
      refine ⟨676034309804900061416471675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450689539869933374277647783 676034309804900061416471675)
      ·
        refine ⟨1014051464707350092124707513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676034309804900061416471675 1014051464707350092124707513)
        ·
          refine ⟨760538598530512569093530635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014051464707350092124707513 760538598530512569093530635)
          ·
            refine ⟨1140807897795768853640295953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760538598530512569093530635 1140807897795768853640295953)
            ·
              refine ⟨855605923346826640230221965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140807897795768853640295953 855605923346826640230221965)
              ·
                refine ⟨320852221255059990086333237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855605923346826640230221965 320852221255059990086333237)
                ·
                  refine ⟨30079895742661874070593741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320852221255059990086333237 30079895742661874070593741)
                  ·
                    refine ⟨11279960903498202776472653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30079895742661874070593741 11279960903498202776472653)
                    ·
                      refine ⟨4229985338811826041177245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11279960903498202776472653 4229985338811826041177245)
                      ·
                        rfl

theorem cell23_8237867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].length) (baseStart_8237867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237867 prefixEnd_8237867 := by exact prefixLift 8237867
  have htrace : WordTrace (prefixWord ++ tailWord_8237867) baseStart_8237867 baseEnd_8237867 := by
    simpa [prefixWord, tailWord_8237867, baseEnd_8237867] using wordTrace_append hprefix tailTrace_8237867
  have hstable : (prefixWord ++ tailWord_8237867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237867).length < 2 ^ (prefixWord ++ tailWord_8237867).sum := by decide
  have hdescent : baseEnd_8237867 < baseStart_8237867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237868 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_8237868 : Nat := 118140960795 + 8237868 * 2 ^ 59
def prefixEnd_8237868 : Nat := 4983230072969 + 3 ^ 40 * 8237868 * 2
def baseEnd_8237868 : Nat := 4229985852292480537264741

theorem tailTrace_8237868 : CollatzResearch.WordTrace tailWord_8237868 prefixEnd_8237868 4229985852292480537264741 := by
  unfold tailWord_8237868
  simp only [CollatzResearch.WordTrace]
  refine ⟨150229864859809313344609129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200306486479745751126145505 150229864859809313344609129)
  ·
    refine ⟨112672398644856985008456847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150229864859809313344609129 112672398644856985008456847)
    ·
      refine ⟨169008597967285477512685271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112672398644856985008456847 169008597967285477512685271)
      ·
        refine ⟨253512896950928216269027907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169008597967285477512685271 253512896950928216269027907)
        ·
          refine ⟨380269345426392324403541861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253512896950928216269027907 380269345426392324403541861)
          ·
            refine ⟨71300502267448560825664099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380269345426392324403541861 71300502267448560825664099)
            ·
              refine ⟨106950753401172841238496149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71300502267448560825664099 106950753401172841238496149)
              ·
                refine ⟨5013316565679976933054507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106950753401172841238496149 5013316565679976933054507)
                ·
                  refine ⟨7519974848519965399581761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013316565679976933054507 7519974848519965399581761)
                  ·
                    refine ⟨5639981136389974049686321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7519974848519965399581761 5639981136389974049686321)
                    ·
                      refine ⟨4229985852292480537264741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5639981136389974049686321 4229985852292480537264741)
                      ·
                        rfl

theorem cell23_8237868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_8237868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237868 prefixEnd_8237868 := by exact prefixLift 8237868
  have htrace : WordTrace (prefixWord ++ tailWord_8237868) baseStart_8237868 baseEnd_8237868 := by
    simpa [prefixWord, tailWord_8237868, baseEnd_8237868] using wordTrace_append hprefix tailTrace_8237868
  have hstable : (prefixWord ++ tailWord_8237868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237868).length < 2 ^ (prefixWord ++ tailWord_8237868).sum := by decide
  have hdescent : baseEnd_8237868 < baseStart_8237868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237878 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_8237878 : Nat := 118140960795 + 8237878 * 2 ^ 59
def prefixEnd_8237878 : Nat := 4983230072969 + 3 ^ 40 * 8237878 * 2
def baseEnd_8237878 : Nat := 1409996995699675166046565

theorem tailTrace_8237878 : CollatzResearch.WordTrace tailWord_8237878 prefixEnd_8237878 1409996995699675166046565 := by
  unfold tailWord_8237878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778755903098899899817643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200306729633054932264721525 18778755903098899899817643)
  ·
    refine ⟨28168133854648349849726465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18778755903098899899817643 28168133854648349849726465)
    ·
      refine ⟨21126100390986262387294849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28168133854648349849726465 21126100390986262387294849)
      ·
        refine ⟨15844575293239696790471137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21126100390986262387294849 15844575293239696790471137)
        ·
          refine ⟨11883431469929772592853353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15844575293239696790471137 11883431469929772592853353)
          ·
            refine ⟨8912573602447329444640015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11883431469929772592853353 8912573602447329444640015)
            ·
              refine ⟨13368860403670994166960023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912573602447329444640015 13368860403670994166960023)
              ·
                refine ⟨20053290605506491250440035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13368860403670994166960023 20053290605506491250440035)
                ·
                  refine ⟨30079935908259736875660053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20053290605506491250440035 30079935908259736875660053)
                  ·
                    refine ⟨1409996995699675166046565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30079935908259736875660053 1409996995699675166046565)
                    ·
                      rfl

theorem cell23_8237878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_8237878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237878 prefixEnd_8237878 := by exact prefixLift 8237878
  have htrace : WordTrace (prefixWord ++ tailWord_8237878) baseStart_8237878 baseEnd_8237878 := by
    simpa [prefixWord, tailWord_8237878, baseEnd_8237878] using wordTrace_append hprefix tailTrace_8237878
  have hstable : (prefixWord ++ tailWord_8237878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237878).length < 2 ^ (prefixWord ++ tailWord_8237878).sum := by decide
  have hdescent : baseEnd_8237878 < baseStart_8237878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237897 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_8237897 : Nat := 118140960795 + 8237897 * 2 ^ 59
def prefixEnd_8237897 : Nat := 4983230072969 + 3 ^ 40 * 8237897 * 2
def baseEnd_8237897 : Nat := 4230000743231460923802107

theorem tailTrace_8237897 : CollatzResearch.WordTrace tailWord_8237897 prefixEnd_8237897 4230000743231460923802107 := by
  unfold tailWord_8237897
  simp only [CollatzResearch.WordTrace]
  refine ⟨300460787436513564642023945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200307191624342376428015963 300460787436513564642023945)
  ·
    refine ⟨225345590577385173481517959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300460787436513564642023945 225345590577385173481517959)
    ·
      refine ⟨338018385866077760222276939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225345590577385173481517959 338018385866077760222276939)
      ·
        refine ⟨507027578799116640333415409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338018385866077760222276939 507027578799116640333415409)
        ·
          refine ⟨380270684099337480250061557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507027578799116640333415409 380270684099337480250061557)
          ·
            refine ⟨35650376634312888773443271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380270684099337480250061557 35650376634312888773443271)
            ·
              refine ⟨53475564951469333160164907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35650376634312888773443271 53475564951469333160164907)
              ·
                refine ⟨80213347427203999740247361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53475564951469333160164907 80213347427203999740247361)
                ·
                  refine ⟨60160010570402999805185521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80213347427203999740247361 60160010570402999805185521)
                  ·
                    refine ⟨45120007927802249853889141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60160010570402999805185521 45120007927802249853889141)
                    ·
                      refine ⟨4230000743231460923802107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45120007927802249853889141 4230000743231460923802107)
                      ·
                        rfl

theorem cell23_8237897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_8237897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237897 prefixEnd_8237897 := by exact prefixLift 8237897
  have htrace : WordTrace (prefixWord ++ tailWord_8237897) baseStart_8237897 baseEnd_8237897 := by
    simpa [prefixWord, tailWord_8237897, baseEnd_8237897] using wordTrace_append hprefix tailTrace_8237897
  have hstable : (prefixWord ++ tailWord_8237897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237897).length < 2 ^ (prefixWord ++ tailWord_8237897).sum := by decide
  have hdescent : baseEnd_8237897 < baseStart_8237897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237947 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 7]
def baseStart_8237947 : Nat := 118140960795 + 8237947 * 2 ^ 59
def prefixEnd_8237947 : Nat := 4983230072969 + 3 ^ 40 * 8237947 * 2
def baseEnd_8237947 : Nat := 470002935251576192019653

theorem tailTrace_8237947 : CollatzResearch.WordTrace tailWord_8237947 prefixEnd_8237947 470002935251576192019653 := by
  unfold tailWord_8237947
  simp only [CollatzResearch.WordTrace]
  refine ⟨300462611086332423181344095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200308407390888282120896063 300462611086332423181344095)
  ·
    refine ⟨450693916629498634772016143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300462611086332423181344095 450693916629498634772016143)
    ·
      refine ⟨676040874944247952158024215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450693916629498634772016143 676040874944247952158024215)
      ·
        refine ⟨1014061312416371928237036323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676040874944247952158024215 1014061312416371928237036323)
        ·
          refine ⟨1521091968624557892355554485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014061312416371928237036323 1521091968624557892355554485)
          ·
            refine ⟨142602372058552302408333233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1521091968624557892355554485 142602372058552302408333233)
            ·
              refine ⟨106951779043914226806249925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142602372058552302408333233 106951779043914226806249925)
              ·
                refine ⟨20053458570733917526171861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106951779043914226806249925 20053458570733917526171861)
                ·
                  refine ⟨470002935251576192019653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20053458570733917526171861 470002935251576192019653)
                  ·
                    rfl

theorem cell23_8237947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 7].length) (baseStart_8237947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237947 prefixEnd_8237947 := by exact prefixLift 8237947
  have htrace : WordTrace (prefixWord ++ tailWord_8237947) baseStart_8237947 baseEnd_8237947 := by
    simpa [prefixWord, tailWord_8237947, baseEnd_8237947] using wordTrace_append hprefix tailTrace_8237947
  have hstable : (prefixWord ++ tailWord_8237947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237947).length < 2 ^ (prefixWord ++ tailWord_8237947).sum := by decide
  have hdescent : baseEnd_8237947 < baseStart_8237947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237977 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_8237977 : Nat := 118140960795 + 8237977 * 2 ^ 59
def prefixEnd_8237977 : Nat := 4983230072969 + 3 ^ 40 * 8237977 * 2
def baseEnd_8237977 : Nat := 1410013940561273536933913

theorem tailTrace_8237977 : CollatzResearch.WordTrace tailWord_8237977 prefixEnd_8237977 1410013940561273536933913 := by
  unfold tailWord_8237977
  simp only [CollatzResearch.WordTrace]
  refine ⟨300463705276223738304936185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200309136850815825536624123 300463705276223738304936185)
  ·
    refine ⟨225347778957167803728702139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300463705276223738304936185 225347778957167803728702139)
    ·
      refine ⟨338021668435751705593053209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225347778957167803728702139 338021668435751705593053209)
      ·
        refine ⟨253516251326813779194789907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338021668435751705593053209 253516251326813779194789907)
        ·
          refine ⟨380274376990220668792184861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253516251326813779194789907 380274376990220668792184861)
          ·
            refine ⟨142602891371332750797069323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380274376990220668792184861 142602891371332750797069323)
            ·
              refine ⟨213904337056999126195603985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142602891371332750797069323 213904337056999126195603985)
              ·
                refine ⟨160428252792749344646702989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213904337056999126195603985 160428252792749344646702989)
                ·
                  refine ⟨60160594797281004242513621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160428252792749344646702989 60160594797281004242513621)
                  ·
                    refine ⟨1410013940561273536933913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60160594797281004242513621 1410013940561273536933913)
                    ·
                      rfl

theorem cell23_8237977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_8237977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237977 prefixEnd_8237977 := by exact prefixLift 8237977
  have htrace : WordTrace (prefixWord ++ tailWord_8237977) baseStart_8237977 baseEnd_8237977 := by
    simpa [prefixWord, tailWord_8237977, baseEnd_8237977] using wordTrace_append hprefix tailTrace_8237977
  have hstable : (prefixWord ++ tailWord_8237977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237977).length < 2 ^ (prefixWord ++ tailWord_8237977).sum := by decide
  have hdescent : baseEnd_8237977 < baseStart_8237977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8237981 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 5]
def baseStart_8237981 : Nat := 118140960795 + 8237981 * 2 ^ 59
def prefixEnd_8237981 : Nat := 4983230072969 + 3 ^ 40 * 8237981 * 2
def baseEnd_8237981 : Nat := 470004875067382066127969

theorem tailTrace_8237981 : CollatzResearch.WordTrace tailWord_8237981 prefixEnd_8237981 470004875067382066127969 := by
  unfold tailWord_8237981
  simp only [CollatzResearch.WordTrace]
  refine ⟨300463851168209246988081797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200309234112139497992054531 300463851168209246988081797)
  ·
    refine ⟨56336972094039233810265337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300463851168209246988081797 56336972094039233810265337)
    ·
      refine ⟨42252729070529425357699003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56336972094039233810265337 42252729070529425357699003)
      ·
        refine ⟨63379093605794138036548505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42252729070529425357699003 63379093605794138036548505)
        ·
          refine ⟨47534320204345603527411379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63379093605794138036548505 47534320204345603527411379)
          ·
            refine ⟨71301480306518405291117069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47534320204345603527411379 71301480306518405291117069)
            ·
              refine ⟨26738055114944401984168901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71301480306518405291117069 26738055114944401984168901)
              ·
                refine ⟨5013385334052075372031669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26738055114944401984168901 5013385334052075372031669)
                ·
                  refine ⟨470004875067382066127969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013385334052075372031669 470004875067382066127969)
                  ·
                    rfl

theorem cell23_8237981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_8237981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8237981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8237981 prefixEnd_8237981 := by exact prefixLift 8237981
  have htrace : WordTrace (prefixWord ++ tailWord_8237981) baseStart_8237981 baseEnd_8237981 := by
    simpa [prefixWord, tailWord_8237981, baseEnd_8237981] using wordTrace_append hprefix tailTrace_8237981
  have hstable : (prefixWord ++ tailWord_8237981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8237981).length < 2 ^ (prefixWord ++ tailWord_8237981).sum := by decide
  have hdescent : baseEnd_8237981 < baseStart_8237981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8237981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238031 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 4, 2]
def baseStart_8238031 : Nat := 118140960795 + 8238031 * 2 ^ 59
def prefixEnd_8238031 : Nat := 4983230072969 + 3 ^ 40 * 8238031 * 2
def baseEnd_8238031 : Nat := 4230069549639163399526491

theorem tailTrace_8238031 : CollatzResearch.WordTrace tailWord_8238031 prefixEnd_8238031 4230069549639163399526491 := by
  unfold tailWord_8238031
  simp only [CollatzResearch.WordTrace]
  refine ⟨300465674818028105527401947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200310449878685403684934631 300465674818028105527401947)
  ·
    refine ⟨450698512227042158291102921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300465674818028105527401947 450698512227042158291102921)
    ·
      refine ⟨338023884170281618718327191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450698512227042158291102921 338023884170281618718327191)
      ·
        refine ⟨507035826255422428077490787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338023884170281618718327191 507035826255422428077490787)
        ·
          refine ⟨760553739383133642116236181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507035826255422428077490787 760553739383133642116236181)
          ·
            refine ⟨35650956533584389474198571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 760553739383133642116236181 35650956533584389474198571)
            ·
              refine ⟨53476434800376584211297857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35650956533584389474198571 53476434800376584211297857)
              ·
                refine ⟨40107326100282438158473393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53476434800376584211297857 40107326100282438158473393)
                ·
                  refine ⟨30080494575211828618855045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40107326100282438158473393 30080494575211828618855045)
                  ·
                    refine ⟨5640092732852217866035321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30080494575211828618855045 5640092732852217866035321)
                    ·
                      refine ⟨4230069549639163399526491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640092732852217866035321 4230069549639163399526491)
                      ·
                        rfl

theorem cell23_8238031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4, 2].length) (baseStart_8238031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238031 prefixEnd_8238031 := by exact prefixLift 8238031
  have htrace : WordTrace (prefixWord ++ tailWord_8238031) baseStart_8238031 baseEnd_8238031 := by
    simpa [prefixWord, tailWord_8238031, baseEnd_8238031] using wordTrace_append hprefix tailTrace_8238031
  have hstable : (prefixWord ++ tailWord_8238031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238031).length < 2 ^ (prefixWord ++ tailWord_8238031).sum := by decide
  have hdescent : baseEnd_8238031 < baseStart_8238031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238041 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_8238041 : Nat := 118140960795 + 8238041 * 2 ^ 59
def prefixEnd_8238041 : Nat := 4983230072969 + 3 ^ 40 * 8238041 * 2
def baseEnd_8238041 : Nat := 1410024894815236120133815

theorem tailTrace_8238041 : CollatzResearch.WordTrace tailWord_8238041 prefixEnd_8238041 1410024894815236120133815 := by
  unfold tailWord_8238041
  simp only [CollatzResearch.WordTrace]
  refine ⟨300466039547991877235265977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200310693031994584823510651 300466039547991877235265977)
  ·
    refine ⟨225349529660993907926449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300466039547991877235265977 225349529660993907926449483)
    ·
      refine ⟨338024294491490861889674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225349529660993907926449483 338024294491490861889674225)
      ·
        refine ⟨253518220868618146417255669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338024294491490861889674225 253518220868618146417255669)
        ·
          refine ⟨23767333206432951226617719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253518220868618146417255669 23767333206432951226617719)
          ·
            refine ⟨35650999809649426839926579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23767333206432951226617719 35650999809649426839926579)
            ·
              refine ⟨53476499714474140259889869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35650999809649426839926579 53476499714474140259889869)
              ·
                refine ⟨20053687392927802597458701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53476499714474140259889869 20053687392927802597458701)
                ·
                  refine ⟨7520132772347925974047013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20053687392927802597458701 7520132772347925974047013)
                  ·
                    refine ⟨1410024894815236120133815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520132772347925974047013 1410024894815236120133815)
                    ·
                      rfl

theorem cell23_8238041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_8238041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238041 prefixEnd_8238041 := by exact prefixLift 8238041
  have htrace : WordTrace (prefixWord ++ tailWord_8238041) baseStart_8238041 baseEnd_8238041 := by
    simpa [prefixWord, tailWord_8238041, baseEnd_8238041] using wordTrace_append hprefix tailTrace_8238041
  have hstable : (prefixWord ++ tailWord_8238041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238041).length < 2 ^ (prefixWord ++ tailWord_8238041).sum := by decide
  have hdescent : baseEnd_8238041 < baseStart_8238041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238064 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_8238064 : Nat := 118140960795 + 8238064 * 2 ^ 59
def prefixEnd_8238064 : Nat := 4983230072969 + 3 ^ 40 * 8238064 * 2
def baseEnd_8238064 : Nat := 4230086494500761770413839

theorem tailTrace_8238064 : CollatzResearch.WordTrace tailWord_8238064 prefixEnd_8238064 4230086494500761770413839 := by
  unfold tailWord_8238064
  simp only [CollatzResearch.WordTrace]
  refine ⟨150233439213454276081676623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200311252284605701442235497 150233439213454276081676623)
  ·
    refine ⟨225350158820181414122514935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150233439213454276081676623 225350158820181414122514935)
    ·
      refine ⟨338025238230272121183772403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225350158820181414122514935 338025238230272121183772403)
      ·
        refine ⟨507037857345408181775658605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338025238230272121183772403 507037857345408181775658605)
        ·
          refine ⟨190139196504528068165871977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507037857345408181775658605 190139196504528068165871977)
          ·
            refine ⟨142604397378396051124403983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190139196504528068165871977 142604397378396051124403983)
            ·
              refine ⟨213906596067594076686605975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142604397378396051124403983 213906596067594076686605975)
              ·
                refine ⟨320859894101391115029908963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213906596067594076686605975 320859894101391115029908963)
                ·
                  refine ⟨481289841152086672544863445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320859894101391115029908963 481289841152086672544863445)
                  ·
                    refine ⟨11280230652002031387770237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 481289841152086672544863445 11280230652002031387770237)
                    ·
                      refine ⟨4230086494500761770413839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280230652002031387770237 4230086494500761770413839)
                      ·
                        rfl

theorem cell23_8238064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_8238064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238064 prefixEnd_8238064 := by exact prefixLift 8238064
  have htrace : WordTrace (prefixWord ++ tailWord_8238064) baseStart_8238064 baseEnd_8238064 := by
    simpa [prefixWord, tailWord_8238064, baseEnd_8238064] using wordTrace_append hprefix tailTrace_8238064
  have hstable : (prefixWord ++ tailWord_8238064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238064).length < 2 ^ (prefixWord ++ tailWord_8238064).sum := by decide
  have hdescent : baseEnd_8238064 < baseStart_8238064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238188 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_8238188 : Nat := 118140960795 + 8238188 * 2 ^ 59
def prefixEnd_8238188 : Nat := 4983230072969 + 3 ^ 40 * 8238188 * 2
def baseEnd_8238188 : Nat := 4230150166101919285263269

theorem tailTrace_8238188 : CollatzResearch.WordTrace tailWord_8238188 prefixEnd_8238188 4230150166101919285263269 := by
  unfold tailWord_8238188
  simp only [CollatzResearch.WordTrace]
  refine ⟨150235700539229660670433609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200314267385639547560578145 150235700539229660670433609)
  ·
    refine ⟨112676775404422245502825207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150235700539229660670433609 112676775404422245502825207)
    ·
      refine ⟨169015163106633368254237811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112676775404422245502825207 169015163106633368254237811)
      ·
        refine ⟨253522744659950052381356717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169015163106633368254237811 253522744659950052381356717)
        ·
          refine ⟨95071029247481269643008769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253522744659950052381356717 95071029247481269643008769)
          ·
            refine ⟨71303271935610952232256577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95071029247481269643008769 71303271935610952232256577)
            ·
              refine ⟨53477453951708214174192433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71303271935610952232256577 53477453951708214174192433)
              ·
                refine ⟨40108090463781160630644325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53477453951708214174192433 40108090463781160630644325)
                ·
                  refine ⟨7520266961958967618245811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40108090463781160630644325 7520266961958967618245811)
                  ·
                    refine ⟨11280400442938451427368717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7520266961958967618245811 11280400442938451427368717)
                    ·
                      refine ⟨4230150166101919285263269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280400442938451427368717 4230150166101919285263269)
                      ·
                        rfl

theorem cell23_8238188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_8238188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238188 prefixEnd_8238188 := by exact prefixLift 8238188
  have htrace : WordTrace (prefixWord ++ tailWord_8238188) baseStart_8238188 baseEnd_8238188 := by
    simpa [prefixWord, tailWord_8238188, baseEnd_8238188] using wordTrace_append hprefix tailTrace_8238188
  have hstable : (prefixWord ++ tailWord_8238188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238188).length < 2 ^ (prefixWord ++ tailWord_8238188).sum := by decide
  have hdescent : baseEnd_8238188 < baseStart_8238188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238189 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_8238189 : Nat := 118140960795 + 8238189 * 2 ^ 59
def prefixEnd_8238189 : Nat := 4983230072969 + 3 ^ 40 * 8238189 * 2
def baseEnd_8238189 : Nat := 4230150679582573781350765

theorem tailTrace_8238189 : CollatzResearch.WordTrace tailWord_8238189 prefixEnd_8238189 4230150679582573781350765 := by
  unfold tailWord_8238189
  simp only [CollatzResearch.WordTrace]
  refine ⟨300471437551455698511653621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200314291700970465674435747 300471437551455698511653621)
  ·
    refine ⟨28169197270448971735467527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300471437551455698511653621 28169197270448971735467527)
    ·
      refine ⟨42253795905673457603201291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169197270448971735467527 42253795905673457603201291)
      ·
        refine ⟨63380693858510186404801937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42253795905673457603201291 63380693858510186404801937)
        ·
          refine ⟨47535520393882639803601453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63380693858510186404801937 47535520393882639803601453)
          ·
            refine ⟨17825820147705989926350545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47535520393882639803601453 17825820147705989926350545)
            ·
              refine ⟨13369365110779492444762909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17825820147705989926350545 13369365110779492444762909)
              ·
                refine ⟨5013511916542309666786091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13369365110779492444762909 5013511916542309666786091)
                ·
                  refine ⟨7520267874813464500179137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013511916542309666786091 7520267874813464500179137)
                  ·
                    refine ⟨5640200906110098375134353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520267874813464500179137 5640200906110098375134353)
                    ·
                      refine ⟨4230150679582573781350765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640200906110098375134353 4230150679582573781350765)
                      ·
                        rfl

theorem cell23_8238189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_8238189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238189 prefixEnd_8238189 := by exact prefixLift 8238189
  have htrace : WordTrace (prefixWord ++ tailWord_8238189) baseStart_8238189 baseEnd_8238189 := by
    simpa [prefixWord, tailWord_8238189, baseEnd_8238189] using wordTrace_append hprefix tailTrace_8238189
  have hstable : (prefixWord ++ tailWord_8238189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238189).length < 2 ^ (prefixWord ++ tailWord_8238189).sum := by decide
  have hdescent : baseEnd_8238189 < baseStart_8238189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238232 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_8238232 : Nat := 118140960795 + 8238232 * 2 ^ 59
def prefixEnd_8238232 : Nat := 4983230072969 + 3 ^ 40 * 8238232 * 2
def baseEnd_8238232 : Nat := 4230172759250717113113067

theorem tailTrace_8238232 : CollatzResearch.WordTrace tailWord_8238232 prefixEnd_8238232 4230172759250717113113067 := by
  unfold tailWord_8238232
  simp only [CollatzResearch.WordTrace]
  refine ⟨150236502945149958427734475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200315337260199944570312633 150236502945149958427734475)
  ·
    refine ⟨225354754417724937641601713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150236502945149958427734475 225354754417724937641601713)
    ·
      refine ⟨169016065813293703231201285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225354754417724937641601713 169016065813293703231201285)
      ·
        refine ⟨31690512339992569355850241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169016065813293703231201285 31690512339992569355850241)
        ·
          refine ⟨23767884254994427016887681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31690512339992569355850241 23767884254994427016887681)
          ·
            refine ⟨17825913191245820262665761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23767884254994427016887681 17825913191245820262665761)
            ·
              refine ⟨13369434893434365196999321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17825913191245820262665761 13369434893434365196999321)
              ·
                refine ⟨10027076170075773897749491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13369434893434365196999321 10027076170075773897749491)
                ·
                  refine ⟨15040614255113660846624237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10027076170075773897749491 15040614255113660846624237)
                  ·
                    refine ⟨5640230345667622817484089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15040614255113660846624237 5640230345667622817484089)
                    ·
                      refine ⟨4230172759250717113113067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640230345667622817484089 4230172759250717113113067)
                      ·
                        rfl

theorem cell23_8238232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_8238232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238232 prefixEnd_8238232 := by exact prefixLift 8238232
  have htrace : WordTrace (prefixWord ++ tailWord_8238232) baseStart_8238232 baseEnd_8238232 := by
    simpa [prefixWord, tailWord_8238232, baseEnd_8238232] using wordTrace_append hprefix tailTrace_8238232
  have hstable : (prefixWord ++ tailWord_8238232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238232).length < 2 ^ (prefixWord ++ tailWord_8238232).sum := by decide
  have hdescent : baseEnd_8238232 < baseStart_8238232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238245 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_8238245 : Nat := 118140960795 + 8238245 * 2 ^ 59
def prefixEnd_8238245 : Nat := 4983230072969 + 3 ^ 40 * 8238245 * 2
def baseEnd_8238245 : Nat := 4230179434499225562250507

theorem tailTrace_8238245 : CollatzResearch.WordTrace tailWord_8238245 prefixEnd_8238245 4230179434499225562250507 := by
  unfold tailWord_8238245
  simp only [CollatzResearch.WordTrace]
  refine ⟨300473480039252820075692189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200315653359501880050461459 300473480039252820075692189)
  ·
    refine ⟨112677555014719807528384571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300473480039252820075692189 112677555014719807528384571)
    ·
      refine ⟨169016332522079711292576857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112677555014719807528384571 169016332522079711292576857)
      ·
        refine ⟨126762249391559783469432643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169016332522079711292576857 126762249391559783469432643)
        ·
          refine ⟨190143374087339675204148965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126762249391559783469432643 190143374087339675204148965)
          ·
            refine ⟨35651882641376189100777931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190143374087339675204148965 35651882641376189100777931)
            ·
              refine ⟨53477823962064283651166897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35651882641376189100777931 53477823962064283651166897)
              ·
                refine ⟨40108367971548212738375173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53477823962064283651166897 40108367971548212738375173)
                ·
                  refine ⟨7520318994665289888445345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40108367971548212738375173 7520318994665289888445345)
                  ·
                    refine ⟨5640239245998967416334009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520318994665289888445345 5640239245998967416334009)
                    ·
                      refine ⟨4230179434499225562250507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640239245998967416334009 4230179434499225562250507)
                      ·
                        rfl

theorem cell23_8238245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_8238245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238245 prefixEnd_8238245 := by exact prefixLift 8238245
  have htrace : WordTrace (prefixWord ++ tailWord_8238245) baseStart_8238245 baseEnd_8238245 := by
    simpa [prefixWord, tailWord_8238245, baseEnd_8238245] using wordTrace_append hprefix tailTrace_8238245
  have hstable : (prefixWord ++ tailWord_8238245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238245).length < 2 ^ (prefixWord ++ tailWord_8238245).sum := by decide
  have hdescent : baseEnd_8238245 < baseStart_8238245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238268 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 7]
def baseStart_8238268 : Nat := 118140960795 + 8238268 * 2 ^ 59
def prefixEnd_8238268 : Nat := 4983230072969 + 3 ^ 40 * 8238268 * 2
def baseEnd_8238268 : Nat := 470021249394919885806989

theorem tailTrace_8238268 : CollatzResearch.WordTrace tailWord_8238268 prefixEnd_8238268 470021249394919885806989 := by
  unfold tailWord_8238268
  simp only [CollatzResearch.WordTrace]
  refine ⟨150237159459084747501889729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200316212612112996669186305 150237159459084747501889729)
  ·
    refine ⟨112677869594313560626417297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150237159459084747501889729 112677869594313560626417297)
    ·
      refine ⟨84508402195735170469812973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112677869594313560626417297 84508402195735170469812973)
      ·
        refine ⟨31690650823400688926179865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84508402195735170469812973 31690650823400688926179865)
        ·
          refine ⟨23767988117550516694634899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31690650823400688926179865 23767988117550516694634899)
          ·
            refine ⟨35651982176325775041952349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23767988117550516694634899 35651982176325775041952349)
            ·
              refine ⟨13369493316122165640732131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35651982176325775041952349 13369493316122165640732131)
              ·
                refine ⟨20054239974183248461098197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13369493316122165640732131 20054239974183248461098197)
                ·
                  refine ⟨470021249394919885806989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20054239974183248461098197 470021249394919885806989)
                  ·
                    rfl

theorem cell23_8238268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_8238268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238268 prefixEnd_8238268 := by exact prefixLift 8238268
  have htrace : WordTrace (prefixWord ++ tailWord_8238268) baseStart_8238268 baseEnd_8238268 := by
    simpa [prefixWord, tailWord_8238268, baseEnd_8238268] using wordTrace_append hprefix tailTrace_8238268
  have hstable : (prefixWord ++ tailWord_8238268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238268).length < 2 ^ (prefixWord ++ tailWord_8238268).sum := by decide
  have hdescent : baseEnd_8238268 < baseStart_8238268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238319 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 5]
def baseStart_8238319 : Nat := 118140960795 + 8238319 * 2 ^ 59
def prefixEnd_8238319 : Nat := 4983230072969 + 3 ^ 40 * 8238319 * 2
def baseEnd_8238319 : Nat := 470024159118628696969463

theorem tailTrace_8238319 : CollatzResearch.WordTrace tailWord_8238319 prefixEnd_8238319 470024159118628696969463 := by
  unfold tailWord_8238319
  simp only [CollatzResearch.WordTrace]
  refine ⟨300476179040984730713886011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200317452693989820475924007 300476179040984730713886011)
  ·
    refine ⟨450714268561477096070829017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300476179040984730713886011 450714268561477096070829017)
    ·
      refine ⟨338035701421107822053121763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450714268561477096070829017 338035701421107822053121763)
      ·
        refine ⟨507053552131661733079682645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338035701421107822053121763 507053552131661733079682645)
        ·
          refine ⟨5942033814042910934527531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 507053552131661733079682645 5942033814042910934527531)
          ·
            refine ⟨8913050721064366401791297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942033814042910934527531 8913050721064366401791297)
            ·
              refine ⟨6684788040798274801343473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8913050721064366401791297 6684788040798274801343473)
              ·
                refine ⟨5013591030598706101007605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684788040798274801343473 5013591030598706101007605)
                ·
                  refine ⟨470024159118628696969463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013591030598706101007605 470024159118628696969463)
                  ·
                    rfl

theorem cell23_8238319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 5].length) (baseStart_8238319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238319 prefixEnd_8238319 := by exact prefixLift 8238319
  have htrace : WordTrace (prefixWord ++ tailWord_8238319) baseStart_8238319 baseEnd_8238319 := by
    simpa [prefixWord, tailWord_8238319, baseEnd_8238319] using wordTrace_append hprefix tailTrace_8238319
  have hstable : (prefixWord ++ tailWord_8238319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238319).length < 2 ^ (prefixWord ++ tailWord_8238319).sum := by decide
  have hdescent : baseEnd_8238319 < baseStart_8238319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238321 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_8238321 : Nat := 118140960795 + 8238321 * 2 ^ 59
def prefixEnd_8238321 : Nat := 4983230072969 + 3 ^ 40 * 8238321 * 2
def baseEnd_8238321 : Nat := 4230218459028967264900157

theorem tailTrace_8238321 : CollatzResearch.WordTrace tailWord_8238321 prefixEnd_8238321 4230218459028967264900157 := by
  unfold tailWord_8238321
  simp only [CollatzResearch.WordTrace]
  refine ⟨300476251986977485055458817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200317501324651656703639211 300476251986977485055458817)
  ·
    refine ⟨225357188990233113791594113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300476251986977485055458817 225357188990233113791594113)
    ·
      refine ⟨169017891742674835343695585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225357188990233113791594113 169017891742674835343695585)
      ·
        refine ⟨126763418807006126507771689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169017891742674835343695585 126763418807006126507771689)
        ·
          refine ⟨95072564105254594880828767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126763418807006126507771689 95072564105254594880828767)
          ·
            refine ⟨142608846157881892321243151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95072564105254594880828767 142608846157881892321243151)
            ·
              refine ⟨213913269236822838481864727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142608846157881892321243151 213913269236822838481864727)
              ·
                refine ⟨320869903855234257722797091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213913269236822838481864727 320869903855234257722797091)
                ·
                  refine ⟨481304855782851386584195637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320869903855234257722797091 481304855782851386584195637)
                  ·
                    refine ⟨45122330229642317492268341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 481304855782851386584195637 45122330229642317492268341)
                    ·
                      refine ⟨4230218459028967264900157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45122330229642317492268341 4230218459028967264900157)
                      ·
                        rfl

theorem cell23_8238321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_8238321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238321 prefixEnd_8238321 := by exact prefixLift 8238321
  have htrace : WordTrace (prefixWord ++ tailWord_8238321) baseStart_8238321 baseEnd_8238321 := by
    simpa [prefixWord, tailWord_8238321, baseEnd_8238321] using wordTrace_append hprefix tailTrace_8238321
  have hstable : (prefixWord ++ tailWord_8238321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238321).length < 2 ^ (prefixWord ++ tailWord_8238321).sum := by decide
  have hdescent : baseEnd_8238321 < baseStart_8238321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238335 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 4, 2]
def baseStart_8238335 : Nat := 118140960795 + 8238335 * 2 ^ 59
def prefixEnd_8238335 : Nat := 4983230072969 + 3 ^ 40 * 8238335 * 2
def baseEnd_8238335 : Nat := 4230225647758130210125093

theorem tailTrace_8238335 : CollatzResearch.WordTrace tailWord_8238335 prefixEnd_8238335 4230225647758130210125093 := by
  unfold tailWord_8238335
  simp only [CollatzResearch.WordTrace]
  refine ⟨300476762608926765446468459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200317841739284510297645639 300476762608926765446468459)
  ·
    refine ⟨450715143913390148169702689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300476762608926765446468459 450715143913390148169702689)
    ·
      refine ⟨338036357935042611127277017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450715143913390148169702689 338036357935042611127277017)
      ·
        refine ⟨253527268451281958345457763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338036357935042611127277017 253527268451281958345457763)
        ·
          refine ⟨380290902676922937518186645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253527268451281958345457763 380290902676922937518186645)
          ·
            refine ⟨17826136062980762696164999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380290902676922937518186645 17826136062980762696164999)
            ·
              refine ⟨26739204094471144044247499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826136062980762696164999 26739204094471144044247499)
              ·
                refine ⟨40108806141706716066371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26739204094471144044247499 40108806141706716066371249)
                ·
                  refine ⟨30081604606280037049778437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40108806141706716066371249 30081604606280037049778437)
                  ·
                    refine ⟨5640300863677506946833457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30081604606280037049778437 5640300863677506946833457)
                    ·
                      refine ⟨4230225647758130210125093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640300863677506946833457 4230225647758130210125093)
                      ·
                        rfl

theorem cell23_8238335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_8238335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238335 prefixEnd_8238335 := by exact prefixLift 8238335
  have htrace : WordTrace (prefixWord ++ tailWord_8238335) baseStart_8238335 baseEnd_8238335 := by
    simpa [prefixWord, tailWord_8238335, baseEnd_8238335] using wordTrace_append hprefix tailTrace_8238335
  have hstable : (prefixWord ++ tailWord_8238335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238335).length < 2 ^ (prefixWord ++ tailWord_8238335).sum := by decide
  have hdescent : baseEnd_8238335 < baseStart_8238335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238361 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_8238361 : Nat := 118140960795 + 8238361 * 2 ^ 59
def prefixEnd_8238361 : Nat := 4983230072969 + 3 ^ 40 * 8238361 * 2
def baseEnd_8238361 : Nat := 4230238998255147108399973

theorem tailTrace_8238361 : CollatzResearch.WordTrace tailWord_8238361 prefixEnd_8238361 4230238998255147108399973 := by
  unfold tailWord_8238361
  simp only [CollatzResearch.WordTrace]
  refine ⟨300477710906832571886914937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200318473937888381257943291 300477710906832571886914937)
  ·
    refine ⟨225358283180124428915186203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300477710906832571886914937 225358283180124428915186203)
    ·
      refine ⟨338037424770186643372779305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225358283180124428915186203 338037424770186643372779305)
      ·
        refine ⟨253528068577639982529584479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338037424770186643372779305 253528068577639982529584479)
        ·
          refine ⟨380292102866459973794376719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253528068577639982529584479 380292102866459973794376719)
          ·
            refine ⟨570438154299689960691565079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380292102866459973794376719 570438154299689960691565079)
            ·
              refine ⟨855657231449534941037347619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570438154299689960691565079 855657231449534941037347619)
              ·
                refine ⟨1283485847174302411556021429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855657231449534941037347619 1283485847174302411556021429)
                ·
                  refine ⟨120326798172590851083377009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283485847174302411556021429 120326798172590851083377009)
                  ·
                    refine ⟨90245098629443138312532757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120326798172590851083377009 90245098629443138312532757)
                    ·
                      refine ⟨4230238998255147108399973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90245098629443138312532757 4230238998255147108399973)
                      ·
                        rfl

theorem cell23_8238361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_8238361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238361 prefixEnd_8238361 := by exact prefixLift 8238361
  have htrace : WordTrace (prefixWord ++ tailWord_8238361) baseStart_8238361 baseEnd_8238361 := by
    simpa [prefixWord, tailWord_8238361, baseEnd_8238361] using wordTrace_append hprefix tailTrace_8238361
  have hstable : (prefixWord ++ tailWord_8238361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238361).length < 2 ^ (prefixWord ++ tailWord_8238361).sum := by decide
  have hdescent : baseEnd_8238361 < baseStart_8238361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238362 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_8238362 : Nat := 118140960795 + 8238362 * 2 ^ 59
def prefixEnd_8238362 : Nat := 4983230072969 + 3 ^ 40 * 8238362 * 2
def baseEnd_8238362 : Nat := 1410079837245267201495823

theorem tailTrace_8238362 : CollatzResearch.WordTrace tailWord_8238362 prefixEnd_8238362 1410079837245267201495823 := by
  unfold tailWord_8238362
  simp only [CollatzResearch.WordTrace]
  refine ⟨75119436844957237264425335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200318498253219299371800893 75119436844957237264425335)
  ·
    refine ⟨112679155267435855896638003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75119436844957237264425335 112679155267435855896638003)
    ·
      refine ⟨169018732901153783844957005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112679155267435855896638003 169018732901153783844957005)
      ·
        refine ⟨63382024837932668941858877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169018732901153783844957005 63382024837932668941858877)
        ·
          refine ⟨23768259314224750853197079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63382024837932668941858877 23768259314224750853197079)
          ·
            refine ⟨35652388971337126279795619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23768259314224750853197079 35652388971337126279795619)
            ·
              refine ⟨53478583457005689419693429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35652388971337126279795619 53478583457005689419693429)
              ·
                refine ⟨5013617199094283383096259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53478583457005689419693429 5013617199094283383096259)
                ·
                  refine ⟨7520425798641425074644389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013617199094283383096259 7520425798641425074644389)
                  ·
                    refine ⟨1410079837245267201495823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520425798641425074644389 1410079837245267201495823)
                    ·
                      rfl

theorem cell23_8238362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_8238362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238362 prefixEnd_8238362 := by exact prefixLift 8238362
  have htrace : WordTrace (prefixWord ++ tailWord_8238362) baseStart_8238362 baseEnd_8238362 := by
    simpa [prefixWord, tailWord_8238362, baseEnd_8238362] using wordTrace_append hprefix tailTrace_8238362
  have hstable : (prefixWord ++ tailWord_8238362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238362).length < 2 ^ (prefixWord ++ tailWord_8238362).sum := by decide
  have hdescent : baseEnd_8238362 < baseStart_8238362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238413 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_8238413 : Nat := 118140960795 + 8238413 * 2 ^ 59
def prefixEnd_8238413 : Nat := 4983230072969 + 3 ^ 40 * 8238413 * 2
def baseEnd_8238413 : Nat := 1410088566416393634983245

theorem tailTrace_8238413 : CollatzResearch.WordTrace tailWord_8238413 prefixEnd_8238413 1410088566416393634983245 := by
  unfold tailWord_8238413
  simp only [CollatzResearch.WordTrace]
  refine ⟨300479607502644184767807893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200319738335096123178538595 300479607502644184767807893)
  ·
    refine ⟨14084981601686446160990995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300479607502644184767807893 14084981601686446160990995)
    ·
      refine ⟨21127472402529669241486493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14084981601686446160990995 21127472402529669241486493)
      ·
        refine ⟨7922802150948625965557435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21127472402529669241486493 7922802150948625965557435)
        ·
          refine ⟨11884203226422938948336153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922802150948625965557435 11884203226422938948336153)
          ·
            refine ⟨8913152419817204211252115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11884203226422938948336153 8913152419817204211252115)
            ·
              refine ⟨13369728629725806316878173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913152419817204211252115 13369728629725806316878173)
              ·
                refine ⟨5013648236147177368829315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13369728629725806316878173 5013648236147177368829315)
                ·
                  refine ⟨7520472354220766053243973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013648236147177368829315 7520472354220766053243973)
                  ·
                    refine ⟨1410088566416393634983245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520472354220766053243973 1410088566416393634983245)
                    ·
                      rfl

theorem cell23_8238413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_8238413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238413 prefixEnd_8238413 := by exact prefixLift 8238413
  have htrace : WordTrace (prefixWord ++ tailWord_8238413) baseStart_8238413 baseEnd_8238413 := by
    simpa [prefixWord, tailWord_8238413, baseEnd_8238413] using wordTrace_append hprefix tailTrace_8238413
  have hstable : (prefixWord ++ tailWord_8238413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238413).length < 2 ^ (prefixWord ++ tailWord_8238413).sum := by decide
  have hdescent : baseEnd_8238413 < baseStart_8238413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238418 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_8238418 : Nat := 118140960795 + 8238418 * 2 ^ 59
def prefixEnd_8238418 : Nat := 4983230072969 + 3 ^ 40 * 8238418 * 2
def baseEnd_8238418 : Nat := 1410089422217484461795737

theorem tailTrace_8238418 : CollatzResearch.WordTrace tailWord_8238418 prefixEnd_8238418 1410089422217484461795737 := by
  unfold tailWord_8238418
  simp only [CollatzResearch.WordTrace]
  refine ⟨75119947466906517655434977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200319859911750713747826605 75119947466906517655434977)
  ·
    refine ⟨56339960600179888241576233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75119947466906517655434977 56339960600179888241576233)
    ·
      refine ⟨42254970450134916181182175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56339960600179888241576233 42254970450134916181182175)
      ·
        refine ⟨63382455675202374271773263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42254970450134916181182175 63382455675202374271773263)
        ·
          refine ⟨95073683512803561407659895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63382455675202374271773263 95073683512803561407659895)
          ·
            refine ⟨142610525269205342111489843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95073683512803561407659895 142610525269205342111489843)
            ·
              refine ⟨213915787903808013167234765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142610525269205342111489843 213915787903808013167234765)
              ·
                refine ⟨80218420463928004937713037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213915787903808013167234765 80218420463928004937713037)
                ·
                  refine ⟨30081907673973001851642389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80218420463928004937713037 30081907673973001851642389)
                  ·
                    refine ⟨1410089422217484461795737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30081907673973001851642389 1410089422217484461795737)
                    ·
                      rfl

theorem cell23_8238418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_8238418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238418 prefixEnd_8238418 := by exact prefixLift 8238418
  have htrace : WordTrace (prefixWord ++ tailWord_8238418) baseStart_8238418 baseEnd_8238418 := by
    simpa [prefixWord, tailWord_8238418, baseEnd_8238418] using wordTrace_append hprefix tailTrace_8238418
  have hstable : (prefixWord ++ tailWord_8238418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238418).length < 2 ^ (prefixWord ++ tailWord_8238418).sum := by decide
  have hdescent : baseEnd_8238418 < baseStart_8238418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238425 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_8238425 : Nat := 118140960795 + 8238425 * 2 ^ 59
def prefixEnd_8238425 : Nat := 4983230072969 + 3 ^ 40 * 8238425 * 2
def baseEnd_8238425 : Nat := 4230271861017034857999679

theorem tailTrace_8238425 : CollatzResearch.WordTrace tailWord_8238425 prefixEnd_8238425 4230271861017034857999679 := by
  unfold tailWord_8238425
  simp only [CollatzResearch.WordTrace]
  refine ⟨300480045178600710817244729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200320030119067140544829819 300480045178600710817244729)
  ·
    refine ⟨225360033883950533112933547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300480045178600710817244729 225360033883950533112933547)
    ·
      refine ⟨338040050825925799669400321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225360033883950533112933547 338040050825925799669400321)
      ·
        refine ⟨253530038119444349752050241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338040050825925799669400321 253530038119444349752050241)
        ·
          refine ⟨190147528589583262314037681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253530038119444349752050241 190147528589583262314037681)
          ·
            refine ⟨142610646442187446735528261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190147528589583262314037681 142610646442187446735528261)
            ·
              refine ⟨26739496207910146262911549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142610646442187446735528261 26739496207910146262911549)
              ·
                refine ⟨10027311077966304848591831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26739496207910146262911549 10027311077966304848591831)
                ·
                  refine ⟨15040966616949457272887747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10027311077966304848591831 15040966616949457272887747)
                  ·
                    refine ⟨22561449925424185909331621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15040966616949457272887747 22561449925424185909331621)
                    ·
                      refine ⟨4230271861017034857999679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22561449925424185909331621 4230271861017034857999679)
                      ·
                        rfl

theorem cell23_8238425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_8238425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238425 prefixEnd_8238425 := by exact prefixLift 8238425
  have htrace : WordTrace (prefixWord ++ tailWord_8238425) baseStart_8238425 baseEnd_8238425 := by
    simpa [prefixWord, tailWord_8238425, baseEnd_8238425] using wordTrace_append hprefix tailTrace_8238425
  have hstable : (prefixWord ++ tailWord_8238425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238425).length < 2 ^ (prefixWord ++ tailWord_8238425).sum := by decide
  have hdescent : baseEnd_8238425 < baseStart_8238425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238435 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 4, 4]
def baseStart_8238435 : Nat := 118140960795 + 8238435 * 2 ^ 59
def prefixEnd_8238435 : Nat := 4983230072969 + 3 ^ 40 * 8238435 * 2
def baseEnd_8238435 : Nat := 1410092331941193272958211

theorem tailTrace_8238435 : CollatzResearch.WordTrace tailWord_8238435 prefixEnd_8238435 1410092331941193272958211 := by
  unfold tailWord_8238435
  simp only [CollatzResearch.WordTrace]
  refine ⟨300480409908564482525108759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200320273272376321683405839 300480409908564482525108759)
  ·
    refine ⟨450720614862846723787663139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300480409908564482525108759 450720614862846723787663139)
    ·
      refine ⟨676080922294270085681494709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450720614862846723787663139 676080922294270085681494709)
      ·
        refine ⟨63382586465087820532640129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 676080922294270085681494709 63382586465087820532640129)
        ·
          refine ⟨47536939848815865399480097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63382586465087820532640129 47536939848815865399480097)
          ·
            refine ⟨35652704886611899049610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47536939848815865399480097 35652704886611899049610073)
            ·
              refine ⟨26739528664958924287207555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35652704886611899049610073 26739528664958924287207555)
              ·
                refine ⟨40109292997438386430811333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26739528664958924287207555 40109292997438386430811333)
                ·
                  refine ⟨7520492437019697455777125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40109292997438386430811333 7520492437019697455777125)
                  ·
                    refine ⟨1410092331941193272958211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7520492437019697455777125 1410092331941193272958211)
                    ·
                      rfl

theorem cell23_8238435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 4].length) (baseStart_8238435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238435 prefixEnd_8238435 := by exact prefixLift 8238435
  have htrace : WordTrace (prefixWord ++ tailWord_8238435) baseStart_8238435 baseEnd_8238435 := by
    simpa [prefixWord, tailWord_8238435, baseEnd_8238435] using wordTrace_append hprefix tailTrace_8238435
  have hstable : (prefixWord ++ tailWord_8238435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238435).length < 2 ^ (prefixWord ++ tailWord_8238435).sum := by decide
  have hdescent : baseEnd_8238435 < baseStart_8238435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238436 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_8238436 : Nat := 118140960795 + 8238436 * 2 ^ 59
def prefixEnd_8238436 : Nat := 4983230072969 + 3 ^ 40 * 8238436 * 2
def baseEnd_8238436 : Nat := 4230277509304234314962129

theorem tailTrace_8238436 : CollatzResearch.WordTrace tailWord_8238436 prefixEnd_8238436 4230277509304234314962129 := by
  unfold tailWord_8238436
  simp only [CollatzResearch.WordTrace]
  refine ⟨150240223190780429847947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200320297587707239797263441 150240223190780429847947581)
  ·
    refine ⟨56340083696542661192980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150240223190780429847947581 56340083696542661192980343)
    ·
      refine ⟨84510125544813991789470515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56340083696542661192980343 84510125544813991789470515)
      ·
        refine ⟨126765188317220987684205773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84510125544813991789470515 126765188317220987684205773)
        ·
          refine ⟨47536945618957870381577165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126765188317220987684205773 47536945618957870381577165)
          ·
            refine ⟨17826354607109201393091437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47536945618957870381577165 17826354607109201393091437)
            ·
              refine ⟨6684882977665950522409289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17826354607109201393091437 6684882977665950522409289)
              ·
                refine ⟨5013662233249462891806967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684882977665950522409289 5013662233249462891806967)
                ·
                  refine ⟨7520493349874194337710451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013662233249462891806967 7520493349874194337710451)
                  ·
                    refine ⟨11280740024811291506565677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7520493349874194337710451 11280740024811291506565677)
                    ·
                      refine ⟨4230277509304234314962129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280740024811291506565677 4230277509304234314962129)
                      ·
                        rfl

theorem cell23_8238436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_8238436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238436 prefixEnd_8238436 := by exact prefixLift 8238436
  have htrace : WordTrace (prefixWord ++ tailWord_8238436) baseStart_8238436 baseEnd_8238436 := by
    simpa [prefixWord, tailWord_8238436, baseEnd_8238436] using wordTrace_append hprefix tailTrace_8238436
  have hstable : (prefixWord ++ tailWord_8238436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238436).length < 2 ^ (prefixWord ++ tailWord_8238436).sum := by decide
  have hdescent : baseEnd_8238436 < baseStart_8238436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238445 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_8238445 : Nat := 118140960795 + 8238445 * 2 ^ 59
def prefixEnd_8238445 : Nat := 4983230072969 + 3 ^ 40 * 8238445 * 2
def baseEnd_8238445 : Nat := 4230282130630124779749587

theorem tailTrace_8238445 : CollatzResearch.WordTrace tailWord_8238445 prefixEnd_8238445 4230282130630124779749587 := by
  unfold tailWord_8238445
  simp only [CollatzResearch.WordTrace]
  refine ⟨300480774638528254232972789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200320516425685502821981859 300480774638528254232972789)
  ·
    refine ⟨28170072622362023834341199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300480774638528254232972789 28170072622362023834341199)
    ·
      refine ⟨42255108933543035751511799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28170072622362023834341199 42255108933543035751511799)
      ·
        refine ⟨63382663400314553627267699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255108933543035751511799 63382663400314553627267699)
        ·
          refine ⟨95073995100471830440901549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63382663400314553627267699 95073995100471830440901549)
          ·
            refine ⟨35652748162676936415338081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95073995100471830440901549 35652748162676936415338081)
            ·
              refine ⟨26739561122007702311503561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35652748162676936415338081 26739561122007702311503561)
              ·
                refine ⟨20054670841505776733627671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26739561122007702311503561 20054670841505776733627671)
                ·
                  refine ⟨30082006262258665100441507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20054670841505776733627671 30082006262258665100441507)
                  ·
                    refine ⟨45123009393387997650662261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30082006262258665100441507 45123009393387997650662261)
                    ·
                      refine ⟨4230282130630124779749587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45123009393387997650662261 4230282130630124779749587)
                      ·
                        rfl

theorem cell23_8238445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_8238445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238445 prefixEnd_8238445 := by exact prefixLift 8238445
  have htrace : WordTrace (prefixWord ++ tailWord_8238445) baseStart_8238445 baseEnd_8238445 := by
    simpa [prefixWord, tailWord_8238445, baseEnd_8238445] using wordTrace_append hprefix tailTrace_8238445
  have hstable : (prefixWord ++ tailWord_8238445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238445).length < 2 ^ (prefixWord ++ tailWord_8238445).sum := by decide
  have hdescent : baseEnd_8238445 < baseStart_8238445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238448 : List Nat := [2, 1, 1, 1, 4, 2, 4, 8]
def baseStart_8238448 : Nat := 118140960795 + 8238448 * 2 ^ 59
def prefixEnd_8238448 : Nat := 4983230072969 + 3 ^ 40 * 8238448 * 2
def baseEnd_8238448 : Nat := 156677173002669935852299

theorem tailTrace_8238448 : CollatzResearch.WordTrace tailWord_8238448 prefixEnd_8238448 156677173002669935852299 := by
  unfold tailWord_8238448
  simp only [CollatzResearch.WordTrace]
  refine ⟨150240442028758692872665999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200320589371678257163554665 150240442028758692872665999)
  ·
    refine ⟨225360663043138039308998999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150240442028758692872665999 225360663043138039308998999)
    ·
      refine ⟨338040994564707058963498499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225360663043138039308998999 338040994564707058963498499)
      ·
        refine ⟨507061491847060588445247749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338040994564707058963498499 507061491847060588445247749)
        ·
          refine ⟨95074029721323860333483953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507061491847060588445247749 95074029721323860333483953)
          ·
            refine ⟨71305522290992895250112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95074029721323860333483953 71305522290992895250112965)
            ·
              refine ⟨13369785429561167859396181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71305522290992895250112965 13369785429561167859396181)
              ·
                refine ⟨156677173002669935852299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13369785429561167859396181 156677173002669935852299)
                ·
                  rfl

theorem cell23_8238448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_8238448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238448 prefixEnd_8238448 := by exact prefixLift 8238448
  have htrace : WordTrace (prefixWord ++ tailWord_8238448) baseStart_8238448 baseEnd_8238448 := by
    simpa [prefixWord, tailWord_8238448, baseEnd_8238448] using wordTrace_append hprefix tailTrace_8238448
  have hstable : (prefixWord ++ tailWord_8238448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238448).length < 2 ^ (prefixWord ++ tailWord_8238448).sum := by decide
  have hdescent : baseEnd_8238448 < baseStart_8238448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238475 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3]
def baseStart_8238475 : Nat := 118140960795 + 8238475 * 2 ^ 59
def prefixEnd_8238475 : Nat := 4983230072969 + 3 ^ 40 * 8238475 * 2
def baseEnd_8238475 : Nat := 4230297535049759662374449

theorem tailTrace_8238475 : CollatzResearch.WordTrace tailWord_8238475 prefixEnd_8238475 4230297535049759662374449 := by
  unfold tailWord_8238475
  simp only [CollatzResearch.WordTrace]
  refine ⟨300481868828419569356564879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200321245885613046237709919 300481868828419569356564879)
  ·
    refine ⟨450722803242629354034847319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300481868828419569356564879 450722803242629354034847319)
    ·
      refine ⟨676084204863944031052270979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450722803242629354034847319 676084204863944031052270979)
      ·
        refine ⟨1014126307295916046578406469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676084204863944031052270979 1014126307295916046578406469)
        ·
          refine ⟨190148682617984258733451213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1014126307295916046578406469 190148682617984258733451213)
          ·
            refine ⟨71305755981744097025044205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190148682617984258733451213 71305755981744097025044205)
            ·
              refine ⟨26739658493154036384391577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71305755981744097025044205 26739658493154036384391577)
              ·
                refine ⟨20054743869865527288293683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26739658493154036384391577 20054743869865527288293683)
                ·
                  refine ⟨30082115804798290932440525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20054743869865527288293683 30082115804798290932440525)
                  ·
                    refine ⟨11280793426799359099665197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30082115804798290932440525 11280793426799359099665197)
                    ·
                      refine ⟨4230297535049759662374449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280793426799359099665197 4230297535049759662374449)
                      ·
                        rfl

theorem cell23_8238475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].length) (baseStart_8238475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238475 prefixEnd_8238475 := by exact prefixLift 8238475
  have htrace : WordTrace (prefixWord ++ tailWord_8238475) baseStart_8238475 baseEnd_8238475 := by
    simpa [prefixWord, tailWord_8238475, baseEnd_8238475] using wordTrace_append hprefix tailTrace_8238475
  have hstable : (prefixWord ++ tailWord_8238475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238475).length < 2 ^ (prefixWord ++ tailWord_8238475).sum := by decide
  have hdescent : baseEnd_8238475 < baseStart_8238475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238482 : List Nat := [3, 2, 3, 3, 2, 10]
def baseStart_8238482 : Nat := 118140960795 + 8238482 * 2 ^ 59
def prefixEnd_8238482 : Nat := 4983230072969 + 3 ^ 40 * 8238482 * 2
def baseEnd_8238482 : Nat := 17408646623104284506119

theorem tailTrace_8238482 : CollatzResearch.WordTrace tailWord_8238482 prefixEnd_8238482 17408646623104284506119 := by
  unfold tailWord_8238482
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120531034848552388017425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200321416092929473034713133 75120531034848552388017425)
  ·
    refine ⟨56340398276136414291013069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75120531034848552388017425 56340398276136414291013069)
    ·
      refine ⟨21127649353551155359129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56340398276136414291013069 21127649353551155359129901)
      ·
        refine ⟨7922868507581683259673713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21127649353551155359129901 7922868507581683259673713)
        ·
          refine ⟨5942151380686262444755285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7922868507581683259673713 5942151380686262444755285)
          ·
            refine ⟨17408646623104284506119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5942151380686262444755285 17408646623104284506119)
            ·
              rfl

theorem cell23_8238482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 10].length) (baseStart_8238482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238482 prefixEnd_8238482 := by exact prefixLift 8238482
  have htrace : WordTrace (prefixWord ++ tailWord_8238482) baseStart_8238482 baseEnd_8238482 := by
    simpa [prefixWord, tailWord_8238482, baseEnd_8238482] using wordTrace_append hprefix tailTrace_8238482
  have hstable : (prefixWord ++ tailWord_8238482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238482).length < 2 ^ (prefixWord ++ tailWord_8238482).sum := by decide
  have hdescent : baseEnd_8238482 < baseStart_8238482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238493 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_8238493 : Nat := 118140960795 + 8238493 * 2 ^ 59
def prefixEnd_8238493 : Nat := 4983230072969 + 3 ^ 40 * 8238493 * 2
def baseEnd_8238493 : Nat := 4230306777701540591949367

theorem tailTrace_8238493 : CollatzResearch.WordTrace tailWord_8238493 prefixEnd_8238493 4230306777701540591949367 := by
  unfold tailWord_8238493
  simp only [CollatzResearch.WordTrace]
  refine ⟨300482525342354358430720133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200321683561569572287146755 300482525342354358430720133)
  ·
    refine ⟨56340473501691442205760025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300482525342354358430720133 56340473501691442205760025)
    ·
      refine ⟨42255355126268581654320019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56340473501691442205760025 42255355126268581654320019)
      ·
        refine ⟨63383032689402872481480029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255355126268581654320019 63383032689402872481480029)
        ·
          refine ⟨23768637258526077180555011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63383032689402872481480029 23768637258526077180555011)
          ·
            refine ⟨35652955887789115770832517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23768637258526077180555011 35652955887789115770832517)
            ·
              refine ⟨6684929228960459207031097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35652955887789115770832517 6684929228960459207031097)
              ·
                refine ⟨5013696921720344405273323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684929228960459207031097 5013696921720344405273323)
                ·
                  refine ⟨7520545382580516607909985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013696921720344405273323 7520545382580516607909985)
                  ·
                    refine ⟨5640409036935387455932489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520545382580516607909985 5640409036935387455932489)
                    ·
                      refine ⟨4230306777701540591949367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640409036935387455932489 4230306777701540591949367)
                      ·
                        rfl

theorem cell23_8238493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_8238493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238493 prefixEnd_8238493 := by exact prefixLift 8238493
  have htrace : WordTrace (prefixWord ++ tailWord_8238493) baseStart_8238493 baseEnd_8238493 := by
    simpa [prefixWord, tailWord_8238493, baseEnd_8238493] using wordTrace_append hprefix tailTrace_8238493
  have hstable : (prefixWord ++ tailWord_8238493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238493).length < 2 ^ (prefixWord ++ tailWord_8238493).sum := by decide
  have hdescent : baseEnd_8238493 < baseStart_8238493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238508 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_8238508 : Nat := 118140960795 + 8238508 * 2 ^ 59
def prefixEnd_8238508 : Nat := 4983230072969 + 3 ^ 40 * 8238508 * 2
def baseEnd_8238508 : Nat := 1410104826637119344420599

theorem tailTrace_8238508 : CollatzResearch.WordTrace tailWord_8238508 prefixEnd_8238508 1410104826637119344420599 := by
  unfold tailWord_8238508
  simp only [CollatzResearch.WordTrace]
  refine ⟨150241536218650007996258089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200322048291533343995010785 150241536218650007996258089)
  ·
    refine ⟨112681152163987505997193567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150241536218650007996258089 112681152163987505997193567)
    ·
      refine ⟨169021728245981258995790351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112681152163987505997193567 169021728245981258995790351)
      ·
        refine ⟨253532592368971888493685527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169021728245981258995790351 253532592368971888493685527)
        ·
          refine ⟨380298888553457832740528291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253532592368971888493685527 380298888553457832740528291)
          ·
            refine ⟨570448332830186749110792437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380298888553457832740528291 570448332830186749110792437)
            ·
              refine ⟨53479531202830007729136791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 570448332830186749110792437 53479531202830007729136791)
              ·
                refine ⟨80219296804245011593705187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53479531202830007729136791 80219296804245011593705187)
                ·
                  refine ⟨120328945206367517390557781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80219296804245011593705187 120328945206367517390557781)
                  ·
                    refine ⟨1410104826637119344420599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120328945206367517390557781 1410104826637119344420599)
                    ·
                      rfl

theorem cell23_8238508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_8238508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238508 prefixEnd_8238508 := by exact prefixLift 8238508
  have htrace : WordTrace (prefixWord ++ tailWord_8238508) baseStart_8238508 baseEnd_8238508 := by
    simpa [prefixWord, tailWord_8238508, baseEnd_8238508] using wordTrace_append hprefix tailTrace_8238508
  have hstable : (prefixWord ++ tailWord_8238508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238508).length < 2 ^ (prefixWord ++ tailWord_8238508).sum := by decide
  have hdescent : baseEnd_8238508 < baseStart_8238508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238509 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_8238509 : Nat := 118140960795 + 8238509 * 2 ^ 59
def prefixEnd_8238509 : Nat := 4983230072969 + 3 ^ 40 * 8238509 * 2
def baseEnd_8238509 : Nat := 4230314993392012529349293

theorem tailTrace_8238509 : CollatzResearch.WordTrace tailWord_8238509 prefixEnd_8238509 4230314993392012529349293 := by
  unfold tailWord_8238509
  simp only [CollatzResearch.WordTrace]
  refine ⟨300483108910296393163302581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200322072606864262108868387 300483108910296393163302581)
  ·
    refine ⟨28170291460340286859059617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300483108910296393163302581 28170291460340286859059617)
    ·
      refine ⟨21127718595255215144294713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28170291460340286859059617 21127718595255215144294713)
      ·
        refine ⟨15845788946441411358221035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21127718595255215144294713 15845788946441411358221035)
        ·
          refine ⟨23768683419662117037331553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15845788946441411358221035 23768683419662117037331553)
          ·
            refine ⟨17826512564746587777998665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23768683419662117037331553 17826512564746587777998665)
            ·
              refine ⟨13369884423559940833498999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17826512564746587777998665 13369884423559940833498999)
              ·
                refine ⟨20054826635339911250248499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13369884423559940833498999 20054826635339911250248499)
                ·
                  refine ⟨30082239953009866875372749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20054826635339911250248499 30082239953009866875372749)
                  ·
                    refine ⟨11280839982378700078264781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30082239953009866875372749 11280839982378700078264781)
                    ·
                      refine ⟨4230314993392012529349293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280839982378700078264781 4230314993392012529349293)
                      ·
                        rfl

theorem cell23_8238509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_8238509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238509 prefixEnd_8238509 := by exact prefixLift 8238509
  have htrace : WordTrace (prefixWord ++ tailWord_8238509) baseStart_8238509 baseEnd_8238509 := by
    simpa [prefixWord, tailWord_8238509, baseEnd_8238509] using wordTrace_append hprefix tailTrace_8238509
  have hstable : (prefixWord ++ tailWord_8238509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238509).length < 2 ^ (prefixWord ++ tailWord_8238509).sum := by decide
  have hdescent : baseEnd_8238509 < baseStart_8238509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238530 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8238530 : Nat := 118140960795 + 8238530 * 2 ^ 59
def prefixEnd_8238530 : Nat := 4983230072969 + 3 ^ 40 * 8238530 * 2
def baseEnd_8238530 : Nat := 4230325776485756947186697

theorem tailTrace_8238530 : CollatzResearch.WordTrace tailWord_8238530 prefixEnd_8238530 4230325776485756947186697 := by
  unfold tailWord_8238530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120968710805078437454261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200322583228813542499878029 75120968710805078437454261)
  ·
    refine ⟨7042590816637976103511337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75120968710805078437454261 7042590816637976103511337)
    ·
      refine ⟨5281943112478482077633503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7042590816637976103511337 5281943112478482077633503)
      ·
        refine ⟨7922914668717723116450255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281943112478482077633503 7922914668717723116450255)
        ·
          refine ⟨11884372003076584674675383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922914668717723116450255 11884372003076584674675383)
          ·
            refine ⟨17826558004614877012013075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884372003076584674675383 17826558004614877012013075)
            ·
              refine ⟨26739837006922315518019613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826558004614877012013075 26739837006922315518019613)
              ·
                refine ⟨10027438877595868319257355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26739837006922315518019613 10027438877595868319257355)
                ·
                  refine ⟨15041158316393802478886033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10027438877595868319257355 15041158316393802478886033)
                  ·
                    refine ⟨11280868737295351859164525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15041158316393802478886033 11280868737295351859164525)
                    ·
                      refine ⟨4230325776485756947186697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11280868737295351859164525 4230325776485756947186697)
                      ·
                        rfl

theorem cell23_8238530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8238530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238530 prefixEnd_8238530 := by exact prefixLift 8238530
  have htrace : WordTrace (prefixWord ++ tailWord_8238530) baseStart_8238530 baseEnd_8238530 := by
    simpa [prefixWord, tailWord_8238530, baseEnd_8238530] using wordTrace_append hprefix tailTrace_8238530
  have hstable : (prefixWord ++ tailWord_8238530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238530).length < 2 ^ (prefixWord ++ tailWord_8238530).sum := by decide
  have hdescent : baseEnd_8238530 < baseStart_8238530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238549 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_8238549 : Nat := 118140960795 + 8238549 * 2 ^ 59
def prefixEnd_8238549 : Nat := 4983230072969 + 3 ^ 40 * 8238549 * 2
def baseEnd_8238549 : Nat := 4230335532618192372849109

theorem tailTrace_8238549 : CollatzResearch.WordTrace tailWord_8238549 prefixEnd_8238549 4230335532618192372849109 := by
  unfold tailWord_8238549
  simp only [CollatzResearch.WordTrace]
  refine ⟨300484567830151479994758701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200323045220100986663172467 300484567830151479994758701)
  ·
    refine ⟨112681712936306804998034513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300484567830151479994758701 112681712936306804998034513)
    ·
      refine ⟨84511284702230103748525885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112681712936306804998034513 84511284702230103748525885)
      ·
        refine ⟨31691731763336288905697207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84511284702230103748525885 31691731763336288905697207)
        ·
          refine ⟨47537597645004433358545811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31691731763336288905697207 47537597645004433358545811)
          ·
            refine ⟨71306396467506650037818717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47537597645004433358545811 71306396467506650037818717)
            ·
              refine ⟨26739898675314993764182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71306396467506650037818717 26739898675314993764182019)
              ·
                refine ⟨40109848012972490646273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26739898675314993764182019 40109848012972490646273029)
                ·
                  refine ⟨7520596502432341996176193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40109848012972490646273029 7520596502432341996176193)
                  ·
                    refine ⟨5640447376824256497132145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520596502432341996176193 5640447376824256497132145)
                    ·
                      refine ⟨4230335532618192372849109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5640447376824256497132145 4230335532618192372849109)
                      ·
                        rfl

theorem cell23_8238549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_8238549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238549 prefixEnd_8238549 := by exact prefixLift 8238549
  have htrace : WordTrace (prefixWord ++ tailWord_8238549) baseStart_8238549 baseEnd_8238549 := by
    simpa [prefixWord, tailWord_8238549, baseEnd_8238549] using wordTrace_append hprefix tailTrace_8238549
  have hstable : (prefixWord ++ tailWord_8238549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238549).length < 2 ^ (prefixWord ++ tailWord_8238549).sum := by decide
  have hdescent : baseEnd_8238549 < baseStart_8238549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238585 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_8238585 : Nat := 118140960795 + 8238585 * 2 ^ 59
def prefixEnd_8238585 : Nat := 4983230072969 + 3 ^ 40 * 8238585 * 2
def baseEnd_8238585 : Nat := 1410118005973918077332981

theorem tailTrace_8238585 : CollatzResearch.WordTrace tailWord_8238585 prefixEnd_8238585 1410118005973918077332981 := by
  unfold tailWord_8238585
  simp only [CollatzResearch.WordTrace]
  refine ⟨300485880858021058143069209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200323920572014038762046139 300485880858021058143069209)
  ·
    refine ⟨225364410643515793607301907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300485880858021058143069209 225364410643515793607301907)
    ·
      refine ⟨338046615965273690410952861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225364410643515793607301907 338046615965273690410952861)
      ·
        refine ⟨126767480986977633904107323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338046615965273690410952861 126767480986977633904107323)
        ·
          refine ⟨190151221480466450856160985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126767480986977633904107323 190151221480466450856160985)
          ·
            refine ⟨142613416110349838142120739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190151221480466450856160985 142613416110349838142120739)
            ·
              refine ⟨213920124165524757213181109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142613416110349838142120739 213920124165524757213181109)
              ·
                refine ⟨20055011640517945988735729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213920124165524757213181109 20055011640517945988735729)
                ·
                  refine ⟨15041258730388459491551797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20055011640517945988735729 15041258730388459491551797)
                  ·
                    refine ⟨1410118005973918077332981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15041258730388459491551797 1410118005973918077332981)
                    ·
                      rfl

theorem cell23_8238585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_8238585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238585 prefixEnd_8238585 := by exact prefixLift 8238585
  have htrace : WordTrace (prefixWord ++ tailWord_8238585) baseStart_8238585 baseEnd_8238585 := by
    simpa [prefixWord, tailWord_8238585, baseEnd_8238585] using wordTrace_append hprefix tailTrace_8238585
  have hstable : (prefixWord ++ tailWord_8238585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238585).length < 2 ^ (prefixWord ++ tailWord_8238585).sum := by decide
  have hdescent : baseEnd_8238585 < baseStart_8238585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238589 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 5]
def baseStart_8238589 : Nat := 118140960795 + 8238589 * 2 ^ 59
def prefixEnd_8238589 : Nat := 4983230072969 + 3 ^ 40 * 8238589 * 2
def baseEnd_8238589 : Nat := 470039563538263579594325

theorem tailTrace_8238589 : CollatzResearch.WordTrace tailWord_8238589 prefixEnd_8238589 470039563538263579594325 := by
  unfold tailWord_8238589
  simp only [CollatzResearch.WordTrace]
  refine ⟨300486026750006566826214821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200324017833337711217476547 300486026750006566826214821)
  ·
    refine ⟨56341130015626231279915279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300486026750006566826214821 56341130015626231279915279)
    ·
      refine ⟨84511695023439346919872919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56341130015626231279915279 84511695023439346919872919)
      ·
        refine ⟨126767542535159020379809379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84511695023439346919872919 126767542535159020379809379)
        ·
          refine ⟨190151313802738530569714069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126767542535159020379809379 190151313802738530569714069)
          ·
            refine ⟨8913342834503368620455347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190151313802738530569714069 8913342834503368620455347)
            ·
              refine ⟨13370014251755052930683021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913342834503368620455347 13370014251755052930683021)
              ·
                refine ⟨5013755344408144849006133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13370014251755052930683021 5013755344408144849006133)
                ·
                  refine ⟨470039563538263579594325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013755344408144849006133 470039563538263579594325)
                  ·
                    rfl

theorem cell23_8238589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_8238589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238589 prefixEnd_8238589 := by exact prefixLift 8238589
  have htrace : WordTrace (prefixWord ++ tailWord_8238589) baseStart_8238589 baseEnd_8238589 := by
    simpa [prefixWord, tailWord_8238589, baseEnd_8238589] using wordTrace_append hprefix tailTrace_8238589
  have hstable : (prefixWord ++ tailWord_8238589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238589).length < 2 ^ (prefixWord ++ tailWord_8238589).sum := by decide
  have hdescent : baseEnd_8238589 < baseStart_8238589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238602 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_8238602 : Nat := 118140960795 + 8238602 * 2 ^ 59
def prefixEnd_8238602 : Nat := 4983230072969 + 3 ^ 40 * 8238602 * 2
def baseEnd_8238602 : Nat := 1410120915697626888495455

theorem tailTrace_8238602 : CollatzResearch.WordTrace tailWord_8238602 prefixEnd_8238602 1410120915697626888495455 := by
  unfold tailWord_8238602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75121625224739867511609515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200324333932639646697625373 75121625224739867511609515)
  ·
    refine ⟨112682437837109801267414273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75121625224739867511609515 112682437837109801267414273)
    ·
      refine ⟨84511828377832350950560705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112682437837109801267414273 84511828377832350950560705)
      ·
        refine ⟨63383871283374263212920529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84511828377832350950560705 63383871283374263212920529)
        ·
          refine ⟨47537903462530697409690397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63383871283374263212920529 47537903462530697409690397)
          ·
            refine ⟨17826713798449011528633899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47537903462530697409690397 17826713798449011528633899)
            ·
              refine ⟨26740070697673517292950849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826713798449011528633899 26740070697673517292950849)
              ·
                refine ⟨20055053023255137969713137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26740070697673517292950849 20055053023255137969713137)
                ·
                  refine ⟨15041289767441353477284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20055053023255137969713137 15041289767441353477284853)
                  ·
                    refine ⟨1410120915697626888495455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15041289767441353477284853 1410120915697626888495455)
                    ·
                      rfl

theorem cell23_8238602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_8238602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238602 prefixEnd_8238602 := by exact prefixLift 8238602
  have htrace : WordTrace (prefixWord ++ tailWord_8238602) baseStart_8238602 baseEnd_8238602 := by
    simpa [prefixWord, tailWord_8238602, baseEnd_8238602] using wordTrace_append hprefix tailTrace_8238602
  have hstable : (prefixWord ++ tailWord_8238602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238602).length < 2 ^ (prefixWord ++ tailWord_8238602).sum := by decide
  have hdescent : baseEnd_8238602 < baseStart_8238602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238606 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_8238606 : Nat := 118140960795 + 8238606 * 2 ^ 59
def prefixEnd_8238606 : Nat := 4983230072969 + 3 ^ 40 * 8238606 * 2
def baseEnd_8238606 : Nat := 470040533446166516648483

theorem tailTrace_8238606 : CollatzResearch.WordTrace tailWord_8238606 prefixEnd_8238606 470040533446166516648483 := by
  unfold tailWord_8238606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560830848868122341197959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200324431193963319153055781 37560830848868122341197959)
  ·
    refine ⟨56341246273302183511796939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37560830848868122341197959 56341246273302183511796939)
    ·
      refine ⟨84511869409953275267695409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56341246273302183511796939 84511869409953275267695409)
      ·
        refine ⟨63383902057464956450771557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84511869409953275267695409 63383902057464956450771557)
        ·
          refine ⟨11884481635774679334519667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63383902057464956450771557 11884481635774679334519667)
          ·
            refine ⟨17826722453662019001779501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884481635774679334519667 17826722453662019001779501)
            ·
              refine ⟨6685020920123257125667313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17826722453662019001779501 6685020920123257125667313)
              ·
                refine ⟨5013765690092442844250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685020920123257125667313 5013765690092442844250485)
                ·
                  refine ⟨470040533446166516648483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013765690092442844250485 470040533446166516648483)
                  ·
                    rfl

theorem cell23_8238606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_8238606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238606 prefixEnd_8238606 := by exact prefixLift 8238606
  have htrace : WordTrace (prefixWord ++ tailWord_8238606) baseStart_8238606 baseEnd_8238606 := by
    simpa [prefixWord, tailWord_8238606, baseEnd_8238606] using wordTrace_append hprefix tailTrace_8238606
  have hstable : (prefixWord ++ tailWord_8238606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238606).length < 2 ^ (prefixWord ++ tailWord_8238606).sum := by decide
  have hdescent : baseEnd_8238606 < baseStart_8238606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238689 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_8238689 : Nat := 118140960795 + 8238689 * 2 ^ 59
def prefixEnd_8238689 : Nat := 4983230072969 + 3 ^ 40 * 8238689 * 2
def baseEnd_8238689 : Nat := 4230407419909821825098465

theorem tailTrace_8238689 : CollatzResearch.WordTrace tailWord_8238689 prefixEnd_8238689 4230407419909821825098465 := by
  unfold tailWord_8238689
  simp only [CollatzResearch.WordTrace]
  refine ⟨300489674049644283904855121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200326449366429522603236747 300489674049644283904855121)
  ·
    refine ⟨225367255537233212928641341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300489674049644283904855121 225367255537233212928641341)
    ·
      refine ⟨84512720826462454848240503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225367255537233212928641341 84512720826462454848240503)
      ·
        refine ⟨126769081239693682272360755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84512720826462454848240503 126769081239693682272360755)
        ·
          refine ⟨190153621859540523408541133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126769081239693682272360755 190153621859540523408541133)
          ·
            refine ⟨71307608197327696278202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190153621859540523408541133 71307608197327696278202925)
            ·
              refine ⟨26740353073997886104326097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71307608197327696278202925 26740353073997886104326097)
              ·
                refine ⟨20055264805498414578244573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26740353073997886104326097 20055264805498414578244573)
                ·
                  refine ⟨7520724302061905466841715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20055264805498414578244573 7520724302061905466841715)
                  ·
                    refine ⟨11281086453092858200262573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7520724302061905466841715 11281086453092858200262573)
                    ·
                      refine ⟨4230407419909821825098465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11281086453092858200262573 4230407419909821825098465)
                      ·
                        rfl

theorem cell23_8238689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_8238689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238689 prefixEnd_8238689 := by exact prefixLift 8238689
  have htrace : WordTrace (prefixWord ++ tailWord_8238689) baseStart_8238689 baseEnd_8238689 := by
    simpa [prefixWord, tailWord_8238689, baseEnd_8238689] using wordTrace_append hprefix tailTrace_8238689
  have hstable : (prefixWord ++ tailWord_8238689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238689).length < 2 ^ (prefixWord ++ tailWord_8238689).sum := by decide
  have hdescent : baseEnd_8238689 < baseStart_8238689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238692 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_8238692 : Nat := 118140960795 + 8238692 * 2 ^ 59
def prefixEnd_8238692 : Nat := 4983230072969 + 3 ^ 40 * 8238692 * 2
def baseEnd_8238692 : Nat := 1410136320117261771120317

theorem tailTrace_8238692 : CollatzResearch.WordTrace tailWord_8238692 prefixEnd_8238692 1410136320117261771120317 := by
  unfold tailWord_8238692
  simp only [CollatzResearch.WordTrace]
  refine ⟨150244891734316707708607165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200326522312422276944809553 150244891734316707708607165)
  ·
    refine ⟨56341834400368765390727687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150244891734316707708607165 56341834400368765390727687)
    ·
      refine ⟨84512751600553148086091531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56341834400368765390727687 84512751600553148086091531)
      ·
        refine ⟨126769127400829722129137297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84512751600553148086091531 126769127400829722129137297)
        ·
          refine ⟨95076845550622291596852973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126769127400829722129137297 95076845550622291596852973)
          ·
            refine ⟨35653817081483359348819865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95076845550622291596852973 35653817081483359348819865)
            ·
              refine ⟨26740362811112519511614899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35653817081483359348819865 26740362811112519511614899)
              ·
                refine ⟨40110544216668779267422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26740362811112519511614899 40110544216668779267422349)
                ·
                  refine ⟨15041454081250792225283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40110544216668779267422349 15041454081250792225283381)
                  ·
                    refine ⟨1410136320117261771120317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15041454081250792225283381 1410136320117261771120317)
                    ·
                      rfl

theorem cell23_8238692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_8238692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8238692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8238692 prefixEnd_8238692 := by exact prefixLift 8238692
  have htrace : WordTrace (prefixWord ++ tailWord_8238692) baseStart_8238692 baseEnd_8238692 := by
    simpa [prefixWord, tailWord_8238692, baseEnd_8238692] using wordTrace_append hprefix tailTrace_8238692
  have hstable : (prefixWord ++ tailWord_8238692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238692).length < 2 ^ (prefixWord ++ tailWord_8238692).sum := by decide
  have hdescent : baseEnd_8238692 < baseStart_8238692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
