import V185TrunkScan23Chunk1229

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7288580 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_7288580 : Nat := 118140960795 + 7288580 * 2 ^ 59
def prefixEnd_7288580 : Nat := 4983230072969 + 3 ^ 40 * 7288580 * 2
def baseEnd_7288580 : Nat := 3742544828747198630930437

theorem tailTrace_7288580 : CollatzResearch.WordTrace tailWord_7288580 prefixEnd_7288580 3742544828747198630930437 := by
  unfold tailWord_7288580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132918175967363462603143597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177224234623151283470858129 132918175967363462603143597)
  ·
    refine ⟨49844315987761298476178849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132918175967363462603143597 49844315987761298476178849)
    ·
      refine ⟨37383236990820973857134137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49844315987761298476178849 37383236990820973857134137)
      ·
        refine ⟨28037427743115730392850603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37383236990820973857134137 28037427743115730392850603)
        ·
          refine ⟨42056141614673595589275905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28037427743115730392850603 42056141614673595589275905)
          ·
            refine ⟨31542106211005196691956929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42056141614673595589275905 31542106211005196691956929)
            ·
              refine ⟨23656579658253897518967697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31542106211005196691956929 23656579658253897518967697)
              ·
                refine ⟨17742434743690423139225773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23656579658253897518967697 17742434743690423139225773)
                ·
                  refine ⟨6653413028883908677209665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17742434743690423139225773 6653413028883908677209665)
                  ·
                    refine ⟨4990059771662931507907249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653413028883908677209665 4990059771662931507907249)
                    ·
                      refine ⟨3742544828747198630930437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990059771662931507907249 3742544828747198630930437)
                      ·
                        rfl

theorem cell23_7288580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_7288580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288580 prefixEnd_7288580 := by exact prefixLift 7288580
  have htrace : WordTrace (prefixWord ++ tailWord_7288580) baseStart_7288580 baseEnd_7288580 := by
    simpa [prefixWord, tailWord_7288580, baseEnd_7288580] using wordTrace_append hprefix tailTrace_7288580
  have hstable : (prefixWord ++ tailWord_7288580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288580).length < 2 ^ (prefixWord ++ tailWord_7288580).sum := by decide
  have hdescent : baseEnd_7288580 < baseStart_7288580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288586 : List Nat := [3, 1, 2, 2, 1, 3, 4, 7]
def baseStart_7288586 : Nat := 118140960795 + 7288586 * 2 ^ 59
def prefixEnd_7288586 : Nat := 4983230072969 + 3 ^ 40 * 7288586 * 2
def baseEnd_7288586 : Nat := 138612885541893541016867

theorem tailTrace_7288586 : CollatzResearch.WordTrace tailWord_7288586 prefixEnd_7288586 138612885541893541016867 := by
  unfold tailWord_7288586
  simp only [CollatzResearch.WordTrace]
  refine ⟨66459142693176297057751403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177224380515136792154003741 66459142693176297057751403)
  ·
    refine ⟨99688714039764445586627105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66459142693176297057751403 99688714039764445586627105)
    ·
      refine ⟨74766535529823334189970329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99688714039764445586627105 74766535529823334189970329)
      ·
        refine ⟨56074901647367500642477747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74766535529823334189970329 56074901647367500642477747)
        ·
          refine ⟨84112352471051250963716621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56074901647367500642477747 84112352471051250963716621)
          ·
            refine ⟨31542132176644219111393733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84112352471051250963716621 31542132176644219111393733)
            ·
              refine ⟨5914149783120791083386325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31542132176644219111393733 5914149783120791083386325)
              ·
                refine ⟨138612885541893541016867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5914149783120791083386325 138612885541893541016867)
                ·
                  rfl

theorem cell23_7288586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_7288586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288586 prefixEnd_7288586 := by exact prefixLift 7288586
  have htrace : WordTrace (prefixWord ++ tailWord_7288586) baseStart_7288586 baseEnd_7288586 := by
    simpa [prefixWord, tailWord_7288586, baseEnd_7288586] using wordTrace_append hprefix tailTrace_7288586
  have hstable : (prefixWord ++ tailWord_7288586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288586).length < 2 ^ (prefixWord ++ tailWord_7288586).sum := by decide
  have hdescent : baseEnd_7288586 < baseStart_7288586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288597 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_7288597 : Nat := 118140960795 + 7288597 * 2 ^ 59
def prefixEnd_7288597 : Nat := 4983230072969 + 3 ^ 40 * 7288597 * 2
def baseEnd_7288597 : Nat := 3742553557918325064417859

theorem tailTrace_7288597 : CollatzResearch.WordTrace tailWord_7288597 prefixEnd_7288597 3742553557918325064417859 := by
  unfold tailWord_7288597
  simp only [CollatzResearch.WordTrace]
  refine ⟨265836971975665337109656045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177224647983776891406437363 265836971975665337109656045)
  ·
    refine ⟨99688864490874501416121017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265836971975665337109656045 99688864490874501416121017)
    ·
      refine ⟨74766648368155876062090763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99688864490874501416121017 74766648368155876062090763)
      ·
        refine ⟨112149972552233814093136145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74766648368155876062090763 112149972552233814093136145)
        ·
          refine ⟨84112479414175360569852109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112149972552233814093136145 84112479414175360569852109)
          ·
            refine ⟨31542179780315760213694541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84112479414175360569852109 31542179780315760213694541)
            ·
              refine ⟨11828317417618410080135453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31542179780315760213694541 11828317417618410080135453)
              ·
                refine ⟨4435619031606903780050795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11828317417618410080135453 4435619031606903780050795)
                ·
                  refine ⟨6653428547410355670076193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435619031606903780050795 6653428547410355670076193)
                  ·
                    refine ⟨4990071410557766752557145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653428547410355670076193 4990071410557766752557145)
                    ·
                      refine ⟨3742553557918325064417859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990071410557766752557145 3742553557918325064417859)
                      ·
                        rfl

theorem cell23_7288597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_7288597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288597 prefixEnd_7288597 := by exact prefixLift 7288597
  have htrace : WordTrace (prefixWord ++ tailWord_7288597) baseStart_7288597 baseEnd_7288597 := by
    simpa [prefixWord, tailWord_7288597, baseEnd_7288597] using wordTrace_append hprefix tailTrace_7288597
  have hstable : (prefixWord ++ tailWord_7288597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288597).length < 2 ^ (prefixWord ++ tailWord_7288597).sum := by decide
  have hdescent : baseEnd_7288597 < baseStart_7288597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288613 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_7288613 : Nat := 118140960795 + 7288613 * 2 ^ 59
def prefixEnd_7288613 : Nat := 4983230072969 + 3 ^ 40 * 7288613 * 2
def baseEnd_7288613 : Nat := 3742561773608797001817785

theorem tailTrace_7288613 : CollatzResearch.WordTrace tailWord_7288613 prefixEnd_7288613 3742561773608797001817785 := by
  unfold tailWord_7288613
  simp only [CollatzResearch.WordTrace]
  refine ⟨265837555543607371842238493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177225037029071581228158995 265837555543607371842238493)
  ·
    refine ⟨99689083328852764440839435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265837555543607371842238493 99689083328852764440839435)
    ·
      refine ⟨149533624993279146661259153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99689083328852764440839435 149533624993279146661259153)
      ·
        refine ⟨112150218744959359995944365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149533624993279146661259153 112150218744959359995944365)
        ·
          refine ⟨42056332029359759998479137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112150218744959359995944365 42056332029359759998479137)
          ·
            refine ⟨31542249022019819998859353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42056332029359759998479137 31542249022019819998859353)
            ·
              refine ⟨23656686766514864999144515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31542249022019819998859353 23656686766514864999144515)
              ·
                refine ⟨35485030149772297498716773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23656686766514864999144515 35485030149772297498716773)
                ·
                  refine ⟨6653443153082305781009395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35485030149772297498716773 6653443153082305781009395)
                  ·
                    refine ⟨9980164729623458671514093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6653443153082305781009395 9980164729623458671514093)
                    ·
                      refine ⟨3742561773608797001817785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980164729623458671514093 3742561773608797001817785)
                      ·
                        rfl

theorem cell23_7288613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_7288613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288613 prefixEnd_7288613 := by exact prefixLift 7288613
  have htrace : WordTrace (prefixWord ++ tailWord_7288613) baseStart_7288613 baseEnd_7288613 := by
    simpa [prefixWord, tailWord_7288613, baseEnd_7288613] using wordTrace_append hprefix tailTrace_7288613
  have hstable : (prefixWord ++ tailWord_7288613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288613).length < 2 ^ (prefixWord ++ tailWord_7288613).sum := by decide
  have hdescent : baseEnd_7288613 < baseStart_7288613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288657 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_7288657 : Nat := 118140960795 + 7288657 * 2 ^ 59
def prefixEnd_7288657 : Nat := 4983230072969 + 3 ^ 40 * 7288657 * 2
def baseEnd_7288657 : Nat := 3742584366757594829667583

theorem tailTrace_7288657 : CollatzResearch.WordTrace tailWord_7288657 prefixEnd_7288657 3742584366757594829667583 := by
  unfold tailWord_7288657
  simp only [CollatzResearch.WordTrace]
  refine ⟨265839160355447967356840225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177226106903631978237893483 265839160355447967356840225)
  ·
    refine ⟨199379370266585975517630169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265839160355447967356840225 199379370266585975517630169)
    ·
      refine ⟨149534527699939481638222627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199379370266585975517630169 149534527699939481638222627)
      ·
        refine ⟨224301791549909222457333941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149534527699939481638222627 224301791549909222457333941)
        ·
          refine ⟨21028292957803989605375057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224301791549909222457333941 21028292957803989605375057)
          ·
            refine ⟨15771219718352992204031293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21028292957803989605375057 15771219718352992204031293)
            ·
              refine ⟨5914207394382372076511735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15771219718352992204031293 5914207394382372076511735)
              ·
                refine ⟨8871311091573558114767603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914207394382372076511735 8871311091573558114767603)
                ·
                  refine ⟨13306966637360337172151405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871311091573558114767603 13306966637360337172151405)
                  ·
                    refine ⟨4990112489010126439556777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13306966637360337172151405 4990112489010126439556777)
                    ·
                      refine ⟨3742584366757594829667583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990112489010126439556777 3742584366757594829667583)
                      ·
                        rfl

theorem cell23_7288657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_7288657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288657 prefixEnd_7288657 := by exact prefixLift 7288657
  have htrace : WordTrace (prefixWord ++ tailWord_7288657) baseStart_7288657 baseEnd_7288657 := by
    simpa [prefixWord, tailWord_7288657, baseEnd_7288657] using wordTrace_append hprefix tailTrace_7288657
  have hstable : (prefixWord ++ tailWord_7288657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288657).length < 2 ^ (prefixWord ++ tailWord_7288657).sum := by decide
  have hdescent : baseEnd_7288657 < baseStart_7288657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288666 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_7288666 : Nat := 118140960795 + 7288666 * 2 ^ 59
def prefixEnd_7288666 : Nat := 4983230072969 + 3 ^ 40 * 7288666 * 2
def baseEnd_7288666 : Nat := 3742588988083485294455041

theorem tailTrace_7288666 : CollatzResearch.WordTrace tailWord_7288666 prefixEnd_7288666 3742588988083485294455041 := by
  unfold tailWord_7288666
  simp only [CollatzResearch.WordTrace]
  refine ⟨66459872153103840473479463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177226325741610241262611901 66459872153103840473479463)
  ·
    refine ⟨99689808229655760710219195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66459872153103840473479463 99689808229655760710219195)
    ·
      refine ⟨149534712344483641065328793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99689808229655760710219195 149534712344483641065328793)
      ·
        refine ⟨112151034258362730798996595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149534712344483641065328793 112151034258362730798996595)
        ·
          refine ⟨168226551387544096198494893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112151034258362730798996595 168226551387544096198494893)
          ·
            refine ⟨63084956770329036074435585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168226551387544096198494893 63084956770329036074435585)
            ·
              refine ⟨47313717577746777055826689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63084956770329036074435585 47313717577746777055826689)
              ·
                refine ⟨35485288183310082791870017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47313717577746777055826689 35485288183310082791870017)
                ·
                  refine ⟨26613966137482562093902513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35485288183310082791870017 26613966137482562093902513)
                  ·
                    refine ⟨19960474603111921570426885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26613966137482562093902513 19960474603111921570426885)
                    ·
                      refine ⟨3742588988083485294455041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19960474603111921570426885 3742588988083485294455041)
                      ·
                        rfl

theorem cell23_7288666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_7288666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288666 prefixEnd_7288666 := by exact prefixLift 7288666
  have htrace : WordTrace (prefixWord ++ tailWord_7288666) baseStart_7288666 baseEnd_7288666 := by
    simpa [prefixWord, tailWord_7288666, baseEnd_7288666] using wordTrace_append hprefix tailTrace_7288666
  have hstable : (prefixWord ++ tailWord_7288666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288666).length < 2 ^ (prefixWord ++ tailWord_7288666).sum := by decide
  have hdescent : baseEnd_7288666 < baseStart_7288666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288743 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7288743 : Nat := 118140960795 + 7288743 * 2 ^ 59
def prefixEnd_7288743 : Nat := 4983230072969 + 3 ^ 40 * 7288743 * 2
def baseEnd_7288743 : Nat := 3742628526093881493192187

theorem tailTrace_7288743 : CollatzResearch.WordTrace tailWord_7288743 prefixEnd_7288743 3742628526093881493192187 := by
  unfold tailWord_7288743
  simp only [CollatzResearch.WordTrace]
  refine ⟨265842297033136404044470883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177228198022090936029647255 265842297033136404044470883)
  ·
    refine ⟨398763445549704606066706325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265842297033136404044470883 398763445549704606066706325)
    ·
      refine ⟨18692036510142403409376859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 398763445549704606066706325 18692036510142403409376859)
      ·
        refine ⟨28038054765213605114065289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18692036510142403409376859 28038054765213605114065289)
        ·
          refine ⟨21028541073910203835548967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28038054765213605114065289 21028541073910203835548967)
          ·
            refine ⟨31542811610865305753323451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21028541073910203835548967 31542811610865305753323451)
            ·
              refine ⟨47314217416297958629985177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31542811610865305753323451 47314217416297958629985177)
              ·
                refine ⟨35485663062223468972488883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47314217416297958629985177 35485663062223468972488883)
                ·
                  refine ⟨53228494593335203458733325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35485663062223468972488883 53228494593335203458733325)
                  ·
                    refine ⟨19960685472500701297024997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53228494593335203458733325 19960685472500701297024997)
                    ·
                      refine ⟨3742628526093881493192187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19960685472500701297024997 3742628526093881493192187)
                      ·
                        rfl

theorem cell23_7288743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7288743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288743 prefixEnd_7288743 := by exact prefixLift 7288743
  have htrace : WordTrace (prefixWord ++ tailWord_7288743) baseStart_7288743 baseEnd_7288743 := by
    simpa [prefixWord, tailWord_7288743, baseEnd_7288743] using wordTrace_append hprefix tailTrace_7288743
  have hstable : (prefixWord ++ tailWord_7288743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288743).length < 2 ^ (prefixWord ++ tailWord_7288743).sum := by decide
  have hdescent : baseEnd_7288743 < baseStart_7288743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288780 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7288780 : Nat := 118140960795 + 7288780 * 2 ^ 59
def prefixEnd_7288780 : Nat := 4983230072969 + 3 ^ 40 * 7288780 * 2
def baseEnd_7288780 : Nat := 3742647524878097848429517

theorem tailTrace_7288780 : CollatzResearch.WordTrace tailWord_7288780 prefixEnd_7288780 3742647524878097848429517 := by
  unfold tailWord_7288780
  simp only [CollatzResearch.WordTrace]
  refine ⟨132921823267001179681783897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177229097689334906242378529 132921823267001179681783897)
  ·
    refine ⟨99691367450250884761337923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132921823267001179681783897 99691367450250884761337923)
    ·
      refine ⟨149537051175376327142006885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99691367450250884761337923 149537051175376327142006885)
      ·
        refine ⟨28038197095383061339126291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149537051175376327142006885 28038197095383061339126291)
        ·
          refine ⟨42057295643074592008689437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28038197095383061339126291 42057295643074592008689437)
          ·
            refine ⟨15771485866152972003258539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42057295643074592008689437 15771485866152972003258539)
            ·
              refine ⟨23657228799229458004887809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15771485866152972003258539 23657228799229458004887809)
              ·
                refine ⟨17742921599422093503665857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23657228799229458004887809 17742921599422093503665857)
                ·
                  refine ⟨13307191199566570127749393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17742921599422093503665857 13307191199566570127749393)
                  ·
                    refine ⟨9980393399674927595812045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13307191199566570127749393 9980393399674927595812045)
                    ·
                      refine ⟨3742647524878097848429517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980393399674927595812045 3742647524878097848429517)
                      ·
                        rfl

theorem cell23_7288780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7288780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288780 prefixEnd_7288780 := by exact prefixLift 7288780
  have htrace : WordTrace (prefixWord ++ tailWord_7288780) baseStart_7288780 baseEnd_7288780 := by
    simpa [prefixWord, tailWord_7288780, baseEnd_7288780] using wordTrace_append hprefix tailTrace_7288780
  have hstable : (prefixWord ++ tailWord_7288780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288780).length < 2 ^ (prefixWord ++ tailWord_7288780).sum := by decide
  have hdescent : baseEnd_7288780 < baseStart_7288780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288810 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_7288810 : Nat := 118140960795 + 7288810 * 2 ^ 59
def prefixEnd_7288810 : Nat := 4983230072969 + 3 ^ 40 * 7288810 * 2
def baseEnd_7288810 : Nat := 3742662929297732731054379

theorem tailTrace_7288810 : CollatzResearch.WordTrace tailWord_7288810 prefixEnd_7288810 3742662929297732731054379 := by
  unfold tailWord_7288810
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461185180973418621789971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177229827149262449658106589 66461185180973418621789971)
  ·
    refine ⟨99691777771460127932684957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66461185180973418621789971 99691777771460127932684957)
    ·
      refine ⟨37384416664297547974756859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99691777771460127932684957 37384416664297547974756859)
      ·
        refine ⟨56076624996446321962135289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37384416664297547974756859 56076624996446321962135289)
        ·
          refine ⟨42057468747334741471601467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56076624996446321962135289 42057468747334741471601467)
          ·
            refine ⟨63086203121002112207402201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42057468747334741471601467 63086203121002112207402201)
            ·
              refine ⟨47314652340751584155551651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63086203121002112207402201 47314652340751584155551651)
              ·
                refine ⟨70971978511127376233327477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47314652340751584155551651 70971978511127376233327477)
                ·
                  refine ⟨6653622985418191521874451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70971978511127376233327477 6653622985418191521874451)
                  ·
                    refine ⟨9980434478127287282811677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6653622985418191521874451 9980434478127287282811677)
                    ·
                      refine ⟨3742662929297732731054379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980434478127287282811677 3742662929297732731054379)
                      ·
                        rfl

theorem cell23_7288810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_7288810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288810 prefixEnd_7288810 := by exact prefixLift 7288810
  have htrace : WordTrace (prefixWord ++ tailWord_7288810) baseStart_7288810 baseEnd_7288810 := by
    simpa [prefixWord, tailWord_7288810, baseEnd_7288810] using wordTrace_append hprefix tailTrace_7288810
  have hstable : (prefixWord ++ tailWord_7288810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288810).length < 2 ^ (prefixWord ++ tailWord_7288810).sum := by decide
  have hdescent : baseEnd_7288810 < baseStart_7288810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288860 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7288860 : Nat := 118140960795 + 7288860 * 2 ^ 59
def prefixEnd_7288860 : Nat := 4983230072969 + 3 ^ 40 * 7288860 * 2
def baseEnd_7288860 : Nat := 1247562867776819178476383

theorem tailTrace_7288860 : CollatzResearch.WordTrace tailWord_7288860 prefixEnd_7288860 1247562867776819178476383 := by
  unfold tailWord_7288860
  simp only [CollatzResearch.WordTrace]
  refine ⟨132923282186856266513240017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177231042915808355350986689 132923282186856266513240017)
  ·
    refine ⟨99692461640142199884930013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132923282186856266513240017 99692461640142199884930013)
    ·
      refine ⟨37384673115053324956848755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99692461640142199884930013 37384673115053324956848755)
      ·
        refine ⟨56077009672579987435273133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37384673115053324956848755 56077009672579987435273133)
        ·
          refine ⟨21028878627217495288227425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56077009672579987435273133 21028878627217495288227425)
          ·
            refine ⟨15771658970413121466170569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21028878627217495288227425 15771658970413121466170569)
            ·
              refine ⟨11828744227809841099627927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15771658970413121466170569 11828744227809841099627927)
              ·
                refine ⟨17743116341714761649441891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828744227809841099627927 17743116341714761649441891)
                ·
                  refine ⟨26614674512572142474162837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17743116341714761649441891 26614674512572142474162837)
                  ·
                    refine ⟨1247562867776819178476383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26614674512572142474162837 1247562867776819178476383)
                    ·
                      rfl

theorem cell23_7288860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7288860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288860 prefixEnd_7288860 := by exact prefixLift 7288860
  have htrace : WordTrace (prefixWord ++ tailWord_7288860) baseStart_7288860 baseEnd_7288860 := by
    simpa [prefixWord, tailWord_7288860, baseEnd_7288860] using wordTrace_append hprefix tailTrace_7288860
  have hstable : (prefixWord ++ tailWord_7288860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288860).length < 2 ^ (prefixWord ++ tailWord_7288860).sum := by decide
  have hdescent : baseEnd_7288860 < baseStart_7288860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288867 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 3, 2, 2]
def baseStart_7288867 : Nat := 118140960795 + 7288867 * 2 ^ 59
def prefixEnd_7288867 : Nat := 4983230072969 + 3 ^ 40 * 7288867 * 2
def baseEnd_7288867 : Nat := 3742692197695039008041617

theorem tailTrace_7288867 : CollatzResearch.WordTrace tailWord_7288867 prefixEnd_7288867 3742692197695039008041617 := by
  unfold tailWord_7288867
  simp only [CollatzResearch.WordTrace]
  refine ⟨265846819684687173221984855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177231213123124782147989903 265846819684687173221984855)
  ·
    refine ⟨398770229527030759832977283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265846819684687173221984855 398770229527030759832977283)
    ·
      refine ⟨598155344290546139749465925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398770229527030759832977283 598155344290546139749465925)
      ·
        refine ⟨112154127054477401203024861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598155344290546139749465925 112154127054477401203024861)
        ·
          refine ⟨42057797645429025451134323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112154127054477401203024861 42057797645429025451134323)
          ·
            refine ⟨63086696468143538176701485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42057797645429025451134323 63086696468143538176701485)
            ·
              refine ⟨23657511175553826816263057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63086696468143538176701485 23657511175553826816263057)
              ·
                refine ⟨17743133381665370112197293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23657511175553826816263057 17743133381665370112197293)
                ·
                  refine ⟨6653675018124513792073985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17743133381665370112197293 6653675018124513792073985)
                  ·
                    refine ⟨4990256263593385344055489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653675018124513792073985 4990256263593385344055489)
                    ·
                      refine ⟨3742692197695039008041617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990256263593385344055489 3742692197695039008041617)
                      ·
                        rfl

theorem cell23_7288867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_7288867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288867 prefixEnd_7288867 := by exact prefixLift 7288867
  have htrace : WordTrace (prefixWord ++ tailWord_7288867) baseStart_7288867 baseEnd_7288867 := by
    simpa [prefixWord, tailWord_7288867, baseEnd_7288867] using wordTrace_append hprefix tailTrace_7288867
  have hstable : (prefixWord ++ tailWord_7288867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288867).length < 2 ^ (prefixWord ++ tailWord_7288867).sum := by decide
  have hdescent : baseEnd_7288867 < baseStart_7288867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288871 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7288871 : Nat := 118140960795 + 7288871 * 2 ^ 59
def prefixEnd_7288871 : Nat := 4983230072969 + 3 ^ 40 * 7288871 * 2
def baseEnd_7288871 : Nat := 3742694251617656992391599

theorem tailTrace_7288871 : CollatzResearch.WordTrace tailWord_7288871 prefixEnd_7288871 3742694251617656992391599 := by
  unfold tailWord_7288871
  simp only [CollatzResearch.WordTrace]
  refine ⟨265846965576672681905130467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177231310384448454603420311 265846965576672681905130467)
  ·
    refine ⟨398770448365009022857695701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265846965576672681905130467 398770448365009022857695701)
    ·
      refine ⟨9346182383554898973227243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 398770448365009022857695701 9346182383554898973227243)
      ·
        refine ⟨14019273575332348459840865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346182383554898973227243 14019273575332348459840865)
        ·
          refine ⟨10514455181499261344880649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019273575332348459840865 10514455181499261344880649)
          ·
            refine ⟨7885841386124446008660487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10514455181499261344880649 7885841386124446008660487)
            ·
              refine ⟨11828762079186669012990731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885841386124446008660487 11828762079186669012990731)
              ·
                refine ⟨17743143118780003519486097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828762079186669012990731 17743143118780003519486097)
                ·
                  refine ⟨13307357339085002639614573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17743143118780003519486097 13307357339085002639614573)
                  ·
                    refine ⟨4990259002156875989855465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13307357339085002639614573 4990259002156875989855465)
                    ·
                      refine ⟨3742694251617656992391599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990259002156875989855465 3742694251617656992391599)
                      ·
                        rfl

theorem cell23_7288871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7288871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288871 prefixEnd_7288871 := by exact prefixLift 7288871
  have htrace : WordTrace (prefixWord ++ tailWord_7288871) baseStart_7288871 baseEnd_7288871 := by
    simpa [prefixWord, tailWord_7288871, baseEnd_7288871] using wordTrace_append hprefix tailTrace_7288871
  have hstable : (prefixWord ++ tailWord_7288871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288871).length < 2 ^ (prefixWord ++ tailWord_7288871).sum := by decide
  have hdescent : baseEnd_7288871 < baseStart_7288871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288884 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7288884 : Nat := 118140960795 + 7288884 * 2 ^ 59
def prefixEnd_7288884 : Nat := 4983230072969 + 3 ^ 40 * 7288884 * 2
def baseEnd_7288884 : Nat := 3742700926866165441529039

theorem tailTrace_7288884 : CollatzResearch.WordTrace tailWord_7288884 prefixEnd_7288884 3742700926866165441529039 := by
  unfold tailWord_7288884
  simp only [CollatzResearch.WordTrace]
  refine ⟨132923719862812792562676853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177231626483750390083569137 132923719862812792562676853)
  ·
    refine ⟨12461598737138699302750955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132923719862812792562676853 12461598737138699302750955)
    ·
      refine ⟨18692398105708048954126433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12461598737138699302750955 18692398105708048954126433)
      ·
        refine ⟨14019298579281036715594825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18692398105708048954126433 14019298579281036715594825)
        ·
          refine ⟨10514473934460777536696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019298579281036715594825 10514473934460777536696119)
          ·
            refine ⟨15771710901691166305044179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514473934460777536696119 15771710901691166305044179)
            ·
              refine ⟨23657566352536749457566269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15771710901691166305044179 23657566352536749457566269)
              ·
                refine ⟨8871587382201281046587351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23657566352536749457566269 8871587382201281046587351)
                ·
                  refine ⟨13307381073301921569881027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871587382201281046587351 13307381073301921569881027)
                  ·
                    refine ⟨19961071609952882354821541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13307381073301921569881027 19961071609952882354821541)
                    ·
                      refine ⟨3742700926866165441529039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19961071609952882354821541 3742700926866165441529039)
                      ·
                        rfl

theorem cell23_7288884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7288884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288884 prefixEnd_7288884 := by exact prefixLift 7288884
  have htrace : WordTrace (prefixWord ++ tailWord_7288884) baseStart_7288884 baseEnd_7288884 := by
    simpa [prefixWord, tailWord_7288884, baseEnd_7288884] using wordTrace_append hprefix tailTrace_7288884
  have hstable : (prefixWord ++ tailWord_7288884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288884).length < 2 ^ (prefixWord ++ tailWord_7288884).sum := by decide
  have hdescent : baseEnd_7288884 < baseStart_7288884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288887 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_7288887 : Nat := 118140960795 + 7288887 * 2 ^ 59
def prefixEnd_7288887 : Nat := 4983230072969 + 3 ^ 40 * 7288887 * 2
def baseEnd_7288887 : Nat := 3742702467308128929791525

theorem tailTrace_7288887 : CollatzResearch.WordTrace tailWord_7288887 prefixEnd_7288887 3742702467308128929791525 := by
  unfold tailWord_7288887
  simp only [CollatzResearch.WordTrace]
  refine ⟨265847549144614716637712915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177231699429743144425141943 265847549144614716637712915)
  ·
    refine ⟨398771323716922074956569373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265847549144614716637712915 398771323716922074956569373)
    ·
      refine ⟨149539246393845778108713515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398771323716922074956569373 149539246393845778108713515)
      ·
        refine ⟨224308869590768667163070273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149539246393845778108713515 224308869590768667163070273)
        ·
          refine ⟨168231652193076500372302705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224308869590768667163070273 168231652193076500372302705)
          ·
            refine ⟨126173739144807375279227029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168231652193076500372302705 126173739144807375279227029)
            ·
              refine ⟨5914394022412845716213767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126173739144807375279227029 5914394022412845716213767)
              ·
                refine ⟨8871591033619268574320651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914394022412845716213767 8871591033619268574320651)
                ·
                  refine ⟨13307386550428902861480977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871591033619268574320651 13307386550428902861480977)
                  ·
                    refine ⟨9980539912821677146110733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13307386550428902861480977 9980539912821677146110733)
                    ·
                      refine ⟨3742702467308128929791525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980539912821677146110733 3742702467308128929791525)
                      ·
                        rfl

theorem cell23_7288887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_7288887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288887 prefixEnd_7288887 := by exact prefixLift 7288887
  have htrace : WordTrace (prefixWord ++ tailWord_7288887) baseStart_7288887 baseEnd_7288887 := by
    simpa [prefixWord, tailWord_7288887, baseEnd_7288887] using wordTrace_append hprefix tailTrace_7288887
  have hstable : (prefixWord ++ tailWord_7288887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288887).length < 2 ^ (prefixWord ++ tailWord_7288887).sum := by decide
  have hdescent : baseEnd_7288887 < baseStart_7288887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288914 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_7288914 : Nat := 118140960795 + 7288914 * 2 ^ 59
def prefixEnd_7288914 : Nat := 4983230072969 + 3 ^ 40 * 7288914 * 2
def baseEnd_7288914 : Nat := 3742716331285800324153901

theorem tailTrace_7288914 : CollatzResearch.WordTrace tailWord_7288914 prefixEnd_7288914 3742716331285800324153901 := by
  unfold tailWord_7288914
  simp only [CollatzResearch.WordTrace]
  refine ⟨66462133478879225062236449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177232355943677933499297197 66462133478879225062236449)
  ·
    refine ⟨49846600109159418796677337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66462133478879225062236449 49846600109159418796677337)
    ·
      refine ⟨37384950081869564097508003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49846600109159418796677337 37384950081869564097508003)
      ·
        refine ⟨56077425122804346146262005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37384950081869564097508003 56077425122804346146262005)
        ·
          refine ⟨5257258605262907451212063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56077425122804346146262005 5257258605262907451212063)
          ·
            refine ⟨7885887907894361176818095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257258605262907451212063 7885887907894361176818095)
            ·
              refine ⟨11828831861841541765227143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885887907894361176818095 11828831861841541765227143)
              ·
                refine ⟨17743247792762312647840715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828831861841541765227143 17743247792762312647840715)
                ·
                  refine ⟨26614871689143468971761073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17743247792762312647840715 26614871689143468971761073)
                  ·
                    refine ⟨19961153766857601728820805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26614871689143468971761073 19961153766857601728820805)
                    ·
                      refine ⟨3742716331285800324153901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19961153766857601728820805 3742716331285800324153901)
                      ·
                        rfl

theorem cell23_7288914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_7288914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288914 prefixEnd_7288914 := by exact prefixLift 7288914
  have htrace : WordTrace (prefixWord ++ tailWord_7288914) baseStart_7288914 baseEnd_7288914 := by
    simpa [prefixWord, tailWord_7288914, baseEnd_7288914] using wordTrace_append hprefix tailTrace_7288914
  have hstable : (prefixWord ++ tailWord_7288914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288914).length < 2 ^ (prefixWord ++ tailWord_7288914).sum := by decide
  have hdescent : baseEnd_7288914 < baseStart_7288914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288917 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7288917 : Nat := 118140960795 + 7288917 * 2 ^ 59
def prefixEnd_7288917 : Nat := 4983230072969 + 3 ^ 40 * 7288917 * 2
def baseEnd_7288917 : Nat := 3742717871727763812416387

theorem tailTrace_7288917 : CollatzResearch.WordTrace tailWord_7288917 prefixEnd_7288917 3742717871727763812416387 := by
  unfold tailWord_7288917
  simp only [CollatzResearch.WordTrace]
  refine ⟨265848643334506031761305005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177232428889670687840870003 265848643334506031761305005)
  ·
    refine ⟨99693241250439761910489377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265848643334506031761305005 99693241250439761910489377)
    ·
      refine ⟨74769930937829821432867033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99693241250439761910489377 74769930937829821432867033)
      ·
        refine ⟨56077448203372366074650275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74769930937829821432867033 56077448203372366074650275)
        ·
          refine ⟨84116172305058549111975413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56077448203372366074650275 84116172305058549111975413)
          ·
            refine ⟨7885891153599238979247695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84116172305058549111975413 7885891153599238979247695)
            ·
              refine ⟨11828836730398858468871543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885891153599238979247695 11828836730398858468871543)
              ·
                refine ⟨17743255095598287703307315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828836730398858468871543 17743255095598287703307315)
                ·
                  refine ⟨26614882643397431554960973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17743255095598287703307315 26614882643397431554960973)
                  ·
                    refine ⟨9980580991274036833110365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26614882643397431554960973 9980580991274036833110365)
                    ·
                      refine ⟨3742717871727763812416387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980580991274036833110365 3742717871727763812416387)
                      ·
                        rfl

theorem cell23_7288917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7288917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288917 prefixEnd_7288917 := by exact prefixLift 7288917
  have htrace : WordTrace (prefixWord ++ tailWord_7288917) baseStart_7288917 baseEnd_7288917 := by
    simpa [prefixWord, tailWord_7288917, baseEnd_7288917] using wordTrace_append hprefix tailTrace_7288917
  have hstable : (prefixWord ++ tailWord_7288917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288917).length < 2 ^ (prefixWord ++ tailWord_7288917).sum := by decide
  have hdescent : baseEnd_7288917 < baseStart_7288917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288943 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_7288943 : Nat := 118140960795 + 7288943 * 2 ^ 59
def prefixEnd_7288943 : Nat := 4983230072969 + 3 ^ 40 * 7288943 * 2
def baseEnd_7288943 : Nat := 3742731222224780710691267

theorem tailTrace_7288943 : CollatzResearch.WordTrace tailWord_7288943 prefixEnd_7288943 3742731222224780710691267 := by
  unfold tailWord_7288943
  simp only [CollatzResearch.WordTrace]
  refine ⟨265849591632411838201751483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177233061088274558801167655 265849591632411838201751483)
  ·
    refine ⟨398774387448617757302627225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265849591632411838201751483 398774387448617757302627225)
    ·
      refine ⟨299080790586463317976970419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398774387448617757302627225 299080790586463317976970419)
      ·
        refine ⟨448621185879694976965455629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299080790586463317976970419 448621185879694976965455629)
        ·
          refine ⟨168232944704885616362045861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448621185879694976965455629 168232944704885616362045861)
          ·
            refine ⟨31543677132166053067883599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168232944704885616362045861 31543677132166053067883599)
            ·
              refine ⟨47315515698249079601825399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31543677132166053067883599 47315515698249079601825399)
              ·
                refine ⟨70973273547373619402738099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47315515698249079601825399 70973273547373619402738099)
                ·
                  refine ⟨106459910321060429104107149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70973273547373619402738099 106459910321060429104107149)
                  ·
                    refine ⟨39922466370397660914040181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106459910321060429104107149 39922466370397660914040181)
                    ·
                      refine ⟨3742731222224780710691267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39922466370397660914040181 3742731222224780710691267)
                      ·
                        rfl

theorem cell23_7288943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_7288943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288943 prefixEnd_7288943 := by exact prefixLift 7288943
  have htrace : WordTrace (prefixWord ++ tailWord_7288943) baseStart_7288943 baseEnd_7288943 := by
    simpa [prefixWord, tailWord_7288943, baseEnd_7288943] using wordTrace_append hprefix tailTrace_7288943
  have hstable : (prefixWord ++ tailWord_7288943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288943).length < 2 ^ (prefixWord ++ tailWord_7288943).sum := by decide
  have hdescent : baseEnd_7288943 < baseStart_7288943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289010 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_7289010 : Nat := 118140960795 + 7289010 * 2 ^ 59
def prefixEnd_7289010 : Nat := 4983230072969 + 3 ^ 40 * 7289010 * 2
def baseEnd_7289010 : Nat := 1247588541809543982851153

theorem tailTrace_7289010 : CollatzResearch.WordTrace tailWord_7289010 prefixEnd_7289010 1247588541809543982851153 := by
  unfold tailWord_7289010
  simp only [CollatzResearch.WordTrace]
  refine ⟨66463008830792277161110121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177234690215446072429626989 66463008830792277161110121)
  ·
    refine ⟨49847256623094207870832591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66463008830792277161110121 49847256623094207870832591)
    ·
      refine ⟨74770884934641311806248887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49847256623094207870832591 74770884934641311806248887)
      ·
        refine ⟨112156327401961967709373331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74770884934641311806248887 112156327401961967709373331)
        ·
          refine ⟨168234491102942951564059997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112156327401961967709373331 168234491102942951564059997)
          ·
            refine ⟨63087934163603606836522499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168234491102942951564059997 63087934163603606836522499)
            ·
              refine ⟨94631901245405410254783749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63087934163603606836522499 94631901245405410254783749)
              ·
                refine ⟨17743481483513514422771953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94631901245405410254783749 17743481483513514422771953)
                ·
                  refine ⟨13307611112635135817078965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17743481483513514422771953 13307611112635135817078965)
                  ·
                    refine ⟨1247588541809543982851153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13307611112635135817078965 1247588541809543982851153)
                    ·
                      rfl

theorem cell23_7289010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_7289010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289010 prefixEnd_7289010 := by exact prefixLift 7289010
  have htrace : WordTrace (prefixWord ++ tailWord_7289010) baseStart_7289010 baseEnd_7289010 := by
    simpa [prefixWord, tailWord_7289010, baseEnd_7289010] using wordTrace_append hprefix tailTrace_7289010
  have hstable : (prefixWord ++ tailWord_7289010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289010).length < 2 ^ (prefixWord ++ tailWord_7289010).sum := by decide
  have hdescent : baseEnd_7289010 < baseStart_7289010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289023 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 8]
def baseStart_7289023 : Nat := 118140960795 + 7289023 * 2 ^ 59
def prefixEnd_7289023 : Nat := 4983230072969 + 3 ^ 40 * 7289023 * 2
def baseEnd_7289023 : Nat := 1247590766892380132563633

theorem tailTrace_7289023 : CollatzResearch.WordTrace tailWord_7289023 prefixEnd_7289023 1247590766892380132563633 := by
  unfold tailWord_7289023
  simp only [CollatzResearch.WordTrace]
  refine ⟨265852509472122011864663723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177235006314748007909775815 265852509472122011864663723)
  ·
    refine ⟨398778764208183017796995585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265852509472122011864663723 398778764208183017796995585)
    ·
      refine ⟨299084073156137263347746689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398778764208183017796995585 299084073156137263347746689)
      ·
        refine ⟨224313054867102947510810017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299084073156137263347746689 224313054867102947510810017)
        ·
          refine ⟨168234791150327210633107513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224313054867102947510810017 168234791150327210633107513)
          ·
            refine ⟨126176093362745407974830635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168234791150327210633107513 126176093362745407974830635)
            ·
              refine ⟨189264140044118111962245953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126176093362745407974830635 189264140044118111962245953)
              ·
                refine ⟨141948105033088583971684465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189264140044118111962245953 141948105033088583971684465)
                ·
                  refine ⟨106461078774816437978763349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141948105033088583971684465 106461078774816437978763349)
                  ·
                    refine ⟨1247590766892380132563633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106461078774816437978763349 1247590766892380132563633)
                    ·
                      rfl

theorem cell23_7289023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_7289023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289023 prefixEnd_7289023 := by exact prefixLift 7289023
  have htrace : WordTrace (prefixWord ++ tailWord_7289023) baseStart_7289023 baseEnd_7289023 := by
    simpa [prefixWord, tailWord_7289023, baseEnd_7289023] using wordTrace_append hprefix tailTrace_7289023
  have hstable : (prefixWord ++ tailWord_7289023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289023).length < 2 ^ (prefixWord ++ tailWord_7289023).sum := by decide
  have hdescent : baseEnd_7289023 < baseStart_7289023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_7289043 : Nat := 118140960795 + 7289043 * 2 ^ 59
def prefixEnd_7289043 : Nat := 4983230072969 + 3 ^ 40 * 7289043 * 2
def baseEnd_7289043 : Nat := 3742782570290230319440807

theorem tailTrace_7289043 : CollatzResearch.WordTrace tailWord_7289043 prefixEnd_7289043 3742782570290230319440807 := by
  unfold tailWord_7289043
  simp only [CollatzResearch.WordTrace]
  refine ⟨265853238932049555280391783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177235492621366370186927855 265853238932049555280391783)
  ·
    refine ⟨398779858398074332920587675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265853238932049555280391783 398779858398074332920587675)
    ·
      refine ⟨598169787597111499380881513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398779858398074332920587675 598169787597111499380881513)
      ·
        refine ⟨448627340697833624535661135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598169787597111499380881513 448627340697833624535661135)
        ·
          refine ⟨672941011046750436803491703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448627340697833624535661135 672941011046750436803491703)
          ·
            refine ⟨1009411516570125655205237555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672941011046750436803491703 1009411516570125655205237555)
            ·
              refine ⟨1514117274855188482807856333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009411516570125655205237555 1514117274855188482807856333)
              ·
                refine ⟨567793978070695681052946125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514117274855188482807856333 567793978070695681052946125)
                ·
                  refine ⟨212922741776510880394854797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567793978070695681052946125 212922741776510880394854797)
                  ·
                    refine ⟨79846028166191580148070549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212922741776510880394854797 79846028166191580148070549)
                    ·
                      refine ⟨3742782570290230319440807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79846028166191580148070549 3742782570290230319440807)
                      ·
                        rfl

theorem cell23_7289043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_7289043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289043 prefixEnd_7289043 := by exact prefixLift 7289043
  have htrace : WordTrace (prefixWord ++ tailWord_7289043) baseStart_7289043 baseEnd_7289043 := by
    simpa [prefixWord, tailWord_7289043, baseEnd_7289043] using wordTrace_append hprefix tailTrace_7289043
  have hstable : (prefixWord ++ tailWord_7289043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289043).length < 2 ^ (prefixWord ++ tailWord_7289043).sum := by decide
  have hdescent : baseEnd_7289043 < baseStart_7289043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289074 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_7289074 : Nat := 118140960795 + 7289074 * 2 ^ 59
def prefixEnd_7289074 : Nat := 4983230072969 + 3 ^ 40 * 7289074 * 2
def baseEnd_7289074 : Nat := 1247599496063506566051055

theorem tailTrace_7289074 : CollatzResearch.WordTrace tailWord_7289074 prefixEnd_7289074 1247599496063506566051055 := by
  unfold tailWord_7289074
  simp only [CollatzResearch.WordTrace]
  refine ⟨66463592398734311893692569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177236246396624831716513517 66463592398734311893692569)
  ·
    refine ⟨49847694299050733920269427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66463592398734311893692569 49847694299050733920269427)
    ·
      refine ⟨74771541448576100880404141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49847694299050733920269427 74771541448576100880404141)
      ·
        refine ⟨28039328043216037830151553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74771541448576100880404141 28039328043216037830151553)
        ·
          refine ⟨21029496032412028372613665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28039328043216037830151553 21029496032412028372613665)
          ·
            refine ⟨15772122024309021279460249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21029496032412028372613665 15772122024309021279460249)
            ·
              refine ⟨11829091518231765959595187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15772122024309021279460249 11829091518231765959595187)
              ·
                refine ⟨17743637277347648939392781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11829091518231765959595187 17743637277347648939392781)
                ·
                  refine ⟨6653863979005368352272293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17743637277347648939392781 6653863979005368352272293)
                  ·
                    refine ⟨1247599496063506566051055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6653863979005368352272293 1247599496063506566051055)
                    ·
                      rfl

theorem cell23_7289074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_7289074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289074 prefixEnd_7289074 := by exact prefixLift 7289074
  have htrace : WordTrace (prefixWord ++ tailWord_7289074) baseStart_7289074 baseEnd_7289074 := by
    simpa [prefixWord, tailWord_7289074, baseEnd_7289074] using wordTrace_append hprefix tailTrace_7289074
  have hstable : (prefixWord ++ tailWord_7289074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289074).length < 2 ^ (prefixWord ++ tailWord_7289074).sum := by decide
  have hdescent : baseEnd_7289074 < baseStart_7289074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289087 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 6]
def baseStart_7289087 : Nat := 118140960795 + 7289087 * 2 ^ 59
def prefixEnd_7289087 : Nat := 4983230072969 + 3 ^ 40 * 7289087 * 2
def baseEnd_7289087 : Nat := 415867240382114238587845

theorem tailTrace_7289087 : CollatzResearch.WordTrace tailWord_7289087 prefixEnd_7289087 415867240382114238587845 := by
  unfold tailWord_7289087
  simp only [CollatzResearch.WordTrace]
  refine ⟨265854843743890150794993515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177236562495926767196662343 265854843743890150794993515)
  ·
    refine ⟨398782265615835226192490273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265854843743890150794993515 398782265615835226192490273)
    ·
      refine ⟨299086699211876419644367705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398782265615835226192490273 299086699211876419644367705)
      ·
        refine ⟨224315024408907314733275779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299086699211876419644367705 224315024408907314733275779)
        ·
          refine ⟨336472536613360972099913669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224315024408907314733275779 336472536613360972099913669)
          ·
            refine ⟨63088600615005182268733813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336472536613360972099913669 63088600615005182268733813)
            ·
              refine ⟨5914556307656735837693795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63088600615005182268733813 5914556307656735837693795)
              ·
                refine ⟨8871834461485103756540693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914556307656735837693795 8871834461485103756540693)
                ·
                  refine ⟨415867240382114238587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8871834461485103756540693 415867240382114238587845)
                  ·
                    rfl

theorem cell23_7289087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 6].length) (baseStart_7289087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289087 prefixEnd_7289087 := by exact prefixLift 7289087
  have htrace : WordTrace (prefixWord ++ tailWord_7289087) baseStart_7289087 baseEnd_7289087 := by
    simpa [prefixWord, tailWord_7289087, baseEnd_7289087] using wordTrace_append hprefix tailTrace_7289087
  have hstable : (prefixWord ++ tailWord_7289087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289087).length < 2 ^ (prefixWord ++ tailWord_7289087).sum := by decide
  have hdescent : baseEnd_7289087 < baseStart_7289087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 6, 3, 2]
def baseStart_7289107 : Nat := 118140960795 + 7289107 * 2 ^ 59
def prefixEnd_7289107 : Nat := 4983230072969 + 3 ^ 40 * 7289107 * 2
def baseEnd_7289107 : Nat := 3742815433052118069040513

theorem tailTrace_7289107 : CollatzResearch.WordTrace tailWord_7289107 prefixEnd_7289107 3742815433052118069040513 := by
  unfold tailWord_7289107
  simp only [CollatzResearch.WordTrace]
  refine ⟨265855573203817694210721575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177237048802545129473814383 265855573203817694210721575)
  ·
    refine ⟨398783359805726541316082363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265855573203817694210721575 398783359805726541316082363)
    ·
      refine ⟨598175039708589811974123545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398783359805726541316082363 598175039708589811974123545)
      ·
        refine ⟨448631279781442358980592659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598175039708589811974123545 448631279781442358980592659)
        ·
          refine ⟨672946919672163538470888989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448631279781442358980592659 672946919672163538470888989)
          ·
            refine ⟨252355094877061326926583371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672946919672163538470888989 252355094877061326926583371)
            ·
              refine ⟨378532642315591990389875057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252355094877061326926583371 378532642315591990389875057)
              ·
                refine ⟨283899481736693992792406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378532642315591990389875057 283899481736693992792406293)
                ·
                  refine ⟨13307788206407530912144045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283899481736693992792406293 13307788206407530912144045)
                  ·
                    refine ⟨4990420577402824092054017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13307788206407530912144045 4990420577402824092054017)
                    ·
                      refine ⟨3742815433052118069040513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990420577402824092054017 3742815433052118069040513)
                      ·
                        rfl

theorem cell23_7289107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3, 2].length) (baseStart_7289107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289107 prefixEnd_7289107 := by exact prefixLift 7289107
  have htrace : WordTrace (prefixWord ++ tailWord_7289107) baseStart_7289107 baseEnd_7289107 := by
    simpa [prefixWord, tailWord_7289107, baseEnd_7289107] using wordTrace_append hprefix tailTrace_7289107
  have hstable : (prefixWord ++ tailWord_7289107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289107).length < 2 ^ (prefixWord ++ tailWord_7289107).sum := by decide
  have hdescent : baseEnd_7289107 < baseStart_7289107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289124 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_7289124 : Nat := 118140960795 + 7289124 * 2 ^ 59
def prefixEnd_7289124 : Nat := 4983230072969 + 3 ^ 40 * 7289124 * 2
def baseEnd_7289124 : Nat := 3742824162223244502527935

theorem tailTrace_7289124 : CollatzResearch.WordTrace tailWord_7289124 prefixEnd_7289124 3742824162223244502527935 := by
  unfold tailWord_7289124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132928096622378053057045213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177237462163170737409393617 132928096622378053057045213)
  ·
    refine ⟨49848036233391769896391955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132928096622378053057045213 49848036233391769896391955)
    ·
      refine ⟨74772054350087654844587933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49848036233391769896391955 74772054350087654844587933)
      ·
        refine ⟨28039520381282870566720475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74772054350087654844587933 28039520381282870566720475)
        ·
          refine ⟨42059280571924305850080713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28039520381282870566720475 42059280571924305850080713)
          ·
            refine ⟨31544460428943229387560535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42059280571924305850080713 31544460428943229387560535)
            ·
              refine ⟨47316690643414844081340803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31544460428943229387560535 47316690643414844081340803)
              ·
                refine ⟨70975035965122266122011205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47316690643414844081340803 70975035965122266122011205)
                ·
                  refine ⟨13307819243460424897877101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70975035965122266122011205 13307819243460424897877101)
                  ·
                    refine ⟨4990432216297659336703913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13307819243460424897877101 4990432216297659336703913)
                    ·
                      refine ⟨3742824162223244502527935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990432216297659336703913 3742824162223244502527935)
                      ·
                        rfl

theorem cell23_7289124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_7289124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289124 prefixEnd_7289124 := by exact prefixLift 7289124
  have htrace : WordTrace (prefixWord ++ tailWord_7289124) baseStart_7289124 baseEnd_7289124 := by
    simpa [prefixWord, tailWord_7289124, baseEnd_7289124] using wordTrace_append hprefix tailTrace_7289124
  have hstable : (prefixWord ++ tailWord_7289124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289124).length < 2 ^ (prefixWord ++ tailWord_7289124).sum := by decide
  have hdescent : baseEnd_7289124 < baseStart_7289124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289160 : List Nat := [2, 1, 3, 1, 1, 2, 4, 9]
def baseStart_7289160 : Nat := 118140960795 + 7289160 * 2 ^ 59
def prefixEnd_7289160 : Nat := 4983230072969 + 3 ^ 40 * 7289160 * 2
def baseEnd_7289160 : Nat := 138623801760252087469547

theorem tailTrace_7289160 : CollatzResearch.WordTrace tailWord_7289160 prefixEnd_7289160 138623801760252087469547 := by
  unfold tailWord_7289160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132928753136312842131200467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177238337515083789508267289 132928753136312842131200467)
  ·
    refine ⟨199393129704469263196800701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132928753136312842131200467 199393129704469263196800701)
    ·
      refine ⟨74772423639175973698800263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199393129704469263196800701 74772423639175973698800263)
      ·
        refine ⟨112158635458763960548200395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74772423639175973698800263 112158635458763960548200395)
        ·
          refine ⟨168237953188145940822300593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112158635458763960548200395 168237953188145940822300593)
          ·
            refine ⟨126178464891109455616725445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168237953188145940822300593 126178464891109455616725445)
            ·
              refine ⟨23658462167083022928136021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126178464891109455616725445 23658462167083022928136021)
              ·
                refine ⟨138623801760252087469547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23658462167083022928136021 138623801760252087469547)
                ·
                  rfl

theorem cell23_7289160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 9].length) (baseStart_7289160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289160 prefixEnd_7289160 := by exact prefixLift 7289160
  have htrace : WordTrace (prefixWord ++ tailWord_7289160) baseStart_7289160 baseEnd_7289160 := by
    simpa [prefixWord, tailWord_7289160, baseEnd_7289160] using wordTrace_append hprefix tailTrace_7289160
  have hstable : (prefixWord ++ tailWord_7289160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289160).length < 2 ^ (prefixWord ++ tailWord_7289160).sum := by decide
  have hdescent : baseEnd_7289160 < baseStart_7289160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289187 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3]
def baseStart_7289187 : Nat := 118140960795 + 7289187 * 2 ^ 59
def prefixEnd_7289187 : Nat := 4983230072969 + 3 ^ 40 * 7289187 * 2
def baseEnd_7289187 : Nat := 3742856511504477756040145

theorem tailTrace_7289187 : CollatzResearch.WordTrace tailWord_7289187 prefixEnd_7289187 3742856511504477756040145 := by
  unfold tailWord_7289187
  simp only [CollatzResearch.WordTrace]
  refine ⟨265858491043527867873633815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177238994029018578582422543 265858491043527867873633815)
  ·
    refine ⟨398787736565291801810450723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265858491043527867873633815 398787736565291801810450723)
    ·
      refine ⟨598181604847937702715676085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398787736565291801810450723 598181604847937702715676085)
      ·
        refine ⟨56079525454494159629594633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598181604847937702715676085 56079525454494159629594633)
        ·
          refine ⟨42059644090870619722195975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56079525454494159629594633 42059644090870619722195975)
          ·
            refine ⟨63089466136305929583293963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42059644090870619722195975 63089466136305929583293963)
            ·
              refine ⟨94634199204458894374940945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63089466136305929583293963 94634199204458894374940945)
              ·
                refine ⟨70975649403344170781205709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94634199204458894374940945 70975649403344170781205709)
                ·
                  refine ⟨26615868526254064042952141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70975649403344170781205709 26615868526254064042952141)
                  ·
                    refine ⟨9980950697345274016107053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26615868526254064042952141 9980950697345274016107053)
                    ·
                      refine ⟨3742856511504477756040145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9980950697345274016107053 3742856511504477756040145)
                      ·
                        rfl

theorem cell23_7289187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_7289187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289187 prefixEnd_7289187 := by exact prefixLift 7289187
  have htrace : WordTrace (prefixWord ++ tailWord_7289187) baseStart_7289187 baseEnd_7289187 := by
    simpa [prefixWord, tailWord_7289187, baseEnd_7289187] using wordTrace_append hprefix tailTrace_7289187
  have hstable : (prefixWord ++ tailWord_7289187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289187).length < 2 ^ (prefixWord ++ tailWord_7289187).sum := by decide
  have hdescent : baseEnd_7289187 < baseStart_7289187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289188 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_7289188 : Nat := 118140960795 + 7289188 * 2 ^ 59
def prefixEnd_7289188 : Nat := 4983230072969 + 3 ^ 40 * 7289188 * 2
def baseEnd_7289188 : Nat := 3742857024985132252127641

theorem tailTrace_7289188 : CollatzResearch.WordTrace tailWord_7289188 prefixEnd_7289188 3742857024985132252127641 := by
  unfold tailWord_7289188
  simp only [CollatzResearch.WordTrace]
  refine ⟨132929263758262122522210109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177239018344349496696280145 132929263758262122522210109)
  ·
    refine ⟨49848473909348295945828791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132929263758262122522210109 49848473909348295945828791)
    ·
      refine ⟨74772710864022443918743187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49848473909348295945828791 74772710864022443918743187)
      ·
        refine ⟨112159066296033665878114781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74772710864022443918743187 112159066296033665878114781)
        ·
          refine ⟨42059649861012624704293043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112159066296033665878114781 42059649861012624704293043)
          ·
            refine ⟨63089474791518937056439565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42059649861012624704293043 63089474791518937056439565)
            ·
              refine ⟨23658553046819601396164837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63089474791518937056439565 23658553046819601396164837)
              ·
                refine ⟨4435978696278675261780907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23658553046819601396164837 4435978696278675261780907)
                ·
                  refine ⟨6653968044418012892671361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435978696278675261780907 6653968044418012892671361)
                  ·
                    refine ⟨4990476033313509669503521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653968044418012892671361 4990476033313509669503521)
                    ·
                      refine ⟨3742857024985132252127641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990476033313509669503521 3742857024985132252127641)
                      ·
                        rfl

theorem cell23_7289188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_7289188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289188 prefixEnd_7289188 := by exact prefixLift 7289188
  have htrace : WordTrace (prefixWord ++ tailWord_7289188) baseStart_7289188 baseEnd_7289188 := by
    simpa [prefixWord, tailWord_7289188, baseEnd_7289188] using wordTrace_append hprefix tailTrace_7289188
  have hstable : (prefixWord ++ tailWord_7289188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289188).length < 2 ^ (prefixWord ++ tailWord_7289188).sum := by decide
  have hdescent : baseEnd_7289188 < baseStart_7289188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289194 : List Nat := [3, 1, 3, 3, 1, 3, 1, 8]
def baseStart_7289194 : Nat := 118140960795 + 7289194 * 2 ^ 59
def prefixEnd_7289194 : Nat := 4983230072969 + 3 ^ 40 * 7289194 * 2
def baseEnd_7289194 : Nat := 138624448365520712172319

theorem tailTrace_7289194 : CollatzResearch.WordTrace tailWord_7289194 prefixEnd_7289194 138624448365520712172319 := by
  unfold tailWord_7289194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66464686588625627017284659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177239164236335005379425757 66464686588625627017284659)
  ·
    refine ⟨99697029882938440525926989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66464686588625627017284659 99697029882938440525926989)
    ·
      refine ⟨37386386206101915197222621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99697029882938440525926989 37386386206101915197222621)
      ·
        refine ⟨14019894827288218198958483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37386386206101915197222621 14019894827288218198958483)
        ·
          refine ⟨21029842240932327298437725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14019894827288218198958483 21029842240932327298437725)
          ·
            refine ⟨7886190840349622736914147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21029842240932327298437725 7886190840349622736914147)
            ·
              refine ⟨11829286260524434105371221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886190840349622736914147 11829286260524434105371221)
              ·
                refine ⟨138624448365520712172319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11829286260524434105371221 138624448365520712172319)
                ·
                  rfl

theorem cell23_7289194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_7289194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289194 prefixEnd_7289194 := by exact prefixLift 7289194
  have htrace : WordTrace (prefixWord ++ tailWord_7289194) baseStart_7289194 baseEnd_7289194 := by
    simpa [prefixWord, tailWord_7289194, baseEnd_7289194] using wordTrace_append hprefix tailTrace_7289194
  have hstable : (prefixWord ++ tailWord_7289194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289194).length < 2 ^ (prefixWord ++ tailWord_7289194).sum := by decide
  have hdescent : baseEnd_7289194 < baseStart_7289194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289210 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_7289210 : Nat := 118140960795 + 7289210 * 2 ^ 59
def prefixEnd_7289210 : Nat := 4983230072969 + 3 ^ 40 * 7289210 * 2
def baseEnd_7289210 : Nat := 3742868321559531166052539

theorem tailTrace_7289210 : CollatzResearch.WordTrace tailWord_7289210 prefixEnd_7289210 3742868321559531166052539 := by
  unfold tailWord_7289210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66464832480611135700430271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177239553281629695201147389 66464832480611135700430271)
  ·
    refine ⟨99697248720916703550645407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66464832480611135700430271 99697248720916703550645407)
    ·
      refine ⟨149545873081375055325968111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99697248720916703550645407 149545873081375055325968111)
      ·
        refine ⟨224318809622062582988952167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149545873081375055325968111 224318809622062582988952167)
        ·
          refine ⟨336478214433093874483428251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224318809622062582988952167 336478214433093874483428251)
          ·
            refine ⟨504717321649640811725142377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336478214433093874483428251 504717321649640811725142377)
            ·
              refine ⟨378537991237230608793856783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504717321649640811725142377 378537991237230608793856783)
              ·
                refine ⟨567806986855845913190785175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378537991237230608793856783 567806986855845913190785175)
                ·
                  refine ⟨851710480283768869786177763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567806986855845913190785175 851710480283768869786177763)
                  ·
                    refine ⟨1277565720425653304679266645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851710480283768869786177763 1277565720425653304679266645)
                    ·
                      refine ⟨3742868321559531166052539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1277565720425653304679266645 3742868321559531166052539)
                      ·
                        rfl

theorem cell23_7289210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_7289210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289210 prefixEnd_7289210 := by exact prefixLift 7289210
  have htrace : WordTrace (prefixWord ++ tailWord_7289210) baseStart_7289210 baseEnd_7289210 := by
    simpa [prefixWord, tailWord_7289210, baseEnd_7289210] using wordTrace_append hprefix tailTrace_7289210
  have hstable : (prefixWord ++ tailWord_7289210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289210).length < 2 ^ (prefixWord ++ tailWord_7289210).sum := by decide
  have hdescent : baseEnd_7289210 < baseStart_7289210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289304 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_7289304 : Nat := 118140960795 + 7289304 * 2 ^ 59
def prefixEnd_7289304 : Nat := 4983230072969 + 3 ^ 40 * 7289304 * 2
def baseEnd_7289304 : Nat := 3742916588741053798277107

theorem tailTrace_7289304 : CollatzResearch.WordTrace tailWord_7289304 prefixEnd_7289304 3742916588741053798277107 := by
  unfold tailWord_7289304
  simp only [CollatzResearch.WordTrace]
  refine ⟨132931379192051998427821483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177241838922735997903761977 132931379192051998427821483)
  ·
    refine ⟨199397068788077997641732225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132931379192051998427821483 199397068788077997641732225)
    ·
      refine ⟨149547801591058498231299169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199397068788077997641732225 149547801591058498231299169)
      ·
        refine ⟨112160851193293873673474377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149547801591058498231299169 112160851193293873673474377)
        ·
          refine ⟨84120638394970405255105783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112160851193293873673474377 84120638394970405255105783)
          ·
            refine ⟨126180957592455607882658675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84120638394970405255105783 126180957592455607882658675)
            ·
              refine ⟨189271436388683411823988013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126180957592455607882658675 189271436388683411823988013)
              ·
                refine ⟨70976788645756279433995505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189271436388683411823988013 70976788645756279433995505)
                ·
                  refine ⟨53232591484317209575496629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70976788645756279433995505 53232591484317209575496629)
                  ·
                    refine ⟨4990555451654738397702809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53232591484317209575496629 4990555451654738397702809)
                    ·
                      refine ⟨3742916588741053798277107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990555451654738397702809 3742916588741053798277107)
                      ·
                        rfl

theorem cell23_7289304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_7289304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289304 prefixEnd_7289304 := by exact prefixLift 7289304
  have htrace : WordTrace (prefixWord ++ tailWord_7289304) baseStart_7289304 baseEnd_7289304 := by
    simpa [prefixWord, tailWord_7289304, baseEnd_7289304] using wordTrace_append hprefix tailTrace_7289304
  have hstable : (prefixWord ++ tailWord_7289304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289304).length < 2 ^ (prefixWord ++ tailWord_7289304).sum := by decide
  have hdescent : baseEnd_7289304 < baseStart_7289304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289347 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_7289347 : Nat := 118140960795 + 7289347 * 2 ^ 59
def prefixEnd_7289347 : Nat := 4983230072969 + 3 ^ 40 * 7289347 * 2
def baseEnd_7289347 : Nat := 3742938668409197130039409

theorem tailTrace_7289347 : CollatzResearch.WordTrace tailWord_7289347 prefixEnd_7289347 3742938668409197130039409 := by
  unfold tailWord_7289347
  simp only [CollatzResearch.WordTrace]
  refine ⟨265864326722948215199458295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177242884481965476799638863 265864326722948215199458295)
  ·
    refine ⟨398796490084422322799187443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265864326722948215199458295 398796490084422322799187443)
    ·
      refine ⟨598194735126633484198781165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398796490084422322799187443 598194735126633484198781165)
      ·
        refine ⟨224323025672487556574542937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598194735126633484198781165 224323025672487556574542937)
        ·
          refine ⟨168242269254365667430907203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224323025672487556574542937 168242269254365667430907203)
          ·
            refine ⟨252363403881548501146360805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168242269254365667430907203 252363403881548501146360805)
            ·
              refine ⟨47318138227790343964942651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252363403881548501146360805 47318138227790343964942651)
              ·
                refine ⟨70977207341685515947413977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47318138227790343964942651 70977207341685515947413977)
                ·
                  refine ⟨53232905506264136960560483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70977207341685515947413977 53232905506264136960560483)
                  ·
                    refine ⟨79849358259396205440840725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53232905506264136960560483 79849358259396205440840725)
                    ·
                      refine ⟨3742938668409197130039409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79849358259396205440840725 3742938668409197130039409)
                      ·
                        rfl

theorem cell23_7289347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_7289347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289347 prefixEnd_7289347 := by exact prefixLift 7289347
  have htrace : WordTrace (prefixWord ++ tailWord_7289347) baseStart_7289347 baseEnd_7289347 := by
    simpa [prefixWord, tailWord_7289347, baseEnd_7289347] using wordTrace_append hprefix tailTrace_7289347
  have hstable : (prefixWord ++ tailWord_7289347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289347).length < 2 ^ (prefixWord ++ tailWord_7289347).sum := by decide
  have hdescent : baseEnd_7289347 < baseStart_7289347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289401 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7289401 : Nat := 118140960795 + 7289401 * 2 ^ 59
def prefixEnd_7289401 : Nat := 4983230072969 + 3 ^ 40 * 7289401 * 2
def baseEnd_7289401 : Nat := 3742966396364539918764161

theorem tailTrace_7289401 : CollatzResearch.WordTrace tailWord_7289401 prefixEnd_7289401 3742966396364539918764161 := by
  unfold tailWord_7289401
  simp only [CollatzResearch.WordTrace]
  refine ⟨265866296264752582421924057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177244197509835054947949371 265866296264752582421924057)
  ·
    refine ⟨199399722198564436816443043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265866296264752582421924057 199399722198564436816443043)
    ·
      refine ⟨299099583297846655224664565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199399722198564436816443043 299099583297846655224664565)
      ·
        refine ⟨28040585934173123927312303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299099583297846655224664565 28040585934173123927312303)
        ·
          refine ⟨42060878901259685890968455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28040585934173123927312303 42060878901259685890968455)
          ·
            refine ⟨63091318351889528836452683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42060878901259685890968455 63091318351889528836452683)
            ·
              refine ⟨94636977527834293254679025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63091318351889528836452683 94636977527834293254679025)
              ·
                refine ⟨70977733145875719941009269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94636977527834293254679025 70977733145875719941009269)
                ·
                  refine ⟨6654162482425848744469619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70977733145875719941009269 6654162482425848744469619)
                  ·
                    refine ⟨9981243723638773116704429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654162482425848744469619 9981243723638773116704429)
                    ·
                      refine ⟨3742966396364539918764161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981243723638773116704429 3742966396364539918764161)
                      ·
                        rfl

theorem cell23_7289401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7289401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289401 prefixEnd_7289401 := by exact prefixLift 7289401
  have htrace : WordTrace (prefixWord ++ tailWord_7289401) baseStart_7289401 baseEnd_7289401 := by
    simpa [prefixWord, tailWord_7289401, baseEnd_7289401] using wordTrace_append hprefix tailTrace_7289401
  have hstable : (prefixWord ++ tailWord_7289401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289401).length < 2 ^ (prefixWord ++ tailWord_7289401).sum := by decide
  have hdescent : baseEnd_7289401 < baseStart_7289401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289411 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 2, 3, 2]
def baseStart_7289411 : Nat := 118140960795 + 7289411 * 2 ^ 59
def prefixEnd_7289411 : Nat := 4983230072969 + 3 ^ 40 * 7289411 * 2
def baseEnd_7289411 : Nat := 3742971531171084879639115

theorem tailTrace_7289411 : CollatzResearch.WordTrace tailWord_7289411 prefixEnd_7289411 3742971531171084879639115 := by
  unfold tailWord_7289411
  simp only [CollatzResearch.WordTrace]
  refine ⟨265866660994716354129788087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177244440663144236086525391 265866660994716354129788087)
  ·
    refine ⟨398799991492074531194682131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265866660994716354129788087 398799991492074531194682131)
    ·
      refine ⟨598199987238111796792023197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398799991492074531194682131 598199987238111796792023197)
      ·
        refine ⟨224324995214291923797008699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598199987238111796792023197 224324995214291923797008699)
        ·
          refine ⟨336487492821437885695513049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224324995214291923797008699 336487492821437885695513049)
          ·
            refine ⟨252365619616078414271634787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336487492821437885695513049 252365619616078414271634787)
            ·
              refine ⟨378548429424117621407452181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252365619616078414271634787 378548429424117621407452181)
              ·
                refine ⟨17744457629255513503474321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 378548429424117621407452181 17744457629255513503474321)
                ·
                  refine ⟨13308343221941635127605741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17744457629255513503474321 13308343221941635127605741)
                  ·
                    refine ⟨4990628708228113172852153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13308343221941635127605741 4990628708228113172852153)
                    ·
                      refine ⟨3742971531171084879639115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990628708228113172852153 3742971531171084879639115)
                      ·
                        rfl

theorem cell23_7289411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_7289411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289411 prefixEnd_7289411 := by exact prefixLift 7289411
  have htrace : WordTrace (prefixWord ++ tailWord_7289411) baseStart_7289411 baseEnd_7289411 := by
    simpa [prefixWord, tailWord_7289411, baseEnd_7289411] using wordTrace_append hprefix tailTrace_7289411
  have hstable : (prefixWord ++ tailWord_7289411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289411).length < 2 ^ (prefixWord ++ tailWord_7289411).sum := by decide
  have hdescent : baseEnd_7289411 < baseStart_7289411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289412 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7289412 : Nat := 118140960795 + 7289412 * 2 ^ 59
def prefixEnd_7289412 : Nat := 4983230072969 + 3 ^ 40 * 7289412 * 2
def baseEnd_7289412 : Nat := 1247657348217246458575537

theorem tailTrace_7289412 : CollatzResearch.WordTrace tailWord_7289412 prefixEnd_7289412 1247657348217246458575537 := by
  unfold tailWord_7289412
  simp only [CollatzResearch.WordTrace]
  refine ⟨132933348733856365650287245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177244464978475154200382993 132933348733856365650287245)
  ·
    refine ⟨49850005775196137118857717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132933348733856365650287245 49850005775196137118857717)
    ·
      refine ⟨4673438041424637854892911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49850005775196137118857717 4673438041424637854892911)
      ·
        refine ⟨7010157062136956782339367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673438041424637854892911 7010157062136956782339367)
        ·
          refine ⟨10515235593205435173509051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010157062136956782339367 10515235593205435173509051)
          ·
            refine ⟨15772853389808152760263577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515235593205435173509051 15772853389808152760263577)
            ·
              refine ⟨11829640042356114570197683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15772853389808152760263577 11829640042356114570197683)
              ·
                refine ⟨17744460063534171855296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11829640042356114570197683 17744460063534171855296525)
                ·
                  refine ⟨6654172523825314445736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17744460063534171855296525 6654172523825314445736197)
                  ·
                    refine ⟨1247657348217246458575537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6654172523825314445736197 1247657348217246458575537)
                    ·
                      rfl

theorem cell23_7289412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7289412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289412 prefixEnd_7289412 := by exact prefixLift 7289412
  have htrace : WordTrace (prefixWord ++ tailWord_7289412) baseStart_7289412 baseEnd_7289412 := by
    simpa [prefixWord, tailWord_7289412, baseEnd_7289412] using wordTrace_append hprefix tailTrace_7289412
  have hstable : (prefixWord ++ tailWord_7289412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289412).length < 2 ^ (prefixWord ++ tailWord_7289412).sum := by decide
  have hdescent : baseEnd_7289412 < baseStart_7289412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289417 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_7289417 : Nat := 118140960795 + 7289417 * 2 ^ 59
def prefixEnd_7289417 : Nat := 4983230072969 + 3 ^ 40 * 7289417 * 2
def baseEnd_7289417 : Nat := 1247658204018337285388029

theorem tailTrace_7289417 : CollatzResearch.WordTrace tailWord_7289417 prefixEnd_7289417 1247658204018337285388029 := by
  unfold tailWord_7289417
  simp only [CollatzResearch.WordTrace]
  refine ⟨265866879832694617154506505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177244586555129744769671003 265866879832694617154506505)
  ·
    refine ⟨199400159874520962865879879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265866879832694617154506505 199400159874520962865879879)
    ·
      refine ⟨299100239811781444298819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199400159874520962865879879 299100239811781444298819819)
      ·
        refine ⟨448650359717672166448229729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299100239811781444298819819 448650359717672166448229729)
        ·
          refine ⟨336487769788254124836172297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448650359717672166448229729 336487769788254124836172297)
          ·
            refine ⟨252365827341190593627129223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336487769788254124836172297 252365827341190593627129223)
            ·
              refine ⟨378548741011785890440693835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252365827341190593627129223 378548741011785890440693835)
              ·
                refine ⟨567823111517678835661040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378548741011785890440693835 567823111517678835661040753)
                ·
                  refine ⟨425867333638259126745780565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567823111517678835661040753 425867333638259126745780565)
                  ·
                    refine ⟨1247658204018337285388029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 425867333638259126745780565 1247658204018337285388029)
                    ·
                      rfl

theorem cell23_7289417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_7289417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289417 prefixEnd_7289417 := by exact prefixLift 7289417
  have htrace : WordTrace (prefixWord ++ tailWord_7289417) baseStart_7289417 baseEnd_7289417 := by
    simpa [prefixWord, tailWord_7289417, baseEnd_7289417] using wordTrace_append hprefix tailTrace_7289417
  have hstable : (prefixWord ++ tailWord_7289417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289417).length < 2 ^ (prefixWord ++ tailWord_7289417).sum := by decide
  have hdescent : baseEnd_7289417 < baseStart_7289417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289418 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_7289418 : Nat := 118140960795 + 7289418 * 2 ^ 59
def prefixEnd_7289418 : Nat := 4983230072969 + 3 ^ 40 * 7289418 * 2
def baseEnd_7289418 : Nat := 3742975125535666352251583

theorem tailTrace_7289418 : CollatzResearch.WordTrace tailWord_7289418 prefixEnd_7289418 3742975125535666352251583 := by
  unfold tailWord_7289418
  simp only [CollatzResearch.WordTrace]
  refine ⟨66466729076422748581323227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177244610870460662883528605 66466729076422748581323227)
  ·
    refine ⟨99700093614634122871984841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66466729076422748581323227 99700093614634122871984841)
    ·
      refine ⟨74775070210975592153988631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99700093614634122871984841 74775070210975592153988631)
      ·
        refine ⟨112162605316463388230982947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74775070210975592153988631 112162605316463388230982947)
        ·
          refine ⟨168243907974695082346474421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112162605316463388230982947 168243907974695082346474421)
          ·
            refine ⟨15772866372627663969981977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168243907974695082346474421 15772866372627663969981977)
            ·
              refine ⟨11829649779470747977486483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15772866372627663969981977 11829649779470747977486483)
              ·
                refine ⟨17744474669206121966229725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11829649779470747977486483 17744474669206121966229725)
                ·
                  refine ⟨6654178000952295737336147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17744474669206121966229725 6654178000952295737336147)
                  ·
                    refine ⟨9981267001428443606004221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654178000952295737336147 9981267001428443606004221)
                    ·
                      refine ⟨3742975125535666352251583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981267001428443606004221 3742975125535666352251583)
                      ·
                        rfl

theorem cell23_7289418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_7289418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289418 prefixEnd_7289418 := by exact prefixLift 7289418
  have htrace : WordTrace (prefixWord ++ tailWord_7289418) baseStart_7289418 baseEnd_7289418 := by
    simpa [prefixWord, tailWord_7289418, baseEnd_7289418] using wordTrace_append hprefix tailTrace_7289418
  have hstable : (prefixWord ++ tailWord_7289418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289418).length < 2 ^ (prefixWord ++ tailWord_7289418).sum := by decide
  have hdescent : baseEnd_7289418 < baseStart_7289418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289424 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_7289424 : Nat := 118140960795 + 7289424 * 2 ^ 59
def prefixEnd_7289424 : Nat := 4983230072969 + 3 ^ 40 * 7289424 * 2
def baseEnd_7289424 : Nat := 3742978206419593328776555

theorem tailTrace_7289424 : CollatzResearch.WordTrace tailWord_7289424 prefixEnd_7289424 3742978206419593328776555 := by
  unfold tailWord_7289424
  simp only [CollatzResearch.WordTrace]
  refine ⟨132933567571834628675005663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177244756762446171566674217 132933567571834628675005663)
  ·
    refine ⟨199400351357751943012508495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132933567571834628675005663 199400351357751943012508495)
    ·
      refine ⟨299100527036627914518762743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199400351357751943012508495 299100527036627914518762743)
      ·
        refine ⟨448650790554941871778144115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299100527036627914518762743 448650790554941871778144115)
        ·
          refine ⟨672976185832412807667216173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448650790554941871778144115 672976185832412807667216173)
          ·
            refine ⟨252366069687154802875206065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672976185832412807667216173 252366069687154802875206065)
            ·
              refine ⟨189274552265366102156404549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252366069687154802875206065 189274552265366102156404549)
              ·
                refine ⟨35488978549756144154325853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189274552265366102156404549 35488978549756144154325853)
                ·
                  refine ⟨13308366956158554057872195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35488978549756144154325853 13308366956158554057872195)
                  ·
                    refine ⟨19962550434237831086808293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13308366956158554057872195 19962550434237831086808293)
                    ·
                      refine ⟨3742978206419593328776555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19962550434237831086808293 3742978206419593328776555)
                      ·
                        rfl

theorem cell23_7289424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_7289424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289424 prefixEnd_7289424 := by exact prefixLift 7289424
  have htrace : WordTrace (prefixWord ++ tailWord_7289424) baseStart_7289424 baseEnd_7289424 := by
    simpa [prefixWord, tailWord_7289424, baseEnd_7289424] using wordTrace_append hprefix tailTrace_7289424
  have hstable : (prefixWord ++ tailWord_7289424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289424).length < 2 ^ (prefixWord ++ tailWord_7289424).sum := by decide
  have hdescent : baseEnd_7289424 < baseStart_7289424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289441 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_7289441 : Nat := 118140960795 + 7289441 * 2 ^ 59
def prefixEnd_7289441 : Nat := 4983230072969 + 3 ^ 40 * 7289441 * 2
def baseEnd_7289441 : Nat := 3742986935590719762263977

theorem tailTrace_7289441 : CollatzResearch.WordTrace tailWord_7289441 prefixEnd_7289441 3742986935590719762263977 := by
  unfold tailWord_7289441
  simp only [CollatzResearch.WordTrace]
  refine ⟨265867755184607669253380177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177245170123071779502253451 265867755184607669253380177)
  ·
    refine ⟨199400816388455751940035133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265867755184607669253380177 199400816388455751940035133)
    ·
      refine ⟨74775306145670906977513175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199400816388455751940035133 74775306145670906977513175)
      ·
        refine ⟨112162959218506360466269763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74775306145670906977513175 112162959218506360466269763)
        ·
          refine ⟨168244438827759540699404645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112162959218506360466269763 168244438827759540699404645)
          ·
            refine ⟨31545832280204913881138371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168244438827759540699404645 31545832280204913881138371)
            ·
              refine ⟨47318748420307370821707557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31545832280204913881138371 47318748420307370821707557)
              ·
                refine ⟨8872265328807632029070167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47318748420307370821707557 8872265328807632029070167)
                ·
                  refine ⟨13308397993211448043605251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8872265328807632029070167 13308397993211448043605251)
                  ·
                    refine ⟨19962596989817172065407877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13308397993211448043605251 19962596989817172065407877)
                    ·
                      refine ⟨3742986935590719762263977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19962596989817172065407877 3742986935590719762263977)
                      ·
                        rfl

theorem cell23_7289441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_7289441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289441 prefixEnd_7289441 := by exact prefixLift 7289441
  have htrace : WordTrace (prefixWord ++ tailWord_7289441) baseStart_7289441 baseEnd_7289441 := by
    simpa [prefixWord, tailWord_7289441, baseEnd_7289441] using wordTrace_append hprefix tailTrace_7289441
  have hstable : (prefixWord ++ tailWord_7289441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289441).length < 2 ^ (prefixWord ++ tailWord_7289441).sum := by decide
  have hdescent : baseEnd_7289441 < baseStart_7289441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289444 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_7289444 : Nat := 118140960795 + 7289444 * 2 ^ 59
def prefixEnd_7289444 : Nat := 4983230072969 + 3 ^ 40 * 7289444 * 2
def baseEnd_7289444 : Nat := 3742988476032683250526463

theorem tailTrace_7289444 : CollatzResearch.WordTrace tailWord_7289444 prefixEnd_7289444 3742988476032683250526463 := by
  unfold tailWord_7289444
  simp only [CollatzResearch.WordTrace]
  refine ⟨132933932301798400382869693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177245243069064533843826257 132933932301798400382869693)
  ·
    refine ⟨49850224613174400143576135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132933932301798400382869693 49850224613174400143576135)
    ·
      refine ⟨74775336919761600215364203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49850224613174400143576135 74775336919761600215364203)
      ·
        refine ⟨112163005379642400323046305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74775336919761600215364203 112163005379642400323046305)
        ·
          refine ⟨84122254034731800242284729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112163005379642400323046305 84122254034731800242284729)
          ·
            refine ⟨63091690526048850181713547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84122254034731800242284729 63091690526048850181713547)
            ·
              refine ⟨94637535789073275272570321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63091690526048850181713547 94637535789073275272570321)
              ·
                refine ⟨70978151841804956454427741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94637535789073275272570321 70978151841804956454427741)
                ·
                  refine ⟨26616806940676858670410403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70978151841804956454427741 26616806940676858670410403)
                  ·
                    refine ⟨39925210411015288005615605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26616806940676858670410403 39925210411015288005615605)
                    ·
                      refine ⟨3742988476032683250526463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39925210411015288005615605 3742988476032683250526463)
                      ·
                        rfl

theorem cell23_7289444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_7289444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289444 prefixEnd_7289444 := by exact prefixLift 7289444
  have htrace : WordTrace (prefixWord ++ tailWord_7289444) baseStart_7289444 baseEnd_7289444 := by
    simpa [prefixWord, tailWord_7289444, baseEnd_7289444] using wordTrace_append hprefix tailTrace_7289444
  have hstable : (prefixWord ++ tailWord_7289444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289444).length < 2 ^ (prefixWord ++ tailWord_7289444).sum := by decide
  have hdescent : baseEnd_7289444 < baseStart_7289444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289475 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 1, 2, 2]
def baseStart_7289475 : Nat := 118140960795 + 7289475 * 2 ^ 59
def prefixEnd_7289475 : Nat := 4983230072969 + 3 ^ 40 * 7289475 * 2
def baseEnd_7289475 : Nat := 3743004393932972629238821

theorem tailTrace_7289475 : CollatzResearch.WordTrace tailWord_7289475 prefixEnd_7289475 3743004393932972629238821 := by
  unfold tailWord_7289475
  simp only [CollatzResearch.WordTrace]
  refine ⟨265868995266484493060117879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177245996844322995373411919 265868995266484493060117879)
  ·
    refine ⟨398803492899726739590176819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265868995266484493060117879 398803492899726739590176819)
    ·
      refine ⟨598205239349590109385265229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398803492899726739590176819 598205239349590109385265229)
      ·
        refine ⟨224326964756096291019474461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598205239349590109385265229 224326964756096291019474461)
        ·
          refine ⟨84122611783536109132302923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224326964756096291019474461 84122611783536109132302923)
          ·
            refine ⟨126183917675304163698454385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84122611783536109132302923 126183917675304163698454385)
            ·
              refine ⟨94637938256478122773840789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126183917675304163698454385 94637938256478122773840789)
              ·
                refine ⟨4436153355772412005023787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94637938256478122773840789 4436153355772412005023787)
                ·
                  refine ⟨6654230033658618007535681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436153355772412005023787 6654230033658618007535681)
                  ·
                    refine ⟨4990672525243963505651761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654230033658618007535681 4990672525243963505651761)
                    ·
                      refine ⟨3743004393932972629238821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990672525243963505651761 3743004393932972629238821)
                      ·
                        rfl

theorem cell23_7289475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_7289475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289475 prefixEnd_7289475 := by exact prefixLift 7289475
  have htrace : WordTrace (prefixWord ++ tailWord_7289475) baseStart_7289475 baseEnd_7289475 := by
    simpa [prefixWord, tailWord_7289475, baseEnd_7289475] using wordTrace_append hprefix tailTrace_7289475
  have hstable : (prefixWord ++ tailWord_7289475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289475).length < 2 ^ (prefixWord ++ tailWord_7289475).sum := by decide
  have hdescent : baseEnd_7289475 < baseStart_7289475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289525 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7289525 : Nat := 118140960795 + 7289525 * 2 ^ 59
def prefixEnd_7289525 : Nat := 4983230072969 + 3 ^ 40 * 7289525 * 2
def baseEnd_7289525 : Nat := 3743030067965697433613591

theorem tailTrace_7289525 : CollatzResearch.WordTrace tailWord_7289525 prefixEnd_7289525 3743030067965697433613591 := by
  unfold tailWord_7289525
  simp only [CollatzResearch.WordTrace]
  refine ⟨265870818916303351599438029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177247212610868901066292019 265870818916303351599438029)
  ·
    refine ⟨99701557093613756849789261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265870818916303351599438029 99701557093613756849789261)
    ·
      refine ⟨37388083910105158818670973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99701557093613756849789261 37388083910105158818670973)
      ·
        refine ⟨14020531466289434557001615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37388083910105158818670973 14020531466289434557001615)
        ·
          refine ⟨21030797199434151835502423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14020531466289434557001615 21030797199434151835502423)
          ·
            refine ⟨31546195799151227753253635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21030797199434151835502423 31546195799151227753253635)
            ·
              refine ⟨47319293698726841629880453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31546195799151227753253635 47319293698726841629880453)
              ·
                refine ⟨8872367568511282805602585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47319293698726841629880453 8872367568511282805602585)
                ·
                  refine ⟨6654275676383462104201939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8872367568511282805602585 6654275676383462104201939)
                  ·
                    refine ⟨9981413514575193156302909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654275676383462104201939 9981413514575193156302909)
                    ·
                      refine ⟨3743030067965697433613591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981413514575193156302909 3743030067965697433613591)
                      ·
                        rfl

theorem cell23_7289525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7289525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289525 prefixEnd_7289525 := by exact prefixLift 7289525
  have htrace : WordTrace (prefixWord ++ tailWord_7289525) baseStart_7289525 baseEnd_7289525 := by
    simpa [prefixWord, tailWord_7289525, baseEnd_7289525] using wordTrace_append hprefix tailTrace_7289525
  have hstable : (prefixWord ++ tailWord_7289525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289525).length < 2 ^ (prefixWord ++ tailWord_7289525).sum := by decide
  have hdescent : baseEnd_7289525 < baseStart_7289525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289526 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7289526 : Nat := 118140960795 + 7289526 * 2 ^ 59
def prefixEnd_7289526 : Nat := 4983230072969 + 3 ^ 40 * 7289526 * 2
def baseEnd_7289526 : Nat := 3743030581446351929701087

theorem tailTrace_7289526 : CollatzResearch.WordTrace tailWord_7289526 prefixEnd_7289526 3743030581446351929701087 := by
  unfold tailWord_7289526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616928461831233048139027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177247236926199819180149621 16616928461831233048139027)
  ·
    refine ⟨24925392692746849572208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16616928461831233048139027 24925392692746849572208541)
    ·
      refine ⟨9347022259780068589578203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24925392692746849572208541 9347022259780068589578203)
      ·
        refine ⟨14020533389670102884367305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9347022259780068589578203 14020533389670102884367305)
        ·
          refine ⟨10515400042252577163275479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14020533389670102884367305 10515400042252577163275479)
          ·
            refine ⟨15773100063378865744913219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515400042252577163275479 15773100063378865744913219)
            ·
              refine ⟨23659650095068298617369829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773100063378865744913219 23659650095068298617369829)
              ·
                refine ⟨4436184392825305990756843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23659650095068298617369829 4436184392825305990756843)
                ·
                  refine ⟨6654276589237958986135265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436184392825305990756843 6654276589237958986135265)
                  ·
                    refine ⟨4990707441928469239601449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654276589237958986135265 4990707441928469239601449)
                    ·
                      refine ⟨3743030581446351929701087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990707441928469239601449 3743030581446351929701087)
                      ·
                        rfl

theorem cell23_7289526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7289526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289526 prefixEnd_7289526 := by exact prefixLift 7289526
  have htrace : WordTrace (prefixWord ++ tailWord_7289526) baseStart_7289526 baseEnd_7289526 := by
    simpa [prefixWord, tailWord_7289526, baseEnd_7289526] using wordTrace_append hprefix tailTrace_7289526
  have hstable : (prefixWord ++ tailWord_7289526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289526).length < 2 ^ (prefixWord ++ tailWord_7289526).sum := by decide
  have hdescent : baseEnd_7289526 < baseStart_7289526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289582 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_7289582 : Nat := 118140960795 + 7289582 * 2 ^ 59
def prefixEnd_7289582 : Nat := 4983230072969 + 3 ^ 40 * 7289582 * 2
def baseEnd_7289582 : Nat := 3743059336363003710600829

theorem tailTrace_7289582 : CollatzResearch.WordTrace tailWord_7289582 prefixEnd_7289582 3743059336363003710600829 := by
  unfold tailWord_7289582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33234112234637106291782875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177248598584731233556175333 33234112234637106291782875)
  ·
    refine ⟨49851168351955659437674313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33234112234637106291782875 49851168351955659437674313)
    ·
      refine ⟨37388376263966744578255735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49851168351955659437674313 37388376263966744578255735)
      ·
        refine ⟨56082564395950116867383603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37388376263966744578255735 56082564395950116867383603)
        ·
          refine ⟨84123846593925175301075405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56082564395950116867383603 84123846593925175301075405)
          ·
            refine ⟨31546442472721940737903277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84123846593925175301075405 31546442472721940737903277)
            ·
              refine ⟨11829915927270727776713729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31546442472721940737903277 11829915927270727776713729)
              ·
                refine ⟨8872436945453045832535297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11829915927270727776713729 8872436945453045832535297)
                ·
                  refine ⟨6654327709089784374401473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8872436945453045832535297 6654327709089784374401473)
                  ·
                    refine ⟨4990745781817338280801105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654327709089784374401473 4990745781817338280801105)
                    ·
                      refine ⟨3743059336363003710600829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990745781817338280801105 3743059336363003710600829)
                      ·
                        rfl

theorem cell23_7289582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_7289582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289582 prefixEnd_7289582 := by exact prefixLift 7289582
  have htrace : WordTrace (prefixWord ++ tailWord_7289582) baseStart_7289582 baseEnd_7289582 := by
    simpa [prefixWord, tailWord_7289582, baseEnd_7289582] using wordTrace_append hprefix tailTrace_7289582
  have hstable : (prefixWord ++ tailWord_7289582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289582).length < 2 ^ (prefixWord ++ tailWord_7289582).sum := by decide
  have hdescent : baseEnd_7289582 < baseStart_7289582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289621 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7289621 : Nat := 118140960795 + 7289621 * 2 ^ 59
def prefixEnd_7289621 : Nat := 4983230072969 + 3 ^ 40 * 7289621 * 2
def baseEnd_7289621 : Nat := 3743079362108529058013149

theorem tailTrace_7289621 : CollatzResearch.WordTrace tailWord_7289621 prefixEnd_7289621 3743079362108529058013149 := by
  unfold tailWord_7289621
  simp only [CollatzResearch.WordTrace]
  refine ⟨265874320323955559994932717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177249546882637039996621811 265874320323955559994932717)
  ·
    refine ⟨99702870121483334998099769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265874320323955559994932717 99702870121483334998099769)
    ·
      refine ⟨74777152591112501248574827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99702870121483334998099769 74777152591112501248574827)
      ·
        refine ⟨112165728886668751872862241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74777152591112501248574827 112165728886668751872862241)
        ·
          refine ⟨84124296665001563904646681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112165728886668751872862241 84124296665001563904646681)
          ·
            refine ⟨63093222498751172928485011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84124296665001563904646681 63093222498751172928485011)
            ·
              refine ⟨94639833748126759392727517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63093222498751172928485011 94639833748126759392727517)
              ·
                refine ⟨35489937655547534772272819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94639833748126759392727517 35489937655547534772272819)
                ·
                  refine ⟨53234906483321302158409229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35489937655547534772272819 53234906483321302158409229)
                  ·
                    refine ⟨19963089931245488309403461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53234906483321302158409229 19963089931245488309403461)
                    ·
                      refine ⟨3743079362108529058013149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19963089931245488309403461 3743079362108529058013149)
                      ·
                        rfl

theorem cell23_7289621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7289621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289621 prefixEnd_7289621 := by exact prefixLift 7289621
  have htrace : WordTrace (prefixWord ++ tailWord_7289621) baseStart_7289621 baseEnd_7289621 := by
    simpa [prefixWord, tailWord_7289621, baseEnd_7289621] using wordTrace_append hprefix tailTrace_7289621
  have hstable : (prefixWord ++ tailWord_7289621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289621).length < 2 ^ (prefixWord ++ tailWord_7289621).sum := by decide
  have hdescent : baseEnd_7289621 < baseStart_7289621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289699 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 1, 4]
def baseStart_7289699 : Nat := 118140960795 + 7289699 * 2 ^ 59
def prefixEnd_7289699 : Nat := 4983230072969 + 3 ^ 40 * 7289699 * 2
def baseEnd_7289699 : Nat := 1247706471199859917612597

theorem tailTrace_7289699 : CollatzResearch.WordTrace tailWord_7289699 prefixEnd_7289699 1247706471199859917612597 := by
  unfold tailWord_7289699
  simp only [CollatzResearch.WordTrace]
  refine ⟨265877165217672979316272151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177251443478448652877514767 265877165217672979316272151)
  ·
    refine ⟨398815747826509468974408227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265877165217672979316272151 398815747826509468974408227)
    ·
      refine ⟨598223621739764203461612341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398815747826509468974408227 598223621739764203461612341)
      ·
        refine ⟨56083464538102894074526157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598223621739764203461612341 56083464538102894074526157)
        ·
          refine ⟨21031299201788585277947309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56083464538102894074526157 21031299201788585277947309)
          ·
            refine ⟨7886737200670719479230241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21031299201788585277947309 7886737200670719479230241)
            ·
              refine ⟨5915052900503039609422681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7886737200670719479230241 5915052900503039609422681)
              ·
                refine ⟨4436289675377279707067011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915052900503039609422681 4436289675377279707067011)
                ·
                  refine ⟨6654434513065919560600517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436289675377279707067011 6654434513065919560600517)
                  ·
                    refine ⟨1247706471199859917612597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6654434513065919560600517 1247706471199859917612597)
                    ·
                      rfl

theorem cell23_7289699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 4].length) (baseStart_7289699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289699 prefixEnd_7289699 := by exact prefixLift 7289699
  have htrace : WordTrace (prefixWord ++ tailWord_7289699) baseStart_7289699 baseEnd_7289699 := by
    simpa [prefixWord, tailWord_7289699, baseEnd_7289699] using wordTrace_append hprefix tailTrace_7289699
  have hstable : (prefixWord ++ tailWord_7289699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289699).length < 2 ^ (prefixWord ++ tailWord_7289699).sum := by decide
  have hdescent : baseEnd_7289699 < baseStart_7289699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289726 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7289726 : Nat := 118140960795 + 7289726 * 2 ^ 59
def prefixEnd_7289726 : Nat := 4983230072969 + 3 ^ 40 * 7289726 * 2
def baseEnd_7289726 : Nat := 3743133277577251147200167

theorem tailTrace_7289726 : CollatzResearch.WordTrace tailWord_7289726 prefixEnd_7289726 3743133277577251147200167 := by
  unfold tailWord_7289726
  simp only [CollatzResearch.WordTrace]
  refine ⟨33234768748571895365938129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177252099992383441951670021 33234768748571895365938129)
  ·
    refine ⟨24926076561428921524453597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33234768748571895365938129 24926076561428921524453597)
    ·
      refine ⟨9347278710535845571670099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24926076561428921524453597 9347278710535845571670099)
      ·
        refine ⟨14020918065803768357505149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9347278710535845571670099 14020918065803768357505149)
        ·
          refine ⟨5257844274676413134064431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14020918065803768357505149 5257844274676413134064431)
          ·
            refine ⟨7886766412014619701096647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257844274676413134064431 7886766412014619701096647)
            ·
              refine ⟨11830149618021929551644971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886766412014619701096647 11830149618021929551644971)
              ·
                refine ⟨17745224427032894327467457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830149618021929551644971 17745224427032894327467457)
                ·
                  refine ⟨13308918320274670745600593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17745224427032894327467457 13308918320274670745600593)
                  ·
                    refine ⟨9981688740206003059200445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13308918320274670745600593 9981688740206003059200445)
                    ·
                      refine ⟨3743133277577251147200167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981688740206003059200445 3743133277577251147200167)
                      ·
                        rfl

theorem cell23_7289726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7289726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289726 prefixEnd_7289726 := by exact prefixLift 7289726
  have htrace : WordTrace (prefixWord ++ tailWord_7289726) baseStart_7289726 baseEnd_7289726 := by
    simpa [prefixWord, tailWord_7289726, baseEnd_7289726] using wordTrace_append hprefix tailTrace_7289726
  have hstable : (prefixWord ++ tailWord_7289726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289726).length < 2 ^ (prefixWord ++ tailWord_7289726).sum := by decide
  have hdescent : baseEnd_7289726 < baseStart_7289726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289728 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2]
def baseStart_7289728 : Nat := 118140960795 + 7289728 * 2 ^ 59
def prefixEnd_7289728 : Nat := 4983230072969 + 3 ^ 40 * 7289728 * 2
def baseEnd_7289728 : Nat := 3743134304538560139375157

theorem tailTrace_7289728 : CollatzResearch.WordTrace tailWord_7289728 prefixEnd_7289728 3743134304538560139375157 := by
  unfold tailWord_7289728
  simp only [CollatzResearch.WordTrace]
  refine ⟨132939111467283958634538919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177252148623045278179385225 132939111467283958634538919)
  ·
    refine ⟨199408667200925937951808379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132939111467283958634538919 199408667200925937951808379)
    ·
      refine ⟨299113000801388906927712569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199408667200925937951808379 299113000801388906927712569)
      ·
        refine ⟨224334750601041680195784427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299113000801388906927712569 224334750601041680195784427)
        ·
          refine ⟨336502125901562520293676641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224334750601041680195784427 336502125901562520293676641)
          ·
            refine ⟨252376594426171890220257481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336502125901562520293676641 252376594426171890220257481)
            ·
              refine ⟨189282445819628917665193111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252376594426171890220257481 189282445819628917665193111)
              ·
                refine ⟨283923668729443376497789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189282445819628917665193111 283923668729443376497789667)
                ·
                  refine ⟨425885503094165064746684501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283923668729443376497789667 425885503094165064746684501)
                  ·
                    refine ⟨4990845739384746852500209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 425885503094165064746684501 4990845739384746852500209)
                    ·
                      refine ⟨3743134304538560139375157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990845739384746852500209 3743134304538560139375157)
                      ·
                        rfl

theorem cell23_7289728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_7289728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289728 prefixEnd_7289728 := by exact prefixLift 7289728
  have htrace : WordTrace (prefixWord ++ tailWord_7289728) baseStart_7289728 baseEnd_7289728 := by
    simpa [prefixWord, tailWord_7289728, baseEnd_7289728] using wordTrace_append hprefix tailTrace_7289728
  have hstable : (prefixWord ++ tailWord_7289728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289728).length < 2 ^ (prefixWord ++ tailWord_7289728).sum := by decide
  have hdescent : baseEnd_7289728 < baseStart_7289728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289745 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_7289745 : Nat := 118140960795 + 7289745 * 2 ^ 59
def prefixEnd_7289745 : Nat := 4983230072969 + 3 ^ 40 * 7289745 * 2
def baseEnd_7289745 : Nat := 3743143033709686572862579

theorem tailTrace_7289745 : CollatzResearch.WordTrace tailWord_7289745 prefixEnd_7289745 3743143033709686572862579 := by
  unfold tailWord_7289745
  simp only [CollatzResearch.WordTrace]
  refine ⟨265878842975506329172446689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177252561983670886114964459 265878842975506329172446689)
  ·
    refine ⟨199409132231629746879335017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265878842975506329172446689 199409132231629746879335017)
    ·
      refine ⟨149556849173722310159501263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199409132231629746879335017 149556849173722310159501263)
      ·
        refine ⟨224335273760583465239251895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149556849173722310159501263 224335273760583465239251895)
        ·
          refine ⟨336502910640875197858877843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224335273760583465239251895 336502910640875197858877843)
          ·
            refine ⟨504754365961312796788316765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336502910640875197858877843 504754365961312796788316765)
            ·
              refine ⟨189282887235492298795618787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504754365961312796788316765 189282887235492298795618787)
              ·
                refine ⟨283924330853238448193428181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189282887235492298795618787 283924330853238448193428181)
                ·
                  refine ⟨6654476504372776129533473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283924330853238448193428181 6654476504372776129533473)
                  ·
                    refine ⟨4990857378279582097150105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654476504372776129533473 4990857378279582097150105)
                    ·
                      refine ⟨3743143033709686572862579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990857378279582097150105 3743143033709686572862579)
                      ·
                        rfl

theorem cell23_7289745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_7289745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289745 prefixEnd_7289745 := by exact prefixLift 7289745
  have htrace : WordTrace (prefixWord ++ tailWord_7289745) baseStart_7289745 baseEnd_7289745 := by
    simpa [prefixWord, tailWord_7289745, baseEnd_7289745] using wordTrace_append hprefix tailTrace_7289745
  have hstable : (prefixWord ++ tailWord_7289745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289745).length < 2 ^ (prefixWord ++ tailWord_7289745).sum := by decide
  have hdescent : baseEnd_7289745 < baseStart_7289745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289751 : List Nat := [1, 1, 3, 3, 1, 2, 12]
def baseStart_7289751 : Nat := 118140960795 + 7289751 * 2 ^ 59
def prefixEnd_7289751 : Nat := 4983230072969 + 3 ^ 40 * 7289751 * 2
def baseEnd_7289751 : Nat := 46211680427081648757871

theorem tailTrace_7289751 : CollatzResearch.WordTrace tailWord_7289751 prefixEnd_7289751 46211680427081648757871 := by
  unfold tailWord_7289751
  simp only [CollatzResearch.WordTrace]
  refine ⟨265879061813484592197165107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177252707875656394798110071 265879061813484592197165107)
  ·
    refine ⟨398818592720226888295747661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265879061813484592197165107 398818592720226888295747661)
    ·
      refine ⟨149556972270085083110905373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398818592720226888295747661 149556972270085083110905373)
      ·
        refine ⟨56083864601281906166589515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149556972270085083110905373 56083864601281906166589515)
        ·
          refine ⟨84125796901922859249884273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56083864601281906166589515 84125796901922859249884273)
          ·
            refine ⟨63094347676442144437413205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84125796901922859249884273 63094347676442144437413205)
            ·
              refine ⟨46211680427081648757871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63094347676442144437413205 46211680427081648757871)
              ·
                rfl

theorem cell23_7289751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 12].length) (baseStart_7289751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289751 prefixEnd_7289751 := by exact prefixLift 7289751
  have htrace : WordTrace (prefixWord ++ tailWord_7289751) baseStart_7289751 baseEnd_7289751 := by
    simpa [prefixWord, tailWord_7289751, baseEnd_7289751] using wordTrace_append hprefix tailTrace_7289751
  have hstable : (prefixWord ++ tailWord_7289751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289751).length < 2 ^ (prefixWord ++ tailWord_7289751).sum := by decide
  have hdescent : baseEnd_7289751 < baseStart_7289751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_7289771 : Nat := 118140960795 + 7289771 * 2 ^ 59
def prefixEnd_7289771 : Nat := 4983230072969 + 3 ^ 40 * 7289771 * 2
def baseEnd_7289771 : Nat := 3743156384206703471137459

theorem tailTrace_7289771 : CollatzResearch.WordTrace tailWord_7289771 prefixEnd_7289771 3743156384206703471137459 := by
  unfold tailWord_7289771
  simp only [CollatzResearch.WordTrace]
  refine ⟨265879791273412135612893167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177253194182274757075262111 265879791273412135612893167)
  ·
    refine ⟨398819686910118203419339751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265879791273412135612893167 398819686910118203419339751)
    ·
      refine ⟨598229530365177305129009627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398819686910118203419339751 598229530365177305129009627)
      ·
        refine ⟨897344295547765957693514441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598229530365177305129009627 897344295547765957693514441)
        ·
          refine ⟨673008221660824468270135831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897344295547765957693514441 673008221660824468270135831)
          ·
            refine ⟨1009512332491236702405203747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673008221660824468270135831 1009512332491236702405203747)
            ·
              refine ⟨1514268498736855053607805621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009512332491236702405203747 1514268498736855053607805621)
              ·
                refine ⟨141962671756580161275731777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514268498736855053607805621 141962671756580161275731777)
                ·
                  refine ⟨106472003817435120956798833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141962671756580161275731777 106472003817435120956798833)
                  ·
                    refine ⟨79854002863076340717599125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106472003817435120956798833 79854002863076340717599125)
                    ·
                      refine ⟨3743156384206703471137459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79854002863076340717599125 3743156384206703471137459)
                      ·
                        rfl

theorem cell23_7289771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_7289771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289771 prefixEnd_7289771 := by exact prefixLift 7289771
  have htrace : WordTrace (prefixWord ++ tailWord_7289771) baseStart_7289771 baseEnd_7289771 := by
    simpa [prefixWord, tailWord_7289771, baseEnd_7289771] using wordTrace_append hprefix tailTrace_7289771
  have hstable : (prefixWord ++ tailWord_7289771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289771).length < 2 ^ (prefixWord ++ tailWord_7289771).sum := by decide
  have hdescent : baseEnd_7289771 < baseStart_7289771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289785 : List Nat := [1, 2, 1, 4, 2, 4, 2, 7]
def baseStart_7289785 : Nat := 118140960795 + 7289785 * 2 ^ 59
def prefixEnd_7289785 : Nat := 4983230072969 + 3 ^ 40 * 7289785 * 2
def baseEnd_7289785 : Nat := 138635687886513570976385

theorem tailTrace_7289785 : CollatzResearch.WordTrace tailWord_7289785 prefixEnd_7289785 138635687886513570976385 := by
  unfold tailWord_7289785
  simp only [CollatzResearch.WordTrace]
  refine ⟨265880301895361416003902809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177253534596907610669268539 265880301895361416003902809)
  ·
    refine ⟨199410226421521062002927107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265880301895361416003902809 199410226421521062002927107)
    ·
      refine ⟨299115339632281593004390661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199410226421521062002927107 299115339632281593004390661)
      ·
        refine ⟨56084126181052798688323249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299115339632281593004390661 56084126181052798688323249)
        ·
          refine ⟨42063094635789599016242437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56084126181052798688323249 42063094635789599016242437)
          ·
            refine ⟨7886830244210549815545457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42063094635789599016242437 7886830244210549815545457)
            ·
              refine ⟨5915122683157912361659093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7886830244210549815545457 5915122683157912361659093)
              ·
                refine ⟨138635687886513570976385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5915122683157912361659093 138635687886513570976385)
                ·
                  rfl

theorem cell23_7289785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 7].length) (baseStart_7289785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289785 prefixEnd_7289785 := by exact prefixLift 7289785
  have htrace : WordTrace (prefixWord ++ tailWord_7289785) baseStart_7289785 baseEnd_7289785 := by
    simpa [prefixWord, tailWord_7289785, baseEnd_7289785] using wordTrace_append hprefix tailTrace_7289785
  have hstable : (prefixWord ++ tailWord_7289785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289785).length < 2 ^ (prefixWord ++ tailWord_7289785).sum := by decide
  have hdescent : baseEnd_7289785 < baseStart_7289785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289812 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7289812 : Nat := 118140960795 + 7289812 * 2 ^ 59
def prefixEnd_7289812 : Nat := 4983230072969 + 3 ^ 40 * 7289812 * 2
def baseEnd_7289812 : Nat := 3743177436913537810724771

theorem tailTrace_7289812 : CollatzResearch.WordTrace tailWord_7289812 prefixEnd_7289812 3743177436913537810724771 := by
  unfold tailWord_7289812
  simp only [CollatzResearch.WordTrace]
  refine ⟨132940643333131799807567845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177254191110842399743423793 132940643333131799807567845)
  ·
    refine ⟨24926370624962212463918971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132940643333131799807567845 24926370624962212463918971)
    ·
      refine ⟨37389555937443318695878457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24926370624962212463918971 37389555937443318695878457)
      ·
        refine ⟨28042166953082489021908843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37389555937443318695878457 28042166953082489021908843)
        ·
          refine ⟨42063250429623733532863265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28042166953082489021908843 42063250429623733532863265)
          ·
            refine ⟨31547437822217800149647449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42063250429623733532863265 31547437822217800149647449)
            ·
              refine ⟨23660578366663350112235587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31547437822217800149647449 23660578366663350112235587)
              ·
                refine ⟨35490867549995025168353381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23660578366663350112235587 35490867549995025168353381)
                ·
                  refine ⟨6654537665624067219066259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35490867549995025168353381 6654537665624067219066259)
                  ·
                    refine ⟨9981806498436100828599389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654537665624067219066259 9981806498436100828599389)
                    ·
                      refine ⟨3743177436913537810724771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981806498436100828599389 3743177436913537810724771)
                      ·
                        rfl

theorem cell23_7289812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7289812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289812 prefixEnd_7289812 := by exact prefixLift 7289812
  have htrace : WordTrace (prefixWord ++ tailWord_7289812) baseStart_7289812 baseEnd_7289812 := by
    simpa [prefixWord, tailWord_7289812, baseEnd_7289812] using wordTrace_append hprefix tailTrace_7289812
  have hstable : (prefixWord ++ tailWord_7289812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289812).length < 2 ^ (prefixWord ++ tailWord_7289812).sum := by decide
  have hdescent : baseEnd_7289812 < baseStart_7289812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289813 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7289813 : Nat := 118140960795 + 7289813 * 2 ^ 59
def prefixEnd_7289813 : Nat := 4983230072969 + 3 ^ 40 * 7289813 * 2
def baseEnd_7289813 : Nat := 3743177950394192306812267

theorem tailTrace_7289813 : CollatzResearch.WordTrace tailWord_7289813 prefixEnd_7289813 3743177950394192306812267 := by
  unfold tailWord_7289813
  simp only [CollatzResearch.WordTrace]
  refine ⟨265881323139259976785922093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177254215426173317857281395 265881323139259976785922093)
  ·
    refine ⟨99705496177222491294720785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265881323139259976785922093 99705496177222491294720785)
    ·
      refine ⟨74779122132916868471040589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99705496177222491294720785 74779122132916868471040589)
      ·
        refine ⟨28042170799843825676640221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74779122132916868471040589 28042170799843825676640221)
        ·
          refine ⟨10515814049941434628740083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28042170799843825676640221 10515814049941434628740083)
          ·
            refine ⟨15773721074912151943110125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515814049941434628740083 15773721074912151943110125)
            ·
              refine ⟨5915145403092056978666297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15773721074912151943110125 5915145403092056978666297)
              ·
                refine ⟨4436359052319042733999723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915145403092056978666297 4436359052319042733999723)
                ·
                  refine ⟨6654538578478564100999585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436359052319042733999723 6654538578478564100999585)
                  ·
                    refine ⟨4990903933858923075749689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654538578478564100999585 4990903933858923075749689)
                    ·
                      refine ⟨3743177950394192306812267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990903933858923075749689 3743177950394192306812267)
                      ·
                        rfl

theorem cell23_7289813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7289813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289813 prefixEnd_7289813 := by exact prefixLift 7289813
  have htrace : WordTrace (prefixWord ++ tailWord_7289813) baseStart_7289813 baseEnd_7289813 := by
    simpa [prefixWord, tailWord_7289813, baseEnd_7289813] using wordTrace_append hprefix tailTrace_7289813
  have hstable : (prefixWord ++ tailWord_7289813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289813).length < 2 ^ (prefixWord ++ tailWord_7289813).sum := by decide
  have hdescent : baseEnd_7289813 < baseStart_7289813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289839 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 1, 3, 2]
def baseStart_7289839 : Nat := 118140960795 + 7289839 * 2 ^ 59
def prefixEnd_7289839 : Nat := 4983230072969 + 3 ^ 40 * 7289839 * 2
def baseEnd_7289839 : Nat := 3743191300891209205087147

theorem tailTrace_7289839 : CollatzResearch.WordTrace tailWord_7289839 prefixEnd_7289839 3743191300891209205087147 := by
  unfold tailWord_7289839
  simp only [CollatzResearch.WordTrace]
  refine ⟨265882271437165783226368571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177254847624777188817579047 265882271437165783226368571)
  ·
    refine ⟨398823407155748674839552857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265882271437165783226368571 398823407155748674839552857)
    ·
      refine ⟨299117555366811506129664643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398823407155748674839552857 299117555366811506129664643)
      ·
        refine ⟨448676333050217259194496965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299117555366811506129664643 448676333050217259194496965)
        ·
          refine ⟨84126812446915736098968181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448676333050217259194496965 84126812446915736098968181)
          ·
            refine ⟨7886888666898350259278267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84126812446915736098968181 7886888666898350259278267)
            ·
              refine ⟨11830333000347525388917401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886888666898350259278267 11830333000347525388917401)
              ·
                refine ⟨8872749750260644041688051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11830333000347525388917401 8872749750260644041688051)
                ·
                  refine ⟨13309124625390966062532077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8872749750260644041688051 13309124625390966062532077)
                  ·
                    refine ⟨4990921734521612273449529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13309124625390966062532077 4990921734521612273449529)
                    ·
                      refine ⟨3743191300891209205087147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990921734521612273449529 3743191300891209205087147)
                      ·
                        rfl

theorem cell23_7289839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3, 2].length) (baseStart_7289839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289839 prefixEnd_7289839 := by exact prefixLift 7289839
  have htrace : WordTrace (prefixWord ++ tailWord_7289839) baseStart_7289839 baseEnd_7289839 := by
    simpa [prefixWord, tailWord_7289839, baseEnd_7289839] using wordTrace_append hprefix tailTrace_7289839
  have hstable : (prefixWord ++ tailWord_7289839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289839).length < 2 ^ (prefixWord ++ tailWord_7289839).sum := by decide
  have hdescent : baseEnd_7289839 < baseStart_7289839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289848 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_7289848 : Nat := 118140960795 + 7289848 * 2 ^ 59
def prefixEnd_7289848 : Nat := 4983230072969 + 3 ^ 40 * 7289848 * 2
def baseEnd_7289848 : Nat := 3743195922217099669874605

theorem tailTrace_7289848 : CollatzResearch.WordTrace tailWord_7289848 prefixEnd_7289848 3743195922217099669874605 := by
  unfold tailWord_7289848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132941299847066588881723099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177255066462755451842297465 132941299847066588881723099)
  ·
    refine ⟨199411949770599883322584649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132941299847066588881723099 199411949770599883322584649)
    ·
      refine ⟨149558962327949912491938487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199411949770599883322584649 149558962327949912491938487)
      ·
        refine ⟨224338443491924868737907731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149558962327949912491938487 224338443491924868737907731)
        ·
          refine ⟨336507665237887303106861597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224338443491924868737907731 336507665237887303106861597)
          ·
            refine ⟨126190374464207738665073099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336507665237887303106861597 126190374464207738665073099)
            ·
              refine ⟨189285561696311607997609649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126190374464207738665073099 189285561696311607997609649)
              ·
                refine ⟨141964171272233705998207237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189285561696311607997609649 141964171272233705998207237)
                ·
                  refine ⟨26618282113543819874663857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141964171272233705998207237 26618282113543819874663857)
                  ·
                    refine ⟨19963711585157864905997893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26618282113543819874663857 19963711585157864905997893)
                    ·
                      refine ⟨3743195922217099669874605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19963711585157864905997893 3743195922217099669874605)
                      ·
                        rfl

theorem cell23_7289848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_7289848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289848 prefixEnd_7289848 := by exact prefixLift 7289848
  have htrace : WordTrace (prefixWord ++ tailWord_7289848) baseStart_7289848 baseEnd_7289848 := by
    simpa [prefixWord, tailWord_7289848, baseEnd_7289848] using wordTrace_append hprefix tailTrace_7289848
  have hstable : (prefixWord ++ tailWord_7289848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289848).length < 2 ^ (prefixWord ++ tailWord_7289848).sum := by decide
  have hdescent : baseEnd_7289848 < baseStart_7289848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289852 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_7289852 : Nat := 118140960795 + 7289852 * 2 ^ 59
def prefixEnd_7289852 : Nat := 4983230072969 + 3 ^ 40 * 7289852 * 2
def baseEnd_7289852 : Nat := 3743197976139717654224587

theorem tailTrace_7289852 : CollatzResearch.WordTrace tailWord_7289852 prefixEnd_7289852 3743197976139717654224587 := by
  unfold tailWord_7289852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132941372793059343223295905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177255163724079124297727873 132941372793059343223295905)
  ·
    refine ⟨99706029594794507417471929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132941372793059343223295905 99706029594794507417471929)
    ·
      refine ⟨74779522196095880563103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99706029594794507417471929 74779522196095880563103947)
      ·
        refine ⟨112169283294143820844655921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74779522196095880563103947 112169283294143820844655921)
        ·
          refine ⟨84126962470607865633491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112169283294143820844655921 84126962470607865633491941)
          ·
            refine ⟨15773805463238974806279739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84126962470607865633491941 15773805463238974806279739)
            ·
              refine ⟨23660708194858462209419609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773805463238974806279739 23660708194858462209419609)
              ·
                refine ⟨17745531146143846657064707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23660708194858462209419609 17745531146143846657064707)
                ·
                  refine ⟨26618296719215769985597061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17745531146143846657064707 26618296719215769985597061)
                  ·
                    refine ⟨4990930634852956872299449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26618296719215769985597061 4990930634852956872299449)
                    ·
                      refine ⟨3743197976139717654224587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990930634852956872299449 3743197976139717654224587)
                      ·
                        rfl

theorem cell23_7289852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_7289852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289852 prefixEnd_7289852 := by exact prefixLift 7289852
  have htrace : WordTrace (prefixWord ++ tailWord_7289852) baseStart_7289852 baseEnd_7289852 := by
    simpa [prefixWord, tailWord_7289852, baseEnd_7289852] using wordTrace_append hprefix tailTrace_7289852
  have hstable : (prefixWord ++ tailWord_7289852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289852).length < 2 ^ (prefixWord ++ tailWord_7289852).sum := by decide
  have hdescent : baseEnd_7289852 < baseStart_7289852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289925 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_7289925 : Nat := 118140960795 + 7289925 * 2 ^ 59
def prefixEnd_7289925 : Nat := 4983230072969 + 3 ^ 40 * 7289925 * 2
def baseEnd_7289925 : Nat := 3743235460227495868611751

theorem tailTrace_7289925 : CollatzResearch.WordTrace tailWord_7289925 prefixEnd_7289925 3743235460227495868611751 := by
  unfold tailWord_7289925
  simp only [CollatzResearch.WordTrace]
  refine ⟨265885408114854219913999229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177256938743236146609332819 265885408114854219913999229)
  ·
    refine ⟨99707028043070332467749711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265885408114854219913999229 99707028043070332467749711)
    ·
      refine ⟨149560542064605498701624567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99707028043070332467749711 149560542064605498701624567)
      ·
        refine ⟨224340813096908248052436851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149560542064605498701624567 224340813096908248052436851)
        ·
          refine ⟨336511219645362372078655277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224340813096908248052436851 336511219645362372078655277)
          ·
            refine ⟨126191707367010889529495729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336511219645362372078655277 126191707367010889529495729)
            ·
              refine ⟨94643780525258167147121797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126191707367010889529495729 94643780525258167147121797)
              ·
                refine ⟨17745708848485906340085337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94643780525258167147121797 17745708848485906340085337)
                ·
                  refine ⟨13309281636364429755064003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17745708848485906340085337 13309281636364429755064003)
                  ·
                    refine ⟨19963922454546644632596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13309281636364429755064003 19963922454546644632596005)
                    ·
                      refine ⟨3743235460227495868611751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19963922454546644632596005 3743235460227495868611751)
                      ·
                        rfl

theorem cell23_7289925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_7289925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289925 prefixEnd_7289925 := by exact prefixLift 7289925
  have htrace : WordTrace (prefixWord ++ tailWord_7289925) baseStart_7289925 baseEnd_7289925 := by
    simpa [prefixWord, tailWord_7289925, baseEnd_7289925] using wordTrace_append hprefix tailTrace_7289925
  have hstable : (prefixWord ++ tailWord_7289925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289925).length < 2 ^ (prefixWord ++ tailWord_7289925).sum := by decide
  have hdescent : baseEnd_7289925 < baseStart_7289925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289945 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_7289945 : Nat := 118140960795 + 7289945 * 2 ^ 59
def prefixEnd_7289945 : Nat := 4983230072969 + 3 ^ 40 * 7289945 * 2
def baseEnd_7289945 : Nat := 3743245729840585790361659

theorem tailTrace_7289945 : CollatzResearch.WordTrace tailWord_7289945 prefixEnd_7289945 3743245729840585790361659 := by
  unfold tailWord_7289945
  simp only [CollatzResearch.WordTrace]
  refine ⟨265886137574781763329727289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177257425049854508886484859 265886137574781763329727289)
  ·
    refine ⟨199414603181086322497295467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265886137574781763329727289 199414603181086322497295467)
    ·
      refine ⟨299121904771629483745943201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199414603181086322497295467 299121904771629483745943201)
      ·
        refine ⟨224341428578722112809457401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299121904771629483745943201 224341428578722112809457401)
        ·
          refine ⟨168256071434041584607093051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224341428578722112809457401 168256071434041584607093051)
          ·
            refine ⟨252384107151062376910639577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168256071434041584607093051 252384107151062376910639577)
            ·
              refine ⟨189288080363296782682979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252384107151062376910639577 189288080363296782682979683)
              ·
                refine ⟨283932120544945174024469525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189288080363296782682979683 283932120544945174024469525)
                ·
                  refine ⟨13309318150544305032397009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283932120544945174024469525 13309318150544305032397009)
                  ·
                    refine ⟨9981988612908228774297757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13309318150544305032397009 9981988612908228774297757)
                    ·
                      refine ⟨3743245729840585790361659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9981988612908228774297757 3743245729840585790361659)
                      ·
                        rfl

theorem cell23_7289945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_7289945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289945 prefixEnd_7289945 := by exact prefixLift 7289945
  have htrace : WordTrace (prefixWord ++ tailWord_7289945) baseStart_7289945 baseEnd_7289945 := by
    simpa [prefixWord, tailWord_7289945, baseEnd_7289945] using wordTrace_append hprefix tailTrace_7289945
  have hstable : (prefixWord ++ tailWord_7289945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289945).length < 2 ^ (prefixWord ++ tailWord_7289945).sum := by decide
  have hdescent : baseEnd_7289945 < baseStart_7289945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289962 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7289962 : Nat := 118140960795 + 7289962 * 2 ^ 59
def prefixEnd_7289962 : Nat := 4983230072969 + 3 ^ 40 * 7289962 * 2
def baseEnd_7289962 : Nat := 3743254459011712223849081

theorem tailTrace_7289962 : CollatzResearch.WordTrace tailWord_7289962 prefixEnd_7289962 3743254459011712223849081 := by
  unfold tailWord_7289962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66471689403930043808274035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177257838410480116822064093 66471689403930043808274035)
  ·
    refine ⟨99707534105895065712411053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66471689403930043808274035 99707534105895065712411053)
    ·
      refine ⟨37390325289710649642154145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99707534105895065712411053 37390325289710649642154145)
      ·
        refine ⟨28042743967282987231615609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37390325289710649642154145 28042743967282987231615609)
        ·
          refine ⟨21032057975462240423711707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28042743967282987231615609 21032057975462240423711707)
          ·
            refine ⟨31548086963193360635567561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21032057975462240423711707 31548086963193360635567561)
            ·
              refine ⟨23661065222395020476675671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31548086963193360635567561 23661065222395020476675671)
              ·
                refine ⟨35491597833592530715013507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23661065222395020476675671 35491597833592530715013507)
                ·
                  refine ⟨53237396750388796072520261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35491597833592530715013507 53237396750388796072520261)
                  ·
                    refine ⟨9982011890697899263597549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53237396750388796072520261 9982011890697899263597549)
                    ·
                      refine ⟨3743254459011712223849081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982011890697899263597549 3743254459011712223849081)
                      ·
                        rfl

theorem cell23_7289962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7289962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289962 prefixEnd_7289962 := by exact prefixLift 7289962
  have htrace : WordTrace (prefixWord ++ tailWord_7289962) baseStart_7289962 baseEnd_7289962 := by
    simpa [prefixWord, tailWord_7289962, baseEnd_7289962] using wordTrace_append hprefix tailTrace_7289962
  have hstable : (prefixWord ++ tailWord_7289962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289962).length < 2 ^ (prefixWord ++ tailWord_7289962).sum := by decide
  have hdescent : baseEnd_7289962 < baseStart_7289962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7289965 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 8]
def baseStart_7289965 : Nat := 118140960795 + 7289965 * 2 ^ 59
def prefixEnd_7289965 : Nat := 4983230072969 + 3 ^ 40 * 7289965 * 2
def baseEnd_7289965 : Nat := 415917333272630634679063

theorem tailTrace_7289965 : CollatzResearch.WordTrace tailWord_7289965 prefixEnd_7289965 415917333272630634679063 := by
  unfold tailWord_7289965
  simp only [CollatzResearch.WordTrace]
  refine ⟨265886867034709306745455349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177257911356472871163636899 265886867034709306745455349)
  ·
    refine ⟨24926893784503997507386439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265886867034709306745455349 24926893784503997507386439)
    ·
      refine ⟨37390340676755996261079659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24926893784503997507386439 37390340676755996261079659)
      ·
        refine ⟨56085511015133994391619489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37390340676755996261079659 56085511015133994391619489)
        ·
          refine ⟨42064133261350495793714617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56085511015133994391619489 42064133261350495793714617)
          ·
            refine ⟨31548099946012871845285963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42064133261350495793714617 31548099946012871845285963)
            ·
              refine ⟨47322149919019307767928945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31548099946012871845285963 47322149919019307767928945)
              ·
                refine ⟨35491612439264480825946709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47322149919019307767928945 35491612439264480825946709)
                ·
                  refine ⟨415917333272630634679063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35491612439264480825946709 415917333272630634679063)
                  ·
                    rfl

theorem cell23_7289965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_7289965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7289965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7289965 prefixEnd_7289965 := by exact prefixLift 7289965
  have htrace : WordTrace (prefixWord ++ tailWord_7289965) baseStart_7289965 baseEnd_7289965 := by
    simpa [prefixWord, tailWord_7289965, baseEnd_7289965] using wordTrace_append hprefix tailTrace_7289965
  have hstable : (prefixWord ++ tailWord_7289965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7289965).length < 2 ^ (prefixWord ++ tailWord_7289965).sum := by decide
  have hdescent : baseEnd_7289965 < baseStart_7289965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7289965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290012 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7290012 : Nat := 118140960795 + 7290012 * 2 ^ 59
def prefixEnd_7290012 : Nat := 4983230072969 + 3 ^ 40 * 7290012 * 2
def baseEnd_7290012 : Nat := 1247760044348145676074617

theorem tailTrace_7290012 : CollatzResearch.WordTrace tailWord_7290012 prefixEnd_7290012 1247760044348145676074617 := by
  unfold tailWord_7290012
  simp only [CollatzResearch.WordTrace]
  refine ⟨132944290632769516886208145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177259054177026022514944193 132944290632769516886208145)
  ·
    refine ⟨99708217974577137664656109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132944290632769516886208145 99708217974577137664656109)
    ·
      refine ⟨37390581740466426624246041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99708217974577137664656109 37390581740466426624246041)
      ·
        refine ⟨28042936305349819968184531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37390581740466426624246041 28042936305349819968184531)
        ·
          refine ⟨42064404458024729952276797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28042936305349819968184531 42064404458024729952276797)
          ·
            refine ⟨15774151671759273732103799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42064404458024729952276797 15774151671759273732103799)
            ·
              refine ⟨23661227507638910598155699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774151671759273732103799 23661227507638910598155699)
              ·
                refine ⟨35491841261458365897233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23661227507638910598155699 35491841261458365897233549)
                ·
                  refine ⟨13309440473046887211462581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35491841261458365897233549 13309440473046887211462581)
                  ·
                    refine ⟨1247760044348145676074617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309440473046887211462581 1247760044348145676074617)
                    ·
                      rfl

theorem cell23_7290012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7290012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290012 prefixEnd_7290012 := by exact prefixLift 7290012
  have htrace : WordTrace (prefixWord ++ tailWord_7290012) baseStart_7290012 baseEnd_7290012 := by
    simpa [prefixWord, tailWord_7290012, baseEnd_7290012] using wordTrace_append hprefix tailTrace_7290012
  have hstable : (prefixWord ++ tailWord_7290012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290012).length < 2 ^ (prefixWord ++ tailWord_7290012).sum := by decide
  have hdescent : baseEnd_7290012 < baseStart_7290012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290045 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7290045 : Nat := 118140960795 + 7290045 * 2 ^ 59
def prefixEnd_7290045 : Nat := 4983230072969 + 3 ^ 40 * 7290045 * 2
def baseEnd_7290045 : Nat := 3743297077906035399111199

theorem tailTrace_7290045 : CollatzResearch.WordTrace tailWord_7290045 prefixEnd_7290045 3743297077906035399111199 := by
  unfold tailWord_7290045
  simp only [CollatzResearch.WordTrace]
  refine ⟨265889784874419480408367589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177259856582946320272245059 265889784874419480408367589)
  ·
    refine ⟨49854334663953652576568923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265889784874419480408367589 49854334663953652576568923)
    ·
      refine ⟨74781501995930478864853385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49854334663953652576568923 74781501995930478864853385)
      ·
        refine ⟨56086126496947859148640039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74781501995930478864853385 56086126496947859148640039)
        ·
          refine ⟨84129189745421788722960059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56086126496947859148640039 84129189745421788722960059)
          ·
            refine ⟨126193784618132683084440089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84129189745421788722960059 126193784618132683084440089)
            ·
              refine ⟨94645338463599512313330067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126193784618132683084440089 94645338463599512313330067)
              ·
                refine ⟨141968007695399268469995101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94645338463599512313330067 141968007695399268469995101)
                ·
                  refine ⟨53238002885774725676248163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141968007695399268469995101 53238002885774725676248163)
                  ·
                    refine ⟨79857004328662088514372245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53238002885774725676248163 79857004328662088514372245)
                    ·
                      refine ⟨3743297077906035399111199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79857004328662088514372245 3743297077906035399111199)
                      ·
                        rfl

theorem cell23_7290045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7290045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290045 prefixEnd_7290045 := by exact prefixLift 7290045
  have htrace : WordTrace (prefixWord ++ tailWord_7290045) baseStart_7290045 baseEnd_7290045 := by
    simpa [prefixWord, tailWord_7290045, baseEnd_7290045] using wordTrace_append hprefix tailTrace_7290045
  have hstable : (prefixWord ++ tailWord_7290045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290045).length < 2 ^ (prefixWord ++ tailWord_7290045).sum := by decide
  have hdescent : baseEnd_7290045 < baseStart_7290045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290049 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7290049 : Nat := 118140960795 + 7290049 * 2 ^ 59
def prefixEnd_7290049 : Nat := 4983230072969 + 3 ^ 40 * 7290049 * 2
def baseEnd_7290049 : Nat := 3743299131828653383461181

theorem tailTrace_7290049 : CollatzResearch.WordTrace tailWord_7290049 prefixEnd_7290049 3743299131828653383461181 := by
  unfold tailWord_7290049
  simp only [CollatzResearch.WordTrace]
  refine ⟨265889930766404989091513201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177259953844269992727675467 265889930766404989091513201)
  ·
    refine ⟨199417448074803741818634901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265889930766404989091513201 199417448074803741818634901)
    ·
      refine ⟨9347692878506425397748511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199417448074803741818634901 9347692878506425397748511)
      ·
        refine ⟨14021539317759638096622767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9347692878506425397748511 14021539317759638096622767)
        ·
          refine ⟨21032308976639457144934151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021539317759638096622767 21032308976639457144934151)
          ·
            refine ⟨31548463464959185717401227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21032308976639457144934151 31548463464959185717401227)
            ·
              refine ⟨47322695197438778576101841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31548463464959185717401227 47322695197438778576101841)
              ·
                refine ⟨35492021398079083932076381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47322695197438778576101841 35492021398079083932076381)
                ·
                  refine ⟨13309508024279656474528643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35492021398079083932076381 13309508024279656474528643)
                  ·
                    refine ⟨19964262036419484711792965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13309508024279656474528643 19964262036419484711792965)
                    ·
                      refine ⟨3743299131828653383461181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19964262036419484711792965 3743299131828653383461181)
                      ·
                        rfl

theorem cell23_7290049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7290049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290049 prefixEnd_7290049 := by exact prefixLift 7290049
  have htrace : WordTrace (prefixWord ++ tailWord_7290049) baseStart_7290049 baseEnd_7290049 := by
    simpa [prefixWord, tailWord_7290049, baseEnd_7290049] using wordTrace_append hprefix tailTrace_7290049
  have hstable : (prefixWord ++ tailWord_7290049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290049).length < 2 ^ (prefixWord ++ tailWord_7290049).sum := by decide
  have hdescent : baseEnd_7290049 < baseStart_7290049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290066 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7290066 : Nat := 118140960795 + 7290066 * 2 ^ 59
def prefixEnd_7290066 : Nat := 4983230072969 + 3 ^ 40 * 7290066 * 2
def baseEnd_7290066 : Nat := 3743307860999779816948603

theorem tailTrace_7290066 : CollatzResearch.WordTrace tailWord_7290066 prefixEnd_7290066 3743307860999779816948603 := by
  unfold tailWord_7290066
  simp only [CollatzResearch.WordTrace]
  refine ⟨66472637701835850248720513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177260367204895600663254701 66472637701835850248720513)
  ·
    refine ⟨49854478276376887686540385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66472637701835850248720513 49854478276376887686540385)
    ·
      refine ⟨37390858707282665764905289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49854478276376887686540385 37390858707282665764905289)
      ·
        refine ⟨28043144030461999323678967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37390858707282665764905289 28043144030461999323678967)
        ·
          refine ⟨42064716045692998985518451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28043144030461999323678967 42064716045692998985518451)
          ·
            refine ⟨63097074068539498478277677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42064716045692998985518451 63097074068539498478277677)
            ·
              refine ⟨23661402775702311929354129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63097074068539498478277677 23661402775702311929354129)
              ·
                refine ⟨17746052081776733947015597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23661402775702311929354129 17746052081776733947015597)
                ·
                  refine ⟨6654769530666275230130849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17746052081776733947015597 6654769530666275230130849)
                  ·
                    refine ⟨4991077147999706422598137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654769530666275230130849 4991077147999706422598137)
                    ·
                      refine ⟨3743307860999779816948603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991077147999706422598137 3743307860999779816948603)
                      ·
                        rfl

theorem cell23_7290066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7290066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290066 prefixEnd_7290066 := by exact prefixLift 7290066
  have htrace : WordTrace (prefixWord ++ tailWord_7290066) baseStart_7290066 baseEnd_7290066 := by
    simpa [prefixWord, tailWord_7290066, baseEnd_7290066] using wordTrace_append hprefix tailTrace_7290066
  have hstable : (prefixWord ++ tailWord_7290066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290066).length < 2 ^ (prefixWord ++ tailWord_7290066).sum := by decide
  have hdescent : baseEnd_7290066 < baseStart_7290066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290069 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7290069 : Nat := 118140960795 + 7290069 * 2 ^ 59
def prefixEnd_7290069 : Nat := 4983230072969 + 3 ^ 40 * 7290069 * 2
def baseEnd_7290069 : Nat := 3743309401441743305211089

theorem tailTrace_7290069 : CollatzResearch.WordTrace tailWord_7290069 prefixEnd_7290069 3743309401441743305211089 := by
  unfold tailWord_7290069
  simp only [CollatzResearch.WordTrace]
  refine ⟨265890660226332532507241261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177260440150888355004827507 265890660226332532507241261)
  ·
    refine ⟨99708997584874699690215473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265890660226332532507241261 99708997584874699690215473)
    ·
      refine ⟨74781748188656024767661605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99708997584874699690215473 74781748188656024767661605)
      ·
        refine ⟨14021577785373004643936551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74781748188656024767661605 14021577785373004643936551)
        ·
          refine ⟨21032366678059506965904827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021577785373004643936551 21032366678059506965904827)
          ·
            refine ⟨31548550017089260448857241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21032366678059506965904827 31548550017089260448857241)
            ·
              refine ⟨23661412512816945336642931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31548550017089260448857241 23661412512816945336642931)
              ·
                refine ⟨35492118769225418004964397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23661412512816945336642931 35492118769225418004964397)
                ·
                  refine ⟨13309544538459531751861649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35492118769225418004964397 13309544538459531751861649)
                  ·
                    refine ⟨9982158403844648813896237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13309544538459531751861649 9982158403844648813896237)
                    ·
                      refine ⟨3743309401441743305211089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982158403844648813896237 3743309401441743305211089)
                      ·
                        rfl

theorem cell23_7290069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7290069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290069 prefixEnd_7290069 := by exact prefixLift 7290069
  have htrace : WordTrace (prefixWord ++ tailWord_7290069) baseStart_7290069 baseEnd_7290069 := by
    simpa [prefixWord, tailWord_7290069, baseEnd_7290069] using wordTrace_append hprefix tailTrace_7290069
  have hstable : (prefixWord ++ tailWord_7290069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290069).length < 2 ^ (prefixWord ++ tailWord_7290069).sum := by decide
  have hdescent : baseEnd_7290069 < baseStart_7290069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290070 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7290070 : Nat := 118140960795 + 7290070 * 2 ^ 59
def prefixEnd_7290070 : Nat := 4983230072969 + 3 ^ 40 * 7290070 * 2
def baseEnd_7290070 : Nat := 3743309914922397801298585

theorem tailTrace_7290070 : CollatzResearch.WordTrace tailWord_7290070 prefixEnd_7290070 3743309914922397801298585 := by
  unfold tailWord_7290070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16618168543708056854876729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177260464466219273118685109 16618168543708056854876729)
  ·
    refine ⟨12463626407781042641157547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16618168543708056854876729 12463626407781042641157547)
    ·
      refine ⟨18695439611671563961736321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12463626407781042641157547 18695439611671563961736321)
      ·
        refine ⟨14021579708753672971302241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18695439611671563961736321 14021579708753672971302241)
        ·
          refine ⟨10516184781565254728476681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14021579708753672971302241 10516184781565254728476681)
          ·
            refine ⟨7887138586173941046357511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10516184781565254728476681 7887138586173941046357511)
            ·
              refine ⟨11830707879260911569536267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887138586173941046357511 11830707879260911569536267)
              ·
                refine ⟨17746061818891367354304401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830707879260911569536267 17746061818891367354304401)
                ·
                  refine ⟨13309546364168525515728301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17746061818891367354304401 13309546364168525515728301)
                  ·
                    refine ⟨4991079886563197068398113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13309546364168525515728301 4991079886563197068398113)
                    ·
                      refine ⟨3743309914922397801298585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991079886563197068398113 3743309914922397801298585)
                      ·
                        rfl

theorem cell23_7290070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7290070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290070 prefixEnd_7290070 := by exact prefixLift 7290070
  have htrace : WordTrace (prefixWord ++ tailWord_7290070) baseStart_7290070 baseEnd_7290070 := by
    simpa [prefixWord, tailWord_7290070, baseEnd_7290070] using wordTrace_append hprefix tailTrace_7290070
  have hstable : (prefixWord ++ tailWord_7290070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290070).length < 2 ^ (prefixWord ++ tailWord_7290070).sum := by decide
  have hdescent : baseEnd_7290070 < baseStart_7290070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290099 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 3]
def baseStart_7290099 : Nat := 118140960795 + 7290099 * 2 ^ 59
def prefixEnd_7290099 : Nat := 4983230072969 + 3 ^ 40 * 7290099 * 2
def baseEnd_7290099 : Nat := 3743324805861378187835951

theorem tailTrace_7290099 : CollatzResearch.WordTrace tailWord_7290099 prefixEnd_7290099 3743324805861378187835951 := by
  unfold tailWord_7290099
  simp only [CollatzResearch.WordTrace]
  refine ⟨265891754416223847630833351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177261169610815898420555567 265891754416223847630833351)
  ·
    refine ⟨398837631624335771446250027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265891754416223847630833351 398837631624335771446250027)
    ·
      refine ⟨598256447436503657169375041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398837631624335771446250027 598256447436503657169375041)
      ·
        refine ⟨448692335577377742877031281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598256447436503657169375041 448692335577377742877031281)
        ·
          refine ⟨336519251683033307157773461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448692335577377742877031281 336519251683033307157773461)
          ·
            refine ⟨15774339922642186273020631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336519251683033307157773461 15774339922642186273020631)
            ·
              refine ⟨23661509883963279409530947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774339922642186273020631 23661509883963279409530947)
              ·
                refine ⟨35492264825944919114296421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23661509883963279409530947 35492264825944919114296421)
                ·
                  refine ⟨6654799654864672333930579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35492264825944919114296421 6654799654864672333930579)
                  ·
                    refine ⟨9982199482297008500895869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654799654864672333930579 9982199482297008500895869)
                    ·
                      refine ⟨3743324805861378187835951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982199482297008500895869 3743324805861378187835951)
                      ·
                        rfl

theorem cell23_7290099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_7290099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290099 prefixEnd_7290099 := by exact prefixLift 7290099
  have htrace : WordTrace (prefixWord ++ tailWord_7290099) baseStart_7290099 baseEnd_7290099 := by
    simpa [prefixWord, tailWord_7290099, baseEnd_7290099] using wordTrace_append hprefix tailTrace_7290099
  have hstable : (prefixWord ++ tailWord_7290099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290099).length < 2 ^ (prefixWord ++ tailWord_7290099).sum := by decide
  have hdescent : baseEnd_7290099 < baseStart_7290099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290116 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_7290116 : Nat := 118140960795 + 7290116 * 2 ^ 59
def prefixEnd_7290116 : Nat := 4983230072969 + 3 ^ 40 * 7290116 * 2
def baseEnd_7290116 : Nat := 3743333535032504621323373

theorem tailTrace_7290116 : CollatzResearch.WordTrace tailWord_7290116 prefixEnd_7290116 3743333535032504621323373 := by
  unfold tailWord_7290116
  simp only [CollatzResearch.WordTrace]
  refine ⟨132946187228581129767101101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177261582971441506356134801 132946187228581129767101101)
  ·
    refine ⟨49854820210717923662662913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132946187228581129767101101 49854820210717923662662913)
    ·
      refine ⟨37391115158038442746997185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49854820210717923662662913 37391115158038442746997185)
      ·
        refine ⟨28043336368528832060247889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37391115158038442746997185 28043336368528832060247889)
        ·
          refine ⟨21032502276396624045185917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28043336368528832060247889 21032502276396624045185917)
          ·
            refine ⟨7887188353648734016944719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21032502276396624045185917 7887188353648734016944719)
            ·
              refine ⟨11830782530473101025417079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887188353648734016944719 11830782530473101025417079)
              ·
                refine ⟨17746173795709651538125619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830782530473101025417079 17746173795709651538125619)
                ·
                  refine ⟨26619260693564477307188429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746173795709651538125619 26619260693564477307188429)
                  ·
                    refine ⟨9982222760086678990195661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26619260693564477307188429 9982222760086678990195661)
                    ·
                      refine ⟨3743333535032504621323373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982222760086678990195661 3743333535032504621323373)
                      ·
                        rfl

theorem cell23_7290116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_7290116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290116 prefixEnd_7290116 := by exact prefixLift 7290116
  have htrace : WordTrace (prefixWord ++ tailWord_7290116) baseStart_7290116 baseEnd_7290116 := by
    simpa [prefixWord, tailWord_7290116, baseEnd_7290116] using wordTrace_append hprefix tailTrace_7290116
  have hstable : (prefixWord ++ tailWord_7290116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290116).length < 2 ^ (prefixWord ++ tailWord_7290116).sum := by decide
  have hdescent : baseEnd_7290116 < baseStart_7290116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290126 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7290126 : Nat := 118140960795 + 7290126 * 2 ^ 59
def prefixEnd_7290126 : Nat := 4983230072969 + 3 ^ 40 * 7290126 * 2
def baseEnd_7290126 : Nat := 3743338669839049582198327

theorem tailTrace_7290126 : CollatzResearch.WordTrace tailWord_7290126 prefixEnd_7290126 3743338669839049582198327 := by
  unfold tailWord_7290126
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236592398390753905258279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177261826124750687494710821 33236592398390753905258279)
  ·
    refine ⟨49854888597586130857887419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33236592398390753905258279 49854888597586130857887419)
    ·
      refine ⟨74782332896379196286831129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49854888597586130857887419 74782332896379196286831129)
      ·
        refine ⟨56086749672284397215123347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74782332896379196286831129 56086749672284397215123347)
        ·
          refine ⟨84130124508426595822685021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56086749672284397215123347 84130124508426595822685021)
          ·
            refine ⟨31548796690659973433506883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84130124508426595822685021 31548796690659973433506883)
            ·
              refine ⟨47323195035989960150260325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31548796690659973433506883 47323195035989960150260325)
              ·
                refine ⟨8873099069248117528173811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47323195035989960150260325 8873099069248117528173811)
                ·
                  refine ⟨13309648603872176292260717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873099069248117528173811 13309648603872176292260717)
                  ·
                    refine ⟨4991118226452066109597769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13309648603872176292260717 4991118226452066109597769)
                    ·
                      refine ⟨3743338669839049582198327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991118226452066109597769 3743338669839049582198327)
                      ·
                        rfl

theorem cell23_7290126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7290126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290126 prefixEnd_7290126 := by exact prefixLift 7290126
  have htrace : WordTrace (prefixWord ++ tailWord_7290126) baseStart_7290126 baseEnd_7290126 := by
    simpa [prefixWord, tailWord_7290126, baseEnd_7290126] using wordTrace_append hprefix tailTrace_7290126
  have hstable : (prefixWord ++ tailWord_7290126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290126).length < 2 ^ (prefixWord ++ tailWord_7290126).sum := by decide
  have hdescent : baseEnd_7290126 < baseStart_7290126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290156 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_7290156 : Nat := 118140960795 + 7290156 * 2 ^ 59
def prefixEnd_7290156 : Nat := 4983230072969 + 3 ^ 40 * 7290156 * 2
def baseEnd_7290156 : Nat := 3743354074258684464823189

theorem tailTrace_7290156 : CollatzResearch.WordTrace tailWord_7290156 prefixEnd_7290156 3743354074258684464823189 := by
  unfold tailWord_7290156
  simp only [CollatzResearch.WordTrace]
  refine ⟨132946916688508673182829161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177262555584678230910438881 132946916688508673182829161)
  ·
    refine ⟨99710187516381504887121871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132946916688508673182829161 99710187516381504887121871)
    ·
      refine ⟨149565281274572257330682807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99710187516381504887121871 149565281274572257330682807)
      ·
        refine ⟨224347921911858385996024211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149565281274572257330682807 224347921911858385996024211)
        ·
          refine ⟨336521882867787578994036317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224347921911858385996024211 336521882867787578994036317)
          ·
            refine ⟨126195706075420342122763619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336521882867787578994036317 126195706075420342122763619)
            ·
              refine ⟨189293559113130513184145429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126195706075420342122763619 189293559113130513184145429)
              ·
                refine ⟨8873135583427992805506817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189293559113130513184145429 8873135583427992805506817)
                ·
                  refine ⟨6654851687570994604130113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873135583427992805506817 6654851687570994604130113)
                  ·
                    refine ⟨4991138765678245953097585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6654851687570994604130113 4991138765678245953097585)
                    ·
                      refine ⟨3743354074258684464823189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991138765678245953097585 3743354074258684464823189)
                      ·
                        rfl

theorem cell23_7290156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_7290156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290156 prefixEnd_7290156 := by exact prefixLift 7290156
  have htrace : WordTrace (prefixWord ++ tailWord_7290156) baseStart_7290156 baseEnd_7290156 := by
    simpa [prefixWord, tailWord_7290156, baseEnd_7290156] using wordTrace_append hprefix tailTrace_7290156
  have hstable : (prefixWord ++ tailWord_7290156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290156).length < 2 ^ (prefixWord ++ tailWord_7290156).sum := by decide
  have hdescent : baseEnd_7290156 < baseStart_7290156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290202 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_7290202 : Nat := 118140960795 + 7290202 * 2 ^ 59
def prefixEnd_7290202 : Nat := 4983230072969 + 3 ^ 40 * 7290202 * 2
def baseEnd_7290202 : Nat := 3743377694368791284847977

theorem tailTrace_7290202 : CollatzResearch.WordTrace tailWord_7290202 prefixEnd_7290202 3743377694368791284847977 := by
  unfold tailWord_7290202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66473877783712674055458215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177263674089900464147888573 66473877783712674055458215)
  ·
    refine ⟨99710816675569011083187323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66473877783712674055458215 99710816675569011083187323)
    ·
      refine ⟨149566225013353516624780985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99710816675569011083187323 149566225013353516624780985)
      ·
        refine ⟨112174668760015137468585739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149566225013353516624780985 112174668760015137468585739)
        ·
          refine ⟨168262003140022706202878609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112174668760015137468585739 168262003140022706202878609)
          ·
            refine ⟨126196502355017029652158957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168262003140022706202878609 126196502355017029652158957)
            ·
              refine ⟨47323688383131386119559609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126196502355017029652158957 47323688383131386119559609)
              ·
                refine ⟨35492766287348539589669707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47323688383131386119559609 35492766287348539589669707)
                ·
                  refine ⟨53239149431022809384504561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35492766287348539589669707 53239149431022809384504561)
                  ·
                    refine ⟨39929362073267107038378421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53239149431022809384504561 39929362073267107038378421)
                    ·
                      refine ⟨3743377694368791284847977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39929362073267107038378421 3743377694368791284847977)
                      ·
                        rfl

theorem cell23_7290202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_7290202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290202 prefixEnd_7290202 := by exact prefixLift 7290202
  have htrace : WordTrace (prefixWord ++ tailWord_7290202) baseStart_7290202 baseEnd_7290202 := by
    simpa [prefixWord, tailWord_7290202, baseEnd_7290202] using wordTrace_append hprefix tailTrace_7290202
  have hstable : (prefixWord ++ tailWord_7290202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290202).length < 2 ^ (prefixWord ++ tailWord_7290202).sum := by decide
  have hdescent : baseEnd_7290202 < baseStart_7290202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290252 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 8]
def baseStart_7290252 : Nat := 118140960795 + 7290252 * 2 ^ 59
def prefixEnd_7290252 : Nat := 4983230072969 + 3 ^ 40 * 7290252 * 2
def baseEnd_7290252 : Nat := 415933707600168454358083

theorem tailTrace_7290252 : CollatzResearch.WordTrace tailWord_7290252 prefixEnd_7290252 415933707600168454358083 := by
  unfold tailWord_7290252
  simp only [CollatzResearch.WordTrace]
  refine ⟨132948667392334777380576505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177264889856446369840768673 132948667392334777380576505)
  ·
    refine ⟨99711500544251083035432379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132948667392334777380576505 99711500544251083035432379)
    ·
      refine ⟨149567250816376624553148569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99711500544251083035432379 149567250816376624553148569)
      ·
        refine ⟨112175438112282468414861427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149567250816376624553148569 112175438112282468414861427)
        ·
          refine ⟨168263157168423702622292141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112175438112282468414861427 168263157168423702622292141)
          ·
            refine ⟨63098683938158888483359553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168263157168423702622292141 63098683938158888483359553)
            ·
              refine ⟨47324012953619166362519665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63098683938158888483359553 47324012953619166362519665)
              ·
                refine ⟨35493009715214374771889749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47324012953619166362519665 35493009715214374771889749)
                ·
                  refine ⟨415933707600168454358083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35493009715214374771889749 415933707600168454358083)
                  ·
                    rfl

theorem cell23_7290252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_7290252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290252 prefixEnd_7290252 := by exact prefixLift 7290252
  have htrace : WordTrace (prefixWord ++ tailWord_7290252) baseStart_7290252 baseEnd_7290252 := by
    simpa [prefixWord, tailWord_7290252, baseEnd_7290252] using wordTrace_append hprefix tailTrace_7290252
  have hstable : (prefixWord ++ tailWord_7290252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290252).length < 2 ^ (prefixWord ++ tailWord_7290252).sum := by decide
  have hdescent : baseEnd_7290252 < baseStart_7290252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290269 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 8]
def baseStart_7290269 : Nat := 118140960795 + 7290269 * 2 ^ 59
def prefixEnd_7290269 : Nat := 4983230072969 + 3 ^ 40 * 7290269 * 2
def baseEnd_7290269 : Nat := 415934677508071391412241

theorem tailTrace_7290269 : CollatzResearch.WordTrace tailWord_7290269 prefixEnd_7290269 415934677508071391412241 := by
  unfold tailWord_7290269
  simp only [CollatzResearch.WordTrace]
  refine ⟨265897954825607966664521861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177265303217071977776347907 265897954825607966664521861)
  ·
    refine ⟨49855866529801493749597849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265897954825607966664521861 49855866529801493749597849)
    ·
      refine ⟨37391899897351120312198387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49855866529801493749597849 37391899897351120312198387)
      ·
        refine ⟨56087849846026680468297581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37391899897351120312198387 56087849846026680468297581)
        ·
          refine ⟨21032943692260005175611593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56087849846026680468297581 21032943692260005175611593)
          ·
            refine ⟨15774707769195003881708695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21032943692260005175611593 15774707769195003881708695)
            ·
              refine ⟨23662061653792505822563043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774707769195003881708695 23662061653792505822563043)
              ·
                refine ⟨35493092480688758733844565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23662061653792505822563043 35493092480688758733844565)
                ·
                  refine ⟨415934677508071391412241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35493092480688758733844565 415934677508071391412241)
                  ·
                    rfl

theorem cell23_7290269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_7290269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290269 prefixEnd_7290269 := by exact prefixLift 7290269
  have htrace : WordTrace (prefixWord ++ tailWord_7290269) baseStart_7290269 baseEnd_7290269 := by
    simpa [prefixWord, tailWord_7290269, baseEnd_7290269] using wordTrace_append hprefix tailTrace_7290269
  have hstable : (prefixWord ++ tailWord_7290269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290269).length < 2 ^ (prefixWord ++ tailWord_7290269).sum := by decide
  have hdescent : baseEnd_7290269 < baseStart_7290269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290272 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7290272 : Nat := 118140960795 + 7290272 * 2 ^ 59
def prefixEnd_7290272 : Nat := 4983230072969 + 3 ^ 40 * 7290272 * 2
def baseEnd_7290272 : Nat := 3743413638014606010972655

theorem tailTrace_7290272 : CollatzResearch.WordTrace tailWord_7290272 prefixEnd_7290272 3743413638014606010972655 := by
  unfold tailWord_7290272
  simp only [CollatzResearch.WordTrace]
  refine ⟨132949032122298549088440535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177265376163064732117920713 132949032122298549088440535)
  ·
    refine ⟨199423548183447823632660803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132949032122298549088440535 199423548183447823632660803)
    ·
      refine ⟨299135322275171735448991205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199423548183447823632660803 299135322275171735448991205)
      ·
        refine ⟨56087872926594700396685851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299135322275171735448991205 56087872926594700396685851)
        ·
          refine ⟨84131809389892050595028777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56087872926594700396685851 84131809389892050595028777)
          ·
            refine ⟨63098857042419037946271583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84131809389892050595028777 63098857042419037946271583)
            ·
              refine ⟨94648285563628556919407375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63098857042419037946271583 94648285563628556919407375)
              ·
                refine ⟨141972428345442835379111063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94648285563628556919407375 141972428345442835379111063)
                ·
                  refine ⟨212958642518164253068666595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141972428345442835379111063 212958642518164253068666595)
                  ·
                    refine ⟨319437963777246379602999893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212958642518164253068666595 319437963777246379602999893)
                    ·
                      refine ⟨3743413638014606010972655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319437963777246379602999893 3743413638014606010972655)
                      ·
                        rfl

theorem cell23_7290272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7290272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290272 prefixEnd_7290272 := by exact prefixLift 7290272
  have htrace : WordTrace (prefixWord ++ tailWord_7290272) baseStart_7290272 baseEnd_7290272 := by
    simpa [prefixWord, tailWord_7290272, baseEnd_7290272] using wordTrace_append hprefix tailTrace_7290272
  have hstable : (prefixWord ++ tailWord_7290272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290272).length < 2 ^ (prefixWord ++ tailWord_7290272).sum := by decide
  have hdescent : baseEnd_7290272 < baseStart_7290272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290296 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_7290296 : Nat := 118140960795 + 7290296 * 2 ^ 59
def prefixEnd_7290296 : Nat := 4983230072969 + 3 ^ 40 * 7290296 * 2
def baseEnd_7290296 : Nat := 3743425961550313917072545

theorem tailTrace_7290296 : CollatzResearch.WordTrace tailWord_7290296 prefixEnd_7290296 3743425961550313917072545 := by
  unfold tailWord_7290296
  simp only [CollatzResearch.WordTrace]
  refine ⟨132949469798255075137877371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177265959731006766850503161 132949469798255075137877371)
  ·
    refine ⟨199424204697382612706816057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132949469798255075137877371 199424204697382612706816057)
    ·
      refine ⟨149568153523036959530112043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199424204697382612706816057 149568153523036959530112043)
      ·
        refine ⟨224352230284555439295168065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149568153523036959530112043 224352230284555439295168065)
        ·
          refine ⟨168264172713416579471376049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224352230284555439295168065 168264172713416579471376049)
          ·
            refine ⟨126198129535062434603532037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168264172713416579471376049 126198129535062434603532037)
            ·
              refine ⟨23662149287824206488162257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126198129535062434603532037 23662149287824206488162257)
              ·
                refine ⟨17746611965868154866121693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662149287824206488162257 17746611965868154866121693)
                ·
                  refine ⟨6654979487200558074795635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17746611965868154866121693 6654979487200558074795635)
                  ·
                    refine ⟨9982469230800837112193453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654979487200558074795635 9982469230800837112193453)
                    ·
                      refine ⟨3743425961550313917072545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982469230800837112193453 3743425961550313917072545)
                      ·
                        rfl

theorem cell23_7290296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_7290296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290296 prefixEnd_7290296 := by exact prefixLift 7290296
  have htrace : WordTrace (prefixWord ++ tailWord_7290296) baseStart_7290296 baseEnd_7290296 := by
    simpa [prefixWord, tailWord_7290296, baseEnd_7290296] using wordTrace_append hprefix tailTrace_7290296
  have hstable : (prefixWord ++ tailWord_7290296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290296).length < 2 ^ (prefixWord ++ tailWord_7290296).sum := by decide
  have hdescent : baseEnd_7290296 < baseStart_7290296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290316 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_7290316 : Nat := 118140960795 + 7290316 * 2 ^ 59
def prefixEnd_7290316 : Nat := 4983230072969 + 3 ^ 40 * 7290316 * 2
def baseEnd_7290316 : Nat := 1247812077054467946274151

theorem tailTrace_7290316 : CollatzResearch.WordTrace tailWord_7290316 prefixEnd_7290316 1247812077054467946274151 := by
  unfold tailWord_7290316
  simp only [CollatzResearch.WordTrace]
  refine ⟨132949834528218846845741401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177266446037625129127655201 132949834528218846845741401)
  ·
    refine ⟨99712375896164135134306051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132949834528218846845741401 99712375896164135134306051)
    ·
      refine ⟨149568563844246202701459077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99712375896164135134306051 149568563844246202701459077)
      ·
        refine ⟨28044105720796163006523577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149568563844246202701459077 28044105720796163006523577)
        ·
          refine ⟨21033079290597122254892683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28044105720796163006523577 21033079290597122254892683)
          ·
            refine ⟨31549618935895683382339025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21033079290597122254892683 31549618935895683382339025)
            ·
              refine ⟨23662214201921762536754269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31549618935895683382339025 23662214201921762536754269)
              ·
                refine ⟨8873330325720660951282851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23662214201921762536754269 8873330325720660951282851)
                ·
                  refine ⟨13309995488580991426924277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873330325720660951282851 13309995488580991426924277)
                  ·
                    refine ⟨1247812077054467946274151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309995488580991426924277 1247812077054467946274151)
                    ·
                      rfl

theorem cell23_7290316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_7290316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290316 prefixEnd_7290316 := by exact prefixLift 7290316
  have htrace : WordTrace (prefixWord ++ tailWord_7290316) baseStart_7290316 baseEnd_7290316 := by
    simpa [prefixWord, tailWord_7290316, baseEnd_7290316] using wordTrace_append hprefix tailTrace_7290316
  have hstable : (prefixWord ++ tailWord_7290316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290316).length < 2 ^ (prefixWord ++ tailWord_7290316).sum := by decide
  have hdescent : baseEnd_7290316 < baseStart_7290316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290353 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_7290353 : Nat := 118140960795 + 7290353 * 2 ^ 59
def prefixEnd_7290353 : Nat := 4983230072969 + 3 ^ 40 * 7290353 * 2
def baseEnd_7290353 : Nat := 3743455229947620194059783

theorem tailTrace_7290353 : CollatzResearch.WordTrace tailWord_7290353 prefixEnd_7290353 3743455229947620194059783 := by
  unfold tailWord_7290353
  simp only [CollatzResearch.WordTrace]
  refine ⟨265901018557303649010579713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177267345704869099340386475 265901018557303649010579713)
  ·
    refine ⟨199425763917977736757934785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265901018557303649010579713 199425763917977736757934785)
    ·
      refine ⟨149569322938483302568451089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199425763917977736757934785 149569322938483302568451089)
      ·
        refine ⟨112176992203862476926338317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149569322938483302568451089 112176992203862476926338317)
        ·
          refine ⟨42066372076448428847376869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112176992203862476926338317 42066372076448428847376869)
          ·
            refine ⟨7887444764334080408883163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42066372076448428847376869 7887444764334080408883163)
            ·
              refine ⟨11831167146501120613324745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887444764334080408883163 11831167146501120613324745)
              ·
                refine ⟨8873375359875840459993559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11831167146501120613324745 8873375359875840459993559)
                ·
                  refine ⟨13310063039813760689990339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873375359875840459993559 13310063039813760689990339)
                  ·
                    refine ⟨19965094559720641034985509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13310063039813760689990339 19965094559720641034985509)
                    ·
                      refine ⟨3743455229947620194059783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19965094559720641034985509 3743455229947620194059783)
                      ·
                        rfl

theorem cell23_7290353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_7290353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290353 prefixEnd_7290353 := by exact prefixLift 7290353
  have htrace : WordTrace (prefixWord ++ tailWord_7290353) baseStart_7290353 baseEnd_7290353 := by
    simpa [prefixWord, tailWord_7290353, baseEnd_7290353] using wordTrace_append hprefix tailTrace_7290353
  have hstable : (prefixWord ++ tailWord_7290353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290353).length < 2 ^ (prefixWord ++ tailWord_7290353).sum := by decide
  have hdescent : baseEnd_7290353 < baseStart_7290353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290387 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 1, 2, 2]
def baseStart_7290387 : Nat := 118140960795 + 7290387 * 2 ^ 59
def prefixEnd_7290387 : Nat := 4983230072969 + 3 ^ 40 * 7290387 * 2
def baseEnd_7290387 : Nat := 3743472688289873061034627

theorem tailTrace_7290387 : CollatzResearch.WordTrace tailWord_7290387 prefixEnd_7290387 3743472688289873061034627 := by
  unfold tailWord_7290387
  simp only [CollatzResearch.WordTrace]
  refine ⟨265902258639180472817317415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177268172426120315211544943 265902258639180472817317415)
  ·
    refine ⟨398853387958770709225976123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265902258639180472817317415 398853387958770709225976123)
    ·
      refine ⟨598280081938156063838964185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398853387958770709225976123 598280081938156063838964185)
      ·
        refine ⟨448710061453617047879223139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598280081938156063838964185 448710061453617047879223139)
        ·
          refine ⟨673065092180425571818834709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448710061453617047879223139 673065092180425571818834709)
          ·
            refine ⟨31549926195957448679007877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 673065092180425571818834709 31549926195957448679007877)
            ·
              refine ⟨5915611161742021627313977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31549926195957448679007877 5915611161742021627313977)
              ·
                refine ⟨4436708371306516220485483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915611161742021627313977 4436708371306516220485483)
                ·
                  refine ⟨6655062556959774330728225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436708371306516220485483 6655062556959774330728225)
                  ·
                    refine ⟨4991296917719830748046169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655062556959774330728225 4991296917719830748046169)
                    ·
                      refine ⟨3743472688289873061034627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991296917719830748046169 3743472688289873061034627)
                      ·
                        rfl

theorem cell23_7290387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 2, 2].length) (baseStart_7290387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290387 prefixEnd_7290387 := by exact prefixLift 7290387
  have htrace : WordTrace (prefixWord ++ tailWord_7290387) baseStart_7290387 baseEnd_7290387 := by
    simpa [prefixWord, tailWord_7290387, baseEnd_7290387] using wordTrace_append hprefix tailTrace_7290387
  have hstable : (prefixWord ++ tailWord_7290387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290387).length < 2 ^ (prefixWord ++ tailWord_7290387).sum := by decide
  have hdescent : baseEnd_7290387 < baseStart_7290387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290389 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7290389 : Nat := 118140960795 + 7290389 * 2 ^ 59
def prefixEnd_7290389 : Nat := 4983230072969 + 3 ^ 40 * 7290389 * 2
def baseEnd_7290389 : Nat := 1247824571750394017736539

theorem tailTrace_7290389 : CollatzResearch.WordTrace tailWord_7290389 prefixEnd_7290389 1247824571750394017736539 := by
  unfold tailWord_7290389
  simp only [CollatzResearch.WordTrace]
  refine ⟨265902331585173227158890221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177268221056782151439260147 265902331585173227158890221)
  ·
    refine ⟨99713374344439960184583833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265902331585173227158890221 99713374344439960184583833)
    ·
      refine ⟨74785030758329970138437875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99713374344439960184583833 74785030758329970138437875)
      ·
        refine ⟨112177546137494955207656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74785030758329970138437875 112177546137494955207656813)
        ·
          refine ⟨42066579801560608202871305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112177546137494955207656813 42066579801560608202871305)
          ·
            refine ⟨31549934851170456152153479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42066579801560608202871305 31549934851170456152153479)
            ·
              refine ⟨47324902276755684228230219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31549934851170456152153479 47324902276755684228230219)
              ·
                refine ⟨70987353415133526342345329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47324902276755684228230219 70987353415133526342345329)
                ·
                  refine ⟨53240515061350144756758997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70987353415133526342345329 53240515061350144756758997)
                  ·
                    refine ⟨1247824571750394017736539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53240515061350144756758997 1247824571750394017736539)
                    ·
                      rfl

theorem cell23_7290389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7290389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290389 prefixEnd_7290389 := by exact prefixLift 7290389
  have htrace : WordTrace (prefixWord ++ tailWord_7290389) baseStart_7290389 baseEnd_7290389 := by
    simpa [prefixWord, tailWord_7290389, baseEnd_7290389] using wordTrace_append hprefix tailTrace_7290389
  have hstable : (prefixWord ++ tailWord_7290389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290389).length < 2 ^ (prefixWord ++ tailWord_7290389).sum := by decide
  have hdescent : baseEnd_7290389 < baseStart_7290389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290403 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3]
def baseStart_7290403 : Nat := 118140960795 + 7290403 * 2 ^ 59
def prefixEnd_7290403 : Nat := 4983230072969 + 3 ^ 40 * 7290403 * 2
def baseEnd_7290403 : Nat := 3743480903980344998434553

theorem tailTrace_7290403 : CollatzResearch.WordTrace tailWord_7290403 prefixEnd_7290403 3743480903980344998434553 := by
  unfold tailWord_7290403
  simp only [CollatzResearch.WordTrace]
  refine ⟨265902842207122507549899863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177268561471415005033266575 265902842207122507549899863)
  ·
    refine ⟨398854263310683761324849795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265902842207122507549899863 398854263310683761324849795)
    ·
      refine ⟨598281394966025641987274693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398854263310683761324849795 598281394966025641987274693)
      ·
        refine ⟨112177761556129807872614005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598281394966025641987274693 112177761556129807872614005)
        ·
          refine ⟨10516665145887169488057563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112177761556129807872614005 10516665145887169488057563)
          ·
            refine ⟨15774997718830754232086345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10516665145887169488057563 15774997718830754232086345)
            ·
              refine ⟨11831248289123065674064759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15774997718830754232086345 11831248289123065674064759)
              ·
                refine ⟨17746872433684598511097139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831248289123065674064759 17746872433684598511097139)
                ·
                  refine ⟨26620308650526897766645709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746872433684598511097139 26620308650526897766645709)
                  ·
                    refine ⟨9982615743947586662492141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26620308650526897766645709 9982615743947586662492141)
                    ·
                      refine ⟨3743480903980344998434553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982615743947586662492141 3743480903980344998434553)
                      ·
                        rfl

theorem cell23_7290403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_7290403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290403 prefixEnd_7290403 := by exact prefixLift 7290403
  have htrace : WordTrace (prefixWord ++ tailWord_7290403) baseStart_7290403 baseEnd_7290403 := by
    simpa [prefixWord, tailWord_7290403, baseEnd_7290403] using wordTrace_append hprefix tailTrace_7290403
  have hstable : (prefixWord ++ tailWord_7290403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290403).length < 2 ^ (prefixWord ++ tailWord_7290403).sum := by decide
  have hdescent : baseEnd_7290403 < baseStart_7290403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290454 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7290454 : Nat := 118140960795 + 7290454 * 2 ^ 59
def prefixEnd_7290454 : Nat := 4983230072969 + 3 ^ 40 * 7290454 * 2
def baseEnd_7290454 : Nat := 3743507091493724298896819

theorem tailTrace_7290454 : CollatzResearch.WordTrace tailWord_7290454 prefixEnd_7290454 3743507091493724298896819 := by
  unfold tailWord_7290454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619043895621108953750401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177269801553291828840004277 16619043895621108953750401)
  ·
    refine ⟨12464282921715831715312801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16619043895621108953750401 12464282921715831715312801)
    ·
      refine ⟨9348212191286873786484601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12464282921715831715312801 9348212191286873786484601)
      ·
        refine ⟨7011159143465155339863451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9348212191286873786484601 7011159143465155339863451)
        ·
          refine ⟨10516738715197733009795177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011159143465155339863451 10516738715197733009795177)
          ·
            refine ⟨7887554036398299757346383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10516738715197733009795177 7887554036398299757346383)
            ·
              refine ⟨11831331054597449636019575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887554036398299757346383 11831331054597449636019575)
              ·
                refine ⟨17746996581896174454029363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831331054597449636019575 17746996581896174454029363)
                ·
                  refine ⟨26620494872844261681044045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746996581896174454029363 26620494872844261681044045)
                  ·
                    refine ⟨9982685577316598130391517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26620494872844261681044045 9982685577316598130391517)
                    ·
                      refine ⟨3743507091493724298896819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982685577316598130391517 3743507091493724298896819)
                      ·
                        rfl

theorem cell23_7290454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7290454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290454 prefixEnd_7290454 := by exact prefixLift 7290454
  have htrace : WordTrace (prefixWord ++ tailWord_7290454) baseStart_7290454 baseEnd_7290454 := by
    simpa [prefixWord, tailWord_7290454, baseEnd_7290454] using wordTrace_append hprefix tailTrace_7290454
  have hstable : (prefixWord ++ tailWord_7290454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290454).length < 2 ^ (prefixWord ++ tailWord_7290454).sum := by decide
  have hdescent : baseEnd_7290454 < baseStart_7290454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290460 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7290460 : Nat := 118140960795 + 7290460 * 2 ^ 59
def prefixEnd_7290460 : Nat := 4983230072969 + 3 ^ 40 * 7290460 * 2
def baseEnd_7290460 : Nat := 3743510172377651275421791

theorem tailTrace_7290460 : CollatzResearch.WordTrace tailWord_7290460 prefixEnd_7290460 3743510172377651275421791 := by
  unfold tailWord_7290460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132952460583958003142362417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177269947445277337523149889 132952460583958003142362417)
  ·
    refine ⟨99714345437968502356771813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132952460583958003142362417 99714345437968502356771813)
    ·
      refine ⟨18696439769619094191894715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99714345437968502356771813 18696439769619094191894715)
      ·
        refine ⟨28044659654428641287842073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18696439769619094191894715 28044659654428641287842073)
        ·
          refine ⟨21033494740821480965881555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28044659654428641287842073 21033494740821480965881555)
          ·
            refine ⟨31550242111232221448822333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21033494740821480965881555 31550242111232221448822333)
            ·
              refine ⟨11831340791712083043308375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31550242111232221448822333 11831340791712083043308375)
              ·
                refine ⟨17747011187568124564962563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831340791712083043308375 17747011187568124564962563)
                ·
                  refine ⟨26620516781352186847443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17747011187568124564962563 26620516781352186847443845)
                  ·
                    refine ⟨4991346896503535033895721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26620516781352186847443845 4991346896503535033895721)
                    ·
                      refine ⟨3743510172377651275421791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991346896503535033895721 3743510172377651275421791)
                      ·
                        rfl

theorem cell23_7290460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7290460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290460 prefixEnd_7290460 := by exact prefixLift 7290460
  have htrace : WordTrace (prefixWord ++ tailWord_7290460) baseStart_7290460 baseEnd_7290460 := by
    simpa [prefixWord, tailWord_7290460, baseEnd_7290460] using wordTrace_append hprefix tailTrace_7290460
  have hstable : (prefixWord ++ tailWord_7290460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290460).length < 2 ^ (prefixWord ++ tailWord_7290460).sum := by decide
  have hdescent : baseEnd_7290460 < baseStart_7290460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290496 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_7290496 : Nat := 118140960795 + 7290496 * 2 ^ 59
def prefixEnd_7290496 : Nat := 4983230072969 + 3 ^ 40 * 7290496 * 2
def baseEnd_7290496 : Nat := 1247842885893737711523875

theorem tailTrace_7290496 : CollatzResearch.WordTrace tailWord_7290496 prefixEnd_7290496 1247842885893737711523875 := by
  unfold tailWord_7290496
  simp only [CollatzResearch.WordTrace]
  refine ⟨132953117097892792216517671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177270822797190389622023561 132953117097892792216517671)
  ·
    refine ⟨199429675646839188324776507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132953117097892792216517671 199429675646839188324776507)
    ·
      refine ⟨299144513470258782487164761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199429675646839188324776507 299144513470258782487164761)
      ·
        refine ⟨224358385102694086865373571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299144513470258782487164761 224358385102694086865373571)
        ·
          refine ⟨336537577654041130298060357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224358385102694086865373571 336537577654041130298060357)
          ·
            refine ⟨63100795810132711930886317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336537577654041130298060357 63100795810132711930886317)
            ·
              refine ⟨23662798428799766974082369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63100795810132711930886317 23662798428799766974082369)
              ·
                refine ⟨17747098821599825230561777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662798428799766974082369 17747098821599825230561777)
                ·
                  refine ⟨13310324116199868922921333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17747098821599825230561777 13310324116199868922921333)
                  ·
                    refine ⟨1247842885893737711523875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13310324116199868922921333 1247842885893737711523875)
                    ·
                      rfl

theorem cell23_7290496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_7290496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290496 prefixEnd_7290496 := by exact prefixLift 7290496
  have htrace : WordTrace (prefixWord ++ tailWord_7290496) baseStart_7290496 baseEnd_7290496 := by
    simpa [prefixWord, tailWord_7290496, baseEnd_7290496] using wordTrace_append hprefix tailTrace_7290496
  have hstable : (prefixWord ++ tailWord_7290496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290496).length < 2 ^ (prefixWord ++ tailWord_7290496).sum := by decide
  have hdescent : baseEnd_7290496 < baseStart_7290496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290500 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 7]
def baseStart_7290500 : Nat := 118140960795 + 7290500 * 2 ^ 59
def prefixEnd_7290500 : Nat := 4983230072969 + 3 ^ 40 * 7290500 * 2
def baseEnd_7290500 : Nat := 415947856844870124324623

theorem tailTrace_7290500 : CollatzResearch.WordTrace tailWord_7290500 prefixEnd_7290500 415947856844870124324623 := by
  unfold tailWord_7290500
  simp only [CollatzResearch.WordTrace]
  refine ⟨132953190043885546558090477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177270920058514062077453969 132953190043885546558090477)
  ·
    refine ⟨49857446266457079959283929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132953190043885546558090477 49857446266457079959283929)
    ·
      refine ⟨37393084699842809969462947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49857446266457079959283929 37393084699842809969462947)
      ·
        refine ⟨56089627049764214954194421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37393084699842809969462947 56089627049764214954194421)
        ·
          refine ⟨5258402535915395151955727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56089627049764214954194421 5258402535915395151955727)
          ·
            refine ⟨7887603803873092727933591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258402535915395151955727 7887603803873092727933591)
            ·
              refine ⟨11831405705809639091900387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887603803873092727933591 11831405705809639091900387)
              ·
                refine ⟨17747108558714458637850581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831405705809639091900387 17747108558714458637850581)
                ·
                  refine ⟨415947856844870124324623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17747108558714458637850581 415947856844870124324623)
                  ·
                    rfl

theorem cell23_7290500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_7290500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290500 prefixEnd_7290500 := by exact prefixLift 7290500
  have htrace : WordTrace (prefixWord ++ tailWord_7290500) baseStart_7290500 baseEnd_7290500 := by
    simpa [prefixWord, tailWord_7290500, baseEnd_7290500] using wordTrace_append hprefix tailTrace_7290500
  have hstable : (prefixWord ++ tailWord_7290500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290500).length < 2 ^ (prefixWord ++ tailWord_7290500).sum := by decide
  have hdescent : baseEnd_7290500 < baseStart_7290500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290506 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7290506 : Nat := 118140960795 + 7290506 * 2 ^ 59
def prefixEnd_7290506 : Nat := 4983230072969 + 3 ^ 40 * 7290506 * 2
def baseEnd_7290506 : Nat := 3743533792487758095446579

theorem tailTrace_7290506 : CollatzResearch.WordTrace tailWord_7290506 prefixEnd_7290506 3743533792487758095446579 := by
  unfold tailWord_7290506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66476649731437339035224843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177271065950499570760599581 66476649731437339035224843)
  ·
    refine ⟨99714974597156008552837265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66476649731437339035224843 99714974597156008552837265)
    ·
      refine ⟨74786230947867006414627949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99714974597156008552837265 74786230947867006414627949)
      ·
        refine ⟨28044836605450127405485481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74786230947867006414627949 28044836605450127405485481)
        ·
          refine ⟨21033627454087595554114111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28044836605450127405485481 21033627454087595554114111)
          ·
            refine ⟨31550441181131393331171167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21033627454087595554114111 31550441181131393331171167)
            ·
              refine ⟨47325661771697089996756751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31550441181131393331171167 47325661771697089996756751)
              ·
                refine ⟨70988492657545634995135127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47325661771697089996756751 70988492657545634995135127)
                ·
                  refine ⟨106482738986318452492702691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70988492657545634995135127 106482738986318452492702691)
                  ·
                    refine ⟨159724108479477678739054037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106482738986318452492702691 159724108479477678739054037)
                    ·
                      refine ⟨3743533792487758095446579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159724108479477678739054037 3743533792487758095446579)
                      ·
                        rfl

theorem cell23_7290506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7290506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290506 prefixEnd_7290506 := by exact prefixLift 7290506
  have htrace : WordTrace (prefixWord ++ tailWord_7290506) baseStart_7290506 baseEnd_7290506 := by
    simpa [prefixWord, tailWord_7290506, baseEnd_7290506] using wordTrace_append hprefix tailTrace_7290506
  have hstable : (prefixWord ++ tailWord_7290506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290506).length < 2 ^ (prefixWord ++ tailWord_7290506).sum := by decide
  have hdescent : baseEnd_7290506 < baseStart_7290506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290553 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7290553 : Nat := 118140960795 + 7290553 * 2 ^ 59
def prefixEnd_7290553 : Nat := 4983230072969 + 3 ^ 40 * 7290553 * 2
def baseEnd_7290553 : Nat := 3743557926078519411558863

theorem tailTrace_7290553 : CollatzResearch.WordTrace tailWord_7290553 prefixEnd_7290553 3743557926078519411558863 := by
  unfold tailWord_7290553
  simp only [CollatzResearch.WordTrace]
  refine ⟨265908313156579083167860313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177272208771052722111906875 265908313156579083167860313)
  ·
    refine ⟨199431234867434312375895235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265908313156579083167860313 199431234867434312375895235)
    ·
      refine ⟨299146852301151468563842853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199431234867434312375895235 299146852301151468563842853)
      ·
        refine ⟨56090034806465900355720535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299146852301151468563842853 56090034806465900355720535)
        ·
          refine ⟨84135052209698850533580803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56090034806465900355720535 84135052209698850533580803)
          ·
            refine ⟨126202578314548275800371205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84135052209698850533580803 126202578314548275800371205)
            ·
              refine ⟨23662983433977801712569601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126202578314548275800371205 23662983433977801712569601)
              ·
                refine ⟨17747237575483351284427201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662983433977801712569601 17747237575483351284427201)
                ·
                  refine ⟨13310428181612513463320401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17747237575483351284427201 13310428181612513463320401)
                  ·
                    refine ⟨9982821136209385097490301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13310428181612513463320401 9982821136209385097490301)
                    ·
                      refine ⟨3743557926078519411558863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9982821136209385097490301 3743557926078519411558863)
                      ·
                        rfl

theorem cell23_7290553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7290553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290553 prefixEnd_7290553 := by exact prefixLift 7290553
  have htrace : WordTrace (prefixWord ++ tailWord_7290553) baseStart_7290553 baseEnd_7290553 := by
    simpa [prefixWord, tailWord_7290553, baseEnd_7290553] using wordTrace_append hprefix tailTrace_7290553
  have hstable : (prefixWord ++ tailWord_7290553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290553).length < 2 ^ (prefixWord ++ tailWord_7290553).sum := by decide
  have hdescent : baseEnd_7290553 < baseStart_7290553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290560 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 1, 4]
def baseStart_7290560 : Nat := 118140960795 + 7290560 * 2 ^ 59
def prefixEnd_7290560 : Nat := 4983230072969 + 3 ^ 40 * 7290560 * 2
def baseEnd_7290560 : Nat := 1247853840147700294723777

theorem tailTrace_7290560 : CollatzResearch.WordTrace tailWord_7290560 prefixEnd_7290560 1247853840147700294723777 := by
  unfold tailWord_7290560
  simp only [CollatzResearch.WordTrace]
  refine ⟨132954284233776861681682567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177272378978369148908910089 132954284233776861681682567)
  ·
    refine ⟨199431426350665292522523851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132954284233776861681682567 199431426350665292522523851)
    ·
      refine ⟨299147139525997938783785777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199431426350665292522523851 299147139525997938783785777)
      ·
        refine ⟨224360354644498454087839333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299147139525997938783785777 224360354644498454087839333)
        ·
          refine ⟨42067566495843460141469875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224360354644498454087839333 42067566495843460141469875)
          ·
            refine ⟨63101349743765190212204813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42067566495843460141469875 63101349743765190212204813)
            ·
              refine ⟨23663006153911946329576805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63101349743765190212204813 23663006153911946329576805)
              ·
                refine ⟨4436813653858489936795651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23663006153911946329576805 4436813653858489936795651)
                ·
                  refine ⟨6655220480787734905193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436813653858489936795651 6655220480787734905193477)
                  ·
                    refine ⟨1247853840147700294723777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655220480787734905193477 1247853840147700294723777)
                    ·
                      rfl

theorem cell23_7290560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_7290560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290560 prefixEnd_7290560 := by exact prefixLift 7290560
  have htrace : WordTrace (prefixWord ++ tailWord_7290560) baseStart_7290560 baseEnd_7290560 := by
    simpa [prefixWord, tailWord_7290560, baseEnd_7290560] using wordTrace_append hprefix tailTrace_7290560
  have hstable : (prefixWord ++ tailWord_7290560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290560).length < 2 ^ (prefixWord ++ tailWord_7290560).sum := by decide
  have hdescent : baseEnd_7290560 < baseStart_7290560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290610 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7290610 : Nat := 118140960795 + 7290610 * 2 ^ 59
def prefixEnd_7290610 : Nat := 4983230072969 + 3 ^ 40 * 7290610 * 2
def baseEnd_7290610 : Nat := 3743587194475825688546101

theorem tailTrace_7290610 : CollatzResearch.WordTrace tailWord_7290610 prefixEnd_7290610 3743587194475825688546101 := by
  unfold tailWord_7290610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66477598029343145475671321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177273594744915054601790189 66477598029343145475671321)
  ·
    refine ⟨49858198522007359106753491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66477598029343145475671321 49858198522007359106753491)
    ·
      refine ⟨74787297783011038660130237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858198522007359106753491 74787297783011038660130237)
      ·
        refine ⟨28045236668629139497548839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74787297783011038660130237 28045236668629139497548839)
        ·
          refine ⟨42067855002943709246323259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28045236668629139497548839 42067855002943709246323259)
          ·
            refine ⟨63101782504415563869484889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42067855002943709246323259 63101782504415563869484889)
            ·
              refine ⟨47326336878311672902113667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63101782504415563869484889 47326336878311672902113667)
              ·
                refine ⟨70989505317467509353170501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47326336878311672902113667 70989505317467509353170501)
                ·
                  refine ⟨13310532247025158003719469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70989505317467509353170501 13310532247025158003719469)
                  ·
                    refine ⟨4991449592634434251394801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13310532247025158003719469 4991449592634434251394801)
                    ·
                      refine ⟨3743587194475825688546101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991449592634434251394801 3743587194475825688546101)
                      ·
                        rfl

theorem cell23_7290610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7290610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290610 prefixEnd_7290610 := by exact prefixLift 7290610
  have htrace : WordTrace (prefixWord ++ tailWord_7290610) baseStart_7290610 baseEnd_7290610 := by
    simpa [prefixWord, tailWord_7290610, baseEnd_7290610] using wordTrace_append hprefix tailTrace_7290610
  have hstable : (prefixWord ++ tailWord_7290610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290610).length < 2 ^ (prefixWord ++ tailWord_7290610).sum := by decide
  have hdescent : baseEnd_7290610 < baseStart_7290610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290660 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_7290660 : Nat := 118140960795 + 7290660 * 2 ^ 59
def prefixEnd_7290660 : Nat := 4983230072969 + 3 ^ 40 * 7290660 * 2
def baseEnd_7290660 : Nat := 3743612868508550492920871

theorem tailTrace_7290660 : CollatzResearch.WordTrace tailWord_7290660 prefixEnd_7290660 3743612868508550492920871 := by
  unfold tailWord_7290660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132956107883595720221002717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177274810511460960294670289 132956107883595720221002717)
  ·
    refine ⟨49858540456348395082876019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132956107883595720221002717 49858540456348395082876019)
    ·
      refine ⟨74787810684522592624314029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858540456348395082876019 74787810684522592624314029)
      ·
        refine ⟨28045429006695972234117761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74787810684522592624314029 28045429006695972234117761)
        ·
          refine ⟨21034071755021979175588321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28045429006695972234117761 21034071755021979175588321)
          ·
            refine ⟨15775553816266484381691241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21034071755021979175588321 15775553816266484381691241)
            ·
              refine ⟨11831665362199863286268431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15775553816266484381691241 11831665362199863286268431)
              ·
                refine ⟨17747498043299794929402647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831665362199863286268431 17747498043299794929402647)
                ·
                  refine ⟨26621247064949692394103971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17747498043299794929402647 26621247064949692394103971)
                  ·
                    refine ⟨39931870597424538591155957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26621247064949692394103971 39931870597424538591155957)
                    ·
                      refine ⟨3743612868508550492920871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39931870597424538591155957 3743612868508550492920871)
                      ·
                        rfl

theorem cell23_7290660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_7290660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290660 prefixEnd_7290660 := by exact prefixLift 7290660
  have htrace : WordTrace (prefixWord ++ tailWord_7290660) baseStart_7290660 baseEnd_7290660 := by
    simpa [prefixWord, tailWord_7290660, baseEnd_7290660] using wordTrace_append hprefix tailTrace_7290660
  have hstable : (prefixWord ++ tailWord_7290660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290660).length < 2 ^ (prefixWord ++ tailWord_7290660).sum := by decide
  have hdescent : baseEnd_7290660 < baseStart_7290660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290674 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_7290674 : Nat := 118140960795 + 7290674 * 2 ^ 59
def prefixEnd_7290674 : Nat := 4983230072969 + 3 ^ 40 * 7290674 * 2
def baseEnd_7290674 : Nat := 3743620057237713438145807

theorem tailTrace_7290674 : CollatzResearch.WordTrace tailWord_7290674 prefixEnd_7290674 3743620057237713438145807 := by
  unfold tailWord_7290674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66478181597285180208253769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177275150926093813888676717 66478181597285180208253769)
  ·
    refine ⟨49858636197963885156190327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66478181597285180208253769 49858636197963885156190327)
    ·
      refine ⟨74787954296945827734285491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858636197963885156190327 74787954296945827734285491)
      ·
        refine ⟨112181931445418741601428237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74787954296945827734285491 112181931445418741601428237)
        ·
          refine ⟨42068224292032028100535589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112181931445418741601428237 42068224292032028100535589)
          ·
            refine ⟨7887792054756005268850423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42068224292032028100535589 7887792054756005268850423)
            ·
              refine ⟨11831688082134007903275635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887792054756005268850423 11831688082134007903275635)
              ·
                refine ⟨17747532123201011854913453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831688082134007903275635 17747532123201011854913453)
                ·
                  refine ⟨6655324546200379445592545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17747532123201011854913453 6655324546200379445592545)
                  ·
                    refine ⟨4991493409650284584194409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655324546200379445592545 4991493409650284584194409)
                    ·
                      refine ⟨3743620057237713438145807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991493409650284584194409 3743620057237713438145807)
                      ·
                        rfl

theorem cell23_7290674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_7290674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290674 prefixEnd_7290674 := by exact prefixLift 7290674
  have htrace : WordTrace (prefixWord ++ tailWord_7290674) baseStart_7290674 baseEnd_7290674 := by
    simpa [prefixWord, tailWord_7290674, baseEnd_7290674] using wordTrace_append hprefix tailTrace_7290674
  have hstable : (prefixWord ++ tailWord_7290674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290674).length < 2 ^ (prefixWord ++ tailWord_7290674).sum := by decide
  have hdescent : baseEnd_7290674 < baseStart_7290674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290694 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7290694 : Nat := 118140960795 + 7290694 * 2 ^ 59
def prefixEnd_7290694 : Nat := 4983230072969 + 3 ^ 40 * 7290694 * 2
def baseEnd_7290694 : Nat := 3743630326850803359895715

theorem tailTrace_7290694 : CollatzResearch.WordTrace tailWord_7290694 prefixEnd_7290694 3743630326850803359895715 := by
  unfold tailWord_7290694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309795495283383257773223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177275637232712176165828757 8309795495283383257773223)
  ·
    refine ⟨12464693242925074886659835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309795495283383257773223 12464693242925074886659835)
    ·
      refine ⟨18697039864387612329989753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464693242925074886659835 18697039864387612329989753)
      ·
        refine ⟨14022779898290709247492315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18697039864387612329989753 14022779898290709247492315)
        ·
          refine ⟨21034169847436063871238473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14022779898290709247492315 21034169847436063871238473)
          ·
            refine ⟨15775627385577047903428855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21034169847436063871238473 15775627385577047903428855)
            ·
              refine ⟨23663441078365571855143283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15775627385577047903428855 23663441078365571855143283)
              ·
                refine ⟨35495161617548357782714925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23663441078365571855143283 35495161617548357782714925)
                ·
                  refine ⟨13310685606580634168518097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35495161617548357782714925 13310685606580634168518097)
                  ·
                    refine ⟨9983014204935475626388573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13310685606580634168518097 9983014204935475626388573)
                    ·
                      refine ⟨3743630326850803359895715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983014204935475626388573 3743630326850803359895715)
                      ·
                        rfl

theorem cell23_7290694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7290694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290694 prefixEnd_7290694 := by exact prefixLift 7290694
  have htrace : WordTrace (prefixWord ++ tailWord_7290694) baseStart_7290694 baseEnd_7290694 := by
    simpa [prefixWord, tailWord_7290694, baseEnd_7290694] using wordTrace_append hprefix tailTrace_7290694
  have hstable : (prefixWord ++ tailWord_7290694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290694).length < 2 ^ (prefixWord ++ tailWord_7290694).sum := by decide
  have hdescent : baseEnd_7290694 < baseStart_7290694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290724 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_7290724 : Nat := 118140960795 + 7290724 * 2 ^ 59
def prefixEnd_7290724 : Nat := 4983230072969 + 3 ^ 40 * 7290724 * 2
def baseEnd_7290724 : Nat := 3743645731270438242520577

theorem tailTrace_7290724 : CollatzResearch.WordTrace tailWord_7290724 prefixEnd_7290724 3743645731270438242520577 := by
  unfold tailWord_7290724
  simp only [CollatzResearch.WordTrace]
  refine ⟨132957275019479789686167613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177276366692639719581556817 132957275019479789686167613)
  ·
    refine ⟨49858978132304921132312855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132957275019479789686167613 49858978132304921132312855)
    ·
      refine ⟨74788467198457381698469283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858978132304921132312855 74788467198457381698469283)
      ·
        refine ⟨112182700797686072547703925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74788467198457381698469283 112182700797686072547703925)
        ·
          refine ⟨10517128199783069301347243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112182700797686072547703925 10517128199783069301347243)
          ·
            refine ⟨15775692299674603952020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517128199783069301347243 15775692299674603952020865)
            ·
              refine ⟨11831769224755952964015649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15775692299674603952020865 11831769224755952964015649)
              ·
                refine ⟨8873826918566964723011737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11831769224755952964015649 8873826918566964723011737)
                ·
                  refine ⟨6655370188925223542258803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873826918566964723011737 6655370188925223542258803)
                  ·
                    refine ⟨9983055283387835313388205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6655370188925223542258803 9983055283387835313388205)
                    ·
                      refine ⟨3743645731270438242520577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983055283387835313388205 3743645731270438242520577)
                      ·
                        rfl

theorem cell23_7290724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_7290724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290724 prefixEnd_7290724 := by exact prefixLift 7290724
  have htrace : WordTrace (prefixWord ++ tailWord_7290724) baseStart_7290724 baseEnd_7290724 := by
    simpa [prefixWord, tailWord_7290724, baseEnd_7290724] using wordTrace_append hprefix tailTrace_7290724
  have hstable : (prefixWord ++ tailWord_7290724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290724).length < 2 ^ (prefixWord ++ tailWord_7290724).sum := by decide
  have hdescent : baseEnd_7290724 < baseStart_7290724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290733 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7290733 : Nat := 118140960795 + 7290733 * 2 ^ 59
def prefixEnd_7290733 : Nat := 4983230072969 + 3 ^ 40 * 7290733 * 2
def baseEnd_7290733 : Nat := 3743650352596328707308035

theorem tailTrace_7290733 : CollatzResearch.WordTrace tailWord_7290733 prefixEnd_7290733 3743650352596328707308035 := by
  unfold tailWord_7290733
  simp only [CollatzResearch.WordTrace]
  refine ⟨265914878295926973909412853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177276585530617982606275235 265914878295926973909412853)
  ·
    refine ⟨24929519840243153804007455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265914878295926973909412853 24929519840243153804007455)
    ·
      refine ⟨37394279760364730706011183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24929519840243153804007455 37394279760364730706011183)
      ·
        refine ⟨56091419640547096059016775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394279760364730706011183 56091419640547096059016775)
        ·
          refine ⟨84137129460820644088525163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56091419640547096059016775 84137129460820644088525163)
          ·
            refine ⟨126205694191230966132787745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84137129460820644088525163 126205694191230966132787745)
            ·
              refine ⟨94654270643423224599590809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126205694191230966132787745 94654270643423224599590809)
              ·
                refine ⟨70990702982567418449693107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94654270643423224599590809 70990702982567418449693107)
                ·
                  refine ⟨106486054473851127674539661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70990702982567418449693107 106486054473851127674539661)
                  ·
                    refine ⟨39932270427694172877952373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106486054473851127674539661 39932270427694172877952373)
                    ·
                      refine ⟨3743650352596328707308035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39932270427694172877952373 3743650352596328707308035)
                      ·
                        rfl

theorem cell23_7290733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7290733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290733 prefixEnd_7290733 := by exact prefixLift 7290733
  have htrace : WordTrace (prefixWord ++ tailWord_7290733) baseStart_7290733 baseEnd_7290733 := by
    simpa [prefixWord, tailWord_7290733, baseEnd_7290733] using wordTrace_append hprefix tailTrace_7290733
  have hstable : (prefixWord ++ tailWord_7290733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290733).length < 2 ^ (prefixWord ++ tailWord_7290733).sum := by decide
  have hdescent : baseEnd_7290733 < baseStart_7290733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290763 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3]
def baseStart_7290763 : Nat := 118140960795 + 7290763 * 2 ^ 59
def prefixEnd_7290763 : Nat := 4983230072969 + 3 ^ 40 * 7290763 * 2
def baseEnd_7290763 : Nat := 3743665757015963589932897

theorem tailTrace_7290763 : CollatzResearch.WordTrace tailWord_7290763 prefixEnd_7290763 3743665757015963589932897 := by
  unfold tailWord_7290763
  simp only [CollatzResearch.WordTrace]
  refine ⟨265915972485818289033004943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177277314990545526022003295 265915972485818289033004943)
  ·
    refine ⟨398873958728727433549507415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265915972485818289033004943 398873958728727433549507415)
    ·
      refine ⟨598310938093091150324261123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398873958728727433549507415 598310938093091150324261123)
      ·
        refine ⟨897466407139636725486391685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598310938093091150324261123 897466407139636725486391685)
        ·
          refine ⟨168274951338681886028698441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 897466407139636725486391685 168274951338681886028698441)
          ·
            refine ⟨126206213504011414521523831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168274951338681886028698441 126206213504011414521523831)
            ·
              refine ⟨189309320256017121782285747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126206213504011414521523831 189309320256017121782285747)
              ·
                refine ⟨283963980384025682673428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189309320256017121782285747 283963980384025682673428621)
                ·
                  refine ⟨106486492644009631002535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283963980384025682673428621 106486492644009631002535733)
                  ·
                    refine ⟨9983108685375902906487725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106486492644009631002535733 9983108685375902906487725)
                    ·
                      refine ⟨3743665757015963589932897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983108685375902906487725 3743665757015963589932897)
                      ·
                        rfl

theorem cell23_7290763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 3].length) (baseStart_7290763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290763 prefixEnd_7290763 := by exact prefixLift 7290763
  have htrace : WordTrace (prefixWord ++ tailWord_7290763) baseStart_7290763 baseEnd_7290763 := by
    simpa [prefixWord, tailWord_7290763, baseEnd_7290763] using wordTrace_append hprefix tailTrace_7290763
  have hstable : (prefixWord ++ tailWord_7290763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290763).length < 2 ^ (prefixWord ++ tailWord_7290763).sum := by decide
  have hdescent : baseEnd_7290763 < baseStart_7290763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290781 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_7290781 : Nat := 118140960795 + 7290781 * 2 ^ 59
def prefixEnd_7290781 : Nat := 4983230072969 + 3 ^ 40 * 7290781 * 2
def baseEnd_7290781 : Nat := 3743674999667744519507815

theorem tailTrace_7290781 : CollatzResearch.WordTrace tailWord_7290781 prefixEnd_7290781 3743674999667744519507815 := by
  unfold tailWord_7290781
  simp only [CollatzResearch.WordTrace]
  refine ⟨265916628999753078107160197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177277752666502052071440131 265916628999753078107160197)
  ·
    refine ⟨49859367937453702145092537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265916628999753078107160197 49859367937453702145092537)
    ·
      refine ⟨37394525953090276608819403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49859367937453702145092537 37394525953090276608819403)
      ·
        refine ⟨56091788929635414913229105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394525953090276608819403 56091788929635414913229105)
        ·
          refine ⟨42068841697226561184921829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56091788929635414913229105 42068841697226561184921829)
          ·
            refine ⟨7887907818229980222172843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42068841697226561184921829 7887907818229980222172843)
            ·
              refine ⟨11831861727344970333259265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887907818229980222172843 11831861727344970333259265)
              ·
                refine ⟨8873896295508727749944449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11831861727344970333259265 8873896295508727749944449)
                ·
                  refine ⟨6655422221631545812458337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873896295508727749944449 6655422221631545812458337)
                  ·
                    refine ⟨4991566666223659359343753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655422221631545812458337 4991566666223659359343753)
                    ·
                      refine ⟨3743674999667744519507815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991566666223659359343753 3743674999667744519507815)
                      ·
                        rfl

theorem cell23_7290781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_7290781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290781 prefixEnd_7290781 := by exact prefixLift 7290781
  have htrace : WordTrace (prefixWord ++ tailWord_7290781) baseStart_7290781 baseEnd_7290781 := by
    simpa [prefixWord, tailWord_7290781, baseEnd_7290781] using wordTrace_append hprefix tailTrace_7290781
  have hstable : (prefixWord ++ tailWord_7290781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290781).length < 2 ^ (prefixWord ++ tailWord_7290781).sum := by decide
  have hdescent : baseEnd_7290781 < baseStart_7290781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290803 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_7290803 : Nat := 118140960795 + 7290803 * 2 ^ 59
def prefixEnd_7290803 : Nat := 4983230072969 + 3 ^ 40 * 7290803 * 2
def baseEnd_7290803 : Nat := 3743686296242143433432713

theorem tailTrace_7290803 : CollatzResearch.WordTrace tailWord_7290803 prefixEnd_7290803 3743686296242143433432713 := by
  unfold tailWord_7290803
  simp only [CollatzResearch.WordTrace]
  refine ⟨265917431405673375864461063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177278287603782250576307375 265917431405673375864461063)
  ·
    refine ⟨398876147108510063796691595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265917431405673375864461063 398876147108510063796691595)
    ·
      refine ⟨598314220662765095695037393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398876147108510063796691595 598314220662765095695037393)
      ·
        refine ⟨448735665497073821771278045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598314220662765095695037393 448735665497073821771278045)
        ·
          refine ⟨168275874561402683164229267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448735665497073821771278045 168275874561402683164229267)
          ·
            refine ⟨252413811842104024746343901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168275874561402683164229267 252413811842104024746343901)
            ·
              refine ⟨94655179440789009279878963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252413811842104024746343901 94655179440789009279878963)
              ·
                refine ⟨141982769161183513919818445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94655179440789009279878963 141982769161183513919818445)
                ·
                  refine ⟨53243538435443817719931917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141982769161183513919818445 53243538435443817719931917)
                  ·
                    refine ⟨19966326913291431644974469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53243538435443817719931917 19966326913291431644974469)
                    ·
                      refine ⟨3743686296242143433432713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19966326913291431644974469 3743686296242143433432713)
                      ·
                        rfl

theorem cell23_7290803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_7290803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290803 prefixEnd_7290803 := by exact prefixLift 7290803
  have htrace : WordTrace (prefixWord ++ tailWord_7290803) baseStart_7290803 baseEnd_7290803 := by
    simpa [prefixWord, tailWord_7290803, baseEnd_7290803] using wordTrace_append hprefix tailTrace_7290803
  have hstable : (prefixWord ++ tailWord_7290803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290803).length < 2 ^ (prefixWord ++ tailWord_7290803).sum := by decide
  have hdescent : baseEnd_7290803 < baseStart_7290803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290823 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_7290823 : Nat := 118140960795 + 7290823 * 2 ^ 59
def prefixEnd_7290823 : Nat := 4983230072969 + 3 ^ 40 * 7290823 * 2
def baseEnd_7290823 : Nat := 3743696565855233355182621

theorem tailTrace_7290823 : CollatzResearch.WordTrace tailWord_7290823 prefixEnd_7290823 3743696565855233355182621 := by
  unfold tailWord_7290823
  simp only [CollatzResearch.WordTrace]
  refine ⟨265918160865600919280189123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177278773910400612853459415 265918160865600919280189123)
  ·
    refine ⟨398877241298401378920283685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265918160865600919280189123 398877241298401378920283685)
    ·
      refine ⟨74789482743450258547553191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398877241298401378920283685 74789482743450258547553191)
      ·
        refine ⟨112184224115175387821329787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74789482743450258547553191 112184224115175387821329787)
        ·
          refine ⟨168276336172763081731994681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112184224115175387821329787 168276336172763081731994681)
          ·
            refine ⟨126207252129572311298996011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168276336172763081731994681 126207252129572311298996011)
            ·
              refine ⟨189310878194358466948494017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126207252129572311298996011 189310878194358466948494017)
              ·
                refine ⟨141983158645768850211370513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189310878194358466948494017 141983158645768850211370513)
                ·
                  refine ⟨106487368984326637658527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141983158645768850211370513 106487368984326637658527885)
                  ·
                    refine ⟨39932763369122489121947957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106487368984326637658527885 39932763369122489121947957)
                    ·
                      refine ⟨3743696565855233355182621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39932763369122489121947957 3743696565855233355182621)
                      ·
                        rfl

theorem cell23_7290823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_7290823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290823 prefixEnd_7290823 := by exact prefixLift 7290823
  have htrace : WordTrace (prefixWord ++ tailWord_7290823) baseStart_7290823 baseEnd_7290823 := by
    simpa [prefixWord, tailWord_7290823, baseEnd_7290823] using wordTrace_append hprefix tailTrace_7290823
  have hstable : (prefixWord ++ tailWord_7290823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290823).length < 2 ^ (prefixWord ++ tailWord_7290823).sum := by decide
  have hdescent : baseEnd_7290823 < baseStart_7290823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290833 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_7290833 : Nat := 118140960795 + 7290833 * 2 ^ 59
def prefixEnd_7290833 : Nat := 4983230072969 + 3 ^ 40 * 7290833 * 2
def baseEnd_7290833 : Nat := 3743701700661778316057575

theorem tailTrace_7290833 : CollatzResearch.WordTrace tailWord_7290833 prefixEnd_7290833 3743701700661778316057575 := by
  unfold tailWord_7290833
  simp only [CollatzResearch.WordTrace]
  refine ⟨265918525595564690988053153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177279017063709793992035435 265918525595564690988053153)
  ·
    refine ⟨199438894196673518241039865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265918525595564690988053153 199438894196673518241039865)
    ·
      refine ⟨149579170647505138680779899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199438894196673518241039865 149579170647505138680779899)
      ·
        refine ⟨224368755971257708021169849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149579170647505138680779899 224368755971257708021169849)
        ·
          refine ⟨168276566978443281015877387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224368755971257708021169849 168276566978443281015877387)
          ·
            refine ⟨252414850467664921523816081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168276566978443281015877387 252414850467664921523816081)
            ·
              refine ⟨189311137850748691142862061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252414850467664921523816081 189311137850748691142862061)
              ·
                refine ⟨70991676694030759178573273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189311137850748691142862061 70991676694030759178573273)
                ·
                  refine ⟨53243757520523069383929955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70991676694030759178573273 53243757520523069383929955)
                  ·
                    refine ⟨79865636280784604075894933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53243757520523069383929955 79865636280784604075894933)
                    ·
                      refine ⟨3743701700661778316057575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79865636280784604075894933 3743701700661778316057575)
                      ·
                        rfl

theorem cell23_7290833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_7290833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290833 prefixEnd_7290833 := by exact prefixLift 7290833
  have htrace : WordTrace (prefixWord ++ tailWord_7290833) baseStart_7290833 baseEnd_7290833 := by
    simpa [prefixWord, tailWord_7290833, baseEnd_7290833] using wordTrace_append hprefix tailTrace_7290833
  have hstable : (prefixWord ++ tailWord_7290833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290833).length < 2 ^ (prefixWord ++ tailWord_7290833).sum := by decide
  have hdescent : baseEnd_7290833 < baseStart_7290833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290837 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7290837 : Nat := 118140960795 + 7290837 * 2 ^ 59
def prefixEnd_7290837 : Nat := 4983230072969 + 3 ^ 40 * 7290837 * 2
def baseEnd_7290837 : Nat := 3743703754584396300407557

theorem tailTrace_7290837 : CollatzResearch.WordTrace tailWord_7290837 prefixEnd_7290837 3743703754584396300407557 := by
  unfold tailWord_7290837
  simp only [CollatzResearch.WordTrace]
  refine ⟨265918671487550199671198765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177279114325033466447465843 265918671487550199671198765)
  ·
    refine ⟨99719501807831324876699537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265918671487550199671198765 99719501807831324876699537)
    ·
      refine ⟨74789626355873493657524653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99719501807831324876699537 74789626355873493657524653)
      ·
        refine ⟨28046109883452560121571745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74789626355873493657524653 28046109883452560121571745)
        ·
          refine ⟨21034582412589420091178809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28046109883452560121571745 21034582412589420091178809)
          ·
            refine ⟨15775936809442065068384107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21034582412589420091178809 15775936809442065068384107)
            ·
              refine ⟨23663905214163097602576161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15775936809442065068384107 23663905214163097602576161)
              ·
                refine ⟨17747928910622323201932121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23663905214163097602576161 17747928910622323201932121)
                ·
                  refine ⟨13310946682966742401449091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17747928910622323201932121 13310946682966742401449091)
                  ·
                    refine ⟨19966420024450113602173637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13310946682966742401449091 19966420024450113602173637)
                    ·
                      refine ⟨3743703754584396300407557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19966420024450113602173637 3743703754584396300407557)
                      ·
                        rfl

theorem cell23_7290837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7290837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290837 prefixEnd_7290837 := by exact prefixLift 7290837
  have htrace : WordTrace (prefixWord ++ tailWord_7290837) baseStart_7290837 baseEnd_7290837 := by
    simpa [prefixWord, tailWord_7290837, baseEnd_7290837] using wordTrace_append hprefix tailTrace_7290837
  have hstable : (prefixWord ++ tailWord_7290837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290837).length < 2 ^ (prefixWord ++ tailWord_7290837).sum := by decide
  have hdescent : baseEnd_7290837 < baseStart_7290837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290847 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 3, 4]
def baseStart_7290847 : Nat := 118140960795 + 7290847 * 2 ^ 59
def prefixEnd_7290847 : Nat := 4983230072969 + 3 ^ 40 * 7290847 * 2
def baseEnd_7290847 : Nat := 1247902963130313753760837

theorem tailTrace_7290847 : CollatzResearch.WordTrace tailWord_7290847 prefixEnd_7290847 1247902963130313753760837 := by
  unfold tailWord_7290847
  simp only [CollatzResearch.WordTrace]
  refine ⟨265919036217513971379062795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177279357478342647586041863 265919036217513971379062795)
  ·
    refine ⟨398878554326270957068594193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265919036217513971379062795 398878554326270957068594193)
    ·
      refine ⟨299158915744703217801445645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398878554326270957068594193 299158915744703217801445645)
      ·
        refine ⟨112184593404263706675542117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299158915744703217801445645 112184593404263706675542117)
        ·
          refine ⟨21034611263299445001664147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112184593404263706675542117 21034611263299445001664147)
          ·
            refine ⟨31551916894949167502496221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21034611263299445001664147 31551916894949167502496221)
            ·
              refine ⟨11831968835605937813436083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31551916894949167502496221 11831968835605937813436083)
              ·
                refine ⟨17747953253408906720154125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831968835605937813436083 17747953253408906720154125)
                ·
                  refine ⟨6655482470028340020057797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17747953253408906720154125 6655482470028340020057797)
                  ·
                    refine ⟨1247902963130313753760837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655482470028340020057797 1247902963130313753760837)
                    ·
                      rfl

theorem cell23_7290847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_7290847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290847 prefixEnd_7290847 := by exact prefixLift 7290847
  have htrace : WordTrace (prefixWord ++ tailWord_7290847) baseStart_7290847 baseEnd_7290847 := by
    simpa [prefixWord, tailWord_7290847, baseEnd_7290847] using wordTrace_append hprefix tailTrace_7290847
  have hstable : (prefixWord ++ tailWord_7290847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290847).length < 2 ^ (prefixWord ++ tailWord_7290847).sum := by decide
  have hdescent : baseEnd_7290847 < baseStart_7290847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290883 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_7290883 : Nat := 118140960795 + 7290883 * 2 ^ 59
def prefixEnd_7290883 : Nat := 4983230072969 + 3 ^ 40 * 7290883 * 2
def baseEnd_7290883 : Nat := 3743727374694503120432345

theorem tailTrace_7290883 : CollatzResearch.WordTrace tailWord_7290883 prefixEnd_7290883 3743727374694503120432345 := by
  unfold tailWord_7290883
  simp only [CollatzResearch.WordTrace]
  refine ⟨265920349245383549527373303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177280232830255699684915535 265920349245383549527373303)
  ·
    refine ⟨398880523868075324291059955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265920349245383549527373303 398880523868075324291059955)
    ·
      refine ⟨598320785802112986436589933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398880523868075324291059955 598320785802112986436589933)
      ·
        refine ⟨224370294675792369913721225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598320785802112986436589933 224370294675792369913721225)
        ·
          refine ⟨168277721006844277435290919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224370294675792369913721225 168277721006844277435290919)
          ·
            refine ⟨252416581510266416152936379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168277721006844277435290919 252416581510266416152936379)
            ·
              refine ⟨378624872265399624229404569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252416581510266416152936379 378624872265399624229404569)
              ·
                refine ⟨283968654199049718172053427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378624872265399624229404569 283968654199049718172053427)
                ·
                  refine ⟨425952981298574577258080141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283968654199049718172053427 425952981298574577258080141)
                  ·
                    refine ⟨159732367986965466471780053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425952981298574577258080141 159732367986965466471780053)
                    ·
                      refine ⟨3743727374694503120432345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159732367986965466471780053 3743727374694503120432345)
                      ·
                        rfl

theorem cell23_7290883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_7290883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290883 prefixEnd_7290883 := by exact prefixLift 7290883
  have htrace : WordTrace (prefixWord ++ tailWord_7290883) baseStart_7290883 baseEnd_7290883 := by
    simpa [prefixWord, tailWord_7290883, baseEnd_7290883] using wordTrace_append hprefix tailTrace_7290883
  have hstable : (prefixWord ++ tailWord_7290883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290883).length < 2 ^ (prefixWord ++ tailWord_7290883).sum := by decide
  have hdescent : baseEnd_7290883 < baseStart_7290883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290944 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4]
def baseStart_7290944 : Nat := 118140960795 + 7290944 * 2 ^ 59
def prefixEnd_7290944 : Nat := 4983230072969 + 3 ^ 40 * 7290944 * 2
def baseEnd_7290944 : Nat := 3743758697014427381769565

theorem tailTrace_7290944 : CollatzResearch.WordTrace tailWord_7290944 prefixEnd_7290944 3743758697014427381769565 := by
  unfold tailWord_7290944
  simp only [CollatzResearch.WordTrace]
  refine ⟨132961287049081278472671943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177281716065441704630229257 132961287049081278472671943)
  ·
    refine ⟨199441930573621917709007915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132961287049081278472671943 199441930573621917709007915)
    ·
      refine ⟨299162895860432876563511873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199441930573621917709007915 299162895860432876563511873)
      ·
        refine ⟨224372171895324657422633905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299162895860432876563511873 224372171895324657422633905)
        ·
          refine ⟨168279128921493493066975429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224372171895324657422633905 168279128921493493066975429)
          ·
            refine ⟨31552336672780029950057893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168279128921493493066975429 31552336672780029950057893)
            ·
              refine ⟨5916063126146255615635855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31552336672780029950057893 5916063126146255615635855)
              ·
                refine ⟨8874094689219383423453783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916063126146255615635855 8874094689219383423453783)
                ·
                  refine ⟨13311142033829075135180675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874094689219383423453783 13311142033829075135180675)
                  ·
                    refine ⟨19966713050743612702771013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13311142033829075135180675 19966713050743612702771013)
                    ·
                      refine ⟨3743758697014427381769565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19966713050743612702771013 3743758697014427381769565)
                      ·
                        rfl

theorem cell23_7290944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_7290944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290944 prefixEnd_7290944 := by exact prefixLift 7290944
  have htrace : WordTrace (prefixWord ++ tailWord_7290944) baseStart_7290944 baseEnd_7290944 := by
    simpa [prefixWord, tailWord_7290944, baseEnd_7290944] using wordTrace_append hprefix tailTrace_7290944
  have hstable : (prefixWord ++ tailWord_7290944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290944).length < 2 ^ (prefixWord ++ tailWord_7290944).sum := by decide
  have hdescent : baseEnd_7290944 < baseStart_7290944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290957 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7290957 : Nat := 118140960795 + 7290957 * 2 ^ 59
def prefixEnd_7290957 : Nat := 4983230072969 + 3 ^ 40 * 7290957 * 2
def baseEnd_7290957 : Nat := 3743765372262935830907005

theorem tailTrace_7290957 : CollatzResearch.WordTrace tailWord_7290957 prefixEnd_7290957 3743765372262935830907005 := by
  unfold tailWord_7290957
  simp only [CollatzResearch.WordTrace]
  refine ⟨265923048247115460165567125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177282032164743640110378083 265923048247115460165567125)
  ·
    refine ⟨12465142886583537195260959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265923048247115460165567125 12465142886583537195260959)
    ·
      refine ⟨18697714329875305792891439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12465142886583537195260959 18697714329875305792891439)
      ·
        refine ⟨28046571494812958689337159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18697714329875305792891439 28046571494812958689337159)
        ·
          refine ⟨42069857242219438034005739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28046571494812958689337159 42069857242219438034005739)
          ·
            refine ⟨63104785863329157051008609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42069857242219438034005739 63104785863329157051008609)
            ·
              refine ⟨47328589397496867788256457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63104785863329157051008609 47328589397496867788256457)
              ·
                refine ⟨35496442048122650841192343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47328589397496867788256457 35496442048122650841192343)
                ·
                  refine ⟨53244663072183976261788515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35496442048122650841192343 53244663072183976261788515)
                  ·
                    refine ⟨79866994608275964392682773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53244663072183976261788515 79866994608275964392682773)
                    ·
                      refine ⟨3743765372262935830907005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79866994608275964392682773 3743765372262935830907005)
                      ·
                        rfl

theorem cell23_7290957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7290957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290957 prefixEnd_7290957 := by exact prefixLift 7290957
  have htrace : WordTrace (prefixWord ++ tailWord_7290957) baseStart_7290957 baseEnd_7290957 := by
    simpa [prefixWord, tailWord_7290957, baseEnd_7290957] using wordTrace_append hprefix tailTrace_7290957
  have hstable : (prefixWord ++ tailWord_7290957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290957).length < 2 ^ (prefixWord ++ tailWord_7290957).sum := by decide
  have hdescent : baseEnd_7290957 < baseStart_7290957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290960 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_7290960 : Nat := 118140960795 + 7290960 * 2 ^ 59
def prefixEnd_7290960 : Nat := 4983230072969 + 3 ^ 40 * 7290960 * 2
def baseEnd_7290960 : Nat := 3743766912704899319169491

theorem tailTrace_7290960 : CollatzResearch.WordTrace tailWord_7290960 prefixEnd_7290960 3743766912704899319169491 := by
  unfold tailWord_7290960
  simp only [CollatzResearch.WordTrace]
  refine ⟨132961578833052295838963167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177282105110736394451950889 132961578833052295838963167)
  ·
    refine ⟨199442368249578443758444751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132961578833052295838963167 199442368249578443758444751)
    ·
      refine ⟨299163552374367665637667127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199442368249578443758444751 299163552374367665637667127)
      ·
        refine ⟨448745328561551498456500691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299163552374367665637667127 448745328561551498456500691)
        ·
          refine ⟨673117992842327247684751037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448745328561551498456500691 673117992842327247684751037)
          ·
            refine ⟨252419247315872717881781639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673117992842327247684751037 252419247315872717881781639)
            ·
              refine ⟨378628870973809076822672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252419247315872717881781639 378628870973809076822672459)
              ·
                refine ⟨567943306460713615234008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378628870973809076822672459 567943306460713615234008689)
                ·
                  refine ⟨425957479845535211425506517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567943306460713615234008689 425957479845535211425506517)
                  ·
                    refine ⟨9983378433879731517785309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 425957479845535211425506517 9983378433879731517785309)
                    ·
                      refine ⟨3743766912704899319169491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983378433879731517785309 3743766912704899319169491)
                      ·
                        rfl

theorem cell23_7290960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_7290960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290960 prefixEnd_7290960 := by exact prefixLift 7290960
  have htrace : WordTrace (prefixWord ++ tailWord_7290960) baseStart_7290960 baseEnd_7290960 := by
    simpa [prefixWord, tailWord_7290960, baseEnd_7290960] using wordTrace_append hprefix tailTrace_7290960
  have hstable : (prefixWord ++ tailWord_7290960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290960).length < 2 ^ (prefixWord ++ tailWord_7290960).sum := by decide
  have hdescent : baseEnd_7290960 < baseStart_7290960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290980 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_7290980 : Nat := 118140960795 + 7290980 * 2 ^ 59
def prefixEnd_7290980 : Nat := 4983230072969 + 3 ^ 40 * 7290980 * 2
def baseEnd_7290980 : Nat := 1247925727439329746973133

theorem tailTrace_7290980 : CollatzResearch.WordTrace tailWord_7290980 prefixEnd_7290980 1247925727439329746973133 := by
  unfold tailWord_7290980
  simp only [CollatzResearch.WordTrace]
  refine ⟨132961943563016067546827197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177282591417354756729102929 132961943563016067546827197)
  ·
    refine ⟨49860728836131025330060199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132961943563016067546827197 49860728836131025330060199)
    ·
      refine ⟨74791093254196537995090299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49860728836131025330060199 74791093254196537995090299)
      ·
        refine ⟨112186639881294806992635449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74791093254196537995090299 112186639881294806992635449)
        ·
          refine ⟨84139979910971105244476587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112186639881294806992635449 84139979910971105244476587)
          ·
            refine ⟨126209969866456657866714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84139979910971105244476587 126209969866456657866714881)
            ·
              refine ⟨94657477399842493400036161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126209969866456657866714881 94657477399842493400036161)
              ·
                refine ⟨70993108049881870050027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94657477399842493400036161 70993108049881870050027121)
                ·
                  refine ⟨53244831037411402537520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70993108049881870050027121 53244831037411402537520341)
                  ·
                    refine ⟨1247925727439329746973133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53244831037411402537520341 1247925727439329746973133)
                    ·
                      rfl

theorem cell23_7290980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_7290980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290980 prefixEnd_7290980 := by exact prefixLift 7290980
  have htrace : WordTrace (prefixWord ++ tailWord_7290980) baseStart_7290980 baseEnd_7290980 := by
    simpa [prefixWord, tailWord_7290980, baseEnd_7290980] using wordTrace_append hprefix tailTrace_7290980
  have hstable : (prefixWord ++ tailWord_7290980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290980).length < 2 ^ (prefixWord ++ tailWord_7290980).sum := by decide
  have hdescent : baseEnd_7290980 < baseStart_7290980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7290994 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7290994 : Nat := 118140960795 + 7290994 * 2 ^ 59
def prefixEnd_7290994 : Nat := 4983230072969 + 3 ^ 40 * 7290994 * 2
def baseEnd_7290994 : Nat := 3743784371047152186144335

theorem tailTrace_7290994 : CollatzResearch.WordTrace tailWord_7290994 prefixEnd_7290994 3743784371047152186144335 := by
  unfold tailWord_7290994
  simp only [CollatzResearch.WordTrace]
  refine ⟨66481099436995353871166009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177282931831987610323109357 66481099436995353871166009)
  ·
    refine ⟨49860824577746515403374507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66481099436995353871166009 49860824577746515403374507)
    ·
      refine ⟨74791236866619773105061761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49860824577746515403374507 74791236866619773105061761)
      ·
        refine ⟨56093427649964829828796321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74791236866619773105061761 56093427649964829828796321)
        ·
          refine ⟨42070070737473622371597241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56093427649964829828796321 42070070737473622371597241)
          ·
            refine ⟨31552553053105216778697931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42070070737473622371597241 31552553053105216778697931)
            ·
              refine ⟨47328829579657825168046897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31552553053105216778697931 47328829579657825168046897)
              ·
                refine ⟨35496622184743368876035173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47328829579657825168046897 35496622184743368876035173)
                ·
                  refine ⟨6655616659639381664256595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35496622184743368876035173 6655616659639381664256595)
                  ·
                    refine ⟨9983424989459072496384893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6655616659639381664256595 9983424989459072496384893)
                    ·
                      refine ⟨3743784371047152186144335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983424989459072496384893 3743784371047152186144335)
                      ·
                        rfl

theorem cell23_7290994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7290994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7290994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7290994 prefixEnd_7290994 := by exact prefixLift 7290994
  have htrace : WordTrace (prefixWord ++ tailWord_7290994) baseStart_7290994 baseEnd_7290994 := by
    simpa [prefixWord, tailWord_7290994, baseEnd_7290994] using wordTrace_append hprefix tailTrace_7290994
  have hstable : (prefixWord ++ tailWord_7290994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7290994).length < 2 ^ (prefixWord ++ tailWord_7290994).sum := by decide
  have hdescent : baseEnd_7290994 < baseStart_7290994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7290994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291000 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_7291000 : Nat := 118140960795 + 7291000 * 2 ^ 59
def prefixEnd_7291000 : Nat := 4983230072969 + 3 ^ 40 * 7291000 * 2
def baseEnd_7291000 : Nat := 3743787451931079162669307

theorem tailTrace_7291000 : CollatzResearch.WordTrace tailWord_7291000 prefixEnd_7291000 3743787451931079162669307 := by
  unfold tailWord_7291000
  simp only [CollatzResearch.WordTrace]
  refine ⟨132962308292979839254691227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177283077723973119006254969 132962308292979839254691227)
  ·
    refine ⟨199443462439469758882036841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132962308292979839254691227 199443462439469758882036841)
    ·
      refine ⟨149582596829602319161527631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199443462439469758882036841 149582596829602319161527631)
      ·
        refine ⟨224373895244403478742291447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149582596829602319161527631 224373895244403478742291447)
        ·
          refine ⟨336560842866605218113437171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224373895244403478742291447 336560842866605218113437171)
          ·
            refine ⟨504841264299907827170155757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336560842866605218113437171 504841264299907827170155757)
            ·
              refine ⟨189315474112465435188808409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504841264299907827170155757 189315474112465435188808409)
              ·
                refine ⟨141986605584349076391606307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189315474112465435188808409 141986605584349076391606307)
                ·
                  refine ⟨212979908376523614587409461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141986605584349076391606307 212979908376523614587409461)
                  ·
                    refine ⟨19966866410299088867569637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212979908376523614587409461 19966866410299088867569637)
                    ·
                      refine ⟨3743787451931079162669307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19966866410299088867569637 3743787451931079162669307)
                      ·
                        rfl

theorem cell23_7291000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_7291000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291000 prefixEnd_7291000 := by exact prefixLift 7291000
  have htrace : WordTrace (prefixWord ++ tailWord_7291000) baseStart_7291000 baseEnd_7291000 := by
    simpa [prefixWord, tailWord_7291000, baseEnd_7291000] using wordTrace_append hprefix tailTrace_7291000
  have hstable : (prefixWord ++ tailWord_7291000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291000).length < 2 ^ (prefixWord ++ tailWord_7291000).sum := by decide
  have hdescent : baseEnd_7291000 < baseStart_7291000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291037 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_7291037 : Nat := 118140960795 + 7291037 * 2 ^ 59
def prefixEnd_7291037 : Nat := 4983230072969 + 3 ^ 40 * 7291037 * 2
def baseEnd_7291037 : Nat := 3743806450715295517906637

theorem tailTrace_7291037 : CollatzResearch.WordTrace tailWord_7291037 prefixEnd_7291037 3743806450715295517906637 := by
  unfold tailWord_7291037
  simp only [CollatzResearch.WordTrace]
  refine ⟨265925966086825633828479365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177283977391217089218986243 265925966086825633828479365)
  ·
    refine ⟨49861118641279806342839881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265925966086825633828479365 49861118641279806342839881)
    ·
      refine ⟨37395838980959854757129911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49861118641279806342839881 37395838980959854757129911)
      ·
        refine ⟨56093758471439782135694867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37395838980959854757129911 56093758471439782135694867)
        ·
          refine ⟨84140637707159673203542301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56093758471439782135694867 84140637707159673203542301)
          ·
            refine ⟨31552739140184877451328363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84140637707159673203542301 31552739140184877451328363)
            ·
              refine ⟨47329108710277316176992545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31552739140184877451328363 47329108710277316176992545)
              ·
                refine ⟨35496831532707987132744409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47329108710277316176992545 35496831532707987132744409)
                ·
                  refine ⟨26622623649530990349558307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35496831532707987132744409 26622623649530990349558307)
                  ·
                    refine ⟨39933935474296485524337461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26622623649530990349558307 39933935474296485524337461)
                    ·
                      refine ⟨3743806450715295517906637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39933935474296485524337461 3743806450715295517906637)
                      ·
                        rfl

theorem cell23_7291037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_7291037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291037 prefixEnd_7291037 := by exact prefixLift 7291037
  have htrace : WordTrace (prefixWord ++ tailWord_7291037) baseStart_7291037 baseEnd_7291037 := by
    simpa [prefixWord, tailWord_7291037, baseEnd_7291037] using wordTrace_append hprefix tailTrace_7291037
  have hstable : (prefixWord ++ tailWord_7291037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291037).length < 2 ^ (prefixWord ++ tailWord_7291037).sum := by decide
  have hdescent : baseEnd_7291037 < baseStart_7291037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291038 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7291038 : Nat := 118140960795 + 7291038 * 2 ^ 59
def prefixEnd_7291038 : Nat := 4983230072969 + 3 ^ 40 * 7291038 * 2
def baseEnd_7291038 : Nat := 3743806964195950013994133

theorem tailTrace_7291038 : CollatzResearch.WordTrace tailWord_7291038 prefixEnd_7291038 3743806964195950013994133 := by
  unfold tailWord_7291038
  simp only [CollatzResearch.WordTrace]
  refine ⟨33240750319977751374908221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177284001706548007332843845 33240750319977751374908221)
  ·
    refine ⟨12465281369991656765590583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33240750319977751374908221 12465281369991656765590583)
    ·
      refine ⟨18697922054987485148385875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12465281369991656765590583 18697922054987485148385875)
      ·
        refine ⟨28046883082481227722578813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18697922054987485148385875 28046883082481227722578813)
        ·
          refine ⟨10517581155930460395967055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28046883082481227722578813 10517581155930460395967055)
          ·
            refine ⟨15776371733895690593950583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517581155930460395967055 15776371733895690593950583)
            ·
              refine ⟨23664557600843535890925875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776371733895690593950583 23664557600843535890925875)
              ·
                refine ⟨35496836401265303836388813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23664557600843535890925875 35496836401265303836388813)
                ·
                  refine ⟨13311313650474488938645805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35496836401265303836388813 13311313650474488938645805)
                  ·
                    refine ⟨4991742618927933351992177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13311313650474488938645805 4991742618927933351992177)
                    ·
                      refine ⟨3743806964195950013994133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991742618927933351992177 3743806964195950013994133)
                      ·
                        rfl

theorem cell23_7291038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7291038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291038 prefixEnd_7291038 := by exact prefixLift 7291038
  have htrace : WordTrace (prefixWord ++ tailWord_7291038) baseStart_7291038 baseEnd_7291038 := by
    simpa [prefixWord, tailWord_7291038, baseEnd_7291038] using wordTrace_append hprefix tailTrace_7291038
  have hstable : (prefixWord ++ tailWord_7291038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291038).length < 2 ^ (prefixWord ++ tailWord_7291038).sum := by decide
  have hdescent : baseEnd_7291038 < baseStart_7291038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291067 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3]
def baseStart_7291067 : Nat := 118140960795 + 7291067 * 2 ^ 59
def prefixEnd_7291067 : Nat := 4983230072969 + 3 ^ 40 * 7291067 * 2
def baseEnd_7291067 : Nat := 3743821855134930400531499

theorem tailTrace_7291067 : CollatzResearch.WordTrace tailWord_7291067 prefixEnd_7291067 3743821855134930400531499 := by
  unfold tailWord_7291067
  simp only [CollatzResearch.WordTrace]
  refine ⟨265927060276716948952071455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177284706851144632634714303 265927060276716948952071455)
  ·
    refine ⟨398890590415075423428107183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265927060276716948952071455 398890590415075423428107183)
    ·
      refine ⟨598335885622613135142160775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398890590415075423428107183 598335885622613135142160775)
      ·
        refine ⟨897503828433919702713241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598335885622613135142160775 897503828433919702713241163)
        ·
          refine ⟨1346255742650879554069861745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897503828433919702713241163 1346255742650879554069861745)
          ·
            refine ⟨1009691806988159665552396309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346255742650879554069861745 1009691806988159665552396309)
            ·
              refine ⟨47329303452569984322768577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1009691806988159665552396309 47329303452569984322768577)
              ·
                refine ⟨35496977589427488242076433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47329303452569984322768577 35496977589427488242076433)
                ·
                  refine ⟨26622733192070616181557325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35496977589427488242076433 26622733192070616181557325)
                  ·
                    refine ⟨9983524947026481068083997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26622733192070616181557325 9983524947026481068083997)
                    ·
                      refine ⟨3743821855134930400531499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983524947026481068083997 3743821855134930400531499)
                      ·
                        rfl

theorem cell23_7291067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 3].length) (baseStart_7291067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291067 prefixEnd_7291067 := by exact prefixLift 7291067
  have htrace : WordTrace (prefixWord ++ tailWord_7291067) baseStart_7291067 baseEnd_7291067 := by
    simpa [prefixWord, tailWord_7291067, baseEnd_7291067] using wordTrace_append hprefix tailTrace_7291067
  have hstable : (prefixWord ++ tailWord_7291067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291067).length < 2 ^ (prefixWord ++ tailWord_7291067).sum := by decide
  have hdescent : baseEnd_7291067 < baseStart_7291067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291106 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7291106 : Nat := 118140960795 + 7291106 * 2 ^ 59
def prefixEnd_7291106 : Nat := 4983230072969 + 3 ^ 40 * 7291106 * 2
def baseEnd_7291106 : Nat := 3743841880880455747943821

theorem tailTrace_7291106 : CollatzResearch.WordTrace tailWord_7291106 prefixEnd_7291106 3743841880880455747943821 := by
  unfold tailWord_7291106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66482120680893914653185293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177285655149050439075160781 66482120680893914653185293)
  ·
    refine ⟨24930795255335217994944485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66482120680893914653185293 24930795255335217994944485)
    ·
      refine ⟨4674524110375353374052091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24930795255335217994944485 4674524110375353374052091)
      ·
        refine ⟨7011786165563030061078137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674524110375353374052091 7011786165563030061078137)
        ·
          refine ⟨5258839624172272545808603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011786165563030061078137 5258839624172272545808603)
          ·
            refine ⟨7888259436258408818712905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258839624172272545808603 7888259436258408818712905)
            ·
              refine ⟨5916194577193806614034679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888259436258408818712905 5916194577193806614034679)
              ·
                refine ⟨8874291865790709921052019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916194577193806614034679 8874291865790709921052019)
                ·
                  refine ⟨13311437798686064881578029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874291865790709921052019 13311437798686064881578029)
                  ·
                    refine ⟨4991789174507274330591761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13311437798686064881578029 4991789174507274330591761)
                    ·
                      refine ⟨3743841880880455747943821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991789174507274330591761 3743841880880455747943821)
                      ·
                        rfl

theorem cell23_7291106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7291106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291106 prefixEnd_7291106 := by exact prefixLift 7291106
  have htrace : WordTrace (prefixWord ++ tailWord_7291106) baseStart_7291106 baseEnd_7291106 := by
    simpa [prefixWord, tailWord_7291106, baseEnd_7291106] using wordTrace_append hprefix tailTrace_7291106
  have hstable : (prefixWord ++ tailWord_7291106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291106).length < 2 ^ (prefixWord ++ tailWord_7291106).sum := by decide
  have hdescent : baseEnd_7291106 < baseStart_7291106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291127 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_7291127 : Nat := 118140960795 + 7291127 * 2 ^ 59
def prefixEnd_7291127 : Nat := 4983230072969 + 3 ^ 40 * 7291127 * 2
def baseEnd_7291127 : Nat := 3743852663974200165781223

theorem tailTrace_7291127 : CollatzResearch.WordTrace tailWord_7291127 prefixEnd_7291127 3743852663974200165781223 := by
  unfold tailWord_7291127
  simp only [CollatzResearch.WordTrace]
  refine ⟨265929248656499579199255635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177286165770999719466170423 265929248656499579199255635)
  ·
    refine ⟨398893872984749368798883453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265929248656499579199255635 398893872984749368798883453)
    ·
      refine ⟨149585202369281013299581295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398893872984749368798883453 149585202369281013299581295)
      ·
        refine ⟨224377803553921519949371943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149585202369281013299581295 224377803553921519949371943)
        ·
          refine ⟨336566705330882279924057915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224377803553921519949371943 336566705330882279924057915)
          ·
            refine ⟨504850057996323419886086873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336566705330882279924057915 504850057996323419886086873)
            ·
              refine ⟨378637543497242564914565155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504850057996323419886086873 378637543497242564914565155)
              ·
                refine ⟨567956315245863847371847733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378637543497242564914565155 567956315245863847371847733)
                ·
                  refine ⟨53245904554299735691110725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 567956315245863847371847733 53245904554299735691110725)
                  ·
                    refine ⟨9983607103931200442083261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53245904554299735691110725 9983607103931200442083261)
                    ·
                      refine ⟨3743852663974200165781223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983607103931200442083261 3743852663974200165781223)
                      ·
                        rfl

theorem cell23_7291127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_7291127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291127 prefixEnd_7291127 := by exact prefixLift 7291127
  have htrace : WordTrace (prefixWord ++ tailWord_7291127) baseStart_7291127 baseEnd_7291127 := by
    simpa [prefixWord, tailWord_7291127, baseEnd_7291127] using wordTrace_append hprefix tailTrace_7291127
  have hstable : (prefixWord ++ tailWord_7291127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291127).length < 2 ^ (prefixWord ++ tailWord_7291127).sum := by decide
  have hdescent : baseEnd_7291127 < baseStart_7291127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291137 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7291137 : Nat := 118140960795 + 7291137 * 2 ^ 59
def prefixEnd_7291137 : Nat := 4983230072969 + 3 ^ 40 * 7291137 * 2
def baseEnd_7291137 : Nat := 3743857798780745126656177

theorem tailTrace_7291137 : CollatzResearch.WordTrace tailWord_7291137 prefixEnd_7291137 3743857798780745126656177 := by
  unfold tailWord_7291137
  simp only [CollatzResearch.WordTrace]
  refine ⟨265929613386463350907119665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177286408924308900604746443 265929613386463350907119665)
  ·
    refine ⟨199447210039847513180339749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265929613386463350907119665 199447210039847513180339749)
    ·
      refine ⟨37396351882471408721313703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199447210039847513180339749 37396351882471408721313703)
      ·
        refine ⟨56094527823707113081970555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37396351882471408721313703 56094527823707113081970555)
        ·
          refine ⟨84141791735560669622955833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56094527823707113081970555 84141791735560669622955833)
          ·
            refine ⟨63106343801670502217216875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84141791735560669622955833 63106343801670502217216875)
            ·
              refine ⟨94659515702505753325825313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63106343801670502217216875 94659515702505753325825313)
              ·
                refine ⟨70994636776879314994368985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94659515702505753325825313 70994636776879314994368985)
                ·
                  refine ⟨53245977582659486245776739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70994636776879314994368985 53245977582659486245776739)
                  ·
                    refine ⟨79868966373989229368665109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53245977582659486245776739 79868966373989229368665109)
                    ·
                      refine ⟨3743857798780745126656177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79868966373989229368665109 3743857798780745126656177)
                      ·
                        rfl

theorem cell23_7291137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7291137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291137 prefixEnd_7291137 := by exact prefixLift 7291137
  have htrace : WordTrace (prefixWord ++ tailWord_7291137) baseStart_7291137 baseEnd_7291137 := by
    simpa [prefixWord, tailWord_7291137, baseEnd_7291137] using wordTrace_append hprefix tailTrace_7291137
  have hstable : (prefixWord ++ tailWord_7291137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291137).length < 2 ^ (prefixWord ++ tailWord_7291137).sum := by decide
  have hdescent : baseEnd_7291137 < baseStart_7291137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291144 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_7291144 : Nat := 118140960795 + 7291144 * 2 ^ 59
def prefixEnd_7291144 : Nat := 4983230072969 + 3 ^ 40 * 7291144 * 2
def baseEnd_7291144 : Nat := 3743861393145326599268645

theorem tailTrace_7291144 : CollatzResearch.WordTrace tailWord_7291144 prefixEnd_7291144 3743861393145326599268645 := by
  unfold tailWord_7291144
  simp only [CollatzResearch.WordTrace]
  refine ⟨132964934348718995551312243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177286579131625327401749657 132964934348718995551312243)
  ·
    refine ⟨199447401523078493326968365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132964934348718995551312243 199447401523078493326968365)
    ·
      refine ⟨74792775571154434997613137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199447401523078493326968365 74792775571154434997613137)
      ·
        refine ⟨56094581678365826248209853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74792775571154434997613137 56094581678365826248209853)
        ·
          refine ⟨21035468129387184843078695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56094581678365826248209853 21035468129387184843078695)
          ·
            refine ⟨31553202194080777264618043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035468129387184843078695 31553202194080777264618043)
            ·
              refine ⟨47329803291121165896927065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31553202194080777264618043 47329803291121165896927065)
              ·
                refine ⟨35497352468340874422695299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47329803291121165896927065 35497352468340874422695299)
                ·
                  refine ⟨53246028702511311634042949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35497352468340874422695299 53246028702511311634042949)
                  ·
                    refine ⟨9983630381720870931383053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53246028702511311634042949 9983630381720870931383053)
                    ·
                      refine ⟨3743861393145326599268645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983630381720870931383053 3743861393145326599268645)
                      ·
                        rfl

theorem cell23_7291144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_7291144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291144 prefixEnd_7291144 := by exact prefixLift 7291144
  have htrace : WordTrace (prefixWord ++ tailWord_7291144) baseStart_7291144 baseEnd_7291144 := by
    simpa [prefixWord, tailWord_7291144, baseEnd_7291144] using wordTrace_append hprefix tailTrace_7291144
  have hstable : (prefixWord ++ tailWord_7291144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291144).length < 2 ^ (prefixWord ++ tailWord_7291144).sum := by decide
  have hdescent : baseEnd_7291144 < baseStart_7291144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291168 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 1, 4]
def baseStart_7291168 : Nat := 118140960795 + 7291168 * 2 ^ 59
def prefixEnd_7291168 : Nat := 4983230072969 + 3 ^ 40 * 7291168 * 2
def baseEnd_7291168 : Nat := 1247957905560344835122845

theorem tailTrace_7291168 : CollatzResearch.WordTrace tailWord_7291168 prefixEnd_7291168 1247957905560344835122845 := by
  unfold tailWord_7291168
  simp only [CollatzResearch.WordTrace]
  refine ⟨132965372024675521600749079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177287162699567362134332105 132965372024675521600749079)
  ·
    refine ⟨199448058037013282401123619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132965372024675521600749079 199448058037013282401123619)
    ·
      refine ⟨299172087055519923601685429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199448058037013282401123619 299172087055519923601685429)
      ·
        refine ⟨28047383161454992837658009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299172087055519923601685429 28047383161454992837658009)
        ·
          refine ⟨21035537371091244628243507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28047383161454992837658009 21035537371091244628243507)
          ·
            refine ⟨31553306056636866942365261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035537371091244628243507 31553306056636866942365261)
            ·
              refine ⟨11832489771238825103386973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31553306056636866942365261 11832489771238825103386973)
              ·
                refine ⟨4437183664214559413770115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11832489771238825103386973 4437183664214559413770115)
                ·
                  refine ⟨6655775496321839120655173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437183664214559413770115 6655775496321839120655173)
                  ·
                    refine ⟨1247957905560344835122845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655775496321839120655173 1247957905560344835122845)
                    ·
                      rfl

theorem cell23_7291168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_7291168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291168 prefixEnd_7291168 := by exact prefixLift 7291168
  have htrace : WordTrace (prefixWord ++ tailWord_7291168) baseStart_7291168 baseEnd_7291168 := by
    simpa [prefixWord, tailWord_7291168, baseEnd_7291168] using wordTrace_append hprefix tailTrace_7291168
  have hstable : (prefixWord ++ tailWord_7291168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291168).length < 2 ^ (prefixWord ++ tailWord_7291168).sum := by decide
  have hdescent : baseEnd_7291168 < baseStart_7291168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291175 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7291175 : Nat := 118140960795 + 7291175 * 2 ^ 59
def prefixEnd_7291175 : Nat := 4983230072969 + 3 ^ 40 * 7291175 * 2
def baseEnd_7291175 : Nat := 3743877311045615977981003

theorem tailTrace_7291175 : CollatzResearch.WordTrace tailWord_7291175 prefixEnd_7291175 3743877311045615977981003 := by
  unfold tailWord_7291175
  simp only [CollatzResearch.WordTrace]
  refine ⟨265930999360325683397002979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177287332906883788931335319 265930999360325683397002979)
  ·
    refine ⟨398896499040488525095504469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265930999360325683397002979 398896499040488525095504469)
    ·
      refine ⟨4674568348130724903462943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 398896499040488525095504469 4674568348130724903462943)
      ·
        refine ⟨7011852522196087355194415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674568348130724903462943 7011852522196087355194415)
        ·
          refine ⟨10517778783294131032791623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011852522196087355194415 10517778783294131032791623)
          ·
            refine ⟨15776668174941196549187435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517778783294131032791623 15776668174941196549187435)
            ·
              refine ⟨23665002262411794823781153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776668174941196549187435 23665002262411794823781153)
              ·
                refine ⟨17748751696808846117835865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23665002262411794823781153 17748751696808846117835865)
                ·
                  refine ⟨13311563772606634588376899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17748751696808846117835865 13311563772606634588376899)
                  ·
                    refine ⟨19967345658909951882565349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13311563772606634588376899 19967345658909951882565349)
                    ·
                      refine ⟨3743877311045615977981003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19967345658909951882565349 3743877311045615977981003)
                      ·
                        rfl

theorem cell23_7291175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7291175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291175 prefixEnd_7291175 := by exact prefixLift 7291175
  have htrace : WordTrace (prefixWord ++ tailWord_7291175) baseStart_7291175 baseEnd_7291175 := by
    simpa [prefixWord, tailWord_7291175, baseEnd_7291175] using wordTrace_append hprefix tailTrace_7291175
  have hstable : (prefixWord ++ tailWord_7291175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291175).length < 2 ^ (prefixWord ++ tailWord_7291175).sum := by decide
  have hdescent : baseEnd_7291175 < baseStart_7291175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291178 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7291178 : Nat := 118140960795 + 7291178 * 2 ^ 59
def prefixEnd_7291178 : Nat := 4983230072969 + 3 ^ 40 * 7291178 * 2
def baseEnd_7291178 : Nat := 3743878851487579466243489

theorem tailTrace_7291178 : CollatzResearch.WordTrace tailWord_7291178 prefixEnd_7291178 3743878851487579466243489 := by
  unfold tailWord_7291178
  simp only [CollatzResearch.WordTrace]
  refine ⟨66482777194828703727340547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177287405852876543272908125 66482777194828703727340547)
  ·
    refine ⟨99724165792243055591010821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66482777194828703727340547 99724165792243055591010821)
    ·
      refine ⟨18698281086045572923314529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99724165792243055591010821 18698281086045572923314529)
      ·
        refine ⟨14023710814534179692485897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18698281086045572923314529 14023710814534179692485897)
        ·
          refine ⟨10517783110900634769364423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14023710814534179692485897 10517783110900634769364423)
          ·
            refine ⟨15776674666350952154046635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517783110900634769364423 15776674666350952154046635)
            ·
              refine ⟨23665011999526428231069953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776674666350952154046635 23665011999526428231069953)
              ·
                refine ⟨17748758999644821173302465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23665011999526428231069953 17748758999644821173302465)
                ·
                  refine ⟨13311569249733615879976849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17748758999644821173302465 13311569249733615879976849)
                  ·
                    refine ⟨9983676937300211909982637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13311569249733615879976849 9983676937300211909982637)
                    ·
                      refine ⟨3743878851487579466243489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983676937300211909982637 3743878851487579466243489)
                      ·
                        rfl

theorem cell23_7291178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7291178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291178 prefixEnd_7291178 := by exact prefixLift 7291178
  have htrace : WordTrace (prefixWord ++ tailWord_7291178) baseStart_7291178 baseEnd_7291178 := by
    simpa [prefixWord, tailWord_7291178, baseEnd_7291178] using wordTrace_append hprefix tailTrace_7291178
  have hstable : (prefixWord ++ tailWord_7291178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291178).length < 2 ^ (prefixWord ++ tailWord_7291178).sum := by decide
  have hdescent : baseEnd_7291178 < baseStart_7291178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291184 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2]
def baseStart_7291184 : Nat := 118140960795 + 7291184 * 2 ^ 59
def prefixEnd_7291184 : Nat := 4983230072969 + 3 ^ 40 * 7291184 * 2
def baseEnd_7291184 : Nat := 3743881932371506442768461

theorem tailTrace_7291184 : CollatzResearch.WordTrace tailWord_7291184 prefixEnd_7291184 3743881932371506442768461 := by
  unfold tailWord_7291184
  simp only [CollatzResearch.WordTrace]
  refine ⟨132965663808646538967040303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177287551744862051956053737 132965663808646538967040303)
  ·
    refine ⟨199448495712969808450560455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132965663808646538967040303 199448495712969808450560455)
    ·
      refine ⟨299172743569454712675840683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199448495712969808450560455 299172743569454712675840683)
      ·
        refine ⟨448759115354182069013761025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299172743569454712675840683 448759115354182069013761025)
        ·
          refine ⟨336569336515636551760320769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448759115354182069013761025 336569336515636551760320769)
          ·
            refine ⟨252427002386727413820240577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336569336515636551760320769 252427002386727413820240577)
            ·
              refine ⟨189320251790045560365180433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252427002386727413820240577 189320251790045560365180433)
              ·
                refine ⟨141990188842534170273885325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189320251790045560365180433 141990188842534170273885325)
                ·
                  refine ⟨53246320815950313852706997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141990188842534170273885325 53246320815950313852706997)
                  ·
                    refine ⟨4991842576495341923691281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53246320815950313852706997 4991842576495341923691281)
                    ·
                      refine ⟨3743881932371506442768461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991842576495341923691281 3743881932371506442768461)
                      ·
                        rfl

theorem cell23_7291184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2].length) (baseStart_7291184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291184 prefixEnd_7291184 := by exact prefixLift 7291184
  have htrace : WordTrace (prefixWord ++ tailWord_7291184) baseStart_7291184 baseEnd_7291184 := by
    simpa [prefixWord, tailWord_7291184, baseEnd_7291184] using wordTrace_append hprefix tailTrace_7291184
  have hstable : (prefixWord ++ tailWord_7291184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291184).length < 2 ^ (prefixWord ++ tailWord_7291184).sum := by decide
  have hdescent : baseEnd_7291184 < baseStart_7291184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291185 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 1, 4]
def baseStart_7291185 : Nat := 118140960795 + 7291185 * 2 ^ 59
def prefixEnd_7291185 : Nat := 4983230072969 + 3 ^ 40 * 7291185 * 2
def baseEnd_7291185 : Nat := 1247960815284053646285319

theorem tailTrace_7291185 : CollatzResearch.WordTrace tailWord_7291185 prefixEnd_7291185 1247960815284053646285319 := by
  unfold tailWord_7291185
  simp only [CollatzResearch.WordTrace]
  refine ⟨265931364090289455104867009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177287576060192970069911339 265931364090289455104867009)
  ·
    refine ⟨199448523067717091328650257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265931364090289455104867009 199448523067717091328650257)
    ·
      refine ⟨149586392300787818496487693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199448523067717091328650257 149586392300787818496487693)
      ·
        refine ⟨56094897112795431936182885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149586392300787818496487693 56094897112795431936182885)
        ·
          refine ⟨10517793208649143488034291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56094897112795431936182885 10517793208649143488034291)
          ·
            refine ⟨15776689812973715232051437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517793208649143488034291 15776689812973715232051437)
            ·
              refine ⟨5916258679865143212019289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15776689812973715232051437 5916258679865143212019289)
              ·
                refine ⟨4437194009898857409014467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916258679865143212019289 4437194009898857409014467)
                ·
                  refine ⟨6655791014848286113521701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437194009898857409014467 6655791014848286113521701)
                  ·
                    refine ⟨1247960815284053646285319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655791014848286113521701 1247960815284053646285319)
                    ·
                      rfl

theorem cell23_7291185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_7291185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291185 prefixEnd_7291185 := by exact prefixLift 7291185
  have htrace : WordTrace (prefixWord ++ tailWord_7291185) baseStart_7291185 baseEnd_7291185 := by
    simpa [prefixWord, tailWord_7291185, baseEnd_7291185] using wordTrace_append hprefix tailTrace_7291185
  have hstable : (prefixWord ++ tailWord_7291185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291185).length < 2 ^ (prefixWord ++ tailWord_7291185).sum := by decide
  have hdescent : baseEnd_7291185 < baseStart_7291185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291198 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_7291198 : Nat := 118140960795 + 7291198 * 2 ^ 59
def prefixEnd_7291198 : Nat := 4983230072969 + 3 ^ 40 * 7291198 * 2
def baseEnd_7291198 : Nat := 415987680122296598665933

theorem tailTrace_7291198 : CollatzResearch.WordTrace tailWord_7291198 prefixEnd_7291198 415987680122296598665933 := by
  unfold tailWord_7291198
  simp only [CollatzResearch.WordTrace]
  refine ⟨33241479779905294790636281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177287892159494905550060165 33241479779905294790636281)
  ·
    refine ⟨24931109834928971092977211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33241479779905294790636281 24931109834928971092977211)
    ·
      refine ⟨37396664752393456639465817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24931109834928971092977211 37396664752393456639465817)
      ·
        refine ⟨28047498564295092479599363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37396664752393456639465817 28047498564295092479599363)
        ·
          refine ⟨42071247846442638719399045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047498564295092479599363 42071247846442638719399045)
          ·
            refine ⟨7888358971207994759887321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42071247846442638719399045 7888358971207994759887321)
            ·
              refine ⟨5916269228405996069915491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888358971207994759887321 5916269228405996069915491)
              ·
                refine ⟨8874403842608994104873237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916269228405996069915491 8874403842608994104873237)
                ·
                  refine ⟨415987680122296598665933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8874403842608994104873237 415987680122296598665933)
                  ·
                    rfl

theorem cell23_7291198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_7291198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291198 prefixEnd_7291198 := by exact prefixLift 7291198
  have htrace : WordTrace (prefixWord ++ tailWord_7291198) baseStart_7291198 baseEnd_7291198 := by
    simpa [prefixWord, tailWord_7291198, baseEnd_7291198] using wordTrace_append hprefix tailTrace_7291198
  have hstable : (prefixWord ++ tailWord_7291198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291198).length < 2 ^ (prefixWord ++ tailWord_7291198).sum := by decide
  have hdescent : baseEnd_7291198 < baseStart_7291198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291224 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_7291224 : Nat := 118140960795 + 7291224 * 2 ^ 59
def prefixEnd_7291224 : Nat := 4983230072969 + 3 ^ 40 * 7291224 * 2
def baseEnd_7291224 : Nat := 1247967490532562095422759

theorem tailTrace_7291224 : CollatzResearch.WordTrace tailWord_7291224 prefixEnd_7291224 1247967490532562095422759 := by
  unfold tailWord_7291224
  simp only [CollatzResearch.WordTrace]
  refine ⟨132966393268574082382768363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177288524358098776510357817 132966393268574082382768363)
  ·
    refine ⟨199449589902861123574152545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132966393268574082382768363 199449589902861123574152545)
    ·
      refine ⟨149587192427145842680614409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199449589902861123574152545 149587192427145842680614409)
      ·
        refine ⟨112190394320359382010460807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149587192427145842680614409 112190394320359382010460807)
        ·
          refine ⟨168285591480539073015691211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112190394320359382010460807 168285591480539073015691211)
          ·
            refine ⟨252428387220808609523536817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168285591480539073015691211 252428387220808609523536817)
            ·
              refine ⟨189321290415606457142652613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252428387220808609523536817 189321290415606457142652613)
              ·
                refine ⟨35497741952926210714247365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189321290415606457142652613 35497741952926210714247365)
                ·
                  refine ⟨6655826616173664508921381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35497741952926210714247365 6655826616173664508921381)
                  ·
                    refine ⟨1247967490532562095422759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655826616173664508921381 1247967490532562095422759)
                    ·
                      rfl

theorem cell23_7291224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_7291224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291224 prefixEnd_7291224 := by exact prefixLift 7291224
  have htrace : WordTrace (prefixWord ++ tailWord_7291224) baseStart_7291224 baseEnd_7291224 := by
    simpa [prefixWord, tailWord_7291224, baseEnd_7291224] using wordTrace_append hprefix tailTrace_7291224
  have hstable : (prefixWord ++ tailWord_7291224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291224).length < 2 ^ (prefixWord ++ tailWord_7291224).sum := by decide
  have hdescent : baseEnd_7291224 < baseStart_7291224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291237 : List Nat := [1, 3, 1, 3, 1, 14]
def baseStart_7291237 : Nat := 118140960795 + 7291237 * 2 ^ 59
def prefixEnd_7291237 : Nat := 4983230072969 + 3 ^ 40 * 7291237 * 2
def baseEnd_7291237 : Nat := 15407033526116027717719

theorem tailTrace_7291237 : CollatzResearch.WordTrace tailWord_7291237 prefixEnd_7291237 15407033526116027717719 := by
  unfold tailWord_7291237
  simp only [CollatzResearch.WordTrace]
  refine ⟨265933260686101067985759965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177288840457400711990506643 265933260686101067985759965)
  ·
    refine ⟨99724972757287900494659987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265933260686101067985759965 99724972757287900494659987)
    ·
      refine ⟨149587459135931850741989981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99724972757287900494659987 149587459135931850741989981)
      ·
        refine ⟨56095297175974444028246243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149587459135931850741989981 56095297175974444028246243)
        ·
          refine ⟨84142945763961666042369365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56095297175974444028246243 84142945763961666042369365)
          ·
            refine ⟨15407033526116027717719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 84142945763961666042369365 15407033526116027717719)
            ·
              rfl

theorem cell23_7291237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 14].length) (baseStart_7291237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291237 prefixEnd_7291237 := by exact prefixLift 7291237
  have htrace : WordTrace (prefixWord ++ tailWord_7291237) baseStart_7291237 baseEnd_7291237 := by
    simpa [prefixWord, tailWord_7291237, baseEnd_7291237] using wordTrace_append hprefix tailTrace_7291237
  have hstable : (prefixWord ++ tailWord_7291237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291237).length < 2 ^ (prefixWord ++ tailWord_7291237).sum := by decide
  have hdescent : baseEnd_7291237 < baseStart_7291237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291241 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_7291241 : Nat := 118140960795 + 7291241 * 2 ^ 59
def prefixEnd_7291241 : Nat := 4983230072969 + 3 ^ 40 * 7291241 * 2
def baseEnd_7291241 : Nat := 1247970400256270906585233

theorem tailTrace_7291241 : CollatzResearch.WordTrace tailWord_7291241 prefixEnd_7291241 1247970400256270906585233 := by
  unfold tailWord_7291241
  simp only [CollatzResearch.WordTrace]
  refine ⟨265933406578086576668905577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177288937718724384445937051 265933406578086576668905577)
  ·
    refine ⟨199450054933564932501679183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265933406578086576668905577 199450054933564932501679183)
    ·
      refine ⟨299175082400347398752518775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199450054933564932501679183 299175082400347398752518775)
      ·
        refine ⟨448762623600521098128778163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299175082400347398752518775 448762623600521098128778163)
        ·
          refine ⟨673143935400781647193167245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448762623600521098128778163 673143935400781647193167245)
          ·
            refine ⟨252428975775293117697437717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673143935400781647193167245 252428975775293117697437717)
            ·
              refine ⟨11832608239466864892067393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252428975775293117697437717 11832608239466864892067393)
              ·
                refine ⟨8874456179600148669050545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832608239466864892067393 8874456179600148669050545)
                ·
                  refine ⟨6655842134700111501787909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874456179600148669050545 6655842134700111501787909)
                  ·
                    refine ⟨1247970400256270906585233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655842134700111501787909 1247970400256270906585233)
                    ·
                      rfl

theorem cell23_7291241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_7291241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291241 prefixEnd_7291241 := by exact prefixLift 7291241
  have htrace : WordTrace (prefixWord ++ tailWord_7291241) baseStart_7291241 baseEnd_7291241 := by
    simpa [prefixWord, tailWord_7291241, baseEnd_7291241] using wordTrace_append hprefix tailTrace_7291241
  have hstable : (prefixWord ++ tailWord_7291241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291241).length < 2 ^ (prefixWord ++ tailWord_7291241).sum := by decide
  have hdescent : baseEnd_7291241 < baseStart_7291241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291242 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7291242 : Nat := 118140960795 + 7291242 * 2 ^ 59
def prefixEnd_7291242 : Nat := 4983230072969 + 3 ^ 40 * 7291242 * 2
def baseEnd_7291242 : Nat := 3743911714249467215843195

theorem tailTrace_7291242 : CollatzResearch.WordTrace tailWord_7291242 prefixEnd_7291242 3743911714249467215843195 := by
  unfold tailWord_7291242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66483360762770738459922995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177288962034055302559794653 66483360762770738459922995)
  ·
    refine ⟨99725041144156107689884493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66483360762770738459922995 99725041144156107689884493)
    ·
      refine ⟨37396890429058540383706685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99725041144156107689884493 37396890429058540383706685)
      ·
        refine ⟨14023833910896952643890007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37396890429058540383706685 14023833910896952643890007)
        ·
          refine ⟨21035750866345428965835011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023833910896952643890007 21035750866345428965835011)
          ·
            refine ⟨31553626299518143448752517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035750866345428965835011 31553626299518143448752517)
            ·
              refine ⟨5916304931159651896641097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31553626299518143448752517 5916304931159651896641097)
              ·
                refine ⟨4437228698369738922480823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916304931159651896641097 4437228698369738922480823)
                ·
                  refine ⟨6655843047554608383721235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437228698369738922480823 6655843047554608383721235)
                  ·
                    refine ⟨9983764571331912575581853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6655843047554608383721235 9983764571331912575581853)
                    ·
                      refine ⟨3743911714249467215843195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983764571331912575581853 3743911714249467215843195)
                      ·
                        rfl

theorem cell23_7291242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7291242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291242 prefixEnd_7291242 := by exact prefixLift 7291242
  have htrace : WordTrace (prefixWord ++ tailWord_7291242) baseStart_7291242 baseEnd_7291242 := by
    simpa [prefixWord, tailWord_7291242, baseEnd_7291242] using wordTrace_append hprefix tailTrace_7291242
  have hstable : (prefixWord ++ tailWord_7291242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291242).length < 2 ^ (prefixWord ++ tailWord_7291242).sum := by decide
  have hdescent : baseEnd_7291242 < baseStart_7291242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_7291247 : Nat := 118140960795 + 7291247 * 2 ^ 59
def prefixEnd_7291247 : Nat := 4983230072969 + 3 ^ 40 * 7291247 * 2
def baseEnd_7291247 : Nat := 3743914281652739696280671

theorem tailTrace_7291247 : CollatzResearch.WordTrace tailWord_7291247 prefixEnd_7291247 3743914281652739696280671 := by
  unfold tailWord_7291247
  simp only [CollatzResearch.WordTrace]
  refine ⟨265933625416064839693623995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177289083610709893129082663 265933625416064839693623995)
  ·
    refine ⟨398900438124097259540435993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265933625416064839693623995 398900438124097259540435993)
    ·
      refine ⟨299175328593072944655326995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398900438124097259540435993 299175328593072944655326995)
      ·
        refine ⟨448762992889609416982990493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299175328593072944655326995 448762992889609416982990493)
        ·
          refine ⟨168286122333603531368621435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448762992889609416982990493 168286122333603531368621435)
          ·
            refine ⟨252429183500405297052932153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168286122333603531368621435 252429183500405297052932153)
            ·
              refine ⟨189321887625303972789699115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252429183500405297052932153 189321887625303972789699115)
              ·
                refine ⟨283982831437955959184548673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189321887625303972789699115 283982831437955959184548673)
                ·
                  refine ⟨212987123578466969388411505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283982831437955959184548673 212987123578466969388411505)
                  ·
                    refine ⟨159740342683850227041308629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212987123578466969388411505 159740342683850227041308629)
                    ·
                      refine ⟨3743914281652739696280671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159740342683850227041308629 3743914281652739696280671)
                      ·
                        rfl

theorem cell23_7291247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_7291247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291247 prefixEnd_7291247 := by exact prefixLift 7291247
  have htrace : WordTrace (prefixWord ++ tailWord_7291247) baseStart_7291247 baseEnd_7291247 := by
    simpa [prefixWord, tailWord_7291247, baseEnd_7291247] using wordTrace_append hprefix tailTrace_7291247
  have hstable : (prefixWord ++ tailWord_7291247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291247).length < 2 ^ (prefixWord ++ tailWord_7291247).sum := by decide
  have hdescent : baseEnd_7291247 < baseStart_7291247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291261 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_7291261 : Nat := 118140960795 + 7291261 * 2 ^ 59
def prefixEnd_7291261 : Nat := 4983230072969 + 3 ^ 40 * 7291261 * 2
def baseEnd_7291261 : Nat := 3743921470381902641505607

theorem tailTrace_7291261 : CollatzResearch.WordTrace tailWord_7291261 prefixEnd_7291261 3743921470381902641505607 := by
  unfold tailWord_7291261
  simp only [CollatzResearch.WordTrace]
  refine ⟨265934136038014120084633637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177289424025342746723089091 265934136038014120084633637)
  ·
    refine ⟨49862650507127647515868807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265934136038014120084633637 49862650507127647515868807)
    ·
      refine ⟨74793975760691471273803211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49862650507127647515868807 74793975760691471273803211)
      ·
        refine ⟨112190963641037206910704817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74793975760691471273803211 112190963641037206910704817)
        ·
          refine ⟨84143222730777905183028613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112190963641037206910704817 84143222730777905183028613)
          ·
            refine ⟨15776854262020857221817865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84143222730777905183028613 15776854262020857221817865)
            ·
              refine ⟨11832640696515642916363399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15776854262020857221817865 11832640696515642916363399)
              ·
                refine ⟨17748961044773464374545099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11832640696515642916363399 17748961044773464374545099)
                ·
                  refine ⟨26623441567160196561817649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17748961044773464374545099 26623441567160196561817649)
                  ·
                    refine ⟨19967581175370147421363237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26623441567160196561817649 19967581175370147421363237)
                    ·
                      refine ⟨3743921470381902641505607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19967581175370147421363237 3743921470381902641505607)
                      ·
                        rfl

theorem cell23_7291261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_7291261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291261 prefixEnd_7291261 := by exact prefixLift 7291261
  have htrace : WordTrace (prefixWord ++ tailWord_7291261) baseStart_7291261 baseEnd_7291261 := by
    simpa [prefixWord, tailWord_7291261, baseEnd_7291261] using wordTrace_append hprefix tailTrace_7291261
  have hstable : (prefixWord ++ tailWord_7291261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291261).length < 2 ^ (prefixWord ++ tailWord_7291261).sum := by decide
  have hdescent : baseEnd_7291261 < baseStart_7291261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291265 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7291265 : Nat := 118140960795 + 7291265 * 2 ^ 59
def prefixEnd_7291265 : Nat := 4983230072969 + 3 ^ 40 * 7291265 * 2
def baseEnd_7291265 : Nat := 3743923524304520625855589

theorem tailTrace_7291265 : CollatzResearch.WordTrace tailWord_7291265 prefixEnd_7291265 3743923524304520625855589 := by
  unfold tailWord_7291265
  simp only [CollatzResearch.WordTrace]
  refine ⟨265934281929999628767779249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177289521286666419178519499 265934281929999628767779249)
  ·
    refine ⟨199450711447499721575834437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265934281929999628767779249 199450711447499721575834437)
    ·
      refine ⟨37397008396406197795468957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199450711447499721575834437 37397008396406197795468957)
      ·
        refine ⟨14023878148652324173300859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37397008396406197795468957 14023878148652324173300859)
        ·
          refine ⟨21035817222978486259951289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023878148652324173300859 21035817222978486259951289)
          ·
            refine ⟨15776862917233864694963467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21035817222978486259951289 15776862917233864694963467)
            ·
              refine ⟨23665294375850797042445201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776862917233864694963467 23665294375850797042445201)
              ·
                refine ⟨17748970781888097781833901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23665294375850797042445201 17748970781888097781833901)
                ·
                  refine ⟨6655864043208036668187713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17748970781888097781833901 6655864043208036668187713)
                  ·
                    refine ⟨4991898032406027501140785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655864043208036668187713 4991898032406027501140785)
                    ·
                      refine ⟨3743923524304520625855589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991898032406027501140785 3743923524304520625855589)
                      ·
                        rfl

theorem cell23_7291265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7291265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291265 prefixEnd_7291265 := by exact prefixLift 7291265
  have htrace : WordTrace (prefixWord ++ tailWord_7291265) baseStart_7291265 baseEnd_7291265 := by
    simpa [prefixWord, tailWord_7291265, baseEnd_7291265] using wordTrace_append hprefix tailTrace_7291265
  have hstable : (prefixWord ++ tailWord_7291265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291265).length < 2 ^ (prefixWord ++ tailWord_7291265).sum := by decide
  have hdescent : baseEnd_7291265 < baseStart_7291265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291298 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7291298 : Nat := 118140960795 + 7291298 * 2 ^ 59
def prefixEnd_7291298 : Nat := 4983230072969 + 3 ^ 40 * 7291298 * 2
def baseEnd_7291298 : Nat := 3743940469166118996742937

theorem tailTrace_7291298 : CollatzResearch.WordTrace tailWord_7291298 prefixEnd_7291298 3743940469166118996742937 := by
  unfold tailWord_7291298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66483871384720018850932637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177290323692586716935820365 66483871384720018850932637)
  ·
    refine ⟨24931451769270007069099739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66483871384720018850932637 24931451769270007069099739)
    ·
      refine ⟨37397177653905010603649609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24931451769270007069099739 37397177653905010603649609)
      ·
        refine ⟨28047883240428757952737207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37397177653905010603649609 28047883240428757952737207)
        ·
          refine ⟨42071824860643136929105811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047883240428757952737207 42071824860643136929105811)
          ·
            refine ⟨63107737290964705393658717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42071824860643136929105811 63107737290964705393658717)
            ·
              refine ⟨23665401484111764522622019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63107737290964705393658717 23665401484111764522622019)
              ·
                refine ⟨35498102226167646783933029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23665401484111764522622019 35498102226167646783933029)
                ·
                  refine ⟨6655894167406433771987443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35498102226167646783933029 6655894167406433771987443)
                  ·
                    refine ⟨9983841251109650657981165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6655894167406433771987443 9983841251109650657981165)
                    ·
                      refine ⟨3743940469166118996742937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9983841251109650657981165 3743940469166118996742937)
                      ·
                        rfl

theorem cell23_7291298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7291298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291298 prefixEnd_7291298 := by exact prefixLift 7291298
  have htrace : WordTrace (prefixWord ++ tailWord_7291298) baseStart_7291298 baseEnd_7291298 := by
    simpa [prefixWord, tailWord_7291298, baseEnd_7291298] using wordTrace_append hprefix tailTrace_7291298
  have hstable : (prefixWord ++ tailWord_7291298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291298).length < 2 ^ (prefixWord ++ tailWord_7291298).sum := by decide
  have hdescent : baseEnd_7291298 < baseStart_7291298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291314 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_7291314 : Nat := 118140960795 + 7291314 * 2 ^ 59
def prefixEnd_7291314 : Nat := 4983230072969 + 3 ^ 40 * 7291314 * 2
def baseEnd_7291314 : Nat := 1247982894952196978047621

theorem tailTrace_7291314 : CollatzResearch.WordTrace tailWord_7291314 prefixEnd_7291314 1247982894952196978047621 := by
  unfold tailWord_7291314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66484017276705527534078249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177290712737881406757541997 66484017276705527534078249)
  ·
    refine ⟨49863012957529145650558687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66484017276705527534078249 49863012957529145650558687)
    ·
      refine ⟨74794519436293718475838031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49863012957529145650558687 74794519436293718475838031)
      ·
        refine ⟨112191779154440577713757047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74794519436293718475838031 112191779154440577713757047)
        ·
          refine ⟨168287668731660866570635571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112191779154440577713757047 168287668731660866570635571)
          ·
            refine ⟨252431503097491299855953357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168287668731660866570635571 252431503097491299855953357)
            ·
              refine ⟨94661813661559237445982509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252431503097491299855953357 94661813661559237445982509)
              ·
                refine ⟨35498180123084714042243441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94661813661559237445982509 35498180123084714042243441)
                ·
                  refine ⟨26623635092313535531682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35498180123084714042243441 26623635092313535531682581)
                  ·
                    refine ⟨1247982894952196978047621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26623635092313535531682581 1247982894952196978047621)
                    ·
                      rfl

theorem cell23_7291314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_7291314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291314 prefixEnd_7291314 := by exact prefixLift 7291314
  have htrace : WordTrace (prefixWord ++ tailWord_7291314) baseStart_7291314 baseEnd_7291314 := by
    simpa [prefixWord, tailWord_7291314, baseEnd_7291314] using wordTrace_append hprefix tailTrace_7291314
  have hstable : (prefixWord ++ tailWord_7291314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291314).length < 2 ^ (prefixWord ++ tailWord_7291314).sum := by decide
  have hdescent : baseEnd_7291314 < baseStart_7291314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291325 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_7291325 : Nat := 118140960795 + 7291325 * 2 ^ 59
def prefixEnd_7291325 : Nat := 4983230072969 + 3 ^ 40 * 7291325 * 2
def baseEnd_7291325 : Nat := 3743954333143790391105313

theorem tailTrace_7291325 : CollatzResearch.WordTrace tailWord_7291325 prefixEnd_7291325 3743954333143790391105313 := by
  unfold tailWord_7291325
  simp only [CollatzResearch.WordTrace]
  refine ⟨265936470309782259014963429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177290980206521506009975619 265936470309782259014963429)
  ·
    refine ⟨49863088183084173565305643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265936470309782259014963429 49863088183084173565305643)
    ·
      refine ⟨74794632274626260347958465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49863088183084173565305643 74794632274626260347958465)
      ·
        refine ⟨56095974205969695260968849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74794632274626260347958465 56095974205969695260968849)
        ·
          refine ⟨42071980654477271445726637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56095974205969695260968849 42071980654477271445726637)
          ·
            refine ⟨15776992745428976792147489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42071980654477271445726637 15776992745428976792147489)
            ·
              refine ⟨11832744559071732594110617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15776992745428976792147489 11832744559071732594110617)
              ·
                refine ⟨8874558419303799445582963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832744559071732594110617 8874558419303799445582963)
                ·
                  refine ⟨13311837628955699168374445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874558419303799445582963 13311837628955699168374445)
                  ·
                    refine ⟨4991939110858387188140417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13311837628955699168374445 4991939110858387188140417)
                    ·
                      refine ⟨3743954333143790391105313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991939110858387188140417 3743954333143790391105313)
                      ·
                        rfl

theorem cell23_7291325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_7291325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291325 prefixEnd_7291325 := by exact prefixLift 7291325
  have htrace : WordTrace (prefixWord ++ tailWord_7291325) baseStart_7291325 baseEnd_7291325 := by
    simpa [prefixWord, tailWord_7291325, baseEnd_7291325] using wordTrace_append hprefix tailTrace_7291325
  have hstable : (prefixWord ++ tailWord_7291325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291325).length < 2 ^ (prefixWord ++ tailWord_7291325).sum := by decide
  have hdescent : baseEnd_7291325 < baseStart_7291325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291338 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_7291338 : Nat := 118140960795 + 7291338 * 2 ^ 59
def prefixEnd_7291338 : Nat := 4983230072969 + 3 ^ 40 * 7291338 * 2
def baseEnd_7291338 : Nat := 3743961008392298840242753

theorem tailTrace_7291338 : CollatzResearch.WordTrace tailWord_7291338 prefixEnd_7291338 3743961008392298840242753 := by
  unfold tailWord_7291338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66484236114683790558796667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177291296305823441490124445 66484236114683790558796667)
  ·
    refine ⟨99726354172025685838195001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66484236114683790558796667 99726354172025685838195001)
    ·
      refine ⟨74794765629019264378646251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99726354172025685838195001 74794765629019264378646251)
      ·
        refine ⟨112192148443528896567969377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74794765629019264378646251 112192148443528896567969377)
        ·
          refine ⟨84144111332646672425977033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112192148443528896567969377 84144111332646672425977033)
          ·
            refine ⟨63108083499485004319482775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84144111332646672425977033 63108083499485004319482775)
            ·
              refine ⟨94662125249227506479224163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63108083499485004319482775 94662125249227506479224163)
              ·
                refine ⟨141993187873841259718836245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94662125249227506479224163 141993187873841259718836245)
                ·
                  refine ⟨6655930681586309049320449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141993187873841259718836245 6655930681586309049320449)
                  ·
                    refine ⟨4991948011189731786990337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655930681586309049320449 4991948011189731786990337)
                    ·
                      refine ⟨3743961008392298840242753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4991948011189731786990337 3743961008392298840242753)
                      ·
                        rfl

theorem cell23_7291338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_7291338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291338 prefixEnd_7291338 := by exact prefixLift 7291338
  have htrace : WordTrace (prefixWord ++ tailWord_7291338) baseStart_7291338 baseEnd_7291338 := by
    simpa [prefixWord, tailWord_7291338, baseEnd_7291338] using wordTrace_append hprefix tailTrace_7291338
  have hstable : (prefixWord ++ tailWord_7291338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291338).length < 2 ^ (prefixWord ++ tailWord_7291338).sum := by decide
  have hdescent : baseEnd_7291338 < baseStart_7291338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291354 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_7291354 : Nat := 118140960795 + 7291354 * 2 ^ 59
def prefixEnd_7291354 : Nat := 4983230072969 + 3 ^ 40 * 7291354 * 2
def baseEnd_7291354 : Nat := 3743969224082770777642679

theorem tailTrace_7291354 : CollatzResearch.WordTrace tailWord_7291354 prefixEnd_7291354 3743969224082770777642679 := by
  unfold tailWord_7291354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66484382006669299241942279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177291685351118131311846077 66484382006669299241942279)
  ·
    refine ⟨99726573010003948862913419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66484382006669299241942279 99726573010003948862913419)
    ·
      refine ⟨149589859515005923294370129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99726573010003948862913419 149589859515005923294370129)
      ·
        refine ⟨112192394636254442470777597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149589859515005923294370129 112192394636254442470777597)
        ·
          refine ⟨42072147988595415926541599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112192394636254442470777597 42072147988595415926541599)
          ·
            refine ⟨63108221982893123889812399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42072147988595415926541599 63108221982893123889812399)
            ·
              refine ⟨94662332974339685834718599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63108221982893123889812399 94662332974339685834718599)
              ·
                refine ⟨141993499461509528752077899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94662332974339685834718599 141993499461509528752077899)
                ·
                  refine ⟨212990249192264293128116849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141993499461509528752077899 212990249192264293128116849)
                  ·
                    refine ⟨159742686894198219846087637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212990249192264293128116849 159742686894198219846087637)
                    ·
                      refine ⟨3743969224082770777642679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159742686894198219846087637 3743969224082770777642679)
                      ·
                        rfl

theorem cell23_7291354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_7291354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291354 prefixEnd_7291354 := by exact prefixLift 7291354
  have htrace : WordTrace (prefixWord ++ tailWord_7291354) baseStart_7291354 baseEnd_7291354 := by
    simpa [prefixWord, tailWord_7291354, baseEnd_7291354] using wordTrace_append hprefix tailTrace_7291354
  have hstable : (prefixWord ++ tailWord_7291354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291354).length < 2 ^ (prefixWord ++ tailWord_7291354).sum := by decide
  have hdescent : baseEnd_7291354 < baseStart_7291354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291384 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_7291384 : Nat := 118140960795 + 7291384 * 2 ^ 59
def prefixEnd_7291384 : Nat := 4983230072969 + 3 ^ 40 * 7291384 * 2
def baseEnd_7291384 : Nat := 3743984628502405660267541

theorem tailTrace_7291384 : CollatzResearch.WordTrace tailWord_7291384 prefixEnd_7291384 3743984628502405660267541 := by
  unfold tailWord_7291384
  simp only [CollatzResearch.WordTrace]
  refine ⟨132969311108284256045680603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177292414811045674727574137 132969311108284256045680603)
  ·
    refine ⟨199453966662426384068520905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132969311108284256045680603 199453966662426384068520905)
    ·
      refine ⟨149590474996819788051390679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199453966662426384068520905 149590474996819788051390679)
      ·
        refine ⟨224385712495229682077086019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149590474996819788051390679 224385712495229682077086019)
        ·
          refine ⟨336578568742844523115629029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224385712495229682077086019 336578568742844523115629029)
          ·
            refine ⟨63108481639283348084180443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336578568742844523115629029 63108481639283348084180443)
            ·
              refine ⟨94662722458925022126270665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63108481639283348084180443 94662722458925022126270665)
              ·
                refine ⟨70997041844193766594702999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94662722458925022126270665 70997041844193766594702999)
                ·
                  refine ⟨106495562766290649892054499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70997041844193766594702999 106495562766290649892054499)
                  ·
                    refine ⟨159743344149435974838081749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106495562766290649892054499 159743344149435974838081749)
                    ·
                      refine ⟨3743984628502405660267541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159743344149435974838081749 3743984628502405660267541)
                      ·
                        rfl

theorem cell23_7291384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_7291384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291384 prefixEnd_7291384 := by exact prefixLift 7291384
  have htrace : WordTrace (prefixWord ++ tailWord_7291384) baseStart_7291384 baseEnd_7291384 := by
    simpa [prefixWord, tailWord_7291384, baseEnd_7291384] using wordTrace_append hprefix tailTrace_7291384
  have hstable : (prefixWord ++ tailWord_7291384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291384).length < 2 ^ (prefixWord ++ tailWord_7291384).sum := by decide
  have hdescent : baseEnd_7291384 < baseStart_7291384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291391 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 2, 5]
def baseStart_7291391 : Nat := 118140960795 + 7291391 * 2 ^ 59
def prefixEnd_7291391 : Nat := 4983230072969 + 3 ^ 40 * 7291391 * 2
def baseEnd_7291391 : Nat := 1247996074288995710960003

theorem tailTrace_7291391 : CollatzResearch.WordTrace tailWord_7291391 prefixEnd_7291391 1247996074288995710960003 := by
  unfold tailWord_7291391
  simp only [CollatzResearch.WordTrace]
  refine ⟨265938877527543152286866027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177292585018362101524577351 265938877527543152286866027)
  ·
    refine ⟨398908316291314728430299041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265938877527543152286866027 398908316291314728430299041)
    ·
      refine ⟨299181237218486046322724281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398908316291314728430299041 299181237218486046322724281)
      ·
        refine ⟨224385927913864534742043211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299181237218486046322724281 224385927913864534742043211)
        ·
          refine ⟨336578891870796802113064817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224385927913864534742043211 336578891870796802113064817)
          ·
            refine ⟨252434168903097601584798613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336578891870796802113064817 252434168903097601584798613)
            ·
              refine ⟨11832851667332700074287435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252434168903097601584798613 11832851667332700074287435)
              ·
                refine ⟨17749277500999050111431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11832851667332700074287435 17749277500999050111431153)
                ·
                  refine ⟨13311958125749287583573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17749277500999050111431153 13311958125749287583573365)
                  ·
                    refine ⟨1247996074288995710960003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13311958125749287583573365 1247996074288995710960003)
                    ·
                      rfl

theorem cell23_7291391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_7291391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291391 prefixEnd_7291391 := by exact prefixLift 7291391
  have htrace : WordTrace (prefixWord ++ tailWord_7291391) baseStart_7291391 baseEnd_7291391 := by
    simpa [prefixWord, tailWord_7291391, baseEnd_7291391] using wordTrace_append hprefix tailTrace_7291391
  have hstable : (prefixWord ++ tailWord_7291391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291391).length < 2 ^ (prefixWord ++ tailWord_7291391).sum := by decide
  have hdescent : baseEnd_7291391 < baseStart_7291391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291411 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4]
def baseStart_7291411 : Nat := 118140960795 + 7291411 * 2 ^ 59
def prefixEnd_7291411 : Nat := 4983230072969 + 3 ^ 40 * 7291411 * 2
def baseEnd_7291411 : Nat := 3743998492480077054629917

theorem tailTrace_7291411 : CollatzResearch.WordTrace tailWord_7291411 prefixEnd_7291411 3743998492480077054629917 := by
  unfold tailWord_7291411
  simp only [CollatzResearch.WordTrace]
  refine ⟨265939606987470695702594087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177293071324980463801729391 265939606987470695702594087)
  ·
    refine ⟨398909410481206043553891131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265939606987470695702594087 398909410481206043553891131)
    ·
      refine ⟨598364115721809065330836697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398909410481206043553891131 598364115721809065330836697)
      ·
        refine ⟨448773086791356798998127523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598364115721809065330836697 448773086791356798998127523)
        ·
          refine ⟨673159630187035198497191285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448773086791356798998127523 673159630187035198497191285)
          ·
            refine ⟨63108715330034549859111683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 673159630187035198497191285 63108715330034549859111683)
            ·
              refine ⟨94663072995051824788667525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63108715330034549859111683 94663072995051824788667525)
              ·
                refine ⟨17749326186572217147875161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94663072995051824788667525 17749326186572217147875161)
                ·
                  refine ⟨13311994639929162860906371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17749326186572217147875161 13311994639929162860906371)
                  ·
                    refine ⟨19967991959893744291359557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13311994639929162860906371 19967991959893744291359557)
                    ·
                      refine ⟨3743998492480077054629917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19967991959893744291359557 3743998492480077054629917)
                      ·
                        rfl

theorem cell23_7291411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_7291411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291411 prefixEnd_7291411 := by exact prefixLift 7291411
  have htrace : WordTrace (prefixWord ++ tailWord_7291411) baseStart_7291411 baseEnd_7291411 := by
    simpa [prefixWord, tailWord_7291411, baseEnd_7291411] using wordTrace_append hprefix tailTrace_7291411
  have hstable : (prefixWord ++ tailWord_7291411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291411).length < 2 ^ (prefixWord ++ tailWord_7291411).sum := by decide
  have hdescent : baseEnd_7291411 < baseStart_7291411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291412 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 5]
def baseStart_7291412 : Nat := 118140960795 + 7291412 * 2 ^ 59
def prefixEnd_7291412 : Nat := 4983230072969 + 3 ^ 40 * 7291412 * 2
def baseEnd_7291412 : Nat := 415999889551192394524157

theorem tailTrace_7291412 : CollatzResearch.WordTrace tailWord_7291412 prefixEnd_7291412 415999889551192394524157 := by
  unfold tailWord_7291412
  simp only [CollatzResearch.WordTrace]
  refine ⟨132969821730233536436690245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177293095640311381915586993 132969821730233536436690245)
  ·
    refine ⟨24931841574418788081879421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132969821730233536436690245 24931841574418788081879421)
    ·
      refine ⟨9349440590407045530704783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24931841574418788081879421 9349440590407045530704783)
      ·
        refine ⟨14024160885610568296057175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349440590407045530704783 14024160885610568296057175)
        ·
          refine ⟨21036241328415852444085763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024160885610568296057175 21036241328415852444085763)
          ·
            refine ⟨31554361992623778666128645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036241328415852444085763 31554361992623778666128645)
            ·
              refine ⟨5916442873616958499899121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31554361992623778666128645 5916442873616958499899121)
              ·
                refine ⟨4437332155212718874924341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916442873616958499899121 4437332155212718874924341)
                ·
                  refine ⟨415999889551192394524157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437332155212718874924341 415999889551192394524157)
                  ·
                    rfl

theorem cell23_7291412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_7291412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291412 prefixEnd_7291412 := by exact prefixLift 7291412
  have htrace : WordTrace (prefixWord ++ tailWord_7291412) baseStart_7291412 baseEnd_7291412 := by
    simpa [prefixWord, tailWord_7291412, baseEnd_7291412] using wordTrace_append hprefix tailTrace_7291412
  have hstable : (prefixWord ++ tailWord_7291412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291412).length < 2 ^ (prefixWord ++ tailWord_7291412).sum := by decide
  have hdescent : baseEnd_7291412 < baseStart_7291412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291455 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 1, 4]
def baseStart_7291455 : Nat := 118140960795 + 7291455 * 2 ^ 59
def prefixEnd_7291455 : Nat := 4983230072969 + 3 ^ 40 * 7291455 * 2
def baseEnd_7291455 : Nat := 1248007028542958294159905

theorem tailTrace_7291455 : CollatzResearch.WordTrace tailWord_7291455 prefixEnd_7291455 1248007028542958294159905 := by
  unfold tailWord_7291455
  simp only [CollatzResearch.WordTrace]
  refine ⟨265941211799311291217195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177294141199540860811463879 265941211799311291217195819)
  ·
    refine ⟨398911817698966936825793729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265941211799311291217195819 398911817698966936825793729)
    ·
      refine ⟨299183863274225202619345297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398911817698966936825793729 299183863274225202619345297)
      ·
        refine ⟨224387897455668901964508973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299183863274225202619345297 224387897455668901964508973)
        ·
          refine ⟨84145461545875838236690865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224387897455668901964508973 84145461545875838236690865)
          ·
            refine ⟨63109096159406878677518149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84145461545875838236690865 63109096159406878677518149)
            ·
              refine ⟨11832955529888789752034653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63109096159406878677518149 11832955529888789752034653)
              ·
                refine ⟨4437358323708296157012995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11832955529888789752034653 4437358323708296157012995)
                ·
                  refine ⟨6656037485562444235519493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437358323708296157012995 6656037485562444235519493)
                  ·
                    refine ⟨1248007028542958294159905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656037485562444235519493 1248007028542958294159905)
                    ·
                      rfl

theorem cell23_7291455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_7291455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291455 prefixEnd_7291455 := by exact prefixLift 7291455
  have htrace : WordTrace (prefixWord ++ tailWord_7291455) baseStart_7291455 baseEnd_7291455 := by
    simpa [prefixWord, tailWord_7291455, baseEnd_7291455] using wordTrace_append hprefix tailTrace_7291455
  have hstable : (prefixWord ++ tailWord_7291455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291455).length < 2 ^ (prefixWord ++ tailWord_7291455).sum := by decide
  have hdescent : baseEnd_7291455 < baseStart_7291455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291462 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7291462 : Nat := 118140960795 + 7291462 * 2 ^ 59
def prefixEnd_7291462 : Nat := 4983230072969 + 3 ^ 40 * 7291462 * 2
def baseEnd_7291462 : Nat := 3744024679993456355092183

theorem tailTrace_7291462 : CollatzResearch.WordTrace tailWord_7291462 prefixEnd_7291462 3744024679993456355092183 := by
  unfold tailWord_7291462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310670847196435356646895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177294311406857287608467093 8310670847196435356646895)
  ·
    refine ⟨12466006270794653034970343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8310670847196435356646895 12466006270794653034970343)
    ·
      refine ⟨18699009406191979552455515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466006270794653034970343 18699009406191979552455515)
      ·
        refine ⟨28048514109287969328683273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18699009406191979552455515 28048514109287969328683273)
        ·
          refine ⟨21036385581965976996512455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28048514109287969328683273 21036385581965976996512455)
          ·
            refine ⟨31554578372948965494768683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036385581965976996512455 31554578372948965494768683)
            ·
              refine ⟨47331867559423448242153025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31554578372948965494768683 47331867559423448242153025)
              ·
                refine ⟨35498900669567586181614769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47331867559423448242153025 35498900669567586181614769)
                ·
                  refine ⟨26624175502175689636211077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35498900669567586181614769 26624175502175689636211077)
                  ·
                    refine ⟨4992032906657941806789577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26624175502175689636211077 4992032906657941806789577)
                    ·
                      refine ⟨3744024679993456355092183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992032906657941806789577 3744024679993456355092183)
                      ·
                        rfl

theorem cell23_7291462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7291462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291462 prefixEnd_7291462 := by exact prefixLift 7291462
  have htrace : WordTrace (prefixWord ++ tailWord_7291462) baseStart_7291462 baseEnd_7291462 := by
    simpa [prefixWord, tailWord_7291462, baseEnd_7291462] using wordTrace_append hprefix tailTrace_7291462
  have hstable : (prefixWord ++ tailWord_7291462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291462).length < 2 ^ (prefixWord ++ tailWord_7291462).sum := by decide
  have hdescent : baseEnd_7291462 < baseStart_7291462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291488 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2]
def baseStart_7291488 : Nat := 118140960795 + 7291488 * 2 ^ 59
def prefixEnd_7291488 : Nat := 4983230072969 + 3 ^ 40 * 7291488 * 2
def baseEnd_7291488 : Nat := 3744038030490473253367063

theorem tailTrace_7291488 : CollatzResearch.WordTrace tailWord_7291488 prefixEnd_7291488 3744038030490473253367063 := by
  unfold tailWord_7291488
  simp only [CollatzResearch.WordTrace]
  refine ⟨132971207704095868926573559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177294943605461158568764745 132971207704095868926573559)
  ·
    refine ⟨199456811556143803389860339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132971207704095868926573559 199456811556143803389860339)
    ·
      refine ⟨299185217334215705084790509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199456811556143803389860339 299185217334215705084790509)
      ·
        refine ⟨112194456500330889406796441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299185217334215705084790509 112194456500330889406796441)
        ·
          refine ⟨84145842375248167055097331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112194456500330889406796441 84145842375248167055097331)
          ·
            refine ⟨126218763562872250582645997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84145842375248167055097331 126218763562872250582645997)
            ·
              refine ⟨47332036336077093968492249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126218763562872250582645997 47332036336077093968492249)
              ·
                refine ⟨35499027252057820476369187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47332036336077093968492249 35499027252057820476369187)
                ·
                  refine ⟨53248540878086730714553781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35499027252057820476369187 53248540878086730714553781)
                  ·
                    refine ⟨4992050707320631004489417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53248540878086730714553781 4992050707320631004489417)
                    ·
                      refine ⟨3744038030490473253367063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992050707320631004489417 3744038030490473253367063)
                      ·
                        rfl

theorem cell23_7291488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_7291488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291488 prefixEnd_7291488 := by exact prefixLift 7291488
  have htrace : WordTrace (prefixWord ++ tailWord_7291488) baseStart_7291488 baseEnd_7291488 := by
    simpa [prefixWord, tailWord_7291488, baseEnd_7291488] using wordTrace_append hprefix tailTrace_7291488
  have hstable : (prefixWord ++ tailWord_7291488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291488).length < 2 ^ (prefixWord ++ tailWord_7291488).sum := by decide
  have hdescent : baseEnd_7291488 < baseStart_7291488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291511 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 6]
def baseStart_7291511 : Nat := 118140960795 + 7291511 * 2 ^ 59
def prefixEnd_7291511 : Nat := 4983230072969 + 3 ^ 40 * 7291511 * 2
def baseEnd_7291511 : Nat := 1248016613515175554459819

theorem tailTrace_7291511 : CollatzResearch.WordTrace tailWord_7291511 prefixEnd_7291511 1248016613515175554459819 := by
  unfold tailWord_7291511
  simp only [CollatzResearch.WordTrace]
  refine ⟨265943254287108412781234387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177295502858072275187489591 265943254287108412781234387)
  ·
    refine ⟨398914881430662619171851581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265943254287108412781234387 398914881430662619171851581)
    ·
      refine ⟨149593080536498482189444343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398914881430662619171851581 149593080536498482189444343)
      ·
        refine ⟨224389620804747723284166515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149593080536498482189444343 224389620804747723284166515)
        ·
          refine ⟨336584431207121584926249773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224389620804747723284166515 336584431207121584926249773)
          ·
            refine ⟨126219161702670594347343665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336584431207121584926249773 126219161702670594347343665)
            ·
              refine ⟨94664371277002945760507749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126219161702670594347343665 94664371277002945760507749)
              ·
                refine ⟨17749569614438052330095203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94664371277002945760507749 17749569614438052330095203)
                ·
                  refine ⟨26624354421657078495142805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749569614438052330095203 26624354421657078495142805)
                  ·
                    refine ⟨1248016613515175554459819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26624354421657078495142805 1248016613515175554459819)
                    ·
                      rfl

theorem cell23_7291511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_7291511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291511 prefixEnd_7291511 := by exact prefixLift 7291511
  have htrace : WordTrace (prefixWord ++ tailWord_7291511) baseStart_7291511 baseEnd_7291511 := by
    simpa [prefixWord, tailWord_7291511, baseEnd_7291511] using wordTrace_append hprefix tailTrace_7291511
  have hstable : (prefixWord ++ tailWord_7291511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291511).length < 2 ^ (prefixWord ++ tailWord_7291511).sum := by decide
  have hdescent : baseEnd_7291511 < baseStart_7291511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291531 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_7291531 : Nat := 118140960795 + 7291531 * 2 ^ 59
def prefixEnd_7291531 : Nat := 4983230072969 + 3 ^ 40 * 7291531 * 2
def baseEnd_7291531 : Nat := 3744060110158616585129365

theorem tailTrace_7291531 : CollatzResearch.WordTrace tailWord_7291531 prefixEnd_7291531 3744060110158616585129365 := by
  unfold tailWord_7291531
  simp only [CollatzResearch.WordTrace]
  refine ⟨265943983747035956196962447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177295989164690637464641631 265943983747035956196962447)
  ·
    refine ⟨398915975620553934295443671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265943983747035956196962447 398915975620553934295443671)
    ·
      refine ⟨598373963430830901443165507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398915975620553934295443671 598373963430830901443165507)
      ·
        refine ⟨897560945146246352164748261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598373963430830901443165507 897560945146246352164748261)
        ·
          refine ⟨168292677214921191030890299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 897560945146246352164748261 168292677214921191030890299)
          ·
            refine ⟨252439015822381786546335449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168292677214921191030890299 252439015822381786546335449)
            ·
              refine ⟨189329261866786339909751587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252439015822381786546335449 189329261866786339909751587)
              ·
                refine ⟨283993892800179509864627381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189329261866786339909751587 283993892800179509864627381)
                ·
                  refine ⟨26624427450016829049808817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283993892800179509864627381 26624427450016829049808817)
                  ·
                    refine ⟨19968320587512621787356613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26624427450016829049808817 19968320587512621787356613)
                    ·
                      refine ⟨3744060110158616585129365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968320587512621787356613 3744060110158616585129365)
                      ·
                        rfl

theorem cell23_7291531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_7291531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291531 prefixEnd_7291531 := by exact prefixLift 7291531
  have htrace : WordTrace (prefixWord ++ tailWord_7291531) baseStart_7291531 baseEnd_7291531 := by
    simpa [prefixWord, tailWord_7291531, baseEnd_7291531] using wordTrace_append hprefix tailTrace_7291531
  have hstable : (prefixWord ++ tailWord_7291531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291531).length < 2 ^ (prefixWord ++ tailWord_7291531).sum := by decide
  have hdescent : baseEnd_7291531 < baseStart_7291531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291548 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7291548 : Nat := 118140960795 + 7291548 * 2 ^ 59
def prefixEnd_7291548 : Nat := 4983230072969 + 3 ^ 40 * 7291548 * 2
def baseEnd_7291548 : Nat := 3744068839329743018616787

theorem tailTrace_7291548 : CollatzResearch.WordTrace tailWord_7291548 prefixEnd_7291548 3744068839329743018616787 := by
  unfold tailWord_7291548
  simp only [CollatzResearch.WordTrace]
  refine ⟨132972301893987184050165649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177296402525316245400220865 132972301893987184050165649)
  ·
    refine ⟨99729226420490388037624237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132972301893987184050165649 99729226420490388037624237)
    ·
      refine ⟨37398459907683895514109089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99729226420490388037624237 37398459907683895514109089)
      ·
        refine ⟨28048844930762921635581817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37398459907683895514109089 28048844930762921635581817)
        ·
          refine ⟨21036633698072191226686363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28048844930762921635581817 21036633698072191226686363)
          ·
            refine ⟨31554950547108286840029545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036633698072191226686363 31554950547108286840029545)
            ·
              refine ⟨23666212910331215130022159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31554950547108286840029545 23666212910331215130022159)
              ·
                refine ⟨35499319365496822695033239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23666212910331215130022159 35499319365496822695033239)
                ·
                  refine ⟨53248979048245234042549859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35499319365496822695033239 53248979048245234042549859)
                  ·
                    refine ⟨79873468572367851063824789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53248979048245234042549859 79873468572367851063824789)
                    ·
                      refine ⟨3744068839329743018616787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79873468572367851063824789 3744068839329743018616787)
                      ·
                        rfl

theorem cell23_7291548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7291548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291548 prefixEnd_7291548 := by exact prefixLift 7291548
  have htrace : WordTrace (prefixWord ++ tailWord_7291548) baseStart_7291548 baseEnd_7291548 := by
    simpa [prefixWord, tailWord_7291548, baseEnd_7291548] using wordTrace_append hprefix tailTrace_7291548
  have hstable : (prefixWord ++ tailWord_7291548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291548).length < 2 ^ (prefixWord ++ tailWord_7291548).sum := by decide
  have hdescent : baseEnd_7291548 < baseStart_7291548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291552 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_7291552 : Nat := 118140960795 + 7291552 * 2 ^ 59
def prefixEnd_7291552 : Nat := 4983230072969 + 3 ^ 40 * 7291552 * 2
def baseEnd_7291552 : Nat := 3744070893252361002966769

theorem tailTrace_7291552 : CollatzResearch.WordTrace tailWord_7291552 prefixEnd_7291552 3744070893252361002966769 := by
  unfold tailWord_7291552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132972374839979938391738455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177296499786639917855651273 132972374839979938391738455)
  ·
    refine ⟨199458562259969907587607683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132972374839979938391738455 199458562259969907587607683)
    ·
      refine ⟨299187843389954861381411525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199458562259969907587607683 299187843389954861381411525)
      ·
        refine ⟨56097720635616536509014661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299187843389954861381411525 56097720635616536509014661)
        ·
          refine ⟨10518322619178100595440249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56097720635616536509014661 10518322619178100595440249)
          ·
            refine ⟨7888741964383575446580187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10518322619178100595440249 7888741964383575446580187)
            ·
              refine ⟨11833112946575363169870281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888741964383575446580187 11833112946575363169870281)
              ·
                refine ⟨8874834709931522377402711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11833112946575363169870281 8874834709931522377402711)
                ·
                  refine ⟨13312252064897283566104067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874834709931522377402711 13312252064897283566104067)
                  ·
                    refine ⟨19968378097345925349156101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13312252064897283566104067 19968378097345925349156101)
                    ·
                      refine ⟨3744070893252361002966769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968378097345925349156101 3744070893252361002966769)
                      ·
                        rfl

theorem cell23_7291552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_7291552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291552 prefixEnd_7291552 := by exact prefixLift 7291552
  have htrace : WordTrace (prefixWord ++ tailWord_7291552) baseStart_7291552 baseEnd_7291552 := by
    simpa [prefixWord, tailWord_7291552, baseEnd_7291552] using wordTrace_append hprefix tailTrace_7291552
  have hstable : (prefixWord ++ tailWord_7291552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291552).length < 2 ^ (prefixWord ++ tailWord_7291552).sum := by decide
  have hdescent : baseEnd_7291552 < baseStart_7291552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291562 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7291562 : Nat := 118140960795 + 7291562 * 2 ^ 59
def prefixEnd_7291562 : Nat := 4983230072969 + 3 ^ 40 * 7291562 * 2
def baseEnd_7291562 : Nat := 1248025342686301987947241

theorem tailTrace_7291562 : CollatzResearch.WordTrace tailWord_7291562 prefixEnd_7291562 1248025342686301987947241 := by
  unfold tailWord_7291562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66486278602480912122835235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177296742939949098994227293 66486278602480912122835235)
  ·
    refine ⟨99729417903721368184252853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66486278602480912122835235 99729417903721368184252853)
    ·
      refine ⟨9349632928473878267273705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99729417903721368184252853 9349632928473878267273705)
      ·
        refine ⟨7012224696355408700455279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9349632928473878267273705 7012224696355408700455279)
        ·
          refine ⟨10518337044533113050682919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012224696355408700455279 10518337044533113050682919)
          ·
            refine ⟨15777505566799669576024379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518337044533113050682919 15777505566799669576024379)
            ·
              refine ⟨23666258350199504364036569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15777505566799669576024379 23666258350199504364036569)
              ·
                refine ⟨17749693762649628273027427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23666258350199504364036569 17749693762649628273027427)
                ·
                  refine ⟨26624540643974442409541141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749693762649628273027427 26624540643974442409541141)
                  ·
                    refine ⟨1248025342686301987947241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26624540643974442409541141 1248025342686301987947241)
                    ·
                      rfl

theorem cell23_7291562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7291562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291562 prefixEnd_7291562 := by exact prefixLift 7291562
  have htrace : WordTrace (prefixWord ++ tailWord_7291562) baseStart_7291562 baseEnd_7291562 := by
    simpa [prefixWord, tailWord_7291562, baseEnd_7291562] using wordTrace_append hprefix tailTrace_7291562
  have hstable : (prefixWord ++ tailWord_7291562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291562).length < 2 ^ (prefixWord ++ tailWord_7291562).sum := by decide
  have hdescent : baseEnd_7291562 < baseStart_7291562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291565 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7291565 : Nat := 118140960795 + 7291565 * 2 ^ 59
def prefixEnd_7291565 : Nat := 4983230072969 + 3 ^ 40 * 7291565 * 2
def baseEnd_7291565 : Nat := 3744077568500869452104209

theorem tailTrace_7291565 : CollatzResearch.WordTrace tailWord_7291565 prefixEnd_7291565 3744077568500869452104209 := by
  unfold tailWord_7291565
  simp only [CollatzResearch.WordTrace]
  refine ⟨265945223828912780003700149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177296815885941853335800099 265945223828912780003700149)
  ·
    refine ⟨24932364733960573125346889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265945223828912780003700149 24932364733960573125346889)
    ·
      refine ⟨18699273550470429844010167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24932364733960573125346889 18699273550470429844010167)
      ·
        refine ⟨28048910325705644766015251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18699273550470429844010167 28048910325705644766015251)
        ·
          refine ⟨42073365488558467149022877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28048910325705644766015251 42073365488558467149022877)
          ·
            refine ⟨15777512058209425180883579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42073365488558467149022877 15777512058209425180883579)
            ·
              refine ⟨23666268087314137771325369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15777512058209425180883579 23666268087314137771325369)
              ·
                refine ⟨17749701065485603328494027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23666268087314137771325369 17749701065485603328494027)
                ·
                  refine ⟨26624551598228404992741041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749701065485603328494027 26624551598228404992741041)
                  ·
                    refine ⟨19968413698671303744555781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26624551598228404992741041 19968413698671303744555781)
                    ·
                      refine ⟨3744077568500869452104209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968413698671303744555781 3744077568500869452104209)
                      ·
                        rfl

theorem cell23_7291565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7291565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291565 prefixEnd_7291565 := by exact prefixLift 7291565
  have htrace : WordTrace (prefixWord ++ tailWord_7291565) baseStart_7291565 baseEnd_7291565 := by
    simpa [prefixWord, tailWord_7291565, baseEnd_7291565] using wordTrace_append hprefix tailTrace_7291565
  have hstable : (prefixWord ++ tailWord_7291565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291565).length < 2 ^ (prefixWord ++ tailWord_7291565).sum := by decide
  have hdescent : baseEnd_7291565 < baseStart_7291565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291569 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7291569 : Nat := 118140960795 + 7291569 * 2 ^ 59
def prefixEnd_7291569 : Nat := 4983230072969 + 3 ^ 40 * 7291569 * 2
def baseEnd_7291569 : Nat := 3744079622423487436454191

theorem tailTrace_7291569 : CollatzResearch.WordTrace tailWord_7291569 prefixEnd_7291569 3744079622423487436454191 := by
  unfold tailWord_7291569
  simp only [CollatzResearch.WordTrace]
  refine ⟨265945369720898288686845761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177296913147265525791230507 265945369720898288686845761)
  ·
    refine ⟨199459027290673716515134321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265945369720898288686845761 199459027290673716515134321)
    ·
      refine ⟨149594270468005287386350741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199459027290673716515134321 149594270468005287386350741)
      ·
        refine ⟨7012231428187747846235191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149594270468005287386350741 7012231428187747846235191)
        ·
          refine ⟨10518347142281621769352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012231428187747846235191 10518347142281621769352787)
          ·
            refine ⟨15777520713422432654029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518347142281621769352787 15777520713422432654029181)
            ·
              refine ⟨5916570267533412245260943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15777520713422432654029181 5916570267533412245260943)
              ·
                refine ⟨8874855401300118367891415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916570267533412245260943 8874855401300118367891415)
                ·
                  refine ⟨13312283101950177551837123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874855401300118367891415 13312283101950177551837123)
                  ·
                    refine ⟨19968424652925266327755685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13312283101950177551837123 19968424652925266327755685)
                    ·
                      refine ⟨3744079622423487436454191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968424652925266327755685 3744079622423487436454191)
                      ·
                        rfl

theorem cell23_7291569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7291569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291569 prefixEnd_7291569 := by exact prefixLift 7291569
  have htrace : WordTrace (prefixWord ++ tailWord_7291569) baseStart_7291569 baseEnd_7291569 := by
    simpa [prefixWord, tailWord_7291569, baseEnd_7291569] using wordTrace_append hprefix tailTrace_7291569
  have hstable : (prefixWord ++ tailWord_7291569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291569).length < 2 ^ (prefixWord ++ tailWord_7291569).sum := by decide
  have hdescent : baseEnd_7291569 < baseStart_7291569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291588 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7291588 : Nat := 118140960795 + 7291588 * 2 ^ 59
def prefixEnd_7291588 : Nat := 4983230072969 + 3 ^ 40 * 7291588 * 2
def baseEnd_7291588 : Nat := 1248029792851974287372201

theorem tailTrace_7291588 : CollatzResearch.WordTrace tailWord_7291588 prefixEnd_7291588 1248029792851974287372201 := by
  unfold tailWord_7291588
  simp only [CollatzResearch.WordTrace]
  refine ⟨132973031353914727465893709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177297375138552969954524945 132973031353914727465893709)
  ·
    refine ⟨49864886757718022799710141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132973031353914727465893709 49864886757718022799710141)
    ·
      refine ⟨18699332534144258549891303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49864886757718022799710141 18699332534144258549891303)
      ·
        refine ⟨28048998801216387824836955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18699332534144258549891303 28048998801216387824836955)
        ·
          refine ⟨42073498201824581737255433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28048998801216387824836955 42073498201824581737255433)
          ·
            refine ⟨31555123651368436302941575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42073498201824581737255433 31555123651368436302941575)
            ·
              refine ⟨47332685477052654454412363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31555123651368436302941575 47332685477052654454412363)
              ·
                refine ⟨70999028215578981681618545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47332685477052654454412363 70999028215578981681618545)
                ·
                  refine ⟨53249271161684236261213909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70999028215578981681618545 53249271161684236261213909)
                  ·
                    refine ⟨1248029792851974287372201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53249271161684236261213909 1248029792851974287372201)
                    ·
                      rfl

theorem cell23_7291588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7291588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291588 prefixEnd_7291588 := by exact prefixLift 7291588
  have htrace : WordTrace (prefixWord ++ tailWord_7291588) baseStart_7291588 baseEnd_7291588 := by
    simpa [prefixWord, tailWord_7291588, baseEnd_7291588] using wordTrace_append hprefix tailTrace_7291588
  have hstable : (prefixWord ++ tailWord_7291588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291588).length < 2 ^ (prefixWord ++ tailWord_7291588).sum := by decide
  have hdescent : baseEnd_7291588 < baseStart_7291588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291602 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7291602 : Nat := 118140960795 + 7291602 * 2 ^ 59
def prefixEnd_7291602 : Nat := 4983230072969 + 3 ^ 40 * 7291602 * 2
def baseEnd_7291602 : Nat := 3744096567285085807341539

theorem tailTrace_7291602 : CollatzResearch.WordTrace tailWord_7291602 prefixEnd_7291602 3744096567285085807341539 := by
  unfold tailWord_7291602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66486643332444683830699265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177297715553185823548531373 66486643332444683830699265)
  ·
    refine ⟨49864982499333512873024449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66486643332444683830699265 49864982499333512873024449)
    ·
      refine ⟨37398736874500134654768337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49864982499333512873024449 37398736874500134654768337)
      ·
        refine ⟨28049052655875100991076253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37398736874500134654768337 28049052655875100991076253)
        ·
          refine ⟨10518394745953162871653595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28049052655875100991076253 10518394745953162871653595)
          ·
            refine ⟨15777592118929744307480393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518394745953162871653595 15777592118929744307480393)
            ·
              refine ⟨11833194089197308230610295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15777592118929744307480393 11833194089197308230610295)
              ·
                refine ⟨17749791133795962345915443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11833194089197308230610295 17749791133795962345915443)
                ·
                  refine ⟨26624686700693943518873165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749791133795962345915443 26624686700693943518873165)
                  ·
                    refine ⟨9984257512760228819577437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26624686700693943518873165 9984257512760228819577437)
                    ·
                      refine ⟨3744096567285085807341539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9984257512760228819577437 3744096567285085807341539)
                      ·
                        rfl

theorem cell23_7291602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7291602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291602 prefixEnd_7291602 := by exact prefixLift 7291602
  have htrace : WordTrace (prefixWord ++ tailWord_7291602) baseStart_7291602 baseEnd_7291602 := by
    simpa [prefixWord, tailWord_7291602, baseEnd_7291602] using wordTrace_append hprefix tailTrace_7291602
  have hstable : (prefixWord ++ tailWord_7291602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291602).length < 2 ^ (prefixWord ++ tailWord_7291602).sum := by decide
  have hdescent : baseEnd_7291602 < baseStart_7291602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291611 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_7291611 : Nat := 118140960795 + 7291611 * 2 ^ 59
def prefixEnd_7291611 : Nat := 4983230072969 + 3 ^ 40 * 7291611 * 2
def baseEnd_7291611 : Nat := 3744101188610976272128997

theorem tailTrace_7291611 : CollatzResearch.WordTrace tailWord_7291611 prefixEnd_7291611 3744101188610976272128997 := by
  unfold tailWord_7291611
  simp only [CollatzResearch.WordTrace]
  refine ⟨265946901586746129859874687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177297934391164086573249791 265946901586746129859874687)
  ·
    refine ⟨398920352380119194789812031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265946901586746129859874687 398920352380119194789812031)
    ·
      refine ⟨598380528570178792184718047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398920352380119194789812031 598380528570178792184718047)
      ·
        refine ⟨897570792855268188277077071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598380528570178792184718047 897570792855268188277077071)
        ·
          refine ⟨1346356189282902282415615607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897570792855268188277077071 1346356189282902282415615607)
          ·
            refine ⟨2019534283924353423623423411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346356189282902282415615607 2019534283924353423623423411)
            ·
              refine ⟨3029301425886530135435135117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019534283924353423623423411 3029301425886530135435135117)
              ·
                refine ⟨1135988034707448800788175669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029301425886530135435135117 1135988034707448800788175669)
                ·
                  refine ⟨106498878253823325073891469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135988034707448800788175669 106498878253823325073891469)
                  ·
                    refine ⟨39937079345183746902709301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106498878253823325073891469 39937079345183746902709301)
                    ·
                      refine ⟨3744101188610976272128997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39937079345183746902709301 3744101188610976272128997)
                      ·
                        rfl

theorem cell23_7291611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_7291611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291611 prefixEnd_7291611 := by exact prefixLift 7291611
  have htrace : WordTrace (prefixWord ++ tailWord_7291611) baseStart_7291611 baseEnd_7291611 := by
    simpa [prefixWord, tailWord_7291611, baseEnd_7291611] using wordTrace_append hprefix tailTrace_7291611
  have hstable : (prefixWord ++ tailWord_7291611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291611).length < 2 ^ (prefixWord ++ tailWord_7291611).sum := by decide
  have hdescent : baseEnd_7291611 < baseStart_7291611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291625 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 4, 2]
def baseStart_7291625 : Nat := 118140960795 + 7291625 * 2 ^ 59
def prefixEnd_7291625 : Nat := 4983230072969 + 3 ^ 40 * 7291625 * 2
def baseEnd_7291625 : Nat := 3744108377340139217353933

theorem tailTrace_7291625 : CollatzResearch.WordTrace tailWord_7291625 prefixEnd_7291625 3744108377340139217353933 := by
  unfold tailWord_7291625
  simp only [CollatzResearch.WordTrace]
  refine ⟨265947412208695410250884329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177298274805796940167256219 265947412208695410250884329)
  ·
    refine ⟨199460559156521557688163247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265947412208695410250884329 199460559156521557688163247)
    ·
      refine ⟨299190838734782336532244871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199460559156521557688163247 299190838734782336532244871)
      ·
        refine ⟨448786258102173504798367307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299190838734782336532244871 448786258102173504798367307)
        ·
          refine ⟨673179387153260257197550961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448786258102173504798367307 673179387153260257197550961)
          ·
            refine ⟨504884540364945192898163221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673179387153260257197550961 504884540364945192898163221)
            ·
              refine ⟨23666462829606805917101401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 504884540364945192898163221 23666462829606805917101401)
              ·
                refine ⟨17749847122205104437826051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23666462829606805917101401 17749847122205104437826051)
                ·
                  refine ⟨26624770683307656656739077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749847122205104437826051 26624770683307656656739077)
                  ·
                    refine ⟨4992144503120185623138577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26624770683307656656739077 4992144503120185623138577)
                    ·
                      refine ⟨3744108377340139217353933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992144503120185623138577 3744108377340139217353933)
                      ·
                        rfl

theorem cell23_7291625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4, 2].length) (baseStart_7291625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291625 prefixEnd_7291625 := by exact prefixLift 7291625
  have htrace : WordTrace (prefixWord ++ tailWord_7291625) baseStart_7291625 baseEnd_7291625 := by
    simpa [prefixWord, tailWord_7291625, baseEnd_7291625] using wordTrace_append hprefix tailTrace_7291625
  have hstable : (prefixWord ++ tailWord_7291625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291625).length < 2 ^ (prefixWord ++ tailWord_7291625).sum := by decide
  have hdescent : baseEnd_7291625 < baseStart_7291625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291636 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7291636 : Nat := 118140960795 + 7291636 * 2 ^ 59
def prefixEnd_7291636 : Nat := 4983230072969 + 3 ^ 40 * 7291636 * 2
def baseEnd_7291636 : Nat := 3744114025627338674316383

theorem tailTrace_7291636 : CollatzResearch.WordTrace tailWord_7291636 prefixEnd_7291636 3744114025627338674316383 := by
  unfold tailWord_7291636
  simp only [CollatzResearch.WordTrace]
  refine ⟨132973906705827779564767381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177298542274437039419689841 132973906705827779564767381)
  ·
    refine ⟨6233151876835677167098471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132973906705827779564767381 6233151876835677167098471)
    ·
      refine ⟨9349727815253515750647707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233151876835677167098471 9349727815253515750647707)
      ·
        refine ⟨14024591722880273625971561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349727815253515750647707 14024591722880273625971561)
        ·
          refine ⟨10518443792160205219478671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14024591722880273625971561 10518443792160205219478671)
          ·
            refine ⟨15777665688240307829218007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518443792160205219478671 15777665688240307829218007)
            ·
              refine ⟨23666498532360461743827011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15777665688240307829218007 23666498532360461743827011)
              ·
                refine ⟨35499747798540692615740517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23666498532360461743827011 35499747798540692615740517)
                ·
                  refine ⟨6656202712226379865451347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35499747798540692615740517 6656202712226379865451347)
                  ·
                    refine ⟨9984304068339569798177021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6656202712226379865451347 9984304068339569798177021)
                    ·
                      refine ⟨3744114025627338674316383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9984304068339569798177021 3744114025627338674316383)
                      ·
                        rfl

theorem cell23_7291636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7291636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291636 prefixEnd_7291636 := by exact prefixLift 7291636
  have htrace : WordTrace (prefixWord ++ tailWord_7291636) baseStart_7291636 baseEnd_7291636 := by
    simpa [prefixWord, tailWord_7291636, baseEnd_7291636] using wordTrace_append hprefix tailTrace_7291636
  have hstable : (prefixWord ++ tailWord_7291636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291636).length < 2 ^ (prefixWord ++ tailWord_7291636).sum := by decide
  have hdescent : baseEnd_7291636 < baseStart_7291636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291655 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7291655 : Nat := 118140960795 + 7291655 * 2 ^ 59
def prefixEnd_7291655 : Nat := 4983230072969 + 3 ^ 40 * 7291655 * 2
def baseEnd_7291655 : Nat := 3744123781759774099978795

theorem tailTrace_7291655 : CollatzResearch.WordTrace tailWord_7291655 prefixEnd_7291655 3744123781759774099978795 := by
  unfold tailWord_7291655
  simp only [CollatzResearch.WordTrace]
  refine ⟨265948506398586725374476419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177299004265724483582984279 265948506398586725374476419)
  ·
    refine ⟨398922759597880088061714629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265948506398586725374476419 398922759597880088061714629)
    ·
      refine ⟨74798017424602516511571493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398922759597880088061714629 74798017424602516511571493)
      ·
        refine ⟨14024628267112971845919655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74798017424602516511571493 14024628267112971845919655)
        ·
          refine ⟨21036942400669457768879483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024628267112971845919655 21036942400669457768879483)
          ·
            refine ⟨31555413601004186653319225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036942400669457768879483 31555413601004186653319225)
            ·
              refine ⟨23666560200753139989989419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31555413601004186653319225 23666560200753139989989419)
              ·
                refine ⟨35499840301129709984984129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23666560200753139989989419 35499840301129709984984129)
                ·
                  refine ⟨26624880225847282488738097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35499840301129709984984129 26624880225847282488738097)
                  ·
                    refine ⟨19968660169385461866553573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26624880225847282488738097 19968660169385461866553573)
                    ·
                      refine ⟨3744123781759774099978795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968660169385461866553573 3744123781759774099978795)
                      ·
                        rfl

theorem cell23_7291655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7291655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291655 prefixEnd_7291655 := by exact prefixLift 7291655
  have htrace : WordTrace (prefixWord ++ tailWord_7291655) baseStart_7291655 baseEnd_7291655 := by
    simpa [prefixWord, tailWord_7291655, baseEnd_7291655] using wordTrace_append hprefix tailTrace_7291655
  have hstable : (prefixWord ++ tailWord_7291655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291655).length < 2 ^ (prefixWord ++ tailWord_7291655).sum := by decide
  have hdescent : baseEnd_7291655 < baseStart_7291655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291682 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7291682 : Nat := 118140960795 + 7291682 * 2 ^ 59
def prefixEnd_7291682 : Nat := 4983230072969 + 3 ^ 40 * 7291682 * 2
def baseEnd_7291682 : Nat := 416015293970827277149019

theorem tailTrace_7291682 : CollatzResearch.WordTrace tailWord_7291682 prefixEnd_7291682 416015293970827277149019 := by
  unfold tailWord_7291682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66487372792372227246427325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177299660779659272657139533 66487372792372227246427325)
  ·
    refine ⟨24932764797139585217410247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66487372792372227246427325 24932764797139585217410247)
    ·
      refine ⟨37399147195709377826115371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24932764797139585217410247 37399147195709377826115371)
      ·
        refine ⟨56098720793564066739173057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37399147195709377826115371 56098720793564066739173057)
        ·
          refine ⟨42074040595173050054379793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56098720793564066739173057 42074040595173050054379793)
          ·
            refine ⟨31555530446379787540784845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42074040595173050054379793 31555530446379787540784845)
            ·
              refine ⟨11833323917392420327794317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31555530446379787540784845 11833323917392420327794317)
              ·
                refine ⟨4437496469022157622922869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11833323917392420327794317 4437496469022157622922869)
                ·
                  refine ⟨416015293970827277149019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437496469022157622922869 416015293970827277149019)
                  ·
                    rfl

theorem cell23_7291682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7291682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291682 prefixEnd_7291682 := by exact prefixLift 7291682
  have htrace : WordTrace (prefixWord ++ tailWord_7291682) baseStart_7291682 baseEnd_7291682 := by
    simpa [prefixWord, tailWord_7291682, baseEnd_7291682] using wordTrace_append hprefix tailTrace_7291682
  have hstable : (prefixWord ++ tailWord_7291682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291682).length < 2 ^ (prefixWord ++ tailWord_7291682).sum := by decide
  have hdescent : baseEnd_7291682 < baseStart_7291682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291710 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_7291710 : Nat := 118140960795 + 7291710 * 2 ^ 59
def prefixEnd_7291710 : Nat := 4983230072969 + 3 ^ 40 * 7291710 * 2
def baseEnd_7291710 : Nat := 3744152023195771384791043

theorem tailTrace_7291710 : CollatzResearch.WordTrace tailWord_7291710 prefixEnd_7291710 3744152023195771384791043 := by
  unfold tailWord_7291710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33243814051673433720966073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177300341608924979845152389 33243814051673433720966073)
  ·
    refine ⟨24932860538755075290724555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33243814051673433720966073 24932860538755075290724555)
    ·
      refine ⟨37399290808132612936086833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24932860538755075290724555 37399290808132612936086833)
      ·
        refine ⟨28049468106099459702065125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37399290808132612936086833 28049468106099459702065125)
        ·
          refine ⟨5259275269893648694137211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28049468106099459702065125 5259275269893648694137211)
          ·
            refine ⟨7888912904840473041205817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259275269893648694137211 7888912904840473041205817)
            ·
              refine ⟨5916684678630354780904363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888912904840473041205817 5916684678630354780904363)
              ·
                refine ⟨8875027017945532171356545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916684678630354780904363 8875027017945532171356545)
                ·
                  refine ⟨6656270263459149128517409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8875027017945532171356545 6656270263459149128517409)
                  ·
                    refine ⟨4992202697594361846388057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6656270263459149128517409 4992202697594361846388057)
                    ·
                      refine ⟨3744152023195771384791043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992202697594361846388057 3744152023195771384791043)
                      ·
                        rfl

theorem cell23_7291710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_7291710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291710 prefixEnd_7291710 := by exact prefixLift 7291710
  have htrace : WordTrace (prefixWord ++ tailWord_7291710) baseStart_7291710 baseEnd_7291710 := by
    simpa [prefixWord, tailWord_7291710, baseEnd_7291710] using wordTrace_append hprefix tailTrace_7291710
  have hstable : (prefixWord ++ tailWord_7291710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291710).length < 2 ^ (prefixWord ++ tailWord_7291710).sum := by decide
  have hdescent : baseEnd_7291710 < baseStart_7291710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291715 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 6, 2]
def baseStart_7291715 : Nat := 118140960795 + 7291715 * 2 ^ 59
def prefixEnd_7291715 : Nat := 4983230072969 + 3 ^ 40 * 7291715 * 2
def baseEnd_7291715 : Nat := 3744154590599043865228519

theorem tailTrace_7291715 : CollatzResearch.WordTrace tailWord_7291715 prefixEnd_7291715 3744154590599043865228519 := by
  unfold tailWord_7291715
  simp only [CollatzResearch.WordTrace]
  refine ⟨265950694778369355621660599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177300463185579570414440399 265950694778369355621660599)
  ·
    refine ⟨398926042167554033432490899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265950694778369355621660599 398926042167554033432490899)
    ·
      refine ⟨598389063251331050148736349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398926042167554033432490899 598389063251331050148736349)
      ·
        refine ⟨224395898719249143805776131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598389063251331050148736349 224395898719249143805776131)
        ·
          refine ⟨336593848078873715708664197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224395898719249143805776131 336593848078873715708664197)
          ·
            refine ⟨63111346514788821695374537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336593848078873715708664197 63111346514788821695374537)
            ·
              refine ⟨47333509886091616271530903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63111346514788821695374537 47333509886091616271530903)
              ·
                refine ⟨71000264829137424407296355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47333509886091616271530903 71000264829137424407296355)
                ·
                  refine ⟨106500397243706136610944533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71000264829137424407296355 106500397243706136610944533)
                  ·
                    refine ⟨4992206120798725153638025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106500397243706136610944533 4992206120798725153638025)
                    ·
                      refine ⟨3744154590599043865228519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992206120798725153638025 3744154590599043865228519)
                      ·
                        rfl

theorem cell23_7291715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_7291715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291715 prefixEnd_7291715 := by exact prefixLift 7291715
  have htrace : WordTrace (prefixWord ++ tailWord_7291715) baseStart_7291715 baseEnd_7291715 := by
    simpa [prefixWord, tailWord_7291715, baseEnd_7291715] using wordTrace_append hprefix tailTrace_7291715
  have hstable : (prefixWord ++ tailWord_7291715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291715).length < 2 ^ (prefixWord ++ tailWord_7291715).sum := by decide
  have hdescent : baseEnd_7291715 < baseStart_7291715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291728 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_7291728 : Nat := 118140960795 + 7291728 * 2 ^ 59
def prefixEnd_7291728 : Nat := 4983230072969 + 3 ^ 40 * 7291728 * 2
def baseEnd_7291728 : Nat := 3744161265847552314365959

theorem tailTrace_7291728 : CollatzResearch.WordTrace tailWord_7291728 prefixEnd_7291728 3744161265847552314365959 := by
  unfold tailWord_7291728
  simp only [CollatzResearch.WordTrace]
  refine ⟨132975584463661129420941919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177300779284881505894589225 132975584463661129420941919)
  ·
    refine ⟨199463376695491694131412879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132975584463661129420941919 199463376695491694131412879)
    ·
      refine ⟨299195065043237541197119319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199463376695491694131412879 299195065043237541197119319)
      ·
        refine ⟨448792597564856311795678979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299195065043237541197119319 448792597564856311795678979)
        ·
          refine ⟨673188896347284467693518469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448792597564856311795678979 673188896347284467693518469)
          ·
            refine ⟨126222918065115837692534713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 673188896347284467693518469 126222918065115837692534713)
            ·
              refine ⟨94667188548836878269401035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126222918065115837692534713 94667188548836878269401035)
              ·
                refine ⟨142000782823255317404101553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94667188548836878269401035 142000782823255317404101553)
                ·
                  refine ⟨106500587117441488053076165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142000782823255317404101553 106500587117441488053076165)
                  ·
                    refine ⟨19968860084520279009951781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106500587117441488053076165 19968860084520279009951781)
                    ·
                      refine ⟨3744161265847552314365959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19968860084520279009951781 3744161265847552314365959)
                      ·
                        rfl

theorem cell23_7291728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_7291728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291728 prefixEnd_7291728 := by exact prefixLift 7291728
  have htrace : WordTrace (prefixWord ++ tailWord_7291728) baseStart_7291728 baseEnd_7291728 := by
    simpa [prefixWord, tailWord_7291728, baseEnd_7291728] using wordTrace_append hprefix tailTrace_7291728
  have hstable : (prefixWord ++ tailWord_7291728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291728).length < 2 ^ (prefixWord ++ tailWord_7291728).sum := by decide
  have hdescent : baseEnd_7291728 < baseStart_7291728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291752 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7291752 : Nat := 118140960795 + 7291752 * 2 ^ 59
def prefixEnd_7291752 : Nat := 4983230072969 + 3 ^ 40 * 7291752 * 2
def baseEnd_7291752 : Nat := 3744173589383260220465849

theorem tailTrace_7291752 : CollatzResearch.WordTrace tailWord_7291752 prefixEnd_7291752 3744173589383260220465849 := by
  unfold tailWord_7291752
  simp only [CollatzResearch.WordTrace]
  refine ⟨132976022139617655470378755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177301362852823540627171673 132976022139617655470378755)
  ·
    refine ⟨199464033209426483205568133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132976022139617655470378755 199464033209426483205568133)
    ·
      refine ⟨37399506226767465601044025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199464033209426483205568133 37399506226767465601044025)
      ·
        refine ⟨28049629670075599200783019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37399506226767465601044025 28049629670075599200783019)
        ·
          refine ⟨42074444505113398801174529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28049629670075599200783019 42074444505113398801174529)
          ·
            refine ⟨31555833378835049100880897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42074444505113398801174529 31555833378835049100880897)
            ·
              refine ⟨23666875034126286825660673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31555833378835049100880897 23666875034126286825660673)
              ·
                refine ⟨17750156275594715119245505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23666875034126286825660673 17750156275594715119245505)
                ·
                  refine ⟨13312617206696036339434129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17750156275594715119245505 13312617206696036339434129)
                  ·
                    refine ⟨9984462905022027254575597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13312617206696036339434129 9984462905022027254575597)
                    ·
                      refine ⟨3744173589383260220465849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9984462905022027254575597 3744173589383260220465849)
                      ·
                        rfl

theorem cell23_7291752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7291752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291752 prefixEnd_7291752 := by exact prefixLift 7291752
  have htrace : WordTrace (prefixWord ++ tailWord_7291752) baseStart_7291752 baseEnd_7291752 := by
    simpa [prefixWord, tailWord_7291752, baseEnd_7291752] using wordTrace_append hprefix tailTrace_7291752
  have hstable : (prefixWord ++ tailWord_7291752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291752).length < 2 ^ (prefixWord ++ tailWord_7291752).sum := by decide
  have hdescent : baseEnd_7291752 < baseStart_7291752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291785 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_7291785 : Nat := 118140960795 + 7291785 * 2 ^ 59
def prefixEnd_7291785 : Nat := 4983230072969 + 3 ^ 40 * 7291785 * 2
def baseEnd_7291785 : Nat := 1248063511414952863784399

theorem tailTrace_7291785 : CollatzResearch.WordTrace tailWord_7291785 prefixEnd_7291785 1248063511414952863784399 := by
  unfold tailWord_7291785
  simp only [CollatzResearch.WordTrace]
  refine ⟨265953247888115757576708809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177302165258743838384472539 265953247888115757576708809)
  ·
    refine ⟨199464935916086818182531607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265953247888115757576708809 199464935916086818182531607)
    ·
      refine ⟨299197403874130227273797411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199464935916086818182531607 299197403874130227273797411)
      ·
        refine ⟨448796105811195340910696117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299197403874130227273797411 448796105811195340910696117)
        ·
          refine ⟨42074634919799563210377761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448796105811195340910696117 42074634919799563210377761)
          ·
            refine ⟨31555976189849672407783321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42074634919799563210377761 31555976189849672407783321)
            ·
              refine ⟨23666982142387254305837491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31555976189849672407783321 23666982142387254305837491)
              ·
                refine ⟨35500473213580881458756237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23666982142387254305837491 35500473213580881458756237)
                ·
                  refine ⟨13312677455092830547033589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35500473213580881458756237 13312677455092830547033589)
                  ·
                    refine ⟨1248063511414952863784399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13312677455092830547033589 1248063511414952863784399)
                    ·
                      rfl

theorem cell23_7291785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_7291785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291785 prefixEnd_7291785 := by exact prefixLift 7291785
  have htrace : WordTrace (prefixWord ++ tailWord_7291785) baseStart_7291785 baseEnd_7291785 := by
    simpa [prefixWord, tailWord_7291785, baseEnd_7291785] using wordTrace_append hprefix tailTrace_7291785
  have hstable : (prefixWord ++ tailWord_7291785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291785).length < 2 ^ (prefixWord ++ tailWord_7291785).sum := by decide
  have hdescent : baseEnd_7291785 < baseStart_7291785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291832 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_7291832 : Nat := 118140960795 + 7291832 * 2 ^ 59
def prefixEnd_7291832 : Nat := 4983230072969 + 3 ^ 40 * 7291832 * 2
def baseEnd_7291832 : Nat := 1248071555945206635821827

theorem tailTrace_7291832 : CollatzResearch.WordTrace tailWord_7291832 prefixEnd_7291832 1248071555945206635821827 := by
  unfold tailWord_7291832
  simp only [CollatzResearch.WordTrace]
  refine ⟨132977481059472742301834875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177303308079296989735779833 132977481059472742301834875)
  ·
    refine ⟨199466221589209113452752313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132977481059472742301834875 199466221589209113452752313)
    ·
      refine ⟨149599666191906835089564235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199466221589209113452752313 149599666191906835089564235)
      ·
        refine ⟨224399499287860252634346353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149599666191906835089564235 224399499287860252634346353)
        ·
          refine ⟨168299624465895189475759765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224399499287860252634346353 168299624465895189475759765)
          ·
            refine ⟨7889044896838837006676239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168299624465895189475759765 7889044896838837006676239)
            ·
              refine ⟨11833567345258255510014359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889044896838837006676239 11833567345258255510014359)
              ·
                refine ⟨17750351017887383265021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11833567345258255510014359 17750351017887383265021539)
                ·
                  refine ⟨26625526526831074897532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17750351017887383265021539 26625526526831074897532309)
                  ·
                    refine ⟨1248071555945206635821827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26625526526831074897532309 1248071555945206635821827)
                    ·
                      rfl

theorem cell23_7291832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_7291832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291832 prefixEnd_7291832 := by exact prefixLift 7291832
  have htrace : WordTrace (prefixWord ++ tailWord_7291832) baseStart_7291832 baseEnd_7291832 := by
    simpa [prefixWord, tailWord_7291832, baseEnd_7291832] using wordTrace_append hprefix tailTrace_7291832
  have hstable : (prefixWord ++ tailWord_7291832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291832).length < 2 ^ (prefixWord ++ tailWord_7291832).sum := by decide
  have hdescent : baseEnd_7291832 < baseStart_7291832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291862 : List Nat := [5, 2, 1, 1, 2, 1, 11]
def baseStart_7291862 : Nat := 118140960795 + 7291862 * 2 ^ 59
def prefixEnd_7291862 : Nat := 4983230072969 + 3 ^ 40 * 7291862 * 2
def baseEnd_7291862 : Nat := 46225062620435244322103

theorem tailTrace_7291862 : CollatzResearch.WordTrace tailWord_7291862 prefixEnd_7291862 46225062620435244322103 := by
  unfold tailWord_7291862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622253519302299982953865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177304037539224533151507893 16622253519302299982953865)
  ·
    refine ⟨12466690139476724987215399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16622253519302299982953865 12466690139476724987215399)
    ·
      refine ⟨18700035209215087480823099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466690139476724987215399 18700035209215087480823099)
      ·
        refine ⟨28050052813822631221234649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18700035209215087480823099 28050052813822631221234649)
        ·
          refine ⟨21037539610366973415925987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28050052813822631221234649 21037539610366973415925987)
          ·
            refine ⟨31556309415550460123888981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21037539610366973415925987 31556309415550460123888981)
            ·
              refine ⟨46225062620435244322103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31556309415550460123888981 46225062620435244322103)
              ·
                rfl

theorem cell23_7291862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 11].length) (baseStart_7291862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291862 prefixEnd_7291862 := by exact prefixLift 7291862
  have htrace : WordTrace (prefixWord ++ tailWord_7291862) baseStart_7291862 baseEnd_7291862 := by
    simpa [prefixWord, tailWord_7291862, baseEnd_7291862] using wordTrace_append hprefix tailTrace_7291862
  have hstable : (prefixWord ++ tailWord_7291862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291862).length < 2 ^ (prefixWord ++ tailWord_7291862).sum := by decide
  have hdescent : baseEnd_7291862 < baseStart_7291862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291875 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 7]
def baseStart_7291875 : Nat := 118140960795 + 7291875 * 2 ^ 59
def prefixEnd_7291875 : Nat := 4983230072969 + 3 ^ 40 * 7291875 * 2
def baseEnd_7291875 : Nat := 1248078915834587746409261

theorem tailTrace_7291875 : CollatzResearch.WordTrace tailWord_7291875 prefixEnd_7291875 1248078915834587746409261 := by
  unfold tailWord_7291875
  simp only [CollatzResearch.WordTrace]
  refine ⟨265956530457789702947485079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177304353638526468631656719 265956530457789702947485079)
  ·
    refine ⟨398934795686684554421227619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265956530457789702947485079 398934795686684554421227619)
    ·
      refine ⟨598402193530026831631841429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398934795686684554421227619 598402193530026831631841429)
      ·
        refine ⟨28050102821720007732742567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 598402193530026831631841429 28050102821720007732742567)
        ·
          refine ⟨42075154232580011599113851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28050102821720007732742567 42075154232580011599113851)
          ·
            refine ⟨63112731348870017398670777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42075154232580011599113851 63112731348870017398670777)
            ·
              refine ⟨47334548511652513049003083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63112731348870017398670777 47334548511652513049003083)
              ·
                refine ⟨71001822767478769573504625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47334548511652513049003083 71001822767478769573504625)
                ·
                  refine ⟨53251367075609077180128469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71001822767478769573504625 53251367075609077180128469)
                  ·
                    refine ⟨1248078915834587746409261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53251367075609077180128469 1248078915834587746409261)
                    ·
                      rfl

theorem cell23_7291875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_7291875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291875 prefixEnd_7291875 := by exact prefixLift 7291875
  have htrace : WordTrace (prefixWord ++ tailWord_7291875) baseStart_7291875 baseEnd_7291875 := by
    simpa [prefixWord, tailWord_7291875, baseEnd_7291875] using wordTrace_append hprefix tailTrace_7291875
  have hstable : (prefixWord ++ tailWord_7291875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291875).length < 2 ^ (prefixWord ++ tailWord_7291875).sum := by decide
  have hdescent : baseEnd_7291875 < baseStart_7291875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291929 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 4, 2, 2]
def baseStart_7291929 : Nat := 118140960795 + 7291929 * 2 ^ 59
def prefixEnd_7291929 : Nat := 4983230072969 + 3 ^ 40 * 7291929 * 2
def baseEnd_7291929 : Nat := 3744264475459106027952535

theorem tailTrace_7291929 : CollatzResearch.WordTrace tailWord_7291929 prefixEnd_7291929 3744264475459106027952535 := by
  unfold tailWord_7291929
  simp only [CollatzResearch.WordTrace]
  refine ⟨265958499999594070169950841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177305666666396046779967227 265958499999594070169950841)
  ·
    refine ⟨199468874999695552627463131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265958499999594070169950841 199468874999695552627463131)
    ·
      refine ⟨299203312499543328941194697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199468874999695552627463131 299203312499543328941194697)
      ·
        refine ⟨224402484374657496705896023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299203312499543328941194697 224402484374657496705896023)
        ·
          refine ⟨336603726561986245058844035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224402484374657496705896023 336603726561986245058844035)
          ·
            refine ⟨504905589842979367588266053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336603726561986245058844035 504905589842979367588266053)
            ·
              refine ⟨94669798095558631422799885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 504905589842979367588266053 94669798095558631422799885)
              ·
                refine ⟨35501174285834486783549957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94669798095558631422799885 35501174285834486783549957)
                ·
                  refine ⟨6656470178593966271915617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35501174285834486783549957 6656470178593966271915617)
                  ·
                    refine ⟨4992352633945474703936713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6656470178593966271915617 4992352633945474703936713)
                    ·
                      refine ⟨3744264475459106027952535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992352633945474703936713 3744264475459106027952535)
                      ·
                        rfl

theorem cell23_7291929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_7291929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291929 prefixEnd_7291929 := by exact prefixLift 7291929
  have htrace : WordTrace (prefixWord ++ tailWord_7291929) baseStart_7291929 baseEnd_7291929 := by
    simpa [prefixWord, tailWord_7291929, baseEnd_7291929] using wordTrace_append hprefix tailTrace_7291929
  have hstable : (prefixWord ++ tailWord_7291929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291929).length < 2 ^ (prefixWord ++ tailWord_7291929).sum := by decide
  have hdescent : baseEnd_7291929 < baseStart_7291929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291982 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7291982 : Nat := 118140960795 + 7291982 * 2 ^ 59
def prefixEnd_7291982 : Nat := 4983230072969 + 3 ^ 40 * 7291982 * 2
def baseEnd_7291982 : Nat := 1248097229977931440196597

theorem tailTrace_7291982 : CollatzResearch.WordTrace tailWord_7291982 prefixEnd_7291982 1248097229977931440196597 := by
  unfold tailWord_7291982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33245054133550257527703775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177306955378934706814420133 33245054133550257527703775)
  ·
    refine ⟨49867581200325386291555663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33245054133550257527703775 49867581200325386291555663)
    ·
      refine ⟨74801371800488079437333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49867581200325386291555663 74801371800488079437333495)
      ·
        refine ⟨112202057700732119156000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74801371800488079437333495 112202057700732119156000243)
        ·
          refine ⟨168303086551098178734000365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112202057700732119156000243 168303086551098178734000365)
          ·
            refine ⟨63113657456661817025250137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168303086551098178734000365 63113657456661817025250137)
            ·
              refine ⟨47335243092496362768937603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63113657456661817025250137 47335243092496362768937603)
              ·
                refine ⟨71002864638744544153406405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47335243092496362768937603 71002864638744544153406405)
                ·
                  refine ⟨13313037119764602028763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71002864638744544153406405 13313037119764602028763701)
                  ·
                    refine ⟨1248097229977931440196597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13313037119764602028763701 1248097229977931440196597)
                    ·
                      rfl

theorem cell23_7291982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7291982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291982 prefixEnd_7291982 := by exact prefixLift 7291982
  have htrace : WordTrace (prefixWord ++ tailWord_7291982) baseStart_7291982 baseEnd_7291982 := by
    simpa [prefixWord, tailWord_7291982, baseEnd_7291982] using wordTrace_append hprefix tailTrace_7291982
  have hstable : (prefixWord ++ tailWord_7291982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291982).length < 2 ^ (prefixWord ++ tailWord_7291982).sum := by decide
  have hdescent : baseEnd_7291982 < baseStart_7291982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291997 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7291997 : Nat := 118140960795 + 7291997 * 2 ^ 59
def prefixEnd_7291997 : Nat := 4983230072969 + 3 ^ 40 * 7291997 * 2
def baseEnd_7291997 : Nat := 3744299392143611761902223

theorem tailTrace_7291997 : CollatzResearch.WordTrace tailWord_7291997 prefixEnd_7291997 3744299392143611761902223 := by
  unfold tailWord_7291997
  simp only [CollatzResearch.WordTrace]
  refine ⟨265960980163347717783426245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177307320108898478522284163 265960980163347717783426245)
  ·
    refine ⟨49867683780627697084392421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265960980163347717783426245 49867683780627697084392421)
    ·
      refine ⟨9350190708867693203323579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49867683780627697084392421 9350190708867693203323579)
      ·
        refine ⟨14025286063301539804985369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350190708867693203323579 14025286063301539804985369)
        ·
          refine ⟨10518964547476154853739027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14025286063301539804985369 10518964547476154853739027)
          ·
            refine ⟨15778446821214232280608541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518964547476154853739027 15778446821214232280608541)
            ·
              refine ⟨5916917557955337105228203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15778446821214232280608541 5916917557955337105228203)
              ·
                refine ⟨8875376336933005657842305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916917557955337105228203 8875376336933005657842305)
                ·
                  refine ⟨6656532252699754243381729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8875376336933005657842305 6656532252699754243381729)
                  ·
                    refine ⟨4992399189524815682536297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6656532252699754243381729 4992399189524815682536297)
                    ·
                      refine ⟨3744299392143611761902223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992399189524815682536297 3744299392143611761902223)
                      ·
                        rfl

theorem cell23_7291997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7291997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291997 prefixEnd_7291997 := by exact prefixLift 7291997
  have htrace : WordTrace (prefixWord ++ tailWord_7291997) baseStart_7291997 baseEnd_7291997 := by
    simpa [prefixWord, tailWord_7291997, baseEnd_7291997] using wordTrace_append hprefix tailTrace_7291997
  have hstable : (prefixWord ++ tailWord_7291997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291997).length < 2 ^ (prefixWord ++ tailWord_7291997).sum := by decide
  have hdescent : baseEnd_7291997 < baseStart_7291997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292042 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_7292042 : Nat := 118140960795 + 7292042 * 2 ^ 59
def prefixEnd_7292042 : Nat := 4983230072969 + 3 ^ 40 * 7292042 * 2
def baseEnd_7292042 : Nat := 416035833197007120648835

theorem tailTrace_7292042 : CollatzResearch.WordTrace tailWord_7292042 prefixEnd_7292042 416035833197007120648835 := by
  unfold tailWord_7292042
  simp only [CollatzResearch.WordTrace]
  refine ⟨66490655362046172617203595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177308414298789793645876253 66490655362046172617203595)
  ·
    refine ⟨99735983043069258925805393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66490655362046172617203595 99735983043069258925805393)
    ·
      refine ⟨74801987282301944194354045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99735983043069258925805393 74801987282301944194354045)
      ·
        refine ⟨28050745230863229072882767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74801987282301944194354045 28050745230863229072882767)
        ·
          refine ⟨42076117846294843609324151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28050745230863229072882767 42076117846294843609324151)
          ·
            refine ⟨63114176769442265413986227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42076117846294843609324151 63114176769442265413986227)
            ·
              refine ⟨94671265154163398120979341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63114176769442265413986227 94671265154163398120979341)
              ·
                refine ⟨35501724432811274295367253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94671265154163398120979341 35501724432811274295367253)
                ·
                  refine ⟨416035833197007120648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35501724432811274295367253 416035833197007120648835)
                  ·
                    rfl

theorem cell23_7292042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_7292042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292042 prefixEnd_7292042 := by exact prefixLift 7292042
  have htrace : WordTrace (prefixWord ++ tailWord_7292042) baseStart_7292042 baseEnd_7292042 := by
    simpa [prefixWord, tailWord_7292042, baseEnd_7292042] using wordTrace_append hprefix tailTrace_7292042
  have hstable : (prefixWord ++ tailWord_7292042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292042).length < 2 ^ (prefixWord ++ tailWord_7292042).sum := by decide
  have hdescent : baseEnd_7292042 < baseStart_7292042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292046 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_7292046 : Nat := 118140960795 + 7292046 * 2 ^ 59
def prefixEnd_7292046 : Nat := 4983230072969 + 3 ^ 40 * 7292046 * 2
def baseEnd_7292046 : Nat := 1248108184231894023396499

theorem tailTrace_7292046 : CollatzResearch.WordTrace tailWord_7292046 prefixEnd_7292046 1248108184231894023396499 := by
  unfold tailWord_7292046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33245345917521274893994999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177308511560113466101306661 33245345917521274893994999)
  ·
    refine ⟨49868018876281912340992499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33245345917521274893994999 49868018876281912340992499)
    ·
      refine ⟨74802028314422868511488749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49868018876281912340992499 74802028314422868511488749)
      ·
        refine ⟨28050760617908575691808281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74802028314422868511488749 28050760617908575691808281)
        ·
          refine ⟨21038070463431431768856211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28050760617908575691808281 21038070463431431768856211)
          ·
            refine ⟨31557105695147147653284317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21038070463431431768856211 31557105695147147653284317)
            ·
              refine ⟨11833914635680180369981619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31557105695147147653284317 11833914635680180369981619)
              ·
                refine ⟨17750871953520270554972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11833914635680180369981619 17750871953520270554972429)
                ·
                  refine ⟨6656576982570101458114661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17750871953520270554972429 6656576982570101458114661)
                  ·
                    refine ⟨1248108184231894023396499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656576982570101458114661 1248108184231894023396499)
                    ·
                      rfl

theorem cell23_7292046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_7292046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292046 prefixEnd_7292046 := by exact prefixLift 7292046
  have htrace : WordTrace (prefixWord ++ tailWord_7292046) baseStart_7292046 baseEnd_7292046 := by
    simpa [prefixWord, tailWord_7292046, baseEnd_7292046] using wordTrace_append hprefix tailTrace_7292046
  have hstable : (prefixWord ++ tailWord_7292046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292046).length < 2 ^ (prefixWord ++ tailWord_7292046).sum := by decide
  have hdescent : baseEnd_7292046 < baseStart_7292046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292079 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 5, 2]
def baseStart_7292079 : Nat := 118140960795 + 7292079 * 2 ^ 59
def prefixEnd_7292079 : Nat := 4983230072969 + 3 ^ 40 * 7292079 * 2
def baseEnd_7292079 : Nat := 3744341497557280441076845

theorem tailTrace_7292079 : CollatzResearch.WordTrace tailWord_7292079 prefixEnd_7292079 3744341497557280441076845 := by
  unfold tailWord_7292079
  simp only [CollatzResearch.WordTrace]
  refine ⟨265963970949050645787911291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177309313966033763858607527 265963970949050645787911291)
  ·
    refine ⟨398945956423575968681866937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265963970949050645787911291 398945956423575968681866937)
    ·
      refine ⟨299209467317681976511400203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398945956423575968681866937 299209467317681976511400203)
      ·
        refine ⟨448814200976522964767100305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299209467317681976511400203 448814200976522964767100305)
        ·
          refine ⟨336610650732392223575325229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448814200976522964767100305 336610650732392223575325229)
          ·
            refine ⟨126228994024647083840746961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336610650732392223575325229 126228994024647083840746961)
            ·
              refine ⟨94671745518485312880560221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126228994024647083840746961 94671745518485312880560221)
              ·
                refine ⟨35501904569431992330210083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94671745518485312880560221 35501904569431992330210083)
                ·
                  refine ⟨53252856854147988495315125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35501904569431992330210083 53252856854147988495315125)
                  ·
                    refine ⟨4992455330076373921435793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53252856854147988495315125 4992455330076373921435793)
                    ·
                      refine ⟨3744341497557280441076845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992455330076373921435793 3744341497557280441076845)
                      ·
                        rfl

theorem cell23_7292079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5, 2].length) (baseStart_7292079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292079 prefixEnd_7292079 := by exact prefixLift 7292079
  have htrace : WordTrace (prefixWord ++ tailWord_7292079) baseStart_7292079 baseEnd_7292079 := by
    simpa [prefixWord, tailWord_7292079, baseEnd_7292079] using wordTrace_append hprefix tailTrace_7292079
  have hstable : (prefixWord ++ tailWord_7292079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292079).length < 2 ^ (prefixWord ++ tailWord_7292079).sum := by decide
  have hdescent : baseEnd_7292079 < baseStart_7292079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292097 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7292097 : Nat := 118140960795 + 7292097 * 2 ^ 59
def prefixEnd_7292097 : Nat := 4983230072969 + 3 ^ 40 * 7292097 * 2
def baseEnd_7292097 : Nat := 1248116913403020456883921

theorem tailTrace_7292097 : CollatzResearch.WordTrace tailWord_7292097 prefixEnd_7292097 1248116913403020456883921 := by
  unfold tailWord_7292097
  simp only [CollatzResearch.WordTrace]
  refine ⟨265964627462985434862066545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177309751641990289908044363 265964627462985434862066545)
  ·
    refine ⟨199473470597239076146549909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265964627462985434862066545 199473470597239076146549909)
    ·
      refine ⟨9350318934245581694369527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199473470597239076146549909 9350318934245581694369527)
      ·
        refine ⟨14025478401368372541554291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350318934245581694369527 14025478401368372541554291)
        ·
          refine ⟨21038217602052558812331437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025478401368372541554291 21038217602052558812331437)
          ·
            refine ⟨7889331600769709554624289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21038217602052558812331437 7889331600769709554624289)
            ·
              refine ⟨5916998700577282165968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889331600769709554624289 5916998700577282165968217)
              ·
                refine ⟨4437749025432961624476163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916998700577282165968217 4437749025432961624476163)
                ·
                  refine ⟨6656623538149442436714245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437749025432961624476163 6656623538149442436714245)
                  ·
                    refine ⟨1248116913403020456883921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656623538149442436714245 1248116913403020456883921)
                    ·
                      rfl

theorem cell23_7292097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7292097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292097 prefixEnd_7292097 := by exact prefixLift 7292097
  have htrace : WordTrace (prefixWord ++ tailWord_7292097) baseStart_7292097 baseEnd_7292097 := by
    simpa [prefixWord, tailWord_7292097, baseEnd_7292097] using wordTrace_append hprefix tailTrace_7292097
  have hstable : (prefixWord ++ tailWord_7292097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292097).length < 2 ^ (prefixWord ++ tailWord_7292097).sum := by decide
  have hdescent : baseEnd_7292097 < baseStart_7292097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292132 : List Nat := [2, 3, 1, 1, 1, 2, 2, 11]
def baseStart_7292132 : Nat := 118140960795 + 7292132 * 2 ^ 59
def prefixEnd_7292132 : Nat := 4983230072969 + 3 ^ 40 * 7292132 * 2
def baseEnd_7292132 : Nat := 138680322667850693841263

theorem tailTrace_7292132 : CollatzResearch.WordTrace tailWord_7292132 prefixEnd_7292132 138680322667850693841263 := by
  unfold tailWord_7292132
  simp only [CollatzResearch.WordTrace]
  refine ⟨132982952008929317919795325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177310602678572423893060433 132982952008929317919795325)
  ·
    refine ⟨49868607003348494219923247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132982952008929317919795325 49868607003348494219923247)
    ·
      refine ⟨74802910505022741329884871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49868607003348494219923247 74802910505022741329884871)
      ·
        refine ⟨112204365757534111994827307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74802910505022741329884871 112204365757534111994827307)
        ·
          refine ⟨168306548636301167992240961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112204365757534111994827307 168306548636301167992240961)
          ·
            refine ⟨126229911477225875994180721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168306548636301167992240961 126229911477225875994180721)
            ·
              refine ⟨94672433607919406995635541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126229911477225875994180721 94672433607919406995635541)
              ·
                refine ⟨138680322667850693841263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94672433607919406995635541 138680322667850693841263)
                ·
                  rfl

theorem cell23_7292132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 11].length) (baseStart_7292132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292132 prefixEnd_7292132 := by exact prefixLift 7292132
  have htrace : WordTrace (prefixWord ++ tailWord_7292132) baseStart_7292132 baseEnd_7292132 := by
    simpa [prefixWord, tailWord_7292132, baseEnd_7292132] using wordTrace_append hprefix tailTrace_7292132
  have hstable : (prefixWord ++ tailWord_7292132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292132).length < 2 ^ (prefixWord ++ tailWord_7292132).sum := by decide
  have hdescent : baseEnd_7292132 < baseStart_7292132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292139 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_7292139 : Nat := 118140960795 + 7292139 * 2 ^ 59
def prefixEnd_7292139 : Nat := 4983230072969 + 3 ^ 40 * 7292139 * 2
def baseEnd_7292139 : Nat := 3744372306396550206326569

theorem tailTrace_7292139 : CollatzResearch.WordTrace tailWord_7292139 prefixEnd_7292139 3744372306396550206326569 := by
  unfold tailWord_7292139
  simp only [CollatzResearch.WordTrace]
  refine ⟨265966159328833276035095471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177310772885888850690063647 265966159328833276035095471)
  ·
    refine ⟨398949238993249914052643207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265966159328833276035095471 398949238993249914052643207)
    ·
      refine ⟨598423858489874871078964811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398949238993249914052643207 598423858489874871078964811)
      ·
        refine ⟨897635787734812306618447217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598423858489874871078964811 897635787734812306618447217)
        ·
          refine ⟨673226840801109229963835413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897635787734812306618447217 673226840801109229963835413)
          ·
            refine ⟨31557508162551995154554785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 673226840801109229963835413 31557508162551995154554785)
            ·
              refine ⟨23668131121913996365916089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31557508162551995154554785 23668131121913996365916089)
              ·
                refine ⟨17751098341435497274437067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23668131121913996365916089 17751098341435497274437067)
                ·
                  refine ⟨26626647512153245911655601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17751098341435497274437067 26626647512153245911655601)
                  ·
                    refine ⟨19969985634114934433741701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26626647512153245911655601 19969985634114934433741701)
                    ·
                      refine ⟨3744372306396550206326569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19969985634114934433741701 3744372306396550206326569)
                      ·
                        rfl

theorem cell23_7292139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_7292139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292139 prefixEnd_7292139 := by exact prefixLift 7292139
  have htrace : WordTrace (prefixWord ++ tailWord_7292139) baseStart_7292139 baseEnd_7292139 := by
    simpa [prefixWord, tailWord_7292139, baseEnd_7292139] using wordTrace_append hprefix tailTrace_7292139
  have hstable : (prefixWord ++ tailWord_7292139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292139).length < 2 ^ (prefixWord ++ tailWord_7292139).sum := by decide
  have hdescent : baseEnd_7292139 < baseStart_7292139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292152 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_7292152 : Nat := 118140960795 + 7292152 * 2 ^ 59
def prefixEnd_7292152 : Nat := 4983230072969 + 3 ^ 40 * 7292152 * 2
def baseEnd_7292152 : Nat := 3744378981645058655464009

theorem tailTrace_7292152 : CollatzResearch.WordTrace tailWord_7292152 prefixEnd_7292152 3744378981645058655464009 := by
  unfold tailWord_7292152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132983316738893089627659355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177311088985190786170212473 132983316738893089627659355)
  ·
    refine ⟨199474975108339634441489033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132983316738893089627659355 199474975108339634441489033)
    ·
      refine ⟨149606231331254725831116775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199474975108339634441489033 149606231331254725831116775)
      ·
        refine ⟨224409346996882088746675163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149606231331254725831116775 224409346996882088746675163)
        ·
          refine ⟨336614020495323133120012745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224409346996882088746675163 336614020495323133120012745)
          ·
            refine ⟨252460515371492349840009559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336614020495323133120012745 252460515371492349840009559)
            ·
              refine ⟨378690773057238524760014339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252460515371492349840009559 378690773057238524760014339)
              ·
                refine ⟨568036159585857787140021509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378690773057238524760014339 568036159585857787140021509)
                ·
                  refine ⟨106506779922348335088754033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568036159585857787140021509 106506779922348335088754033)
                  ·
                    refine ⟨79880084941761251316565525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106506779922348335088754033 79880084941761251316565525)
                    ·
                      refine ⟨3744378981645058655464009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79880084941761251316565525 3744378981645058655464009)
                      ·
                        rfl

theorem cell23_7292152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_7292152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292152 prefixEnd_7292152 := by exact prefixLift 7292152
  have htrace : WordTrace (prefixWord ++ tailWord_7292152) baseStart_7292152 baseEnd_7292152 := by
    simpa [prefixWord, tailWord_7292152, baseEnd_7292152] using wordTrace_append hprefix tailTrace_7292152
  have hstable : (prefixWord ++ tailWord_7292152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292152).length < 2 ^ (prefixWord ++ tailWord_7292152).sum := by decide
  have hdescent : baseEnd_7292152 < baseStart_7292152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292194 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_7292194 : Nat := 118140960795 + 7292194 * 2 ^ 59
def prefixEnd_7292194 : Nat := 4983230072969 + 3 ^ 40 * 7292194 * 2
def baseEnd_7292194 : Nat := 3744400547832547491138817

theorem tailTrace_7292194 : CollatzResearch.WordTrace tailWord_7292194 prefixEnd_7292194 3744400547832547491138817 := by
  unfold tailWord_7292194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66492041335908505107086909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177312110229089346952231757 66492041335908505107086909)
  ·
    refine ⟨24934515500965689415157591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66492041335908505107086909 24934515500965689415157591)
    ·
      refine ⟨37401773251448534122736387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24934515500965689415157591 37401773251448534122736387)
      ·
        refine ⟨56102659877172801184104581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37401773251448534122736387 56102659877172801184104581)
        ·
          refine ⟨10519248726969900222019609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56102659877172801184104581 10519248726969900222019609)
          ·
            refine ⟨7889436545227425166514707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519248726969900222019609 7889436545227425166514707)
            ·
              refine ⟨11834154817841137749772061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889436545227425166514707 11834154817841137749772061)
              ·
                refine ⟨4437808056690426656164523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11834154817841137749772061 4437808056690426656164523)
                ·
                  refine ⟨6656712085035639984246785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437808056690426656164523 6656712085035639984246785)
                  ·
                    refine ⟨4992534063776729988185089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6656712085035639984246785 4992534063776729988185089)
                    ·
                      refine ⟨3744400547832547491138817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992534063776729988185089 3744400547832547491138817)
                      ·
                        rfl

theorem cell23_7292194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_7292194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292194 prefixEnd_7292194 := by exact prefixLift 7292194
  have htrace : WordTrace (prefixWord ++ tailWord_7292194) baseStart_7292194 baseEnd_7292194 := by
    simpa [prefixWord, tailWord_7292194, baseEnd_7292194] using wordTrace_append hprefix tailTrace_7292194
  have hstable : (prefixWord ++ tailWord_7292194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292194).length < 2 ^ (prefixWord ++ tailWord_7292194).sum := by decide
  have hdescent : baseEnd_7292194 < baseStart_7292194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292229 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_7292229 : Nat := 118140960795 + 7292229 * 2 ^ 59
def prefixEnd_7292229 : Nat := 4983230072969 + 3 ^ 40 * 7292229 * 2
def baseEnd_7292229 : Nat := 3744418519655454854201155

theorem tailTrace_7292229 : CollatzResearch.WordTrace tailWord_7292229 prefixEnd_7292229 3744418519655454854201155 := by
  unfold tailWord_7292229
  simp only [CollatzResearch.WordTrace]
  refine ⟨265969441898507221405871741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177312961265671480937247827 265969441898507221405871741)
  ·
    refine ⟨99738540711940208027201903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265969441898507221405871741 99738540711940208027201903)
    ·
      refine ⟨149607811067910312040802855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99738540711940208027201903 149607811067910312040802855)
      ·
        refine ⟨224411716601865468061204283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149607811067910312040802855 224411716601865468061204283)
        ·
          refine ⟨336617574902798202091806425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224411716601865468061204283 336617574902798202091806425)
          ·
            refine ⟨252463181177098651568854819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336617574902798202091806425 252463181177098651568854819)
            ·
              refine ⟨378694771765647977353282229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252463181177098651568854819 378694771765647977353282229)
              ·
                refine ⟨35502634853029497876870209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378694771765647977353282229 35502634853029497876870209)
                ·
                  refine ⟨26626976139772123407652657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35502634853029497876870209 26626976139772123407652657)
                  ·
                    refine ⟨19970232104829092555739493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26626976139772123407652657 19970232104829092555739493)
                    ·
                      refine ⟨3744418519655454854201155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19970232104829092555739493 3744418519655454854201155)
                      ·
                        rfl

theorem cell23_7292229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_7292229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292229 prefixEnd_7292229 := by exact prefixLift 7292229
  have htrace : WordTrace (prefixWord ++ tailWord_7292229) baseStart_7292229 baseEnd_7292229 := by
    simpa [prefixWord, tailWord_7292229, baseEnd_7292229] using wordTrace_append hprefix tailTrace_7292229
  have hstable : (prefixWord ++ tailWord_7292229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292229).length < 2 ^ (prefixWord ++ tailWord_7292229).sum := by decide
  have hdescent : baseEnd_7292229 < baseStart_7292229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292237 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7292237 : Nat := 118140960795 + 7292237 * 2 ^ 59
def prefixEnd_7292237 : Nat := 4983230072969 + 3 ^ 40 * 7292237 * 2
def baseEnd_7292237 : Nat := 3744422627500690822901119

theorem tailTrace_7292237 : CollatzResearch.WordTrace tailWord_7292237 prefixEnd_7292237 3744422627500690822901119 := by
  unfold tailWord_7292237
  simp only [CollatzResearch.WordTrace]
  refine ⟨265969733682478238772162965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177313155788318825848108643 265969733682478238772162965)
  ·
    refine ⟨12467331266366167442445139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265969733682478238772162965 12467331266366167442445139)
    ·
      refine ⟨18700996899549251163667709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467331266366167442445139 18700996899549251163667709)
      ·
        refine ⟨7012873837330969186375391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18700996899549251163667709 7012873837330969186375391)
        ·
          refine ⟨10519310755996453779563087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012873837330969186375391 10519310755996453779563087)
          ·
            refine ⟨15778966133994680669344631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10519310755996453779563087 15778966133994680669344631)
            ·
              refine ⟨23668449200992021004016947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15778966133994680669344631 23668449200992021004016947)
              ·
                refine ⟨35502673801488031506025421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23668449200992021004016947 35502673801488031506025421)
                ·
                  refine ⟨13313502675558011814759533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35502673801488031506025421 13313502675558011814759533)
                  ·
                    refine ⟨4992563503334254430534825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13313502675558011814759533 4992563503334254430534825)
                    ·
                      refine ⟨3744422627500690822901119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992563503334254430534825 3744422627500690822901119)
                      ·
                        rfl

theorem cell23_7292237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7292237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292237 prefixEnd_7292237 := by exact prefixLift 7292237
  have htrace : WordTrace (prefixWord ++ tailWord_7292237) baseStart_7292237 baseEnd_7292237 := by
    simpa [prefixWord, tailWord_7292237, baseEnd_7292237] using wordTrace_append hprefix tailTrace_7292237
  have hstable : (prefixWord ++ tailWord_7292237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292237).length < 2 ^ (prefixWord ++ tailWord_7292237).sum := by decide
  have hdescent : baseEnd_7292237 < baseStart_7292237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292273 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 5]
def baseStart_7292273 : Nat := 118140960795 + 7292273 * 2 ^ 59
def prefixEnd_7292273 : Nat := 4983230072969 + 3 ^ 40 * 7292273 * 2
def baseEnd_7292273 : Nat := 416049012533805853561217

theorem tailTrace_7292273 : CollatzResearch.WordTrace tailWord_7292273 prefixEnd_7292273 416049012533805853561217 := by
  unfold tailWord_7292273
  simp only [CollatzResearch.WordTrace]
  refine ⟨265971046710347816920473473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177314031140231877946982315 265971046710347816920473473)
  ·
    refine ⟨199478285032760862690355105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265971046710347816920473473 199478285032760862690355105)
    ·
      refine ⟨149608713774570647017766329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199478285032760862690355105 149608713774570647017766329)
      ·
        refine ⟨112206535330927985263324747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149608713774570647017766329 112206535330927985263324747)
        ·
          refine ⟨168309802996391977894987121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112206535330927985263324747 168309802996391977894987121)
          ·
            refine ⟨126232352247293983421240341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168309802996391977894987121 126232352247293983421240341)
            ·
              refine ⟨5917141511591905472870641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126232352247293983421240341 5917141511591905472870641)
              ·
                refine ⟨4437856133693929104652981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917141511591905472870641 4437856133693929104652981)
                ·
                  refine ⟨416049012533805853561217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437856133693929104652981 416049012533805853561217)
                  ·
                    rfl

theorem cell23_7292273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 5].length) (baseStart_7292273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292273 prefixEnd_7292273 := by exact prefixLift 7292273
  have htrace : WordTrace (prefixWord ++ tailWord_7292273) baseStart_7292273 baseEnd_7292273 := by
    simpa [prefixWord, tailWord_7292273, baseEnd_7292273] using wordTrace_append hprefix tailTrace_7292273
  have hstable : (prefixWord ++ tailWord_7292273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292273).length < 2 ^ (prefixWord ++ tailWord_7292273).sum := by decide
  have hdescent : baseEnd_7292273 < baseStart_7292273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292279 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_7292279 : Nat := 118140960795 + 7292279 * 2 ^ 59
def prefixEnd_7292279 : Nat := 4983230072969 + 3 ^ 40 * 7292279 * 2
def baseEnd_7292279 : Nat := 3744444193688179658575925

theorem tailTrace_7292279 : CollatzResearch.WordTrace tailWord_7292279 prefixEnd_7292279 3744444193688179658575925 := by
  unfold tailWord_7292279
  simp only [CollatzResearch.WordTrace]
  refine ⟨265971265548326079945191891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177314177032217386630127927 265971265548326079945191891)
  ·
    refine ⟨398956898322489119917787837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265971265548326079945191891 398956898322489119917787837)
    ·
      refine ⟨149608836870933419969170439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398956898322489119917787837 149608836870933419969170439)
      ·
        refine ⟨224413255306400129953755659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149608836870933419969170439 224413255306400129953755659)
        ·
          refine ⟨336619882959600194930633489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224413255306400129953755659 336619882959600194930633489)
          ·
            refine ⟨252464912219700146197975117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336619882959600194930633489 252464912219700146197975117)
            ·
              refine ⟨94674342082387554824240669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252464912219700146197975117 94674342082387554824240669)
              ·
                refine ⟨35502878280895333059090251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94674342082387554824240669 35502878280895333059090251)
                ·
                  refine ⟨53254317421342999588635377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35502878280895333059090251 53254317421342999588635377)
                  ·
                    refine ⟨39940738066007249691476533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53254317421342999588635377 39940738066007249691476533)
                    ·
                      refine ⟨3744444193688179658575925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39940738066007249691476533 3744444193688179658575925)
                      ·
                        rfl

theorem cell23_7292279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_7292279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292279 prefixEnd_7292279 := by exact prefixLift 7292279
  have htrace : WordTrace (prefixWord ++ tailWord_7292279) baseStart_7292279 baseEnd_7292279 := by
    simpa [prefixWord, tailWord_7292279, baseEnd_7292279] using wordTrace_append hprefix tailTrace_7292279
  have hstable : (prefixWord ++ tailWord_7292279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292279).length < 2 ^ (prefixWord ++ tailWord_7292279).sum := by decide
  have hdescent : baseEnd_7292279 < baseStart_7292279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292397 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 6]
def baseStart_7292397 : Nat := 118140960795 + 7292397 * 2 ^ 59
def prefixEnd_7292397 : Nat := 4983230072969 + 3 ^ 40 * 7292397 * 2
def baseEnd_7292397 : Nat := 416056087156156688544487

theorem tailTrace_7292397 : CollatzResearch.WordTrace tailWord_7292397 prefixEnd_7292397 416056087156156688544487 := by
  unfold tailWord_7292397
  simp only [CollatzResearch.WordTrace]
  refine ⟨265975569361898586097987445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177317046241265724065324963 265975569361898586097987445)
  ·
    refine ⟨24935209627677992446686323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265975569361898586097987445 24935209627677992446686323)
    ·
      refine ⟨37402814441516988670029485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24935209627677992446686323 37402814441516988670029485)
      ·
        refine ⟨14026055415568870751261057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37402814441516988670029485 14026055415568870751261057)
        ·
          refine ⟨10519541561676653063445793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026055415568870751261057 10519541561676653063445793)
          ·
            refine ⟨7889656171257489797584345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519541561676653063445793 7889656171257489797584345)
            ·
              refine ⟨5917242128443117348188259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889656171257489797584345 5917242128443117348188259)
              ·
                refine ⟨8875863192664676022282389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917242128443117348188259 8875863192664676022282389)
                ·
                  refine ⟨416056087156156688544487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8875863192664676022282389 416056087156156688544487)
                  ·
                    rfl

theorem cell23_7292397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_7292397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292397 prefixEnd_7292397 := by exact prefixLift 7292397
  have htrace : WordTrace (prefixWord ++ tailWord_7292397) baseStart_7292397 baseEnd_7292397 := by
    simpa [prefixWord, tailWord_7292397, baseEnd_7292397] using wordTrace_append hprefix tailTrace_7292397
  have hstable : (prefixWord ++ tailWord_7292397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292397).length < 2 ^ (prefixWord ++ tailWord_7292397).sum := by decide
  have hdescent : baseEnd_7292397 < baseStart_7292397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292413 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_7292413 : Nat := 118140960795 + 7292413 * 2 ^ 59
def prefixEnd_7292413 : Nat := 4983230072969 + 3 ^ 40 * 7292413 * 2
def baseEnd_7292413 : Nat := 3744513000095882134300309

theorem tailTrace_7292413 : CollatzResearch.WordTrace tailWord_7292413 prefixEnd_7292413 3744513000095882134300309 := by
  unfold tailWord_7292413
  simp only [CollatzResearch.WordTrace]
  refine ⟨265976152929840620830569893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177317435286560413887046595 265976152929840620830569893)
  ·
    refine ⟨49870528674345116405731855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265976152929840620830569893 49870528674345116405731855)
    ·
      refine ⟨74805793011517674608597783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49870528674345116405731855 74805793011517674608597783)
      ·
        refine ⟨112208689517276511912896675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74805793011517674608597783 112208689517276511912896675)
        ·
          refine ⟨168313034275914767869345013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112208689517276511912896675 168313034275914767869345013)
          ·
            refine ⟨15779346963367009487751095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168313034275914767869345013 15779346963367009487751095)
            ·
              refine ⟨23669020445050514231626643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15779346963367009487751095 23669020445050514231626643)
              ·
                refine ⟨35503530667575771347439965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23669020445050514231626643 35503530667575771347439965)
                ·
                  refine ⟨13313824000340914255289987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35503530667575771347439965 13313824000340914255289987)
                  ·
                    refine ⟨19970736000511371382934981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13313824000340914255289987 19970736000511371382934981)
                    ·
                      refine ⟨3744513000095882134300309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19970736000511371382934981 3744513000095882134300309)
                      ·
                        rfl

theorem cell23_7292413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_7292413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292413 prefixEnd_7292413 := by exact prefixLift 7292413
  have htrace : WordTrace (prefixWord ++ tailWord_7292413) baseStart_7292413 baseEnd_7292413 := by
    simpa [prefixWord, tailWord_7292413, baseEnd_7292413] using wordTrace_append hprefix tailTrace_7292413
  have hstable : (prefixWord ++ tailWord_7292413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292413).length < 2 ^ (prefixWord ++ tailWord_7292413).sum := by decide
  have hdescent : baseEnd_7292413 < baseStart_7292413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292417 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_7292417 : Nat := 118140960795 + 7292417 * 2 ^ 59
def prefixEnd_7292417 : Nat := 4983230072969 + 3 ^ 40 * 7292417 * 2
def baseEnd_7292417 : Nat := 3744515054018500118650291

theorem tailTrace_7292417 : CollatzResearch.WordTrace tailWord_7292417 prefixEnd_7292417 3744515054018500118650291 := by
  unfold tailWord_7292417
  simp only [CollatzResearch.WordTrace]
  refine ⟨265976298821826129513715505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177317532547884086342477003 265976298821826129513715505)
  ·
    refine ⟨199482224116369597135286629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265976298821826129513715505 199482224116369597135286629)
    ·
      refine ⟨37402917021819299462866243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199482224116369597135286629 37402917021819299462866243)
      ·
        refine ⟨56104375532728949194299365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37402917021819299462866243 56104375532728949194299365)
        ·
          refine ⟨10519570412386677973931131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56104375532728949194299365 10519570412386677973931131)
          ·
            refine ⟨15779355618580016960896697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10519570412386677973931131 15779355618580016960896697)
            ·
              refine ⟨11834516713935012720672523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15779355618580016960896697 11834516713935012720672523)
              ·
                refine ⟨17751775070902519081008785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834516713935012720672523 17751775070902519081008785)
                ·
                  refine ⟨13313831303176889310756589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17751775070902519081008785 13313831303176889310756589)
                  ·
                    refine ⟨4992686738691333491533721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13313831303176889310756589 4992686738691333491533721)
                    ·
                      refine ⟨3744515054018500118650291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992686738691333491533721 3744515054018500118650291)
                      ·
                        rfl

theorem cell23_7292417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_7292417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292417 prefixEnd_7292417 := by exact prefixLift 7292417
  have htrace : WordTrace (prefixWord ++ tailWord_7292417) baseStart_7292417 baseEnd_7292417 := by
    simpa [prefixWord, tailWord_7292417, baseEnd_7292417] using wordTrace_append hprefix tailTrace_7292417
  have hstable : (prefixWord ++ tailWord_7292417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292417).length < 2 ^ (prefixWord ++ tailWord_7292417).sum := by decide
  have hdescent : baseEnd_7292417 < baseStart_7292417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292423 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 6]
def baseStart_7292423 : Nat := 118140960795 + 7292423 * 2 ^ 59
def prefixEnd_7292423 : Nat := 4983230072969 + 3 ^ 40 * 7292423 * 2
def baseEnd_7292423 : Nat := 1248172711634142365058421

theorem tailTrace_7292423 : CollatzResearch.WordTrace tailWord_7292423 prefixEnd_7292423 1248172711634142365058421 := by
  unfold tailWord_7292423
  simp only [CollatzResearch.WordTrace]
  refine ⟨265976517659804392538433923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177317678439869595025622615 265976517659804392538433923)
  ·
    refine ⟨398964776489706588807650885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265976517659804392538433923 398964776489706588807650885)
    ·
      refine ⟨74805895591819985401434541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398964776489706588807650885 74805895591819985401434541)
      ·
        refine ⟨28052210846932494525537953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74805895591819985401434541 28052210846932494525537953)
        ·
          refine ⟨21039158135199370894153465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28052210846932494525537953 21039158135199370894153465)
          ·
            refine ⟨15779368601399528170615099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21039158135199370894153465 15779368601399528170615099)
            ·
              refine ⟨23669052902099292255922649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15779368601399528170615099 23669052902099292255922649)
              ·
                refine ⟨17751789676574469191941987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23669052902099292255922649 17751789676574469191941987)
                ·
                  refine ⟨26627684514861703787912981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17751789676574469191941987 26627684514861703787912981)
                  ·
                    refine ⟨1248172711634142365058421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26627684514861703787912981 1248172711634142365058421)
                    ·
                      rfl

theorem cell23_7292423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_7292423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292423 prefixEnd_7292423 := by exact prefixLift 7292423
  have htrace : WordTrace (prefixWord ++ tailWord_7292423) baseStart_7292423 baseEnd_7292423 := by
    simpa [prefixWord, tailWord_7292423, baseEnd_7292423] using wordTrace_append hprefix tailTrace_7292423
  have hstable : (prefixWord ++ tailWord_7292423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292423).length < 2 ^ (prefixWord ++ tailWord_7292423).sum := by decide
  have hdescent : baseEnd_7292423 < baseStart_7292423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292466 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_7292466 : Nat := 118140960795 + 7292466 * 2 ^ 59
def prefixEnd_7292466 : Nat := 4983230072969 + 3 ^ 40 * 7292466 * 2
def baseEnd_7292466 : Nat := 1248180071523523475645855

theorem tailTrace_7292466 : CollatzResearch.WordTrace tailWord_7292466 prefixEnd_7292466 1248180071523523475645855 := by
  unfold tailWord_7292466
  simp only [CollatzResearch.WordTrace]
  refine ⟨66494521499662152720562313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177318723999099073921499501 66494521499662152720562313)
  ·
    refine ⟨49870891124746614540421735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66494521499662152720562313 49870891124746614540421735)
    ·
      refine ⟨74806336687119921810632603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49870891124746614540421735 74806336687119921810632603)
      ·
        refine ⟨112209505030679882715948905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74806336687119921810632603 112209505030679882715948905)
        ·
          refine ⟨84157128773009912036961679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112209505030679882715948905 84157128773009912036961679)
          ·
            refine ⟨126235693159514868055442519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84157128773009912036961679 126235693159514868055442519)
            ·
              refine ⟨189353539739272302083163779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126235693159514868055442519 189353539739272302083163779)
              ·
                refine ⟨284030309608908453124745669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189353539739272302083163779 284030309608908453124745669)
                ·
                  refine ⟨53255683051670334960889813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284030309608908453124745669 53255683051670334960889813)
                  ·
                    refine ⟨1248180071523523475645855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53255683051670334960889813 1248180071523523475645855)
                    ·
                      rfl

theorem cell23_7292466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_7292466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292466 prefixEnd_7292466 := by exact prefixLift 7292466
  have htrace : WordTrace (prefixWord ++ tailWord_7292466) baseStart_7292466 baseEnd_7292466 := by
    simpa [prefixWord, tailWord_7292466, baseEnd_7292466] using wordTrace_append hprefix tailTrace_7292466
  have hstable : (prefixWord ++ tailWord_7292466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292466).length < 2 ^ (prefixWord ++ tailWord_7292466).sum := by decide
  have hdescent : baseEnd_7292466 < baseStart_7292466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292496 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_7292496 : Nat := 118140960795 + 7292496 * 2 ^ 59
def prefixEnd_7292496 : Nat := 4983230072969 + 3 ^ 40 * 7292496 * 2
def baseEnd_7292496 : Nat := 1248185206330068436520809

theorem tailTrace_7292496 : CollatzResearch.WordTrace tailWord_7292496 prefixEnd_7292496 1248185206330068436520809 := by
  unfold tailWord_7292496
  simp only [CollatzResearch.WordTrace]
  refine ⟨132989590094269963002920671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177319453459026617337227561 132989590094269963002920671)
  ·
    refine ⟨199484385141404944504381007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132989590094269963002920671 199484385141404944504381007)
    ·
      refine ⟨299226577712107416756571511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199484385141404944504381007 299226577712107416756571511)
      ·
        refine ⟨448839866568161125134857267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299226577712107416756571511 448839866568161125134857267)
        ·
          refine ⟨673259799852241687702285901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448839866568161125134857267 673259799852241687702285901)
          ·
            refine ⟨252472424944590632888357213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673259799852241687702285901 252472424944590632888357213)
            ·
              refine ⟨94677159354221487333133955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252472424944590632888357213 94677159354221487333133955)
              ·
                refine ⟨142015739031332230999700933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94677159354221487333133955 142015739031332230999700933)
                ·
                  refine ⟨26627951068374793312443925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142015739031332230999700933 26627951068374793312443925)
                  ·
                    refine ⟨1248185206330068436520809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26627951068374793312443925 1248185206330068436520809)
                    ·
                      rfl

theorem cell23_7292496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_7292496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292496 prefixEnd_7292496 := by exact prefixLift 7292496
  have htrace : WordTrace (prefixWord ++ tailWord_7292496) baseStart_7292496 baseEnd_7292496 := by
    simpa [prefixWord, tailWord_7292496, baseEnd_7292496] using wordTrace_append hprefix tailTrace_7292496
  have hstable : (prefixWord ++ tailWord_7292496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292496).length < 2 ^ (prefixWord ++ tailWord_7292496).sum := by decide
  have hdescent : baseEnd_7292496 < baseStart_7292496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292536 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_7292536 : Nat := 118140960795 + 7292536 * 2 ^ 59
def prefixEnd_7292536 : Nat := 4983230072969 + 3 ^ 40 * 7292536 * 2
def baseEnd_7292536 : Nat := 3744576158216385153062243

theorem tailTrace_7292536 : CollatzResearch.WordTrace tailWord_7292536 prefixEnd_7292536 3744576158216385153062243 := by
  unfold tailWord_7292536
  simp only [CollatzResearch.WordTrace]
  refine ⟨132990319554197506418648731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177320426072263341891531641 132990319554197506418648731)
  ·
    refine ⟨199485479331296259627973097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132990319554197506418648731 199485479331296259627973097)
    ·
      refine ⟨149614109498472194720979823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199485479331296259627973097 149614109498472194720979823)
      ·
        refine ⟨224421164247708292081469735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149614109498472194720979823 224421164247708292081469735)
        ·
          refine ⟨336631746371562438122204603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224421164247708292081469735 336631746371562438122204603)
          ·
            refine ⟨504947619557343657183306905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336631746371562438122204603 504947619557343657183306905)
            ·
              refine ⟨378710714668007742887480179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504947619557343657183306905 378710714668007742887480179)
              ·
                refine ⟨568066072002011614331220269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378710714668007742887480179 568066072002011614331220269)
                ·
                  refine ⟨213024777000754355374207601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568066072002011614331220269 213024777000754355374207601)
                  ·
                    refine ⟨159768582750565766530655701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213024777000754355374207601 159768582750565766530655701)
                    ·
                      refine ⟨3744576158216385153062243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159768582750565766530655701 3744576158216385153062243)
                      ·
                        rfl

theorem cell23_7292536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_7292536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292536 prefixEnd_7292536 := by exact prefixLift 7292536
  have htrace : WordTrace (prefixWord ++ tailWord_7292536) baseStart_7292536 baseEnd_7292536 := by
    simpa [prefixWord, tailWord_7292536, baseEnd_7292536] using wordTrace_append hprefix tailTrace_7292536
  have hstable : (prefixWord ++ tailWord_7292536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292536).length < 2 ^ (prefixWord ++ tailWord_7292536).sum := by decide
  have hdescent : baseEnd_7292536 < baseStart_7292536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292553 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_7292553 : Nat := 118140960795 + 7292553 * 2 ^ 59
def prefixEnd_7292553 : Nat := 4983230072969 + 3 ^ 40 * 7292553 * 2
def baseEnd_7292553 : Nat := 3744584887387511586549665

theorem tailTrace_7292553 : CollatzResearch.WordTrace tailWord_7292553 prefixEnd_7292553 3744584887387511586549665 := by
  unfold tailWord_7292553
  simp only [CollatzResearch.WordTrace]
  refine ⟨265981259149333424740666313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177320839432888949827110875 265981259149333424740666313)
  ·
    refine ⟨199485944362000068555499735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265981259149333424740666313 199485944362000068555499735)
    ·
      refine ⟨299228916543000102833249603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199485944362000068555499735 299228916543000102833249603)
      ·
        refine ⟨448843374814500154249874405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299228916543000102833249603 448843374814500154249874405)
        ·
          refine ⟨84158132777718778921851451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448843374814500154249874405 84158132777718778921851451)
          ·
            refine ⟨126237199166578168382777177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84158132777718778921851451 126237199166578168382777177)
            ·
              refine ⟨94677899374933626287082883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126237199166578168382777177 94677899374933626287082883)
              ·
                refine ⟨142016849062400439430624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94677899374933626287082883 142016849062400439430624325)
                ·
                  refine ⟨26628159199200082393242061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142016849062400439430624325 26628159199200082393242061)
                  ·
                    refine ⟨9985559699700030897465773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26628159199200082393242061 9985559699700030897465773)
                    ·
                      refine ⟨3744584887387511586549665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985559699700030897465773 3744584887387511586549665)
                      ·
                        rfl

theorem cell23_7292553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_7292553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292553 prefixEnd_7292553 := by exact prefixLift 7292553
  have htrace : WordTrace (prefixWord ++ tailWord_7292553) baseStart_7292553 baseEnd_7292553 := by
    simpa [prefixWord, tailWord_7292553, baseEnd_7292553] using wordTrace_append hprefix tailTrace_7292553
  have hstable : (prefixWord ++ tailWord_7292553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292553).length < 2 ^ (prefixWord ++ tailWord_7292553).sum := by decide
  have hdescent : baseEnd_7292553 < baseStart_7292553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292573 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_7292573 : Nat := 118140960795 + 7292573 * 2 ^ 59
def prefixEnd_7292573 : Nat := 4983230072969 + 3 ^ 40 * 7292573 * 2
def baseEnd_7292573 : Nat := 1248198385666867169433191

theorem tailTrace_7292573 : CollatzResearch.WordTrace tailWord_7292573 prefixEnd_7292573 1248198385666867169433191 := by
  unfold tailWord_7292573
  simp only [CollatzResearch.WordTrace]
  refine ⟨265981988609260968156394373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177321325739507312104262915 265981988609260968156394373)
  ·
    refine ⟨49871622864236431529323945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265981988609260968156394373 49871622864236431529323945)
    ·
      refine ⟨37403717148177323646992959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49871622864236431529323945 37403717148177323646992959)
      ·
        refine ⟨56105575722265985470489439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37403717148177323646992959 56105575722265985470489439)
        ·
          refine ⟨84158363583398978205734159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56105575722265985470489439 84158363583398978205734159)
          ·
            refine ⟨126237545375098467308601239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84158363583398978205734159 126237545375098467308601239)
            ·
              refine ⟨189356318062647700962901859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126237545375098467308601239 189356318062647700962901859)
              ·
                refine ⟨284034477093971551444352789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189356318062647700962901859 284034477093971551444352789)
                ·
                  refine ⟨13314116113779916473954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284034477093971551444352789 13314116113779916473954037)
                  ·
                    refine ⟨1248198385666867169433191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13314116113779916473954037 1248198385666867169433191)
                    ·
                      rfl

theorem cell23_7292573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_7292573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292573 prefixEnd_7292573 := by exact prefixLift 7292573
  have htrace : WordTrace (prefixWord ++ tailWord_7292573) baseStart_7292573 baseEnd_7292573 := by
    simpa [prefixWord, tailWord_7292573, baseEnd_7292573] using wordTrace_append hprefix tailTrace_7292573
  have hstable : (prefixWord ++ tailWord_7292573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292573).length < 2 ^ (prefixWord ++ tailWord_7292573).sum := by decide
  have hdescent : baseEnd_7292573 < baseStart_7292573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292654 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7292654 : Nat := 118140960795 + 7292654 * 2 ^ 59
def prefixEnd_7292654 : Nat := 4983230072969 + 3 ^ 40 * 7292654 * 2
def baseEnd_7292654 : Nat := 1248212249644538563795567

theorem tailTrace_7292654 : CollatzResearch.WordTrace tailWord_7292654 prefixEnd_7292654 1248212249644538563795567 := by
  unfold tailWord_7292654
  simp only [CollatzResearch.WordTrace]
  refine ⟨33248117865245939873761627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177323295281311679326728677 33248117865245939873761627)
  ·
    refine ⟨49872176797868909810642441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33248117865245939873761627 49872176797868909810642441)
    ·
      refine ⟨37404132598401682357981831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49872176797868909810642441 37404132598401682357981831)
      ·
        refine ⟨56106198897602523536972747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37404132598401682357981831 56106198897602523536972747)
        ·
          refine ⟨84159298346403785305459121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56106198897602523536972747 84159298346403785305459121)
          ·
            refine ⟨63119473759802838979094341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84159298346403785305459121 63119473759802838979094341)
            ·
              refine ⟨11834901329963032308580189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63119473759802838979094341 11834901329963032308580189)
              ·
                refine ⟨4438087998736137115717571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11834901329963032308580189 4438087998736137115717571)
                ·
                  refine ⟨6657131998104205673576357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438087998736137115717571 6657131998104205673576357)
                  ·
                    refine ⟨1248212249644538563795567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657131998104205673576357 1248212249644538563795567)
                    ·
                      rfl

theorem cell23_7292654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7292654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292654 prefixEnd_7292654 := by exact prefixLift 7292654
  have htrace : WordTrace (prefixWord ++ tailWord_7292654) baseStart_7292654 baseEnd_7292654 := by
    simpa [prefixWord, tailWord_7292654, baseEnd_7292654] using wordTrace_append hprefix tailTrace_7292654
  have hstable : (prefixWord ++ tailWord_7292654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292654).length < 2 ^ (prefixWord ++ tailWord_7292654).sum := by decide
  have hdescent : baseEnd_7292654 < baseStart_7292654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292713 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_7292713 : Nat := 118140960795 + 7292713 * 2 ^ 59
def prefixEnd_7292713 : Nat := 4983230072969 + 3 ^ 40 * 7292713 * 2
def baseEnd_7292713 : Nat := 3744667044292230960548929

theorem tailTrace_7292713 : CollatzResearch.WordTrace tailWord_7292713 prefixEnd_7292713 3744667044292230960548929 := by
  unfold tailWord_7292713
  simp only [CollatzResearch.WordTrace]
  refine ⟨265987094828753772066490793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177324729885835848044327195 265987094828753772066490793)
  ·
    refine ⟨199490321121565329049868095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265987094828753772066490793 199490321121565329049868095)
    ·
      refine ⟨299235481682347993574802143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199490321121565329049868095 299235481682347993574802143)
      ·
        refine ⟨448853222523521990362203215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299235481682347993574802143 448853222523521990362203215)
        ·
          refine ⟨673279833785282985543304823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448853222523521990362203215 673279833785282985543304823)
          ·
            refine ⟨1009919750677924478314957235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673279833785282985543304823 1009919750677924478314957235)
            ·
              refine ⟨1514879626016886717472435853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009919750677924478314957235 1514879626016886717472435853)
              ·
                refine ⟨568079859756332519052163445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514879626016886717472435853 568079859756332519052163445)
                ·
                  refine ⟨53257486852156173661140323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568079859756332519052163445 53257486852156173661140323)
                  ·
                    refine ⟨79886230278234260491710485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53257486852156173661140323 79886230278234260491710485)
                    ·
                      refine ⟨3744667044292230960548929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79886230278234260491710485 3744667044292230960548929)
                      ·
                        rfl

theorem cell23_7292713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_7292713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292713 prefixEnd_7292713 := by exact prefixLift 7292713
  have htrace : WordTrace (prefixWord ++ tailWord_7292713) baseStart_7292713 baseEnd_7292713 := by
    simpa [prefixWord, tailWord_7292713, baseEnd_7292713] using wordTrace_append hprefix tailTrace_7292713
  have hstable : (prefixWord ++ tailWord_7292713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292713).length < 2 ^ (prefixWord ++ tailWord_7292713).sum := by decide
  have hdescent : baseEnd_7292713 < baseStart_7292713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292720 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_7292720 : Nat := 118140960795 + 7292720 * 2 ^ 59
def prefixEnd_7292720 : Nat := 4983230072969 + 3 ^ 40 * 7292720 * 2
def baseEnd_7292720 : Nat := 3744670638656812433161397

theorem tailTrace_7292720 : CollatzResearch.WordTrace tailWord_7292720 prefixEnd_7292720 3744670638656812433161397 := by
  unfold tailWord_7292720
  simp only [CollatzResearch.WordTrace]
  refine ⟨132993675069864206130997807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177324900093152274841330409 132993675069864206130997807)
  ·
    refine ⟨199490512604796309196496711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132993675069864206130997807 199490512604796309196496711)
    ·
      refine ⟨299235768907194463794745067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199490512604796309196496711 299235768907194463794745067)
      ·
        refine ⟨448853653360791695692117601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299235768907194463794745067 448853653360791695692117601)
        ·
          refine ⟨336640240020593771769088201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448853653360791695692117601 336640240020593771769088201)
          ·
            refine ⟨252480180015445328826816151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336640240020593771769088201 252480180015445328826816151)
            ·
              refine ⟨378720270023167993240224227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252480180015445328826816151 378720270023167993240224227)
              ·
                refine ⟨568080405034751989860336341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378720270023167993240224227 568080405034751989860336341)
                ·
                  refine ⟨13314384493001999762351633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 568080405034751989860336341 13314384493001999762351633)
                  ·
                    refine ⟨9985788369751499821763725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314384493001999762351633 9985788369751499821763725)
                    ·
                      refine ⟨3744670638656812433161397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985788369751499821763725 3744670638656812433161397)
                      ·
                        rfl

theorem cell23_7292720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_7292720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292720 prefixEnd_7292720 := by exact prefixLift 7292720
  have htrace : WordTrace (prefixWord ++ tailWord_7292720) baseStart_7292720 baseEnd_7292720 := by
    simpa [prefixWord, tailWord_7292720, baseEnd_7292720] using wordTrace_append hprefix tailTrace_7292720
  have hstable : (prefixWord ++ tailWord_7292720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292720).length < 2 ^ (prefixWord ++ tailWord_7292720).sum := by decide
  have hdescent : baseEnd_7292720 < baseStart_7292720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292730 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_7292730 : Nat := 118140960795 + 7292730 * 2 ^ 59
def prefixEnd_7292730 : Nat := 4983230072969 + 3 ^ 40 * 7292730 * 2
def baseEnd_7292730 : Nat := 3744675773463357394036351

theorem tailTrace_7292730 : CollatzResearch.WordTrace tailWord_7292730 prefixEnd_7292730 3744675773463357394036351 := by
  unfold tailWord_7292730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66496928717423045992464911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177325143246461455979906429 66496928717423045992464911)
  ·
    refine ⟨99745393076134568988697367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66496928717423045992464911 99745393076134568988697367)
    ·
      refine ⟨149618089614201853483046051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99745393076134568988697367 149618089614201853483046051)
      ·
        refine ⟨224427134421302780224569077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149618089614201853483046051 224427134421302780224569077)
        ·
          refine ⟨21040043851997135646053351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224427134421302780224569077 21040043851997135646053351)
          ·
            refine ⟨31560065777995703469080027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21040043851997135646053351 31560065777995703469080027)
            ·
              refine ⟨47340098666993555203620041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31560065777995703469080027 47340098666993555203620041)
              ·
                refine ⟨35505074000245166402715031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47340098666993555203620041 35505074000245166402715031)
                ·
                  refine ⟨53257611000367749604072547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35505074000245166402715031 53257611000367749604072547)
                  ·
                    refine ⟨79886416500551624406108821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53257611000367749604072547 79886416500551624406108821)
                    ·
                      refine ⟨3744675773463357394036351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79886416500551624406108821 3744675773463357394036351)
                      ·
                        rfl

theorem cell23_7292730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_7292730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292730 prefixEnd_7292730 := by exact prefixLift 7292730
  have htrace : WordTrace (prefixWord ++ tailWord_7292730) baseStart_7292730 baseEnd_7292730 := by
    simpa [prefixWord, tailWord_7292730, baseEnd_7292730] using wordTrace_append hprefix tailTrace_7292730
  have hstable : (prefixWord ++ tailWord_7292730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292730).length < 2 ^ (prefixWord ++ tailWord_7292730).sum := by decide
  have hdescent : baseEnd_7292730 < baseStart_7292730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292744 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_7292744 : Nat := 118140960795 + 7292744 * 2 ^ 59
def prefixEnd_7292744 : Nat := 4983230072969 + 3 ^ 40 * 7292744 * 2
def baseEnd_7292744 : Nat := 1248227654064173446420429

theorem tailTrace_7292744 : CollatzResearch.WordTrace tailWord_7292744 prefixEnd_7292744 1248227654064173446420429 := by
  unfold tailWord_7292744
  simp only [CollatzResearch.WordTrace]
  refine ⟨132994112745820732180434643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177325483661094309573912857 132994112745820732180434643)
  ·
    refine ⟨199491169118731098270651965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132994112745820732180434643 199491169118731098270651965)
    ·
      refine ⟨74809188419524161851494487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199491169118731098270651965 74809188419524161851494487)
      ·
        refine ⟨112213782629286242777241731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74809188419524161851494487 112213782629286242777241731)
        ·
          refine ⟨168320673943929364165862597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112213782629286242777241731 168320673943929364165862597)
          ·
            refine ⟨31560126364486755781099237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168320673943929364165862597 31560126364486755781099237)
            ·
              refine ⟨5917523693341266708956107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31560126364486755781099237 5917523693341266708956107)
              ·
                refine ⟨8876285540011900063434161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917523693341266708956107 8876285540011900063434161)
                ·
                  refine ⟨6657214155008925047575621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876285540011900063434161 6657214155008925047575621)
                  ·
                    refine ⟨1248227654064173446420429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657214155008925047575621 1248227654064173446420429)
                    ·
                      rfl

theorem cell23_7292744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_7292744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292744 prefixEnd_7292744 := by exact prefixLift 7292744
  have htrace : WordTrace (prefixWord ++ tailWord_7292744) baseStart_7292744 baseEnd_7292744 := by
    simpa [prefixWord, tailWord_7292744, baseEnd_7292744] using wordTrace_append hprefix tailTrace_7292744
  have hstable : (prefixWord ++ tailWord_7292744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292744).length < 2 ^ (prefixWord ++ tailWord_7292744).sum := by decide
  have hdescent : baseEnd_7292744 < baseStart_7292744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292754 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_7292754 : Nat := 118140960795 + 7292754 * 2 ^ 59
def prefixEnd_7292754 : Nat := 4983230072969 + 3 ^ 40 * 7292754 * 2
def baseEnd_7292754 : Nat := 3744688096999065300136241

theorem tailTrace_7292754 : CollatzResearch.WordTrace tailWord_7292754 prefixEnd_7292754 3744688096999065300136241 := by
  unfold tailWord_7292754
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497147555401309017183329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177325726814403490712488877 66497147555401309017183329)
  ·
    refine ⟨49872860666550981762887497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66497147555401309017183329 49872860666550981762887497)
    ·
      refine ⟨37404645499913236322165623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49872860666550981762887497 37404645499913236322165623)
      ·
        refine ⟨56106968249869854483248435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37404645499913236322165623 56106968249869854483248435)
        ·
          refine ⟨84160452374804781724872653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56106968249869854483248435 84160452374804781724872653)
          ·
            refine ⟨31560169640551793146827245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84160452374804781724872653 31560169640551793146827245)
            ·
              refine ⟨11835063615206922430060217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31560169640551793146827245 11835063615206922430060217)
              ·
                refine ⟨8876297711405191822545163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835063615206922430060217 8876297711405191822545163)
                ·
                  refine ⟨13314446567107787733817745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876297711405191822545163 13314446567107787733817745)
                  ·
                    refine ⟨9985834925330840800363309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314446567107787733817745 9985834925330840800363309)
                    ·
                      refine ⟨3744688096999065300136241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985834925330840800363309 3744688096999065300136241)
                      ·
                        rfl

theorem cell23_7292754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_7292754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292754 prefixEnd_7292754 := by exact prefixLift 7292754
  have htrace : WordTrace (prefixWord ++ tailWord_7292754) baseStart_7292754 baseEnd_7292754 := by
    simpa [prefixWord, tailWord_7292754, baseEnd_7292754] using wordTrace_append hprefix tailTrace_7292754
  have hstable : (prefixWord ++ tailWord_7292754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292754).length < 2 ^ (prefixWord ++ tailWord_7292754).sum := by decide
  have hdescent : baseEnd_7292754 < baseStart_7292754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292764 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7292764 : Nat := 118140960795 + 7292764 * 2 ^ 59
def prefixEnd_7292764 : Nat := 4983230072969 + 3 ^ 40 * 7292764 * 2
def baseEnd_7292764 : Nat := 3744693231805610261011195

theorem tailTrace_7292764 : CollatzResearch.WordTrace tailWord_7292764 prefixEnd_7292764 3744693231805610261011195 := by
  unfold tailWord_7292764
  simp only [CollatzResearch.WordTrace]
  refine ⟨132994477475784503888298673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177325969967712671851064897 132994477475784503888298673)
  ·
    refine ⟨99745858106838377916224005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132994477475784503888298673 99745858106838377916224005)
    ·
      refine ⟨18702348395032195859292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99745858106838377916224005 18702348395032195859292001)
      ·
        refine ⟨14026761296274146894469001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18702348395032195859292001 14026761296274146894469001)
        ·
          refine ⟨10520070972205610170851751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026761296274146894469001 10520070972205610170851751)
          ·
            refine ⟨15780106458308415256277627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520070972205610170851751 15780106458308415256277627)
            ·
              refine ⟨23670159687462622884416441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15780106458308415256277627 23670159687462622884416441)
              ·
                refine ⟨17752619765596967163312331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23670159687462622884416441 17752619765596967163312331)
                ·
                  refine ⟨26628929648395450744968497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17752619765596967163312331 26628929648395450744968497)
                  ·
                    refine ⟨19971697236296588058726373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26628929648395450744968497 19971697236296588058726373)
                    ·
                      refine ⟨3744693231805610261011195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19971697236296588058726373 3744693231805610261011195)
                      ·
                        rfl

theorem cell23_7292764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7292764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292764 prefixEnd_7292764 := by exact prefixLift 7292764
  have htrace : WordTrace (prefixWord ++ tailWord_7292764) baseStart_7292764 baseEnd_7292764 := by
    simpa [prefixWord, tailWord_7292764, baseEnd_7292764] using wordTrace_append hprefix tailTrace_7292764
  have hstable : (prefixWord ++ tailWord_7292764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292764).length < 2 ^ (prefixWord ++ tailWord_7292764).sum := by decide
  have hdescent : baseEnd_7292764 < baseStart_7292764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292767 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_7292767 : Nat := 118140960795 + 7292767 * 2 ^ 59
def prefixEnd_7292767 : Nat := 4983230072969 + 3 ^ 40 * 7292767 * 2
def baseEnd_7292767 : Nat := 3744694772247573749273681

theorem tailTrace_7292767 : CollatzResearch.WordTrace tailWord_7292767 prefixEnd_7292767 3744694772247573749273681 := by
  unfold tailWord_7292767
  simp only [CollatzResearch.WordTrace]
  refine ⟨265989064370558139288956555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177326042913705426192637703 265989064370558139288956555)
  ·
    refine ⟨398983596555837208933434833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265989064370558139288956555 398983596555837208933434833)
    ·
      refine ⟨299237697416877906700076125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398983596555837208933434833 299237697416877906700076125)
      ·
        refine ⟨112214136531329215012528547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299237697416877906700076125 112214136531329215012528547)
        ·
          refine ⟨168321204796993822518792821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112214136531329215012528547 168321204796993822518792821)
          ·
            refine ⟨15780112949718170861136827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168321204796993822518792821 15780112949718170861136827)
            ·
              refine ⟨23670169424577256291705241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15780112949718170861136827 23670169424577256291705241)
              ·
                refine ⟨17752627068432942218778931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23670169424577256291705241 17752627068432942218778931)
                ·
                  refine ⟨26628940602649413328168397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17752627068432942218778931 26628940602649413328168397)
                  ·
                    refine ⟨9985852725993529998063149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26628940602649413328168397 9985852725993529998063149)
                    ·
                      refine ⟨3744694772247573749273681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985852725993529998063149 3744694772247573749273681)
                      ·
                        rfl

theorem cell23_7292767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_7292767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292767 prefixEnd_7292767 := by exact prefixLift 7292767
  have htrace : WordTrace (prefixWord ++ tailWord_7292767) baseStart_7292767 baseEnd_7292767 := by
    simpa [prefixWord, tailWord_7292767, baseEnd_7292767] using wordTrace_append hprefix tailTrace_7292767
  have hstable : (prefixWord ++ tailWord_7292767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292767).length < 2 ^ (prefixWord ++ tailWord_7292767).sum := by decide
  have hdescent : baseEnd_7292767 < baseStart_7292767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292771 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 1, 2, 3]
def baseStart_7292771 : Nat := 118140960795 + 7292771 * 2 ^ 59
def prefixEnd_7292771 : Nat := 4983230072969 + 3 ^ 40 * 7292771 * 2
def baseEnd_7292771 : Nat := 3744696826170191733623663

theorem tailTrace_7292771 : CollatzResearch.WordTrace tailWord_7292771 prefixEnd_7292771 3744696826170191733623663 := by
  unfold tailWord_7292771
  simp only [CollatzResearch.WordTrace]
  refine ⟨265989210262543647972102167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177326140175029098648068111 265989210262543647972102167)
  ·
    refine ⟨398983815393815471958153251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265989210262543647972102167 398983815393815471958153251)
    ·
      refine ⟨598475723090723207937229877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398983815393815471958153251 598475723090723207937229877)
      ·
        refine ⟨56107099039755300744115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598475723090723207937229877 56107099039755300744115301)
        ·
          refine ⟨10520081069954118889521619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56107099039755300744115301 10520081069954118889521619)
          ·
            refine ⟨15780121604931178334282429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520081069954118889521619 15780121604931178334282429)
            ·
              refine ⟨5917545601849191875355911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15780121604931178334282429 5917545601849191875355911)
              ·
                refine ⟨8876318402773787813033867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917545601849191875355911 8876318402773787813033867)
                ·
                  refine ⟨13314477604160681719550801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876318402773787813033867 13314477604160681719550801)
                  ·
                    refine ⟨9985858203120511289663101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314477604160681719550801 9985858203120511289663101)
                    ·
                      refine ⟨3744696826170191733623663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985858203120511289663101 3744696826170191733623663)
                      ·
                        rfl

theorem cell23_7292771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_7292771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292771 prefixEnd_7292771 := by exact prefixLift 7292771
  have htrace : WordTrace (prefixWord ++ tailWord_7292771) baseStart_7292771 baseEnd_7292771 := by
    simpa [prefixWord, tailWord_7292771, baseEnd_7292771] using wordTrace_append hprefix tailTrace_7292771
  have hstable : (prefixWord ++ tailWord_7292771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292771).length < 2 ^ (prefixWord ++ tailWord_7292771).sum := by decide
  have hdescent : baseEnd_7292771 < baseStart_7292771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292800 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_7292800 : Nat := 118140960795 + 7292800 * 2 ^ 59
def prefixEnd_7292800 : Nat := 4983230072969 + 3 ^ 40 * 7292800 * 2
def baseEnd_7292800 : Nat := 1248237239036390706720343

theorem tailTrace_7292800 : CollatzResearch.WordTrace tailWord_7292800 prefixEnd_7292800 1248237239036390706720343 := by
  unfold tailWord_7292800
  simp only [CollatzResearch.WordTrace]
  refine ⟨132995133989719292962453927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177326845319625723949938569 132995133989719292962453927)
  ·
    refine ⟨199492700984578939443680891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132995133989719292962453927 199492700984578939443680891)
    ·
      refine ⟨299239051476868409165521337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199492700984578939443680891 299239051476868409165521337)
      ·
        refine ⟨224429288607651306874141003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299239051476868409165521337 224429288607651306874141003)
        ·
          refine ⟨336643932911476960311211505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224429288607651306874141003 336643932911476960311211505)
          ·
            refine ⟨252482949683607720233408629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336643932911476960311211505 252482949683607720233408629)
            ·
              refine ⟨23670276532838223771882059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252482949683607720233408629 23670276532838223771882059)
              ·
                refine ⟨35505414799257335657823089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23670276532838223771882059 35505414799257335657823089)
                ·
                  refine ⟨26629061099443001743367317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35505414799257335657823089 26629061099443001743367317)
                  ·
                    refine ⟨1248237239036390706720343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26629061099443001743367317 1248237239036390706720343)
                    ·
                      rfl

theorem cell23_7292800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_7292800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292800 prefixEnd_7292800 := by exact prefixLift 7292800
  have htrace : WordTrace (prefixWord ++ tailWord_7292800) baseStart_7292800 baseEnd_7292800 := by
    simpa [prefixWord, tailWord_7292800, baseEnd_7292800] using wordTrace_append hprefix tailTrace_7292800
  have hstable : (prefixWord ++ tailWord_7292800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292800).length < 2 ^ (prefixWord ++ tailWord_7292800).sum := by decide
  have hdescent : baseEnd_7292800 < baseStart_7292800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292801 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7292801 : Nat := 118140960795 + 7292801 * 2 ^ 59
def prefixEnd_7292801 : Nat := 4983230072969 + 3 ^ 40 * 7292801 * 2
def baseEnd_7292801 : Nat := 3744712230589826616248525

theorem tailTrace_7292801 : CollatzResearch.WordTrace tailWord_7292801 prefixEnd_7292801 3744712230589826616248525 := by
  unfold tailWord_7292801
  simp only [CollatzResearch.WordTrace]
  refine ⟨265990304452434963095694257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177326869634956642063796171 265990304452434963095694257)
  ·
    refine ⟨199492728339326222321770693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265990304452434963095694257 199492728339326222321770693)
    ·
      refine ⟨37404886563623666685332005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199492728339326222321770693 37404886563623666685332005)
      ·
        refine ⟨7013416230679437503499751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37404886563623666685332005 7013416230679437503499751)
        ·
          refine ⟨10520124346019156255249627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013416230679437503499751 10520124346019156255249627)
          ·
            refine ⟨15780186519028734382874441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520124346019156255249627 15780186519028734382874441)
            ·
              refine ⟨11835139889271550787155831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780186519028734382874441 11835139889271550787155831)
              ·
                refine ⟨17752709833907326180733747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835139889271550787155831 17752709833907326180733747)
                ·
                  refine ⟨26629064750860989271100621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17752709833907326180733747 26629064750860989271100621)
                  ·
                    refine ⟨9985899281572870976662733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26629064750860989271100621 9985899281572870976662733)
                    ·
                      refine ⟨3744712230589826616248525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985899281572870976662733 3744712230589826616248525)
                      ·
                        rfl

theorem cell23_7292801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7292801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292801 prefixEnd_7292801 := by exact prefixLift 7292801
  have htrace : WordTrace (prefixWord ++ tailWord_7292801) baseStart_7292801 baseEnd_7292801 := by
    simpa [prefixWord, tailWord_7292801, baseEnd_7292801] using wordTrace_append hprefix tailTrace_7292801
  have hstable : (prefixWord ++ tailWord_7292801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292801).length < 2 ^ (prefixWord ++ tailWord_7292801).sum := by decide
  have hdescent : baseEnd_7292801 < baseStart_7292801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292822 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7292822 : Nat := 118140960795 + 7292822 * 2 ^ 59
def prefixEnd_7292822 : Nat := 4983230072969 + 3 ^ 40 * 7292822 * 2
def baseEnd_7292822 : Nat := 3744723013683571034085929

theorem tailTrace_7292822 : CollatzResearch.WordTrace tailWord_7292822 prefixEnd_7292822 3744723013683571034085929 := by
  unfold tailWord_7292822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16624441899084930230138045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177327380256905922454805813 16624441899084930230138045)
  ·
    refine ⟨6234165712156848836301767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16624441899084930230138045 6234165712156848836301767)
    ·
      refine ⟨9351248568235273254452651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234165712156848836301767 9351248568235273254452651)
      ·
        refine ⟨14026872852352909881678977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351248568235273254452651 14026872852352909881678977)
        ·
          refine ⟨10520154639264682411259233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026872852352909881678977 10520154639264682411259233)
          ·
            refine ⟨7890115979448511808444425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10520154639264682411259233 7890115979448511808444425)
            ·
              refine ⟨5917586984586383856333319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890115979448511808444425 5917586984586383856333319)
              ·
                refine ⟨8876380476879575784499979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917586984586383856333319 8876380476879575784499979)
                ·
                  refine ⟨13314570715319363676749969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876380476879575784499979 13314570715319363676749969)
                  ·
                    refine ⟨9985928036489522757562477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314570715319363676749969 9985928036489522757562477)
                    ·
                      refine ⟨3744723013683571034085929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985928036489522757562477 3744723013683571034085929)
                      ·
                        rfl

theorem cell23_7292822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7292822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292822 prefixEnd_7292822 := by exact prefixLift 7292822
  have htrace : WordTrace (prefixWord ++ tailWord_7292822) baseStart_7292822 baseEnd_7292822 := by
    simpa [prefixWord, tailWord_7292822, baseEnd_7292822] using wordTrace_append hprefix tailTrace_7292822
  have hstable : (prefixWord ++ tailWord_7292822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292822).length < 2 ^ (prefixWord ++ tailWord_7292822).sum := by decide
  have hdescent : baseEnd_7292822 < baseStart_7292822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292828 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7292828 : Nat := 118140960795 + 7292828 * 2 ^ 59
def prefixEnd_7292828 : Nat := 4983230072969 + 3 ^ 40 * 7292828 * 2
def baseEnd_7292828 : Nat := 3744726094567498010610901

theorem tailTrace_7292828 : CollatzResearch.WordTrace tailWord_7292828 prefixEnd_7292828 3744726094567498010610901 := by
  unfold tailWord_7292828
  simp only [CollatzResearch.WordTrace]
  refine ⟨132995644611668573353463569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177327526148891431137951425 132995644611668573353463569)
  ·
    refine ⟨99746733458751430015097677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132995644611668573353463569 99746733458751430015097677)
    ·
      refine ⟨37405025047031786255661629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99746733458751430015097677 37405025047031786255661629)
      ·
        refine ⟨14026884392636919845873111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37405025047031786255661629 14026884392636919845873111)
        ·
          refine ⟨21040326588955379768809667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14026884392636919845873111 21040326588955379768809667)
          ·
            refine ⟨31560489883433069653214501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21040326588955379768809667 31560489883433069653214501)
            ·
              refine ⟨5917591853143700559977719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31560489883433069653214501 5917591853143700559977719)
              ·
                refine ⟨8876387779715550839966579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917591853143700559977719 8876387779715550839966579)
                ·
                  refine ⟨13314581669573326259949869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876387779715550839966579 13314581669573326259949869)
                  ·
                    refine ⟨4992968126089997347481201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13314581669573326259949869 4992968126089997347481201)
                    ·
                      refine ⟨3744726094567498010610901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4992968126089997347481201 3744726094567498010610901)
                      ·
                        rfl

theorem cell23_7292828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7292828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292828 prefixEnd_7292828 := by exact prefixLift 7292828
  have htrace : WordTrace (prefixWord ++ tailWord_7292828) baseStart_7292828 baseEnd_7292828 := by
    simpa [prefixWord, tailWord_7292828, baseEnd_7292828] using wordTrace_append hprefix tailTrace_7292828
  have hstable : (prefixWord ++ tailWord_7292828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292828).length < 2 ^ (prefixWord ++ tailWord_7292828).sum := by decide
  have hdescent : baseEnd_7292828 < baseStart_7292828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292847 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 5]
def baseStart_7292847 : Nat := 118140960795 + 7292847 * 2 ^ 59
def prefixEnd_7292847 : Nat := 4983230072969 + 3 ^ 40 * 7292847 * 2
def baseEnd_7292847 : Nat := 416081761188881492919257

theorem tailTrace_7292847 : CollatzResearch.WordTrace tailWord_7292847 prefixEnd_7292847 416081761188881492919257 := by
  unfold tailWord_7292847
  simp only [CollatzResearch.WordTrace]
  refine ⟨265991982210268312951868795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177327988140178875301245863 265991982210268312951868795)
  ·
    refine ⟨398987973315402469427803193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265991982210268312951868795 398987973315402469427803193)
    ·
      refine ⟨299240979986551852070852395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398987973315402469427803193 299240979986551852070852395)
      ·
        refine ⟨448861469979827778106278593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299240979986551852070852395 448861469979827778106278593)
        ·
          refine ⟨336646102484870833579708945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448861469979827778106278593 336646102484870833579708945)
          ·
            refine ⟨252484576863653125184781709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336646102484870833579708945 252484576863653125184781709)
            ·
              refine ⟨94681716323869921944293141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252484576863653125184781709 94681716323869921944293141)
              ·
                refine ⟨4438205452681402591138741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94681716323869921944293141 4438205452681402591138741)
                ·
                  refine ⟨416081761188881492919257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438205452681402591138741 416081761188881492919257)
                  ·
                    rfl

theorem cell23_7292847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 5].length) (baseStart_7292847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292847 prefixEnd_7292847 := by exact prefixLift 7292847
  have htrace : WordTrace (prefixWord ++ tailWord_7292847) baseStart_7292847 baseEnd_7292847 := by
    simpa [prefixWord, tailWord_7292847, baseEnd_7292847] using wordTrace_append hprefix tailTrace_7292847
  have hstable : (prefixWord ++ tailWord_7292847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292847).length < 2 ^ (prefixWord ++ tailWord_7292847).sum := by decide
  have hdescent : baseEnd_7292847 < baseStart_7292847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292857 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7292857 : Nat := 118140960795 + 7292857 * 2 ^ 59
def prefixEnd_7292857 : Nat := 4983230072969 + 3 ^ 40 * 7292857 * 2
def baseEnd_7292857 : Nat := 3744740985506478397148267

theorem tailTrace_7292857 : CollatzResearch.WordTrace tailWord_7292857 prefixEnd_7292857 3744740985506478397148267 := by
  unfold tailWord_7292857
  simp only [CollatzResearch.WordTrace]
  refine ⟨265992346940232084659732825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177328231293488056439821883 265992346940232084659732825)
  ·
    refine ⟨199494260205174063494799619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265992346940232084659732825 199494260205174063494799619)
    ·
      refine ⟨299241390307761095242199429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199494260205174063494799619 299241390307761095242199429)
      ·
        refine ⟨56107760682705205357912393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299241390307761095242199429 56107760682705205357912393)
        ·
          refine ⟨42080820512028904018434295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56107760682705205357912393 42080820512028904018434295)
          ·
            refine ⟨63121230768043356027651443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42080820512028904018434295 63121230768043356027651443)
            ·
              refine ⟨94681846152065034041477165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63121230768043356027651443 94681846152065034041477165)
              ·
                refine ⟨35505692307024387765553937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94681846152065034041477165 35505692307024387765553937)
                ·
                  refine ⟨26629269230268290824165453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35505692307024387765553937 26629269230268290824165453)
                  ·
                    refine ⟨9985975961350609059062045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26629269230268290824165453 9985975961350609059062045)
                    ·
                      refine ⟨3744740985506478397148267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9985975961350609059062045 3744740985506478397148267)
                      ·
                        rfl

theorem cell23_7292857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7292857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292857 prefixEnd_7292857 := by exact prefixLift 7292857
  have htrace : WordTrace (prefixWord ++ tailWord_7292857) baseStart_7292857 baseEnd_7292857 := by
    simpa [prefixWord, tailWord_7292857, baseEnd_7292857] using wordTrace_append hprefix tailTrace_7292857
  have hstable : (prefixWord ++ tailWord_7292857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292857).length < 2 ^ (prefixWord ++ tailWord_7292857).sum := by decide
  have hdescent : baseEnd_7292857 < baseStart_7292857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292897 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_7292897 : Nat := 118140960795 + 7292897 * 2 ^ 59
def prefixEnd_7292897 : Nat := 4983230072969 + 3 ^ 40 * 7292897 * 2
def baseEnd_7292897 : Nat := 3744761524732658240648083

theorem tailTrace_7292897 : CollatzResearch.WordTrace tailWord_7292897 prefixEnd_7292897 3744761524732658240648083 := by
  unfold tailWord_7292897
  simp only [CollatzResearch.WordTrace]
  refine ⟨265993805860087171491188945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177329203906724780994125963 265993805860087171491188945)
  ·
    refine ⟨199495354395065378618391709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265993805860087171491188945 199495354395065378618391709)
    ·
      refine ⟨74810757898149516981896891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199495354395065378618391709 74810757898149516981896891)
      ·
        refine ⟨112216136847224275472845337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74810757898149516981896891 112216136847224275472845337)
        ·
          refine ⟨84162102635418206604634003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112216136847224275472845337 84162102635418206604634003)
          ·
            refine ⟨126243153953127309906951005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84162102635418206604634003 126243153953127309906951005)
            ·
              refine ⟨47341182732422741215106627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126243153953127309906951005 47341182732422741215106627)
              ·
                refine ⟨71011774098634111822659941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47341182732422741215106627 71011774098634111822659941)
                ·
                  refine ⟨13314707643493895966748739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71011774098634111822659941 13314707643493895966748739)
                  ·
                    refine ⟨19972061465240843950123109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13314707643493895966748739 19972061465240843950123109)
                    ·
                      refine ⟨3744761524732658240648083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19972061465240843950123109 3744761524732658240648083)
                      ·
                        rfl

theorem cell23_7292897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_7292897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292897 prefixEnd_7292897 := by exact prefixLift 7292897
  have htrace : WordTrace (prefixWord ++ tailWord_7292897) baseStart_7292897 baseEnd_7292897 := by
    simpa [prefixWord, tailWord_7292897, baseEnd_7292897] using wordTrace_append hprefix tailTrace_7292897
  have hstable : (prefixWord ++ tailWord_7292897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292897).length < 2 ^ (prefixWord ++ tailWord_7292897).sum := by decide
  have hdescent : baseEnd_7292897 < baseStart_7292897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292898 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_7292898 : Nat := 118140960795 + 7292898 * 2 ^ 59
def prefixEnd_7292898 : Nat := 4983230072969 + 3 ^ 40 * 7292898 * 2
def baseEnd_7292898 : Nat := 416084670912590304081731

theorem tailTrace_7292898 : CollatzResearch.WordTrace tailWord_7292898 prefixEnd_7292898 416084670912590304081731 := by
  unfold tailWord_7292898
  simp only [CollatzResearch.WordTrace]
  refine ⟨66498460583270887165493837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177329228222055699107983565 66498460583270887165493837)
  ·
    refine ⟨24936922718726582687060189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66498460583270887165493837 24936922718726582687060189)
    ·
      refine ⟨9351346019522468507647571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24936922718726582687060189 9351346019522468507647571)
      ·
        refine ⟨14027019029283702761471357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351346019522468507647571 14027019029283702761471357)
        ·
          refine ⟨5260132135981388535551759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14027019029283702761471357 5260132135981388535551759)
          ·
            refine ⟨7890198203972082803327639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260132135981388535551759 7890198203972082803327639)
            ·
              refine ⟨11835297305958124204991459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890198203972082803327639 11835297305958124204991459)
              ·
                refine ⟨17752945958937186307487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835297305958124204991459 17752945958937186307487189)
                ·
                  refine ⟨416084670912590304081731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17752945958937186307487189 416084670912590304081731)
                  ·
                    rfl

theorem cell23_7292898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_7292898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292898 prefixEnd_7292898 := by exact prefixLift 7292898
  have htrace : WordTrace (prefixWord ++ tailWord_7292898) baseStart_7292898 baseEnd_7292898 := by
    simpa [prefixWord, tailWord_7292898, baseEnd_7292898] using wordTrace_append hprefix tailTrace_7292898
  have hstable : (prefixWord ++ tailWord_7292898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292898).length < 2 ^ (prefixWord ++ tailWord_7292898).sum := by decide
  have hdescent : baseEnd_7292898 < baseStart_7292898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292909 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7292909 : Nat := 118140960795 + 7292909 * 2 ^ 59
def prefixEnd_7292909 : Nat := 4983230072969 + 3 ^ 40 * 7292909 * 2
def baseEnd_7292909 : Nat := 3744767686500512193698029

theorem tailTrace_7292909 : CollatzResearch.WordTrace tailWord_7292909 prefixEnd_7292909 3744767686500512193698029 := by
  unfold tailWord_7292909
  simp only [CollatzResearch.WordTrace]
  refine ⟨265994243536043697540625781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177329495690695798360417187 265994243536043697540625781)
  ·
    refine ⟨24936960331504096644433667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265994243536043697540625781 24936960331504096644433667)
    ·
      refine ⟨37405440497256144966650501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24936960331504096644433667 37405440497256144966650501)
      ·
        refine ⟨7013520093235527181246969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37405440497256144966650501 7013520093235527181246969)
        ·
          refine ⟨5260140069926645385935227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7013520093235527181246969 5260140069926645385935227)
          ·
            refine ⟨7890210104889968078902841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260140069926645385935227 7890210104889968078902841)
            ·
              refine ⟨5917657578667476059177131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890210104889968078902841 5917657578667476059177131)
              ·
                refine ⟨8876486368001214088765697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917657578667476059177131 8876486368001214088765697)
                ·
                  refine ⟨6657364776000910566574273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876486368001214088765697 6657364776000910566574273)
                  ·
                    refine ⟨4993023582000682924930705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6657364776000910566574273 4993023582000682924930705)
                    ·
                      refine ⟨3744767686500512193698029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993023582000682924930705 3744767686500512193698029)
                      ·
                        rfl

theorem cell23_7292909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7292909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292909 prefixEnd_7292909 := by exact prefixLift 7292909
  have htrace : WordTrace (prefixWord ++ tailWord_7292909) baseStart_7292909 baseEnd_7292909 := by
    simpa [prefixWord, tailWord_7292909, baseEnd_7292909] using wordTrace_append hprefix tailTrace_7292909
  have hstable : (prefixWord ++ tailWord_7292909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292909).length < 2 ^ (prefixWord ++ tailWord_7292909).sum := by decide
  have hdescent : baseEnd_7292909 < baseStart_7292909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292954 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_7292954 : Nat := 118140960795 + 7292954 * 2 ^ 59
def prefixEnd_7292954 : Nat := 4983230072969 + 3 ^ 40 * 7292954 * 2
def baseEnd_7292954 : Nat := 416087865903329390848369

theorem tailTrace_7292954 : CollatzResearch.WordTrace tailWord_7292954 prefixEnd_7292954 416087865903329390848369 := by
  unfold tailWord_7292954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66498971205220167556503479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177330589880587113484009277 66498971205220167556503479)
  ·
    refine ⟨99748456807830251334755219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66498971205220167556503479 99748456807830251334755219)
    ·
      refine ⟨149622685211745377002132829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99748456807830251334755219 149622685211745377002132829)
      ·
        refine ⟨56108506954404516375799811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149622685211745377002132829 56108506954404516375799811)
        ·
          refine ⟨84162760431606774563699717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56108506954404516375799811 84162760431606774563699717)
          ·
            refine ⟨15780517580926270230693697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84162760431606774563699717 15780517580926270230693697)
            ·
              refine ⟨11835388185694702673020273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780517580926270230693697 11835388185694702673020273)
              ·
                refine ⟨8876541139271027004765205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835388185694702673020273 8876541139271027004765205)
                ·
                  refine ⟨416087865903329390848369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8876541139271027004765205 416087865903329390848369)
                  ·
                    rfl

theorem cell23_7292954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_7292954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292954 prefixEnd_7292954 := by exact prefixLift 7292954
  have htrace : WordTrace (prefixWord ++ tailWord_7292954) baseStart_7292954 baseEnd_7292954 := by
    simpa [prefixWord, tailWord_7292954, baseEnd_7292954] using wordTrace_append hprefix tailTrace_7292954
  have hstable : (prefixWord ++ tailWord_7292954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292954).length < 2 ^ (prefixWord ++ tailWord_7292954).sum := by decide
  have hdescent : baseEnd_7292954 < baseStart_7292954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292991 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 2, 3, 2]
def baseStart_7292991 : Nat := 118140960795 + 7292991 * 2 ^ 59
def prefixEnd_7292991 : Nat := 4983230072969 + 3 ^ 40 * 7292991 * 2
def baseEnd_7292991 : Nat := 3744809791914180872872651

theorem tailTrace_7292991 : CollatzResearch.WordTrace tailWord_7292991 prefixEnd_7292991 3744809791914180872872651 := by
  unfold tailWord_7292991
  simp only [CollatzResearch.WordTrace]
  refine ⟨265997234321746625545110827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177331489547831083696740551 265997234321746625545110827)
  ·
    refine ⟨398995851482619938317666241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265997234321746625545110827 398995851482619938317666241)
    ·
      refine ⟨299246888611964953738249681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398995851482619938317666241 299246888611964953738249681)
      ·
        refine ⟨224435166458973715303687261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299246888611964953738249681 224435166458973715303687261)
        ·
          refine ⟨84163187422115143238882723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224435166458973715303687261 84163187422115143238882723)
          ·
            refine ⟨126244781133172714858324085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84163187422115143238882723 126244781133172714858324085)
            ·
              refine ⟨11835448231234942017967883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126244781133172714858324085 11835448231234942017967883)
              ·
                refine ⟨17753172346852413026951825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835448231234942017967883 17753172346852413026951825)
                ·
                  refine ⟨13314879260139309770213869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17753172346852413026951825 13314879260139309770213869)
                  ·
                    refine ⟨4993079722552241163830201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13314879260139309770213869 4993079722552241163830201)
                    ·
                      refine ⟨3744809791914180872872651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993079722552241163830201 3744809791914180872872651)
                      ·
                        rfl

theorem cell23_7292991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_7292991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292991 prefixEnd_7292991 := by exact prefixLift 7292991
  have htrace : WordTrace (prefixWord ++ tailWord_7292991) baseStart_7292991 baseEnd_7292991 := by
    simpa [prefixWord, tailWord_7292991, baseEnd_7292991] using wordTrace_append hprefix tailTrace_7292991
  have hstable : (prefixWord ++ tailWord_7292991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292991).length < 2 ^ (prefixWord ++ tailWord_7292991).sum := by decide
  have hdescent : baseEnd_7292991 < baseStart_7292991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7292998 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7292998 : Nat := 118140960795 + 7292998 * 2 ^ 59
def prefixEnd_7292998 : Nat := 4983230072969 + 3 ^ 40 * 7292998 * 2
def baseEnd_7292998 : Nat := 3744813386278762345485119

theorem tailTrace_7292998 : CollatzResearch.WordTrace tailWord_7292998 prefixEnd_7292998 3744813386278762345485119 := by
  unfold tailWord_7292998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312421551022539554394239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177331659755147510493743765 8312421551022539554394239)
  ·
    refine ⟨12468632326533809331591359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312421551022539554394239 12468632326533809331591359)
    ·
      refine ⟨18702948489800713997387039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468632326533809331591359 18702948489800713997387039)
      ·
        refine ⟨28054422734701070996080559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702948489800713997387039 28054422734701070996080559)
        ·
          refine ⟨42081634102051606494120839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28054422734701070996080559 42081634102051606494120839)
          ·
            refine ⟨63122451153077409741181259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42081634102051606494120839 63122451153077409741181259)
            ·
              refine ⟨94683676729616114611771889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63122451153077409741181259 94683676729616114611771889)
              ·
                refine ⟨71012757547212085958828917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94683676729616114611771889 71012757547212085958828917)
                ·
                  refine ⟨6657446020051133058640211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71012757547212085958828917 6657446020051133058640211)
                  ·
                    refine ⟨9986169030076699587960317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657446020051133058640211 9986169030076699587960317)
                    ·
                      refine ⟨3744813386278762345485119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986169030076699587960317 3744813386278762345485119)
                      ·
                        rfl

theorem cell23_7292998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7292998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7292998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7292998 prefixEnd_7292998 := by exact prefixLift 7292998
  have htrace : WordTrace (prefixWord ++ tailWord_7292998) baseStart_7292998 baseEnd_7292998 := by
    simpa [prefixWord, tailWord_7292998, baseEnd_7292998] using wordTrace_append hprefix tailTrace_7292998
  have hstable : (prefixWord ++ tailWord_7292998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7292998).length < 2 ^ (prefixWord ++ tailWord_7292998).sum := by decide
  have hdescent : baseEnd_7292998 < baseStart_7292998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7292998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293017 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7293017 : Nat := 118140960795 + 7293017 * 2 ^ 59
def prefixEnd_7293017 : Nat := 4983230072969 + 3 ^ 40 * 7293017 * 2
def baseEnd_7293017 : Nat := 3744823142411197771147531

theorem tailTrace_7293017 : CollatzResearch.WordTrace tailWord_7293017 prefixEnd_7293017 3744823142411197771147531 := by
  unfold tailWord_7293017
  simp only [CollatzResearch.WordTrace]
  refine ⟨265998182619652431985557305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177332121746434954657038203 265998182619652431985557305)
  ·
    refine ⟨199498636964739323989167979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265998182619652431985557305 199498636964739323989167979)
    ·
      refine ⟨299247955447108985983751969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199498636964739323989167979 299247955447108985983751969)
      ·
        refine ⟨224435966585331739487813977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299247955447108985983751969 224435966585331739487813977)
        ·
          refine ⟨168326974938998804615860483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224435966585331739487813977 168326974938998804615860483)
          ·
            refine ⟨252490462408498206923790725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168326974938998804615860483 252490462408498206923790725)
            ·
              refine ⟨47341961701593413798210761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252490462408498206923790725 47341961701593413798210761)
              ·
                refine ⟨35506471276195060348658071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47341961701593413798210761 35506471276195060348658071)
                ·
                  refine ⟨53259706914292590522987107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35506471276195060348658071 53259706914292590522987107)
                  ·
                    refine ⟨79889560371438885784480661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53259706914292590522987107 79889560371438885784480661)
                    ·
                      refine ⟨3744823142411197771147531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79889560371438885784480661 3744823142411197771147531)
                      ·
                        rfl

theorem cell23_7293017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7293017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293017 prefixEnd_7293017 := by exact prefixLift 7293017
  have htrace : WordTrace (prefixWord ++ tailWord_7293017) baseStart_7293017 baseEnd_7293017 := by
    simpa [prefixWord, tailWord_7293017, baseEnd_7293017] using wordTrace_append hprefix tailTrace_7293017
  have hstable : (prefixWord ++ tailWord_7293017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293017).length < 2 ^ (prefixWord ++ tailWord_7293017).sum := by decide
  have hdescent : baseEnd_7293017 < baseStart_7293017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293024 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_7293024 : Nat := 118140960795 + 7293024 * 2 ^ 59
def prefixEnd_7293024 : Nat := 4983230072969 + 3 ^ 40 * 7293024 * 2
def baseEnd_7293024 : Nat := 3744826736775779243759999

theorem tailTrace_7293024 : CollatzResearch.WordTrace tailWord_7293024 prefixEnd_7293024 3744826736775779243759999 := by
  unfold tailWord_7293024
  simp only [CollatzResearch.WordTrace]
  refine ⟨132999218965313536090531063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177332291953751381454041417 132999218965313536090531063)
  ·
    refine ⟨199498828447970304135796595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132999218965313536090531063 199498828447970304135796595)
    ·
      refine ⟨299248242671955456203694893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199498828447970304135796595 299248242671955456203694893)
      ·
        refine ⟨112218091001983296076385585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299248242671955456203694893 112218091001983296076385585)
        ·
          refine ⟨84163568251487472057289189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112218091001983296076385585 84163568251487472057289189)
          ·
            refine ⟨15780669047153901010741723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84163568251487472057289189 15780669047153901010741723)
            ·
              refine ⟨23671003570730851516112585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15780669047153901010741723 23671003570730851516112585)
              ·
                refine ⟨17753252678048138637084439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23671003570730851516112585 17753252678048138637084439)
                ·
                  refine ⟨26629879017072207955626659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17753252678048138637084439 26629879017072207955626659)
                  ·
                    refine ⟨39944818525608311933439989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26629879017072207955626659 39944818525608311933439989)
                    ·
                      refine ⟨3744826736775779243759999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39944818525608311933439989 3744826736775779243759999)
                      ·
                        rfl

theorem cell23_7293024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_7293024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293024 prefixEnd_7293024 := by exact prefixLift 7293024
  have htrace : WordTrace (prefixWord ++ tailWord_7293024) baseStart_7293024 baseEnd_7293024 := by
    simpa [prefixWord, tailWord_7293024, baseEnd_7293024] using wordTrace_append hprefix tailTrace_7293024
  have hstable : (prefixWord ++ tailWord_7293024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293024).length < 2 ^ (prefixWord ++ tailWord_7293024).sum := by decide
  have hdescent : baseEnd_7293024 < baseStart_7293024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293038 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_7293038 : Nat := 118140960795 + 7293038 * 2 ^ 59
def prefixEnd_7293038 : Nat := 4983230072969 + 3 ^ 40 * 7293038 * 2
def baseEnd_7293038 : Nat := 3744833925504942188984935

theorem tailTrace_7293038 : CollatzResearch.WordTrace tailWord_7293038 prefixEnd_7293038 3744833925504942188984935 := by
  unfold tailWord_7293038
  simp only [CollatzResearch.WordTrace]
  refine ⟨33249868569072044071508971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177332632368384235048047845 33249868569072044071508971)
  ·
    refine ⟨49874802853608066107263457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33249868569072044071508971 49874802853608066107263457)
    ·
      refine ⟨37406102140206049580447593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49874802853608066107263457 37406102140206049580447593)
      ·
        refine ⟨28054576605154537185335695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37406102140206049580447593 28054576605154537185335695)
        ·
          refine ⟨42081864907731805778003543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28054576605154537185335695 42081864907731805778003543)
          ·
            refine ⟨63122797361597708667005315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42081864907731805778003543 63122797361597708667005315)
            ·
              refine ⟨94684196042396563000507973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63122797361597708667005315 94684196042396563000507973)
              ·
                refine ⟨17753286757949355562595245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94684196042396563000507973 17753286757949355562595245)
                ·
                  refine ⟨6657482534231008335973217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17753286757949355562595245 6657482534231008335973217)
                  ·
                    refine ⟨4993111900673256251979913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6657482534231008335973217 4993111900673256251979913)
                    ·
                      refine ⟨3744833925504942188984935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993111900673256251979913 3744833925504942188984935)
                      ·
                        rfl

theorem cell23_7293038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_7293038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293038 prefixEnd_7293038 := by exact prefixLift 7293038
  have htrace : WordTrace (prefixWord ++ tailWord_7293038) baseStart_7293038 baseEnd_7293038 := by
    simpa [prefixWord, tailWord_7293038, baseEnd_7293038] using wordTrace_append hprefix tailTrace_7293038
  have hstable : (prefixWord ++ tailWord_7293038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293038).length < 2 ^ (prefixWord ++ tailWord_7293038).sum := by decide
  have hdescent : baseEnd_7293038 < baseStart_7293038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293041 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_7293041 : Nat := 118140960795 + 7293041 * 2 ^ 59
def prefixEnd_7293041 : Nat := 4983230072969 + 3 ^ 40 * 7293041 * 2
def baseEnd_7293041 : Nat := 3744835465946905677247421

theorem tailTrace_7293041 : CollatzResearch.WordTrace tailWord_7293041 prefixEnd_7293041 3744835465946905677247421 := by
  unfold tailWord_7293041
  simp only [CollatzResearch.WordTrace]
  refine ⟨265999057971565484084430977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177332705314376989389620651 265999057971565484084430977)
  ·
    refine ⟨199499293478674113063323233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265999057971565484084430977 199499293478674113063323233)
    ·
      refine ⟨149624470109005584797492425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199499293478674113063323233 149624470109005584797492425)
      ·
        refine ⟨112218352581754188598119319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149624470109005584797492425 112218352581754188598119319)
        ·
          refine ⟨168327528872631282897178979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112218352581754188598119319 168327528872631282897178979)
          ·
            refine ⟨252491293308946924345768469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168327528872631282897178979 252491293308946924345768469)
            ·
              refine ⟨11835529373856887078707897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252491293308946924345768469 11835529373856887078707897)
              ·
                refine ⟨8876647030392665309030923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835529373856887078707897 8876647030392665309030923)
                ·
                  refine ⟨13314970545588997963546385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876647030392665309030923 13314970545588997963546385)
                  ·
                    refine ⟨9986227909191748472659789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314970545588997963546385 9986227909191748472659789)
                    ·
                      refine ⟨3744835465946905677247421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986227909191748472659789 3744835465946905677247421)
                      ·
                        rfl

theorem cell23_7293041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_7293041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293041 prefixEnd_7293041 := by exact prefixLift 7293041
  have htrace : WordTrace (prefixWord ++ tailWord_7293041) baseStart_7293041 baseEnd_7293041 := by
    simpa [prefixWord, tailWord_7293041, baseEnd_7293041] using wordTrace_append hprefix tailTrace_7293041
  have hstable : (prefixWord ++ tailWord_7293041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293041).length < 2 ^ (prefixWord ++ tailWord_7293041).sum := by decide
  have hdescent : baseEnd_7293041 < baseStart_7293041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293074 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7293074 : Nat := 118140960795 + 7293074 * 2 ^ 59
def prefixEnd_7293074 : Nat := 4983230072969 + 3 ^ 40 * 7293074 * 2
def baseEnd_7293074 : Nat := 1248284136936168016044923

theorem tailTrace_7293074 : CollatzResearch.WordTrace tailWord_7293074 prefixEnd_7293074 1248284136936168016044923 := by
  unfold tailWord_7293074
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500065395111482680095569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177333507720297287146921517 66500065395111482680095569)
  ·
    refine ⟨49875049046333612010071677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66500065395111482680095569 49875049046333612010071677)
    ·
      refine ⟨18703143392375104503776879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49875049046333612010071677 18703143392375104503776879)
      ·
        refine ⟨28054715088562656755665319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18703143392375104503776879 28054715088562656755665319)
        ·
          refine ⟨42082072632843985133497979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28054715088562656755665319 42082072632843985133497979)
          ·
            refine ⟨63123108949265977700246969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42082072632843985133497979 63123108949265977700246969)
            ·
              refine ⟨47342331711949483275185227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63123108949265977700246969 47342331711949483275185227)
              ·
                refine ⟨71013497567924224912777841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47342331711949483275185227 71013497567924224912777841)
                ·
                  refine ⟨53260123175943168684583381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71013497567924224912777841 53260123175943168684583381)
                  ·
                    refine ⟨1248284136936168016044923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53260123175943168684583381 1248284136936168016044923)
                    ·
                      rfl

theorem cell23_7293074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7293074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293074 prefixEnd_7293074 := by exact prefixLift 7293074
  have htrace : WordTrace (prefixWord ++ tailWord_7293074) baseStart_7293074 baseEnd_7293074 := by
    simpa [prefixWord, tailWord_7293074, baseEnd_7293074] using wordTrace_append hprefix tailTrace_7293074
  have hstable : (prefixWord ++ tailWord_7293074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293074).length < 2 ^ (prefixWord ++ tailWord_7293074).sum := by decide
  have hdescent : baseEnd_7293074 < baseStart_7293074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293082 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_7293082 : Nat := 118140960795 + 7293082 * 2 ^ 59
def prefixEnd_7293082 : Nat := 4983230072969 + 3 ^ 40 * 7293082 * 2
def baseEnd_7293082 : Nat := 1248285506217913338944911

theorem tailTrace_7293082 : CollatzResearch.WordTrace tailWord_7293082 prefixEnd_7293082 1248285506217913338944911 := by
  unfold tailWord_7293082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500138341104237021668375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177333702242944632057782333 66500138341104237021668375)
  ·
    refine ⟨99750207511656355532502563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66500138341104237021668375 99750207511656355532502563)
    ·
      refine ⟨149625311267484533298753845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99750207511656355532502563 149625311267484533298753845)
      ·
        refine ⟨14027372931326674996758173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149625311267484533298753845 14027372931326674996758173)
        ·
          refine ⟨5260264849247503123784315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14027372931326674996758173 5260264849247503123784315)
          ·
            refine ⟨7890397273871254685676473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260264849247503123784315 7890397273871254685676473)
            ·
              refine ⟨5917797955403441014257355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890397273871254685676473 5917797955403441014257355)
              ·
                refine ⟨8876696933105161521386033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917797955403441014257355 8876696933105161521386033)
                ·
                  refine ⟨6657522699828871141039525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876696933105161521386033 6657522699828871141039525)
                  ·
                    refine ⟨1248285506217913338944911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657522699828871141039525 1248285506217913338944911)
                    ·
                      rfl

theorem cell23_7293082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_7293082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293082 prefixEnd_7293082 := by exact prefixLift 7293082
  have htrace : WordTrace (prefixWord ++ tailWord_7293082) baseStart_7293082 baseEnd_7293082 := by
    simpa [prefixWord, tailWord_7293082, baseEnd_7293082] using wordTrace_append hprefix tailTrace_7293082
  have hstable : (prefixWord ++ tailWord_7293082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293082).length < 2 ^ (prefixWord ++ tailWord_7293082).sum := by decide
  have hdescent : baseEnd_7293082 < baseStart_7293082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293088 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_7293088 : Nat := 118140960795 + 7293088 * 2 ^ 59
def prefixEnd_7293088 : Nat := 4983230072969 + 3 ^ 40 * 7293088 * 2
def baseEnd_7293088 : Nat := 3744859599537666993359705

theorem tailTrace_7293088 : CollatzResearch.WordTrace tailWord_7293088 prefixEnd_7293088 3744859599537666993359705 := by
  unfold tailWord_7293088
  simp only [CollatzResearch.WordTrace]
  refine ⟨133000386101197605555695959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177333848134930140740927945 133000386101197605555695959)
  ·
    refine ⟨199500579151796408333543939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133000386101197605555695959 199500579151796408333543939)
    ·
      refine ⟨299250868727694612500315909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199500579151796408333543939 299250868727694612500315909)
      ·
        refine ⟨56109537886442739843809233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299250868727694612500315909 56109537886442739843809233)
        ·
          refine ⟨42082153414832054882856925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56109537886442739843809233 42082153414832054882856925)
          ·
            refine ⟨15780807530562020581071347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42082153414832054882856925 15780807530562020581071347)
            ·
              refine ⟨23671211295843030871607021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15780807530562020581071347 23671211295843030871607021)
              ·
                refine ⟨8876704235941136576852633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23671211295843030871607021 8876704235941136576852633)
                ·
                  refine ⟨6657528176955852432639475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876704235941136576852633 6657528176955852432639475)
                  ·
                    refine ⟨9986292265433778648959213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657528176955852432639475 9986292265433778648959213)
                    ·
                      refine ⟨3744859599537666993359705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986292265433778648959213 3744859599537666993359705)
                      ·
                        rfl

theorem cell23_7293088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_7293088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293088 prefixEnd_7293088 := by exact prefixLift 7293088
  have htrace : WordTrace (prefixWord ++ tailWord_7293088) baseStart_7293088 baseEnd_7293088 := by
    simpa [prefixWord, tailWord_7293088, baseEnd_7293088] using wordTrace_append hprefix tailTrace_7293088
  have hstable : (prefixWord ++ tailWord_7293088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293088).length < 2 ^ (prefixWord ++ tailWord_7293088).sum := by decide
  have hdescent : baseEnd_7293088 < baseStart_7293088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293111 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_7293111 : Nat := 118140960795 + 7293111 * 2 ^ 59
def prefixEnd_7293111 : Nat := 4983230072969 + 3 ^ 40 * 7293111 * 2
def baseEnd_7293111 : Nat := 3744871409592720403372099

theorem tailTrace_7293111 : CollatzResearch.WordTrace tailWord_7293111 prefixEnd_7293111 3744871409592720403372099 := by
  unfold tailWord_7293111
  simp only [CollatzResearch.WordTrace]
  refine ⟨266001611081311886039479187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177334407387541257359652791 266001611081311886039479187)
  ·
    refine ⟨399002416621967829059218781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266001611081311886039479187 399002416621967829059218781)
    ·
      refine ⟨149625906233237935897207043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399002416621967829059218781 149625906233237935897207043)
      ·
        refine ⟨224438859349856903845810565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149625906233237935897207043 224438859349856903845810565)
        ·
          refine ⟨42082286128098169471089481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224438859349856903845810565 42082286128098169471089481)
          ·
            refine ⟨31561714596073627103317111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42082286128098169471089481 31561714596073627103317111)
            ·
              refine ⟨47342571894110440654975667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31561714596073627103317111 47342571894110440654975667)
              ·
                refine ⟨71013857841165660982463501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47342571894110440654975667 71013857841165660982463501)
                ·
                  refine ⟨26630196690437122868423813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71013857841165660982463501 26630196690437122868423813)
                  ·
                    refine ⟨4993161879456960537829465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26630196690437122868423813 4993161879456960537829465)
                    ·
                      refine ⟨3744871409592720403372099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993161879456960537829465 3744871409592720403372099)
                      ·
                        rfl

theorem cell23_7293111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_7293111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293111 prefixEnd_7293111 := by exact prefixLift 7293111
  have htrace : WordTrace (prefixWord ++ tailWord_7293111) baseStart_7293111 baseEnd_7293111 := by
    simpa [prefixWord, tailWord_7293111, baseEnd_7293111] using wordTrace_append hprefix tailTrace_7293111
  have hstable : (prefixWord ++ tailWord_7293111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293111).length < 2 ^ (prefixWord ++ tailWord_7293111).sum := by decide
  have hdescent : baseEnd_7293111 < baseStart_7293111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293114 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_7293114 : Nat := 118140960795 + 7293114 * 2 ^ 59
def prefixEnd_7293114 : Nat := 4983230072969 + 3 ^ 40 * 7293114 * 2
def baseEnd_7293114 : Nat := 3744872950034683891634585

theorem tailTrace_7293114 : CollatzResearch.WordTrace tailWord_7293114 prefixEnd_7293114 3744872950034683891634585 := by
  unfold tailWord_7293114
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500430125075254387959599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177334480333534011701225597 66500430125075254387959599)
  ·
    refine ⟨99750645187612881581939399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66500430125075254387959599 99750645187612881581939399)
    ·
      refine ⟨149625967781419322372909099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99750645187612881581939399 149625967781419322372909099)
      ·
        refine ⟨224438951672128983559363649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149625967781419322372909099 224438951672128983559363649)
        ·
          refine ⟨168329213754096737669522737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224438951672128983559363649 168329213754096737669522737)
          ·
            refine ⟨126246910315572553252142053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168329213754096737669522737 126246910315572553252142053)
            ·
              refine ⟨23671295684169853734776635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126246910315572553252142053 23671295684169853734776635)
              ·
                refine ⟨35506943526254780602164953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23671295684169853734776635 35506943526254780602164953)
                ·
                  refine ⟨26630207644691085451623715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35506943526254780602164953 26630207644691085451623715)
                  ·
                    refine ⟨39945311467036628177435573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26630207644691085451623715 39945311467036628177435573)
                    ·
                      refine ⟨3744872950034683891634585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39945311467036628177435573 3744872950034683891634585)
                      ·
                        rfl

theorem cell23_7293114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_7293114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293114 prefixEnd_7293114 := by exact prefixLift 7293114
  have htrace : WordTrace (prefixWord ++ tailWord_7293114) baseStart_7293114 baseEnd_7293114 := by
    simpa [prefixWord, tailWord_7293114, baseEnd_7293114] using wordTrace_append hprefix tailTrace_7293114
  have hstable : (prefixWord ++ tailWord_7293114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293114).length < 2 ^ (prefixWord ++ tailWord_7293114).sum := by decide
  have hdescent : baseEnd_7293114 < baseStart_7293114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293122 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7293122 : Nat := 118140960795 + 7293122 * 2 ^ 59
def prefixEnd_7293122 : Nat := 4983230072969 + 3 ^ 40 * 7293122 * 2
def baseEnd_7293122 : Nat := 3744877057879919860334549

theorem tailTrace_7293122 : CollatzResearch.WordTrace tailWord_7293122 prefixEnd_7293122 3744877057879919860334549 := by
  unfold tailWord_7293122
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500503071068008729532405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177334674856181356612086413 66500503071068008729532405)
  ·
    refine ⟨6234422162912625818393663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66500503071068008729532405 6234422162912625818393663)
    ·
      refine ⟨9351633244368938727590495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234422162912625818393663 9351633244368938727590495)
      ·
        refine ⟨14027449866553408091385743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351633244368938727590495 14027449866553408091385743)
        ·
          refine ⟨21041174799830112137078615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027449866553408091385743 21041174799830112137078615)
          ·
            refine ⟨31561762199745168205617923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041174799830112137078615 31561762199745168205617923)
            ·
              refine ⟨47342643299617752308426885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31561762199745168205617923 47342643299617752308426885)
              ·
                refine ⟨8876745618678328557830041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47342643299617752308426885 8876745618678328557830041)
                ·
                  refine ⟨6657559214008746418372531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876745618678328557830041 6657559214008746418372531)
                  ·
                    refine ⟨9986338821013119627558797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657559214008746418372531 9986338821013119627558797)
                    ·
                      refine ⟨3744877057879919860334549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986338821013119627558797 3744877057879919860334549)
                      ·
                        rfl

theorem cell23_7293122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7293122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293122 prefixEnd_7293122 := by exact prefixLift 7293122
  have htrace : WordTrace (prefixWord ++ tailWord_7293122) baseStart_7293122 baseEnd_7293122 := by
    simpa [prefixWord, tailWord_7293122, baseEnd_7293122] using wordTrace_append hprefix tailTrace_7293122
  have hstable : (prefixWord ++ tailWord_7293122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293122).length < 2 ^ (prefixWord ++ tailWord_7293122).sum := by decide
  have hdescent : baseEnd_7293122 < baseStart_7293122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293164 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_7293164 : Nat := 118140960795 + 7293164 * 2 ^ 59
def prefixEnd_7293164 : Nat := 4983230072969 + 3 ^ 40 * 7293164 * 2
def baseEnd_7293164 : Nat := 1248299541355802898669785

theorem tailTrace_7293164 : CollatzResearch.WordTrace tailWord_7293164 prefixEnd_7293164 1248299541355802898669785 := by
  unfold tailWord_7293164
  simp only [CollatzResearch.WordTrace]
  refine ⟨133001772075059938045579273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177335696100079917394105697 133001772075059938045579273)
  ·
    refine ⟨99751329056294953534184455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133001772075059938045579273 99751329056294953534184455)
    ·
      refine ⟨149626993584442430301276683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99751329056294953534184455 149626993584442430301276683)
      ·
        refine ⟨224440490376663645451915025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149626993584442430301276683 224440490376663645451915025)
        ·
          refine ⟨168330367782497734088936269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224440490376663645451915025 168330367782497734088936269)
          ·
            refine ⟨63123887918436650283351101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168330367782497734088936269 63123887918436650283351101)
            ·
              refine ⟨23671457969413743856256663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63123887918436650283351101 23671457969413743856256663)
              ·
                refine ⟨35507186954120615784384995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23671457969413743856256663 35507186954120615784384995)
                ·
                  refine ⟨53260780431180923676577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35507186954120615784384995 53260780431180923676577493)
                  ·
                    refine ⟨1248299541355802898669785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53260780431180923676577493 1248299541355802898669785)
                    ·
                      rfl

theorem cell23_7293164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_7293164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293164 prefixEnd_7293164 := by exact prefixLift 7293164
  have htrace : WordTrace (prefixWord ++ tailWord_7293164) baseStart_7293164 baseEnd_7293164 := by
    simpa [prefixWord, tailWord_7293164, baseEnd_7293164] using wordTrace_append hprefix tailTrace_7293164
  have hstable : (prefixWord ++ tailWord_7293164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293164).length < 2 ^ (prefixWord ++ tailWord_7293164).sum := by decide
  have hdescent : baseEnd_7293164 < baseStart_7293164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293211 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 3, 4]
def baseStart_7293211 : Nat := 118140960795 + 7293211 * 2 ^ 59
def prefixEnd_7293211 : Nat := 4983230072969 + 3 ^ 40 * 7293211 * 2
def baseEnd_7293211 : Nat := 1248307585886056670707213

theorem tailTrace_7293211 : CollatzResearch.WordTrace tailWord_7293211 prefixEnd_7293211 1248307585886056670707213 := by
  unfold tailWord_7293211
  simp only [CollatzResearch.WordTrace]
  refine ⟨266005258380949603118119487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177336838920633068745412991 266005258380949603118119487)
  ·
    refine ⟨399007887571424404677179231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266005258380949603118119487 399007887571424404677179231)
    ·
      refine ⟨598511831357136607015768847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399007887571424404677179231 598511831357136607015768847)
      ·
        refine ⟨897767747035704910523653271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598511831357136607015768847 897767747035704910523653271)
        ·
          refine ⟨1346651620553557365785479907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897767747035704910523653271 1346651620553557365785479907)
          ·
            refine ⟨2019977430830336048678219861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346651620553557365785479907 2019977430830336048678219861)
            ·
              refine ⟨23671610517543000570447889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2019977430830336048678219861 23671610517543000570447889)
              ·
                refine ⟨17753707888157250427835917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23671610517543000570447889 17753707888157250427835917)
                ·
                  refine ⟨6657640458058968910438469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17753707888157250427835917 6657640458058968910438469)
                  ·
                    refine ⟨1248307585886056670707213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657640458058968910438469 1248307585886056670707213)
                    ·
                      rfl

theorem cell23_7293211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 4].length) (baseStart_7293211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293211 prefixEnd_7293211 := by exact prefixLift 7293211
  have htrace : WordTrace (prefixWord ++ tailWord_7293211) baseStart_7293211 baseEnd_7293211 := by
    simpa [prefixWord, tailWord_7293211, baseEnd_7293211] using wordTrace_append hprefix tailTrace_7293211
  have hstable : (prefixWord ++ tailWord_7293211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293211).length < 2 ^ (prefixWord ++ tailWord_7293211).sum := by decide
  have hdescent : baseEnd_7293211 < baseStart_7293211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293241 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 8]
def baseStart_7293241 : Nat := 118140960795 + 7293241 * 2 ^ 59
def prefixEnd_7293241 : Nat := 4983230072969 + 3 ^ 40 * 7293241 * 2
def baseEnd_7293241 : Nat := 416104240230867210527389

theorem tailTrace_7293241 : CollatzResearch.WordTrace tailWord_7293241 prefixEnd_7293241 416104240230867210527389 := by
  unfold tailWord_7293241
  simp only [CollatzResearch.WordTrace]
  refine ⟨266006352570840918241711577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177337568380560612161141051 266006352570840918241711577)
  ·
    refine ⟨199504764428130688681283683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266006352570840918241711577 199504764428130688681283683)
    ·
      refine ⟨299257146642196033021925525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199504764428130688681283683 299257146642196033021925525)
      ·
        refine ⟨14027678748852939047902759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299257146642196033021925525 14027678748852939047902759)
        ·
          refine ⟨21041518123279408571854139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027678748852939047902759 21041518123279408571854139)
          ·
            refine ⟨31562277184919112857781209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041518123279408571854139 31562277184919112857781209)
            ·
              refine ⟨23671707888689334643335907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31562277184919112857781209 23671707888689334643335907)
              ·
                refine ⟨35507561833034001965003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23671707888689334643335907 35507561833034001965003861)
                ·
                  refine ⟨416104240230867210527389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35507561833034001965003861 416104240230867210527389)
                  ·
                    rfl

theorem cell23_7293241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_7293241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293241 prefixEnd_7293241 := by exact prefixLift 7293241
  have htrace : WordTrace (prefixWord ++ tailWord_7293241) baseStart_7293241 baseEnd_7293241 := by
    simpa [prefixWord, tailWord_7293241, baseEnd_7293241] using wordTrace_append hprefix tailTrace_7293241
  have hstable : (prefixWord ++ tailWord_7293241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293241).length < 2 ^ (prefixWord ++ tailWord_7293241).sum := by decide
  have hdescent : baseEnd_7293241 < baseStart_7293241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293271 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 3, 5]
def baseStart_7293271 : Nat := 118140960795 + 7293271 * 2 ^ 59
def prefixEnd_7293271 : Nat := 4983230072969 + 3 ^ 40 * 7293271 * 2
def baseEnd_7293271 : Nat := 1248317855499146592457121

theorem tailTrace_7293271 : CollatzResearch.WordTrace tailWord_7293271 prefixEnd_7293271 1248317855499146592457121 := by
  unfold tailWord_7293271
  simp only [CollatzResearch.WordTrace]
  refine ⟨266007446760732233365303667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177338297840488155576869111 266007446760732233365303667)
  ·
    refine ⟨399011170141098350047955501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266007446760732233365303667 399011170141098350047955501)
    ·
      refine ⟨149629188802911881267983313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399011170141098350047955501 149629188802911881267983313)
      ·
        refine ⟨112221891602183910950987485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149629188802911881267983313 112221891602183910950987485)
        ·
          refine ⟨42083209350818966606620307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112221891602183910950987485 42083209350818966606620307)
          ·
            refine ⟨63124814026228449909930461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42083209350818966606620307 63124814026228449909930461)
            ·
              refine ⟨23671805259835668716223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63124814026228449909930461 23671805259835668716223923)
              ·
                refine ⟨35507707889753503074335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23671805259835668716223923 35507707889753503074335885)
                ·
                  refine ⟨13315390458657563652875957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35507707889753503074335885 13315390458657563652875957)
                  ·
                    refine ⟨1248317855499146592457121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13315390458657563652875957 1248317855499146592457121)
                    ·
                      rfl

theorem cell23_7293271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_7293271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293271 prefixEnd_7293271 := by exact prefixLift 7293271
  have htrace : WordTrace (prefixWord ++ tailWord_7293271) baseStart_7293271 baseEnd_7293271 := by
    simpa [prefixWord, tailWord_7293271, baseEnd_7293271] using wordTrace_append hprefix tailTrace_7293271
  have hstable : (prefixWord ++ tailWord_7293271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293271).length < 2 ^ (prefixWord ++ tailWord_7293271).sum := by decide
  have hdescent : baseEnd_7293271 < baseStart_7293271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293338 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7293338 : Nat := 118140960795 + 7293338 * 2 ^ 59
def prefixEnd_7293338 : Nat := 4983230072969 + 3 ^ 40 * 7293338 * 2
def baseEnd_7293338 : Nat := 3744987969701291015233555

theorem tailTrace_7293338 : CollatzResearch.WordTrace tailWord_7293338 prefixEnd_7293338 3744987969701291015233555 := by
  unfold tailWord_7293338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66502472612872375951998167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177339926967659669205328445 66502472612872375951998167)
  ·
    refine ⟨99753708919308563927997251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66502472612872375951998167 99753708919308563927997251)
    ·
      refine ⟨149630563378962845891995877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99753708919308563927997251 149630563378962845891995877)
      ·
        refine ⟨28055730633555533604749227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149630563378962845891995877 28055730633555533604749227)
        ·
          refine ⟨42083595950333300407123841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28055730633555533604749227 42083595950333300407123841)
          ·
            refine ⟨31562696962749975305342881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42083595950333300407123841 31562696962749975305342881)
            ·
              refine ⟨23672022722062481479007161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31562696962749975305342881 23672022722062481479007161)
              ·
                refine ⟨17754017041546861109255371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23672022722062481479007161 17754017041546861109255371)
                ·
                  refine ⟨26631025562320291663883057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17754017041546861109255371 26631025562320291663883057)
                  ·
                    refine ⟨19973269171740218747912293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26631025562320291663883057 19973269171740218747912293)
                    ·
                      refine ⟨3744987969701291015233555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19973269171740218747912293 3744987969701291015233555)
                      ·
                        rfl

theorem cell23_7293338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7293338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293338 prefixEnd_7293338 := by exact prefixLift 7293338
  have htrace : WordTrace (prefixWord ++ tailWord_7293338) baseStart_7293338 baseEnd_7293338 := by
    simpa [prefixWord, tailWord_7293338, baseEnd_7293338] using wordTrace_append hprefix tailTrace_7293338
  have hstable : (prefixWord ++ tailWord_7293338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293338).length < 2 ^ (prefixWord ++ tailWord_7293338).sum := by decide
  have hdescent : baseEnd_7293338 < baseStart_7293338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293342 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7293342 : Nat := 118140960795 + 7293342 * 2 ^ 59
def prefixEnd_7293342 : Nat := 4983230072969 + 3 ^ 40 * 7293342 * 2
def baseEnd_7293342 : Nat := 3744990023623908999583537

theorem tailTrace_7293342 : CollatzResearch.WordTrace tailWord_7293342 prefixEnd_7293342 3744990023623908999583537 := by
  unfold tailWord_7293342
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251254542934376561392285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177340024228983341660758853 33251254542934376561392285)
  ·
    refine ⟨12469220453600391210522107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33251254542934376561392285 12469220453600391210522107)
    ·
      refine ⟨18703830680400586815783161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469220453600391210522107 18703830680400586815783161)
      ·
        refine ⟨14027873010300440111837371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18703830680400586815783161 14027873010300440111837371)
        ·
          refine ⟨21041809515450660167756057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027873010300440111837371 21041809515450660167756057)
          ·
            refine ⟨15781357136587995125817043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21041809515450660167756057 15781357136587995125817043)
            ·
              refine ⟨23672035704881992688725565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781357136587995125817043 23672035704881992688725565)
              ·
                refine ⟨8877013389330747258272087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23672035704881992688725565 8877013389330747258272087)
                ·
                  refine ⟨13315520083996120887408131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877013389330747258272087 13315520083996120887408131)
                  ·
                    refine ⟨19973280125994181331112197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13315520083996120887408131 19973280125994181331112197)
                    ·
                      refine ⟨3744990023623908999583537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19973280125994181331112197 3744990023623908999583537)
                      ·
                        rfl

theorem cell23_7293342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7293342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293342 prefixEnd_7293342 := by exact prefixLift 7293342
  have htrace : WordTrace (prefixWord ++ tailWord_7293342) baseStart_7293342 baseEnd_7293342 := by
    simpa [prefixWord, tailWord_7293342, baseEnd_7293342] using wordTrace_append hprefix tailTrace_7293342
  have hstable : (prefixWord ++ tailWord_7293342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293342).length < 2 ^ (prefixWord ++ tailWord_7293342).sum := by decide
  have hdescent : baseEnd_7293342 < baseStart_7293342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293352 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7293352 : Nat := 118140960795 + 7293352 * 2 ^ 59
def prefixEnd_7293352 : Nat := 4983230072969 + 3 ^ 40 * 7293352 * 2
def baseEnd_7293352 : Nat := 1248331719476817986819497

theorem tailTrace_7293352 : CollatzResearch.WordTrace tailWord_7293352 prefixEnd_7293352 1248331719476817986819497 := by
  unfold tailWord_7293352
  simp only [CollatzResearch.WordTrace]
  refine ⟨133005200536719392099501155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177340267382292522799334873 133005200536719392099501155)
  ·
    refine ⟨199507800805079088149251733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133005200536719392099501155 199507800805079088149251733)
    ·
      refine ⟨9351928162738082256996175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199507800805079088149251733 9351928162738082256996175)
      ·
        refine ⟨14027892244107123385494263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351928162738082256996175 14027892244107123385494263)
        ·
          refine ⟨21041838366160685078241395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027892244107123385494263 21041838366160685078241395)
          ·
            refine ⟨31562757549241027617362093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041838366160685078241395 31562757549241027617362093)
            ·
              refine ⟨11836034080965385356510785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31562757549241027617362093 11836034080965385356510785)
              ·
                refine ⟨8877025560724039017383089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836034080965385356510785 8877025560724039017383089)
                ·
                  refine ⟨6657769170543029263037317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8877025560724039017383089 6657769170543029263037317)
                  ·
                    refine ⟨1248331719476817986819497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657769170543029263037317 1248331719476817986819497)
                    ·
                      rfl

theorem cell23_7293352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7293352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293352 prefixEnd_7293352 := by exact prefixLift 7293352
  have htrace : WordTrace (prefixWord ++ tailWord_7293352) baseStart_7293352 baseEnd_7293352 := by
    simpa [prefixWord, tailWord_7293352, baseEnd_7293352] using wordTrace_append hprefix tailTrace_7293352
  have hstable : (prefixWord ++ tailWord_7293352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293352).length < 2 ^ (prefixWord ++ tailWord_7293352).sum := by decide
  have hdescent : baseEnd_7293352 < baseStart_7293352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293385 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 1, 3, 2]
def baseStart_7293385 : Nat := 118140960795 + 7293385 * 2 ^ 59
def prefixEnd_7293385 : Nat := 4983230072969 + 3 ^ 40 * 7293385 * 2
def baseEnd_7293385 : Nat := 3745012103292052331345839

theorem tailTrace_7293385 : CollatzResearch.WordTrace tailWord_7293385 prefixEnd_7293385 3745012103292052331345839 := by
  unfold tailWord_7293385
  simp only [CollatzResearch.WordTrace]
  refine ⟨266011604682319230834953609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177341069788212820556635739 266011604682319230834953609)
  ·
    refine ⟨199508703511739423126215207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266011604682319230834953609 199508703511739423126215207)
    ·
      refine ⟨299263055267609134689322811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199508703511739423126215207 299263055267609134689322811)
      ·
        refine ⟨448894582901413702033984217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299263055267609134689322811 448894582901413702033984217)
        ·
          refine ⟨336670937176060276525488163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448894582901413702033984217 336670937176060276525488163)
          ·
            refine ⟨505006405764090414788232245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336670937176060276525488163 505006405764090414788232245)
            ·
              refine ⟨47344350540383476386396773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505006405764090414788232245 47344350540383476386396773)
              ·
                refine ⟨8877065726321901822449395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47344350540383476386396773 8877065726321901822449395)
                ·
                  refine ⟨13315598589482852733674093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877065726321901822449395 13315598589482852733674093)
                  ·
                    refine ⟨4993349471056069775127785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13315598589482852733674093 4993349471056069775127785)
                    ·
                      refine ⟨3745012103292052331345839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993349471056069775127785 3745012103292052331345839)
                      ·
                        rfl

theorem cell23_7293385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3, 2].length) (baseStart_7293385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293385 prefixEnd_7293385 := by exact prefixLift 7293385
  have htrace : WordTrace (prefixWord ++ tailWord_7293385) baseStart_7293385 baseEnd_7293385 := by
    simpa [prefixWord, tailWord_7293385, baseEnd_7293385] using wordTrace_append hprefix tailTrace_7293385
  have hstable : (prefixWord ++ tailWord_7293385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293385).length < 2 ^ (prefixWord ++ tailWord_7293385).sum := by decide
  have hdescent : baseEnd_7293385 < baseStart_7293385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293410 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7293410 : Nat := 118140960795 + 7293410 * 2 ^ 59
def prefixEnd_7293410 : Nat := 4983230072969 + 3 ^ 40 * 7293410 * 2
def baseEnd_7293410 : Nat := 3745024940308414733533225

theorem tailTrace_7293410 : CollatzResearch.WordTrace tailWord_7293410 prefixEnd_7293410 3745024940308414733533225 := by
  unfold tailWord_7293410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66503129126807165026153421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177341677671485773403075789 66503129126807165026153421)
  ·
    refine ⟨24938673422552686884807533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66503129126807165026153421 24938673422552686884807533)
    ·
      refine ⟨9352002533457257581802825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24938673422552686884807533 9352002533457257581802825)
      ·
        refine ⟨7014001900092943186352119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352002533457257581802825 7014001900092943186352119)
        ·
          refine ⟨10521002850139414779528179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014001900092943186352119 10521002850139414779528179)
          ·
            refine ⟨15781504275209122169292269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521002850139414779528179 15781504275209122169292269)
            ·
              refine ⟨5918064103203420813484601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15781504275209122169292269 5918064103203420813484601)
              ·
                refine ⟨4438548077402565610113451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5918064103203420813484601 4438548077402565610113451)
                ·
                  refine ⟨6657822116103848415170177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438548077402565610113451 6657822116103848415170177)
                  ·
                    refine ⟨4993366587077886311377633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6657822116103848415170177 4993366587077886311377633)
                    ·
                      refine ⟨3745024940308414733533225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993366587077886311377633 3745024940308414733533225)
                      ·
                        rfl

theorem cell23_7293410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7293410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293410 prefixEnd_7293410 := by exact prefixLift 7293410
  have htrace : WordTrace (prefixWord ++ tailWord_7293410) baseStart_7293410 baseEnd_7293410 := by
    simpa [prefixWord, tailWord_7293410, baseEnd_7293410] using wordTrace_append hprefix tailTrace_7293410
  have hstable : (prefixWord ++ tailWord_7293410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293410).length < 2 ^ (prefixWord ++ tailWord_7293410).sum := by decide
  have hdescent : baseEnd_7293410 < baseStart_7293410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293426 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7293426 : Nat := 118140960795 + 7293426 * 2 ^ 59
def prefixEnd_7293426 : Nat := 4983230072969 + 3 ^ 40 * 7293426 * 2
def baseEnd_7293426 : Nat := 3745033155998886670933151

theorem tailTrace_7293426 : CollatzResearch.WordTrace tailWord_7293426 prefixEnd_7293426 3745033155998886670933151 := by
  unfold tailWord_7293426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66503275018792673709299033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177342066716780463224797421 66503275018792673709299033)
  ·
    refine ⟨49877456264094505281974275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66503275018792673709299033 49877456264094505281974275)
    ·
      refine ⟨74816184396141757922961413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49877456264094505281974275 74816184396141757922961413)
      ·
        refine ⟨14028034574276579610555265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74816184396141757922961413 14028034574276579610555265)
        ·
          refine ⟨10521025930707434707916449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14028034574276579610555265 10521025930707434707916449)
          ·
            refine ⟨7890769448030576030937337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521025930707434707916449 7890769448030576030937337)
            ·
              refine ⟨5918077086022932023203003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890769448030576030937337 5918077086022932023203003)
              ·
                refine ⟨8877115629034398034804505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918077086022932023203003 8877115629034398034804505)
                ·
                  refine ⟨6657836721775798526103379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8877115629034398034804505 6657836721775798526103379)
                  ·
                    refine ⟨9986755082663697789155069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657836721775798526103379 9986755082663697789155069)
                    ·
                      refine ⟨3745033155998886670933151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986755082663697789155069 3745033155998886670933151)
                      ·
                        rfl

theorem cell23_7293426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7293426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293426 prefixEnd_7293426 := by exact prefixLift 7293426
  have htrace : WordTrace (prefixWord ++ tailWord_7293426) baseStart_7293426 baseEnd_7293426 := by
    simpa [prefixWord, tailWord_7293426, baseEnd_7293426] using wordTrace_append hprefix tailTrace_7293426
  have hstable : (prefixWord ++ tailWord_7293426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293426).length < 2 ^ (prefixWord ++ tailWord_7293426).sum := by decide
  have hdescent : baseEnd_7293426 < baseStart_7293426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293432 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_7293432 : Nat := 118140960795 + 7293432 * 2 ^ 59
def prefixEnd_7293432 : Nat := 4983230072969 + 3 ^ 40 * 7293432 * 2
def baseEnd_7293432 : Nat := 3745036236882813647458123

theorem tailTrace_7293432 : CollatzResearch.WordTrace tailWord_7293432 prefixEnd_7293432 3745036236882813647458123 := by
  unfold tailWord_7293432
  simp only [CollatzResearch.WordTrace]
  refine ⟨133006659456574478930957275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177342212608765971907943033 133006659456574478930957275)
  ·
    refine ⟨199509989184861718396435913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133006659456574478930957275 199509989184861718396435913)
    ·
      refine ⟨149632491888646288797326935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199509989184861718396435913 149632491888646288797326935)
      ·
        refine ⟨224448737832969433195990403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149632491888646288797326935 224448737832969433195990403)
        ·
          refine ⟨336673106749454149793985605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224448737832969433195990403 336673106749454149793985605)
          ·
            refine ⟨63126207515522653086372301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336673106749454149793985605 63126207515522653086372301)
            ·
              refine ⟨23672327818320994907389613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63126207515522653086372301 23672327818320994907389613)
              ·
                refine ⟨8877122931870373090271105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23672327818320994907389613 8877122931870373090271105)
                ·
                  refine ⟨6657842198902779817703329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8877122931870373090271105 6657842198902779817703329)
                  ·
                    refine ⟨4993381649177084863277497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6657842198902779817703329 4993381649177084863277497)
                    ·
                      refine ⟨3745036236882813647458123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993381649177084863277497 3745036236882813647458123)
                      ·
                        rfl

theorem cell23_7293432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_7293432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293432 prefixEnd_7293432 := by exact prefixLift 7293432
  have htrace : WordTrace (prefixWord ++ tailWord_7293432) baseStart_7293432 baseEnd_7293432 := by
    simpa [prefixWord, tailWord_7293432, baseEnd_7293432] using wordTrace_append hprefix tailTrace_7293432
  have hstable : (prefixWord ++ tailWord_7293432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293432).length < 2 ^ (prefixWord ++ tailWord_7293432).sum := by decide
  have hdescent : baseEnd_7293432 < baseStart_7293432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293448 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_7293448 : Nat := 118140960795 + 7293448 * 2 ^ 59
def prefixEnd_7293448 : Nat := 4983230072969 + 3 ^ 40 * 7293448 * 2
def baseEnd_7293448 : Nat := 3745044452573285584858049

theorem tailTrace_7293448 : CollatzResearch.WordTrace tailWord_7293448 prefixEnd_7293448 3745044452573285584858049 := by
  unfold tailWord_7293448
  simp only [CollatzResearch.WordTrace]
  refine ⟨133006951240545496297248499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177342601654060661729664665 133006951240545496297248499)
  ·
    refine ⟨199510426860818244445872749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133006951240545496297248499 199510426860818244445872749)
    ·
      refine ⟨74816410072806841667202281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199510426860818244445872749 74816410072806841667202281)
      ·
        refine ⟨56112307554605131250401711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74816410072806841667202281 56112307554605131250401711)
        ·
          refine ⟨84168461331907696875602567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56112307554605131250401711 84168461331907696875602567)
          ·
            refine ⟨126252691997861545313403851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84168461331907696875602567 126252691997861545313403851)
            ·
              refine ⟨189379037996792317970105777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126252691997861545313403851 189379037996792317970105777)
              ·
                refine ⟨142034278497594238477579333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189379037996792317970105777 142034278497594238477579333)
                ·
                  refine ⟨26631427218298919714546125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142034278497594238477579333 26631427218298919714546125)
                  ·
                    refine ⟨9986785206862094892954797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26631427218298919714546125 9986785206862094892954797)
                    ·
                      refine ⟨3745044452573285584858049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986785206862094892954797 3745044452573285584858049)
                      ·
                        rfl

theorem cell23_7293448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_7293448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293448 prefixEnd_7293448 := by exact prefixLift 7293448
  have htrace : WordTrace (prefixWord ++ tailWord_7293448) baseStart_7293448 baseEnd_7293448 := by
    simpa [prefixWord, tailWord_7293448, baseEnd_7293448] using wordTrace_append hprefix tailTrace_7293448
  have hstable : (prefixWord ++ tailWord_7293448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293448).length < 2 ^ (prefixWord ++ tailWord_7293448).sum := by decide
  have hdescent : baseEnd_7293448 < baseStart_7293448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293453 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7293453 : Nat := 118140960795 + 7293453 * 2 ^ 59
def prefixEnd_7293453 : Nat := 4983230072969 + 3 ^ 40 * 7293453 * 2
def baseEnd_7293453 : Nat := 3745047019976558065295527

theorem tailTrace_7293453 : CollatzResearch.WordTrace tailWord_7293453 prefixEnd_7293453 3745047019976558065295527 := by
  unfold tailWord_7293453
  simp only [CollatzResearch.WordTrace]
  refine ⟨266014084846072878448429013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177342723230715252298952675 266014084846072878448429013)
  ·
    refine ⟨6234705113579833088635055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 266014084846072878448429013 6234705113579833088635055)
    ·
      refine ⟨9352057670369749632952583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234705113579833088635055 9352057670369749632952583)
      ·
        refine ⟨14028086505554624449428875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9352057670369749632952583 14028086505554624449428875)
        ·
          refine ⟨21042129758331936674143313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028086505554624449428875 21042129758331936674143313)
          ·
            refine ⟨15781597318748952505607485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21042129758331936674143313 15781597318748952505607485)
            ·
              refine ⟨5918098994530857189602807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15781597318748952505607485 5918098994530857189602807)
              ·
                refine ⟨8877148491796285784404211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918098994530857189602807 8877148491796285784404211)
                ·
                  refine ⟨13315722737694428676606317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877148491796285784404211 13315722737694428676606317)
                  ·
                    refine ⟨4993396026635410753727369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13315722737694428676606317 4993396026635410753727369)
                    ·
                      refine ⟨3745047019976558065295527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993396026635410753727369 3745047019976558065295527)
                      ·
                        rfl

theorem cell23_7293453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7293453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293453 prefixEnd_7293453 := by exact prefixLift 7293453
  have htrace : WordTrace (prefixWord ++ tailWord_7293453) baseStart_7293453 baseEnd_7293453 := by
    simpa [prefixWord, tailWord_7293453, baseEnd_7293453] using wordTrace_append hprefix tailTrace_7293453
  have hstable : (prefixWord ++ tailWord_7293453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293453).length < 2 ^ (prefixWord ++ tailWord_7293453).sum := by decide
  have hdescent : baseEnd_7293453 < baseStart_7293453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293472 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 5]
def baseStart_7293472 : Nat := 118140960795 + 7293472 * 2 ^ 59
def prefixEnd_7293472 : Nat := 4983230072969 + 3 ^ 40 * 7293472 * 2
def baseEnd_7293472 : Nat := 416117419567665943439771

theorem tailTrace_7293472 : CollatzResearch.WordTrace tailWord_7293472 prefixEnd_7293472 416117419567665943439771 := by
  unfold tailWord_7293472
  simp only [CollatzResearch.WordTrace]
  refine ⟨133007388916502022346685335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177343185222002696462247113 133007388916502022346685335)
  ·
    refine ⟨199511083374753033520028003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133007388916502022346685335 199511083374753033520028003)
    ·
      refine ⟨299266625062129550280042005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199511083374753033520028003 299266625062129550280042005)
      ·
        refine ⟨14028123049787322669376969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299266625062129550280042005 14028123049787322669376969)
        ·
          refine ⟨10521092287340492002032727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14028123049787322669376969 10521092287340492002032727)
          ·
            refine ⟨15781638431010738003049091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521092287340492002032727 15781638431010738003049091)
            ·
              refine ⟨23672457646516107004573637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781638431010738003049091 23672457646516107004573637)
              ·
                refine ⟨4438585808721770063357557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23672457646516107004573637 4438585808721770063357557)
                ·
                  refine ⟨416117419567665943439771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438585808721770063357557 416117419567665943439771)
                  ·
                    rfl

theorem cell23_7293472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 5].length) (baseStart_7293472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293472 prefixEnd_7293472 := by exact prefixLift 7293472
  have htrace : WordTrace (prefixWord ++ tailWord_7293472) baseStart_7293472 baseEnd_7293472 := by
    simpa [prefixWord, tailWord_7293472, baseEnd_7293472] using wordTrace_append hprefix tailTrace_7293472
  have hstable : (prefixWord ++ tailWord_7293472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293472).length < 2 ^ (prefixWord ++ tailWord_7293472).sum := by decide
  have hdescent : baseEnd_7293472 < baseStart_7293472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293475 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 5, 2]
def baseStart_7293475 : Nat := 118140960795 + 7293475 * 2 ^ 59
def prefixEnd_7293475 : Nat := 4983230072969 + 3 ^ 40 * 7293475 * 2
def baseEnd_7293475 : Nat := 3745058316550956979220425

theorem tailTrace_7293475 : CollatzResearch.WordTrace tailWord_7293475 prefixEnd_7293475 3745058316550956979220425 := by
  unfold tailWord_7293475
  simp only [CollatzResearch.WordTrace]
  refine ⟨266014887251993176205729879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177343258167995450803819919 266014887251993176205729879)
  ·
    refine ⟨399022330877989764308594819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266014887251993176205729879 399022330877989764308594819)
    ·
      refine ⟨598533496316984646462892229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399022330877989764308594819 598533496316984646462892229)
      ·
        refine ⟨112225030559434621211792293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598533496316984646462892229 112225030559434621211792293)
        ·
          refine ⟨21042193229893991477211055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112225030559434621211792293 21042193229893991477211055)
          ·
            refine ⟨31563289844840987215816583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21042193229893991477211055 31563289844840987215816583)
            ·
              refine ⟨47344934767261480823724875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31563289844840987215816583 47344934767261480823724875)
              ·
                refine ⟨71017402150892221235587313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47344934767261480823724875 71017402150892221235587313)
                ·
                  refine ⟨53263051613169165926690485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71017402150892221235587313 53263051613169165926690485)
                  ·
                    refine ⟨4993411088734609305627233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53263051613169165926690485 4993411088734609305627233)
                    ·
                      refine ⟨3745058316550956979220425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993411088734609305627233 3745058316550956979220425)
                      ·
                        rfl

theorem cell23_7293475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_7293475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293475 prefixEnd_7293475 := by exact prefixLift 7293475
  have htrace : WordTrace (prefixWord ++ tailWord_7293475) baseStart_7293475 baseEnd_7293475 := by
    simpa [prefixWord, tailWord_7293475, baseEnd_7293475] using wordTrace_append hprefix tailTrace_7293475
  have hstable : (prefixWord ++ tailWord_7293475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293475).length < 2 ^ (prefixWord ++ tailWord_7293475).sum := by decide
  have hdescent : baseEnd_7293475 < baseStart_7293475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293488 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_7293488 : Nat := 118140960795 + 7293488 * 2 ^ 59
def prefixEnd_7293488 : Nat := 4983230072969 + 3 ^ 40 * 7293488 * 2
def baseEnd_7293488 : Nat := 3745064991799465428357865

theorem tailTrace_7293488 : CollatzResearch.WordTrace tailWord_7293488 prefixEnd_7293488 3745064991799465428357865 := by
  unfold tailWord_7293488
  simp only [CollatzResearch.WordTrace]
  refine ⟨133007680700473039712976559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177343574267297386283968745 133007680700473039712976559)
  ·
    refine ⟨199511521050709559569464839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133007680700473039712976559 199511521050709559569464839)
    ·
      refine ⟨299267281576064339354197259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199511521050709559569464839 299267281576064339354197259)
      ·
        refine ⟨448900922364096509031295889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299267281576064339354197259 448900922364096509031295889)
        ·
          refine ⟨336675691773072381773471917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448900922364096509031295889 336675691773072381773471917)
          ·
            refine ⟨126253384414902143165051969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336675691773072381773471917 126253384414902143165051969)
            ·
              refine ⟨94690038311176607373788977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126253384414902143165051969 94690038311176607373788977)
              ·
                refine ⟨71017528733382455530341733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94690038311176607373788977 71017528733382455530341733)
                ·
                  refine ⟨13315786637509210411939075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71017528733382455530341733 13315786637509210411939075)
                  ·
                    refine ⟨19973679956263815617908613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13315786637509210411939075 19973679956263815617908613)
                    ·
                      refine ⟨3745064991799465428357865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19973679956263815617908613 3745064991799465428357865)
                      ·
                        rfl

theorem cell23_7293488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_7293488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293488 prefixEnd_7293488 := by exact prefixLift 7293488
  have htrace : WordTrace (prefixWord ++ tailWord_7293488) baseStart_7293488 baseEnd_7293488 := by
    simpa [prefixWord, tailWord_7293488, baseEnd_7293488] using wordTrace_append hprefix tailTrace_7293488
  have hstable : (prefixWord ++ tailWord_7293488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293488).length < 2 ^ (prefixWord ++ tailWord_7293488).sum := by decide
  have hdescent : baseEnd_7293488 < baseStart_7293488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293502 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_7293502 : Nat := 118140960795 + 7293502 * 2 ^ 59
def prefixEnd_7293502 : Nat := 4983230072969 + 3 ^ 40 * 7293502 * 2
def baseEnd_7293502 : Nat := 1248357393509542791194267

theorem tailTrace_7293502 : CollatzResearch.WordTrace tailWord_7293502 prefixEnd_7293502 1248357393509542791194267 := by
  unfold tailWord_7293502
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251984002861919977120345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177343914681930239877975173 33251984002861919977120345)
  ·
    refine ⟨24938988002146439982840259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33251984002861919977120345 24938988002146439982840259)
    ·
      refine ⟨37408482003219659974260389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24938988002146439982840259 37408482003219659974260389)
      ·
        refine ⟨7014090375603686245173823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37408482003219659974260389 7014090375603686245173823)
        ·
          refine ⟨10521135563405529367760735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014090375603686245173823 10521135563405529367760735)
          ·
            refine ⟨15781703345108294051641103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521135563405529367760735 15781703345108294051641103)
            ·
              refine ⟨23672555017662441077461655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781703345108294051641103 23672555017662441077461655)
              ·
                refine ⟨35508832526493661616192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23672555017662441077461655 35508832526493661616192483)
                ·
                  refine ⟨53263248789740492424288725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35508832526493661616192483 53263248789740492424288725)
                  ·
                    refine ⟨1248357393509542791194267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53263248789740492424288725 1248357393509542791194267)
                    ·
                      rfl

theorem cell23_7293502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_7293502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293502 prefixEnd_7293502 := by exact prefixLift 7293502
  have htrace : WordTrace (prefixWord ++ tailWord_7293502) baseStart_7293502 baseEnd_7293502 := by
    simpa [prefixWord, tailWord_7293502, baseEnd_7293502] using wordTrace_append hprefix tailTrace_7293502
  have hstable : (prefixWord ++ tailWord_7293502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293502).length < 2 ^ (prefixWord ++ tailWord_7293502).sum := by decide
  have hdescent : baseEnd_7293502 < baseStart_7293502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293505 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7293505 : Nat := 118140960795 + 7293505 * 2 ^ 59
def prefixEnd_7293505 : Nat := 4983230072969 + 3 ^ 40 * 7293505 * 2
def baseEnd_7293505 : Nat := 3745073720970591861845287

theorem tailTrace_7293505 : CollatzResearch.WordTrace tailWord_7293505 prefixEnd_7293505 3745073720970591861845287 := by
  unfold tailWord_7293505
  simp only [CollatzResearch.WordTrace]
  refine ⟨266015981441884491329321969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177343987627922994219547979 266015981441884491329321969)
  ·
    refine ⟨199511986081413368496991477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266015981441884491329321969 199511986081413368496991477)
    ·
      refine ⟨18704248695132503296592951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199511986081413368496991477 18704248695132503296592951)
      ·
        refine ⟨28056373042698754944889427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18704248695132503296592951 28056373042698754944889427)
        ·
          refine ⟨42084559564048132417334141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28056373042698754944889427 42084559564048132417334141)
          ·
            refine ⟨15781709836518049656500303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42084559564048132417334141 15781709836518049656500303)
            ·
              refine ⟨23672564754777074484750455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781709836518049656500303 23672564754777074484750455)
              ·
                refine ⟨35508847132165611727125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23672564754777074484750455 35508847132165611727125683)
                ·
                  refine ⟨53263270698248417590688525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35508847132165611727125683 53263270698248417590688525)
                  ·
                    refine ⟨19973726511843156596508197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53263270698248417590688525 19973726511843156596508197)
                    ·
                      refine ⟨3745073720970591861845287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19973726511843156596508197 3745073720970591861845287)
                      ·
                        rfl

theorem cell23_7293505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7293505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293505 prefixEnd_7293505 := by exact prefixLift 7293505
  have htrace : WordTrace (prefixWord ++ tailWord_7293505) baseStart_7293505 baseEnd_7293505 := by
    simpa [prefixWord, tailWord_7293505, baseEnd_7293505] using wordTrace_append hprefix tailTrace_7293505
  have hstable : (prefixWord ++ tailWord_7293505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293505).length < 2 ^ (prefixWord ++ tailWord_7293505).sum := by decide
  have hdescent : baseEnd_7293505 < baseStart_7293505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293518 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7293518 : Nat := 118140960795 + 7293518 * 2 ^ 59
def prefixEnd_7293518 : Nat := 4983230072969 + 3 ^ 40 * 7293518 * 2
def baseEnd_7293518 : Nat := 3745080396219100310982727

theorem tailTrace_7293518 : CollatzResearch.WordTrace tailWord_7293518 prefixEnd_7293518 3745080396219100310982727 := by
  unfold tailWord_7293518
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252056948854674318693151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177344303727224929699696805 33252056948854674318693151)
  ·
    refine ⟨49878085423282011478039727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252056948854674318693151 49878085423282011478039727)
    ·
      refine ⟨74817128134923017217059591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49878085423282011478039727 74817128134923017217059591)
      ·
        refine ⟨112225692202384525825589387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74817128134923017217059591 112225692202384525825589387)
        ·
          refine ⟨168338538303576788738384081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112225692202384525825589387 168338538303576788738384081)
          ·
            refine ⟨126253903727682591553788061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168338538303576788738384081 126253903727682591553788061)
            ·
              refine ⟨47345213897880971832670523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126253903727682591553788061 47345213897880971832670523)
              ·
                refine ⟨71017820846821457749005785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47345213897880971832670523 71017820846821457749005785)
                ·
                  refine ⟨53263365635116093311754339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71017820846821457749005785 53263365635116093311754339)
                  ·
                    refine ⟨79895048452674139967631509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53263365635116093311754339 79895048452674139967631509)
                    ·
                      refine ⟨3745080396219100310982727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79895048452674139967631509 3745080396219100310982727)
                      ·
                        rfl

theorem cell23_7293518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7293518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293518 prefixEnd_7293518 := by exact prefixLift 7293518
  have htrace : WordTrace (prefixWord ++ tailWord_7293518) baseStart_7293518 baseEnd_7293518 := by
    simpa [prefixWord, tailWord_7293518, baseEnd_7293518] using wordTrace_append hprefix tailTrace_7293518
  have hstable : (prefixWord ++ tailWord_7293518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293518).length < 2 ^ (prefixWord ++ tailWord_7293518).sum := by decide
  have hdescent : baseEnd_7293518 < baseStart_7293518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293525 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7293525 : Nat := 118140960795 + 7293525 * 2 ^ 59
def prefixEnd_7293525 : Nat := 4983230072969 + 3 ^ 40 * 7293525 * 2
def baseEnd_7293525 : Nat := 3745083990583681783595195

theorem tailTrace_7293525 : CollatzResearch.WordTrace tailWord_7293525 prefixEnd_7293525 3745083990583681783595195 := by
  unfold tailWord_7293525
  simp only [CollatzResearch.WordTrace]
  refine ⟨266016710901812034745050029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177344473934541356496700019 266016710901812034745050029)
  ·
    refine ⟨99756266588179513029393761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266016710901812034745050029 99756266588179513029393761)
    ·
      refine ⟨74817199941134634772045321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99756266588179513029393761 74817199941134634772045321)
      ·
        refine ⟨56112899955850976079033991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74817199941134634772045321 56112899955850976079033991)
        ·
          refine ⟨84169349933776464118550987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56112899955850976079033991 84169349933776464118550987)
          ·
            refine ⟨126254024900664696177826481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84169349933776464118550987 126254024900664696177826481)
            ·
              refine ⟨94690518675498522133369861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126254024900664696177826481 94690518675498522133369861)
              ·
                refine ⟨17754472251655972900006849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94690518675498522133369861 17754472251655972900006849)
                ·
                  refine ⟨13315854188741979675005137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17754472251655972900006849 13315854188741979675005137)
                  ·
                    refine ⟨9986890641556484756253853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13315854188741979675005137 9986890641556484756253853)
                    ·
                      refine ⟨3745083990583681783595195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986890641556484756253853 3745083990583681783595195)
                      ·
                        rfl

theorem cell23_7293525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7293525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293525 prefixEnd_7293525 := by exact prefixLift 7293525
  have htrace : WordTrace (prefixWord ++ tailWord_7293525) baseStart_7293525 baseEnd_7293525 := by
    simpa [prefixWord, tailWord_7293525, baseEnd_7293525] using wordTrace_append hprefix tailTrace_7293525
  have hstable : (prefixWord ++ tailWord_7293525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293525).length < 2 ^ (prefixWord ++ tailWord_7293525).sum := by decide
  have hdescent : baseEnd_7293525 < baseStart_7293525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 3]
def baseStart_7293555 : Nat := 118140960795 + 7293555 * 2 ^ 59
def prefixEnd_7293555 : Nat := 4983230072969 + 3 ^ 40 * 7293555 * 2
def baseEnd_7293555 : Nat := 3745099395003316666220057

theorem tailTrace_7293555 : CollatzResearch.WordTrace tailWord_7293555 prefixEnd_7293555 3745099395003316666220057 := by
  unfold tailWord_7293555
  simp only [CollatzResearch.WordTrace]
  refine ⟨266017805091703349868642119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177345203394468899912428079 266017805091703349868642119)
  ·
    refine ⟨399026707637555024802963179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266017805091703349868642119 399026707637555024802963179)
    ·
      refine ⟨598540061456332537204444769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399026707637555024802963179 598540061456332537204444769)
      ·
        refine ⟨448905046092249402903333577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598540061456332537204444769 448905046092249402903333577)
        ·
          refine ⟨336678784569187052177500183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448905046092249402903333577 336678784569187052177500183)
          ·
            refine ⟨505018176853780578266250275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336678784569187052177500183 505018176853780578266250275)
            ·
              refine ⟨757527265280670867399375413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505018176853780578266250275 757527265280670867399375413)
              ·
                refine ⟨71018181120062893818691445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 757527265280670867399375413 71018181120062893818691445)
                ·
                  refine ⟨6657954480005896295502323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71018181120062893818691445 6657954480005896295502323)
                  ·
                    refine ⟨9986931720008844443253485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657954480005896295502323 9986931720008844443253485)
                    ·
                      refine ⟨3745099395003316666220057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9986931720008844443253485 3745099395003316666220057)
                      ·
                        rfl

theorem cell23_7293555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_7293555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293555 prefixEnd_7293555 := by exact prefixLift 7293555
  have htrace : WordTrace (prefixWord ++ tailWord_7293555) baseStart_7293555 baseEnd_7293555 := by
    simpa [prefixWord, tailWord_7293555, baseEnd_7293555] using wordTrace_append hprefix tailTrace_7293555
  have hstable : (prefixWord ++ tailWord_7293555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293555).length < 2 ^ (prefixWord ++ tailWord_7293555).sum := by decide
  have hdescent : baseEnd_7293555 < baseStart_7293555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293575 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 1, 5]
def baseStart_7293575 : Nat := 118140960795 + 7293575 * 2 ^ 59
def prefixEnd_7293575 : Nat := 4983230072969 + 3 ^ 40 * 7293575 * 2
def baseEnd_7293575 : Nat := 1248369888205468862656655

theorem tailTrace_7293575 : CollatzResearch.WordTrace tailWord_7293575 prefixEnd_7293575 1248369888205468862656655 := by
  unfold tailWord_7293575
  simp only [CollatzResearch.WordTrace]
  refine ⟨266018534551630893284370179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177345689701087262189580119 266018534551630893284370179)
  ·
    refine ⟨399027801827446339926555269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266018534551630893284370179 399027801827446339926555269)
    ·
      refine ⟨74817712842646188736229113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399027801827446339926555269 74817712842646188736229113)
      ·
        refine ⟨56113284631984641552171835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74817712842646188736229113 56113284631984641552171835)
        ·
          refine ⟨84169926947976962328257753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56113284631984641552171835 84169926947976962328257753)
          ·
            refine ⟨63127445210982721746193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84169926947976962328257753 63127445210982721746193315)
            ·
              refine ⟨94691167816474082619289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63127445210982721746193315 94691167816474082619289973)
              ·
                refine ⟨8877296982794445245558435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94691167816474082619289973 8877296982794445245558435)
                ·
                  refine ⟨13315945474191667868337653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877296982794445245558435 13315945474191667868337653)
                  ·
                    refine ⟨1248369888205468862656655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13315945474191667868337653 1248369888205468862656655)
                    ·
                      rfl

theorem cell23_7293575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_7293575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293575 prefixEnd_7293575 := by exact prefixLift 7293575
  have htrace : WordTrace (prefixWord ++ tailWord_7293575) baseStart_7293575 baseEnd_7293575 := by
    simpa [prefixWord, tailWord_7293575, baseEnd_7293575] using wordTrace_append hprefix tailTrace_7293575
  have hstable : (prefixWord ++ tailWord_7293575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293575).length < 2 ^ (prefixWord ++ tailWord_7293575).sum := by decide
  have hdescent : baseEnd_7293575 < baseStart_7293575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293629 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_7293629 : Nat := 118140960795 + 7293629 * 2 ^ 59
def prefixEnd_7293629 : Nat := 4983230072969 + 3 ^ 40 * 7293629 * 2
def baseEnd_7293629 : Nat := 3745137392571749376694717

theorem tailTrace_7293629 : CollatzResearch.WordTrace tailWord_7293629 prefixEnd_7293629 3745137392571749376694717 := by
  unfold tailWord_7293629
  simp only [CollatzResearch.WordTrace]
  refine ⟨266020504093435260506835941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177347002728956840337890627 266020504093435260506835941)
  ·
    refine ⟨49878844517519111345031739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266020504093435260506835941 49878844517519111345031739)
    ·
      refine ⟨74818266776278667017547609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49878844517519111345031739 74818266776278667017547609)
      ·
        refine ⟨56113700082209000263160707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74818266776278667017547609 56113700082209000263160707)
        ·
          refine ⟨84170550123313500394741061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56113700082209000263160707 84170550123313500394741061)
          ·
            refine ⟨15781978148121281324013949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84170550123313500394741061 15781978148121281324013949)
            ·
              refine ⟨5918241805545480496505231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15781978148121281324013949 5918241805545480496505231)
              ·
                refine ⟨8877362708318220744757847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918241805545480496505231 8877362708318220744757847)
                ·
                  refine ⟨13316044062477331117136771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877362708318220744757847 13316044062477331117136771)
                  ·
                    refine ⟨19974066093715996675705157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13316044062477331117136771 19974066093715996675705157)
                    ·
                      refine ⟨3745137392571749376694717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19974066093715996675705157 3745137392571749376694717)
                      ·
                        rfl

theorem cell23_7293629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_7293629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293629 prefixEnd_7293629 := by exact prefixLift 7293629
  have htrace : WordTrace (prefixWord ++ tailWord_7293629) baseStart_7293629 baseEnd_7293629 := by
    simpa [prefixWord, tailWord_7293629, baseEnd_7293629] using wordTrace_append hprefix tailTrace_7293629
  have hstable : (prefixWord ++ tailWord_7293629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293629).length < 2 ^ (prefixWord ++ tailWord_7293629).sum := by decide
  have hdescent : baseEnd_7293629 < baseStart_7293629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293632 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_7293632 : Nat := 118140960795 + 7293632 * 2 ^ 59
def prefixEnd_7293632 : Nat := 4983230072969 + 3 ^ 40 * 7293632 * 2
def baseEnd_7293632 : Nat := 3745138933013712864957203

theorem tailTrace_7293632 : CollatzResearch.WordTrace tailWord_7293632 prefixEnd_7293632 3745138933013712864957203 := by
  unfold tailWord_7293632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133010306756212196009597575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177347075674949594679463433 133010306756212196009597575)
  ·
    refine ⟨199515460134318294014396363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133010306756212196009597575 199515460134318294014396363)
    ·
      refine ⟨299273190201477441021594545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199515460134318294014396363 299273190201477441021594545)
      ·
        refine ⟨224454892651108080766195909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299273190201477441021594545 224454892651108080766195909)
        ·
          refine ⟨42085292372082765143661733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224454892651108080766195909 42085292372082765143661733)
          ·
            refine ⟨7890992319765518464436575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42085292372082765143661733 7890992319765518464436575)
            ·
              refine ⟨11836488479648277696654863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890992319765518464436575 11836488479648277696654863)
              ·
                refine ⟨17754732719472416544982295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836488479648277696654863 17754732719472416544982295)
                ·
                  refine ⟨26632099079208624817473443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17754732719472416544982295 26632099079208624817473443)
                  ·
                    refine ⟨39948148618812937226210165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26632099079208624817473443 39948148618812937226210165)
                    ·
                      refine ⟨3745138933013712864957203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39948148618812937226210165 3745138933013712864957203)
                      ·
                        rfl

theorem cell23_7293632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_7293632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293632 prefixEnd_7293632 := by exact prefixLift 7293632
  have htrace : WordTrace (prefixWord ++ tailWord_7293632) baseStart_7293632 baseEnd_7293632 := by
    simpa [prefixWord, tailWord_7293632, baseEnd_7293632] using wordTrace_append hprefix tailTrace_7293632
  have hstable : (prefixWord ++ tailWord_7293632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293632).length < 2 ^ (prefixWord ++ tailWord_7293632).sum := by decide
  have hdescent : baseEnd_7293632 < baseStart_7293632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293705 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_7293705 : Nat := 118140960795 + 7293705 * 2 ^ 59
def prefixEnd_7293705 : Nat := 4983230072969 + 3 ^ 40 * 7293705 * 2
def baseEnd_7293705 : Nat := 3745176417101491079344367

theorem tailTrace_7293705 : CollatzResearch.WordTrace tailWord_7293705 prefixEnd_7293705 3745176417101491079344367 := by
  unfold tailWord_7293705
  simp only [CollatzResearch.WordTrace]
  refine ⟨266023276041159925486602569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177348850694106616991068379 266023276041159925486602569)
  ·
    refine ⟨199517457030869944114951927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266023276041159925486602569 199517457030869944114951927)
    ·
      refine ⟨299276185546304916172427891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199517457030869944114951927 299276185546304916172427891)
      ·
        refine ⟨448914278319457374258641837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299276185546304916172427891 448914278319457374258641837)
        ·
          refine ⟨168342854369796515346990689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448914278319457374258641837 168342854369796515346990689)
          ·
            refine ⟨126257140777347386510243017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168342854369796515346990689 126257140777347386510243017)
            ·
              refine ⟨94692855583010539882682263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126257140777347386510243017 94692855583010539882682263)
              ·
                refine ⟨142039283374515809824023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94692855583010539882682263 142039283374515809824023395)
                ·
                  refine ⟨213058925061773714736035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142039283374515809824023395 213058925061773714736035093)
                  ·
                    refine ⟨9987137112270642878251645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213058925061773714736035093 9987137112270642878251645)
                    ·
                      refine ⟨3745176417101491079344367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987137112270642878251645 3745176417101491079344367)
                      ·
                        rfl

theorem cell23_7293705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_7293705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293705 prefixEnd_7293705 := by exact prefixLift 7293705
  have htrace : WordTrace (prefixWord ++ tailWord_7293705) baseStart_7293705 baseEnd_7293705 := by
    simpa [prefixWord, tailWord_7293705, baseEnd_7293705] using wordTrace_append hprefix tailTrace_7293705
  have hstable : (prefixWord ++ tailWord_7293705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293705).length < 2 ^ (prefixWord ++ tailWord_7293705).sum := by decide
  have hdescent : baseEnd_7293705 < baseStart_7293705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293715 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_7293715 : Nat := 118140960795 + 7293715 * 2 ^ 59
def prefixEnd_7293715 : Nat := 4983230072969 + 3 ^ 40 * 7293715 * 2
def baseEnd_7293715 : Nat := 3745181551908036040219321

theorem tailTrace_7293715 : CollatzResearch.WordTrace tailWord_7293715 prefixEnd_7293715 3745181551908036040219321 := by
  unfold tailWord_7293715
  simp only [CollatzResearch.WordTrace]
  refine ⟨266023640771123697194466599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177349093847415798129644399 266023640771123697194466599)
  ·
    refine ⟨399035461156685545791699899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266023640771123697194466599 399035461156685545791699899)
    ·
      refine ⟨598553191735028318687549849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399035461156685545791699899 598553191735028318687549849)
      ·
        refine ⟨448914893801271239015662387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598553191735028318687549849 448914893801271239015662387)
        ·
          refine ⟨673372340701906858523493581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448914893801271239015662387 673372340701906858523493581)
          ·
            refine ⟨252514627763215071946310093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673372340701906858523493581 252514627763215071946310093)
            ·
              refine ⟨94692985411205651979866285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252514627763215071946310093 94692985411205651979866285)
              ·
                refine ⟨35509869529202119492449857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94692985411205651979866285 35509869529202119492449857)
                ·
                  refine ⟨26632402146901589619337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35509869529202119492449857 26632402146901589619337393)
                  ·
                    refine ⟨19974301610176192214503045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26632402146901589619337393 19974301610176192214503045)
                    ·
                      refine ⟨3745181551908036040219321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19974301610176192214503045 3745181551908036040219321)
                      ·
                        rfl

theorem cell23_7293715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_7293715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293715 prefixEnd_7293715 := by exact prefixLift 7293715
  have htrace : WordTrace (prefixWord ++ tailWord_7293715) baseStart_7293715 baseEnd_7293715 := by
    simpa [prefixWord, tailWord_7293715, baseEnd_7293715] using wordTrace_append hprefix tailTrace_7293715
  have hstable : (prefixWord ++ tailWord_7293715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293715).length < 2 ^ (prefixWord ++ tailWord_7293715).sum := by decide
  have hdescent : baseEnd_7293715 < baseStart_7293715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293815 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 8]
def baseStart_7293815 : Nat := 118140960795 + 7293815 * 2 ^ 59
def prefixEnd_7293815 : Nat := 4983230072969 + 3 ^ 40 * 7293815 * 2
def baseEnd_7293815 : Nat := 416136988885942849885429

theorem tailTrace_7293815 : CollatzResearch.WordTrace tailWord_7293815 prefixEnd_7293815 416136988885942849885429 := by
  unfold tailWord_7293815
  simp only [CollatzResearch.WordTrace]
  refine ⟨266027288070761414273106899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177351525380507609515404599 266027288070761414273106899)
  ·
    refine ⟨399040932106142121409660349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266027288070761414273106899 399040932106142121409660349)
    ·
      refine ⟨149640349539803295528622631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399040932106142121409660349 149640349539803295528622631)
      ·
        refine ⟨224460524309704943292933947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149640349539803295528622631 224460524309704943292933947)
        ·
          refine ⟨336690786464557414939400921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224460524309704943292933947 336690786464557414939400921)
          ·
            refine ⟨252518089848418061204550691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336690786464557414939400921 252518089848418061204550691)
            ·
              refine ⟨378777134772627091806826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252518089848418061204550691 378777134772627091806826037)
              ·
                refine ⟨35510356384933789856889941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378777134772627091806826037 35510356384933789856889941)
                ·
                  refine ⟨416136988885942849885429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35510356384933789856889941 416136988885942849885429)
                  ·
                    rfl

theorem cell23_7293815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 8].length) (baseStart_7293815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293815 prefixEnd_7293815 := by exact prefixLift 7293815
  have htrace : WordTrace (prefixWord ++ tailWord_7293815) baseStart_7293815 baseEnd_7293815 := by
    simpa [prefixWord, tailWord_7293815, baseEnd_7293815] using wordTrace_append hprefix tailTrace_7293815
  have hstable : (prefixWord ++ tailWord_7293815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293815).length < 2 ^ (prefixWord ++ tailWord_7293815).sum := by decide
  have hdescent : baseEnd_7293815 < baseStart_7293815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293896 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_7293896 : Nat := 118140960795 + 7293896 * 2 ^ 59
def prefixEnd_7293896 : Nat := 4983230072969 + 3 ^ 40 * 7293896 * 2
def baseEnd_7293896 : Nat := 1248424830635499944018663

theorem tailTrace_7293896 : CollatzResearch.WordTrace tailWord_7293896 prefixEnd_7293896 1248424830635499944018663 := by
  unfold tailWord_7293896
  simp only [CollatzResearch.WordTrace]
  refine ⟨133015121191733982553402771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177353494922311976737870361 133015121191733982553402771)
  ·
    refine ⟨199522681787600973830104157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133015121191733982553402771 199522681787600973830104157)
    ·
      refine ⟨74821005670350365186289059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199522681787600973830104157 74821005670350365186289059)
      ·
        refine ⟨112231508505525547779433589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74821005670350365186289059 112231508505525547779433589)
        ·
          refine ⟨10521703922393020104321899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112231508505525547779433589 10521703922393020104321899)
          ·
            refine ⟨15782555883589530156482849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521703922393020104321899 15782555883589530156482849)
            ·
              refine ⟨11836916912692147617362137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15782555883589530156482849 11836916912692147617362137)
              ·
                refine ⟨8877687684519110713021603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836916912692147617362137 8877687684519110713021603)
                ·
                  refine ⟨13316531526778666069532405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877687684519110713021603 13316531526778666069532405)
                  ·
                    refine ⟨1248424830635499944018663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13316531526778666069532405 1248424830635499944018663)
                    ·
                      rfl

theorem cell23_7293896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_7293896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293896 prefixEnd_7293896 := by exact prefixLift 7293896
  have htrace : WordTrace (prefixWord ++ tailWord_7293896) baseStart_7293896 baseEnd_7293896 := by
    simpa [prefixWord, tailWord_7293896, baseEnd_7293896] using wordTrace_append hprefix tailTrace_7293896
  have hstable : (prefixWord ++ tailWord_7293896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293896).length < 2 ^ (prefixWord ++ tailWord_7293896).sum := by decide
  have hdescent : baseEnd_7293896 < baseStart_7293896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293899 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 4]
def baseStart_7293899 : Nat := 118140960795 + 7293899 * 2 ^ 59
def prefixEnd_7293899 : Nat := 4983230072969 + 3 ^ 40 * 7293899 * 2
def baseEnd_7293899 : Nat := 3745276032348463320318475

theorem tailTrace_7293899 : CollatzResearch.WordTrace tailWord_7293899 prefixEnd_7293899 3745276032348463320318475 := by
  unfold tailWord_7293899
  simp only [CollatzResearch.WordTrace]
  refine ⟨266030351802457096619164751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177353567868304731079443167 266030351802457096619164751)
  ·
    refine ⟨399045527703685644928747127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266030351802457096619164751 399045527703685644928747127)
    ·
      refine ⟨598568291555528467393120691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399045527703685644928747127 598568291555528467393120691)
      ·
        refine ⟨897852437333292701089681037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598568291555528467393120691 897852437333292701089681037)
        ·
          refine ⟨336694663999984762908630389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 897852437333292701089681037 336694663999984762908630389)
          ·
            refine ⟨31565124749998571522684099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336694663999984762908630389 31565124749998571522684099)
            ·
              refine ⟨47347687124997857284026149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31565124749998571522684099 47347687124997857284026149)
              ·
                refine ⟨8877691335937098240754903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47347687124997857284026149 8877691335937098240754903)
                ·
                  refine ⟨13316537003905647361132355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877691335937098240754903 13316537003905647361132355)
                  ·
                    refine ⟨19974805505858471041698533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13316537003905647361132355 19974805505858471041698533)
                    ·
                      refine ⟨3745276032348463320318475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19974805505858471041698533 3745276032348463320318475)
                      ·
                        rfl

theorem cell23_7293899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 4].length) (baseStart_7293899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293899 prefixEnd_7293899 := by exact prefixLift 7293899
  have htrace : WordTrace (prefixWord ++ tailWord_7293899) baseStart_7293899 baseEnd_7293899 := by
    simpa [prefixWord, tailWord_7293899, baseEnd_7293899] using wordTrace_append hprefix tailTrace_7293899
  have hstable : (prefixWord ++ tailWord_7293899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293899).length < 2 ^ (prefixWord ++ tailWord_7293899).sum := by decide
  have hdescent : baseEnd_7293899 < baseStart_7293899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293949 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_7293949 : Nat := 118140960795 + 7293949 * 2 ^ 59
def prefixEnd_7293949 : Nat := 4983230072969 + 3 ^ 40 * 7293949 * 2
def baseEnd_7293949 : Nat := 3745301706381188124693245

theorem tailTrace_7293949 : CollatzResearch.WordTrace tailWord_7293949 prefixEnd_7293949 3745301706381188124693245 := by
  unfold tailWord_7293949
  simp only [CollatzResearch.WordTrace]
  refine ⟨266032175452275955158484901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177354783634850636772323267 266032175452275955158484901)
  ·
    refine ⟨49881032897301741592215919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266032175452275955158484901 49881032897301741592215919)
    ·
      refine ⟨74821549345952612388323879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49881032897301741592215919 74821549345952612388323879)
      ·
        refine ⟨112232324018928918582485819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74821549345952612388323879 112232324018928918582485819)
        ·
          refine ⟨168348486028393377873728729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112232324018928918582485819 168348486028393377873728729)
          ·
            refine ⟨126261364521295033405296547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168348486028393377873728729 126261364521295033405296547)
            ·
              refine ⟨189392046781942550107944821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126261364521295033405296547 189392046781942550107944821)
              ·
                refine ⟨17755504385807114072619827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189392046781942550107944821 17755504385807114072619827)
                ·
                  refine ⟨26633256578710671108929741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17755504385807114072619827 26633256578710671108929741)
                  ·
                    refine ⟨9987471217016501665848653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26633256578710671108929741 9987471217016501665848653)
                    ·
                      refine ⟨3745301706381188124693245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987471217016501665848653 3745301706381188124693245)
                      ·
                        rfl

theorem cell23_7293949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_7293949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293949 prefixEnd_7293949 := by exact prefixLift 7293949
  have htrace : WordTrace (prefixWord ++ tailWord_7293949) baseStart_7293949 baseEnd_7293949 := by
    simpa [prefixWord, tailWord_7293949, baseEnd_7293949] using wordTrace_append hprefix tailTrace_7293949
  have hstable : (prefixWord ++ tailWord_7293949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293949).length < 2 ^ (prefixWord ++ tailWord_7293949).sum := by decide
  have hdescent : baseEnd_7293949 < baseStart_7293949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293950 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7293950 : Nat := 118140960795 + 7293950 * 2 ^ 59
def prefixEnd_7293950 : Nat := 4983230072969 + 3 ^ 40 * 7293950 * 2
def baseEnd_7293950 : Nat := 3745302219861842620780741

theorem tailTrace_7293950 : CollatzResearch.WordTrace tailWord_7293950 prefixEnd_7293950 3745302219861842620780741 := by
  unfold tailWord_7293950
  simp only [CollatzResearch.WordTrace]
  refine ⟨33254026490659041541158913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177354807950181554886180869 33254026490659041541158913)
  ·
    refine ⟨24940519867994281155869185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33254026490659041541158913 24940519867994281155869185)
    ·
      refine ⟨18705389900995710866901889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24940519867994281155869185 18705389900995710866901889)
      ·
        refine ⟨14029042425746783150176417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18705389900995710866901889 14029042425746783150176417)
        ·
          refine ⟨10521781819310087362632313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14029042425746783150176417 10521781819310087362632313)
          ·
            refine ⟨7891336364482565521974235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521781819310087362632313 7891336364482565521974235)
            ·
              refine ⟨11837004546723848282961353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891336364482565521974235 11837004546723848282961353)
              ·
                refine ⟨8877753410042886212221015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837004546723848282961353 8877753410042886212221015)
                ·
                  refine ⟨13316630115064329318331523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877753410042886212221015 13316630115064329318331523)
                  ·
                    refine ⟨19974945172596493977497285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13316630115064329318331523 19974945172596493977497285)
                    ·
                      refine ⟨3745302219861842620780741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19974945172596493977497285 3745302219861842620780741)
                      ·
                        rfl

theorem cell23_7293950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7293950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293950 prefixEnd_7293950 := by exact prefixLift 7293950
  have htrace : WordTrace (prefixWord ++ tailWord_7293950) baseStart_7293950 baseEnd_7293950 := by
    simpa [prefixWord, tailWord_7293950, baseEnd_7293950] using wordTrace_append hprefix tailTrace_7293950
  have hstable : (prefixWord ++ tailWord_7293950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293950).length < 2 ^ (prefixWord ++ tailWord_7293950).sum := by decide
  have hdescent : baseEnd_7293950 < baseStart_7293950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293953 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_7293953 : Nat := 118140960795 + 7293953 * 2 ^ 59
def prefixEnd_7293953 : Nat := 4983230072969 + 3 ^ 40 * 7293953 * 2
def baseEnd_7293953 : Nat := 3745303760303806109043227

theorem tailTrace_7293953 : CollatzResearch.WordTrace tailWord_7293953 prefixEnd_7293953 3745303760303806109043227 := by
  unfold tailWord_7293953
  simp only [CollatzResearch.WordTrace]
  refine ⟨266032321344261463841630513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177354880896174309227753675 266032321344261463841630513)
  ·
    refine ⟨199524241008196097881222885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266032321344261463841630513 199524241008196097881222885)
    ·
      refine ⟨37410795189036768352729291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199524241008196097881222885 37410795189036768352729291)
      ·
        refine ⟨56116192783555152529093937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37410795189036768352729291 56116192783555152529093937)
        ·
          refine ⟨42087144587666364396820453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56116192783555152529093937 42087144587666364396820453)
          ·
            refine ⟨7891339610187443324403835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42087144587666364396820453 7891339610187443324403835)
            ·
              refine ⟨11837009415281164986605753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891339610187443324403835 11837009415281164986605753)
              ·
                refine ⟨8877757061460873739954315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837009415281164986605753 8877757061460873739954315)
                ·
                  refine ⟨13316635592191310609931473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877757061460873739954315 13316635592191310609931473)
                  ·
                    refine ⟨9987476694143482957448605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13316635592191310609931473 9987476694143482957448605)
                    ·
                      refine ⟨3745303760303806109043227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987476694143482957448605 3745303760303806109043227)
                      ·
                        rfl

theorem cell23_7293953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_7293953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293953 prefixEnd_7293953 := by exact prefixLift 7293953
  have htrace : WordTrace (prefixWord ++ tailWord_7293953) baseStart_7293953 baseEnd_7293953 := by
    simpa [prefixWord, tailWord_7293953, baseEnd_7293953] using wordTrace_append hprefix tailTrace_7293953
  have hstable : (prefixWord ++ tailWord_7293953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293953).length < 2 ^ (prefixWord ++ tailWord_7293953).sum := by decide
  have hdescent : baseEnd_7293953 < baseStart_7293953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293966 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7293966 : Nat := 118140960795 + 7293966 * 2 ^ 59
def prefixEnd_7293966 : Nat := 4983230072969 + 3 ^ 40 * 7293966 * 2
def baseEnd_7293966 : Nat := 3745310435552314558180667

theorem tailTrace_7293966 : CollatzResearch.WordTrace tailWord_7293966 prefixEnd_7293966 3745310435552314558180667 := by
  unfold tailWord_7293966
  simp only [CollatzResearch.WordTrace]
  refine ⟨33254099436651795882731719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177355196995476244707902501 33254099436651795882731719)
  ·
    refine ⟨49881149154977693824097579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33254099436651795882731719 49881149154977693824097579)
    ·
      refine ⟨74821723732466540736146369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49881149154977693824097579 74821723732466540736146369)
      ·
        refine ⟨56116292799349905552109777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74821723732466540736146369 56116292799349905552109777)
        ·
          refine ⟨42087219599512429164082333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56116292799349905552109777 42087219599512429164082333)
          ·
            refine ⟨15782707349817160936530875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42087219599512429164082333 15782707349817160936530875)
            ·
              refine ⟨23674061024725741404796313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15782707349817160936530875 23674061024725741404796313)
              ·
                refine ⟨17755545768544306053597235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23674061024725741404796313 17755545768544306053597235)
                ·
                  refine ⟨26633318652816459080395853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17755545768544306053597235 26633318652816459080395853)
                  ·
                    refine ⟨9987494494806172155148445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26633318652816459080395853 9987494494806172155148445)
                    ·
                      refine ⟨3745310435552314558180667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987494494806172155148445 3745310435552314558180667)
                      ·
                        rfl

theorem cell23_7293966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7293966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293966 prefixEnd_7293966 := by exact prefixLift 7293966
  have htrace : WordTrace (prefixWord ++ tailWord_7293966) baseStart_7293966 baseEnd_7293966 := by
    simpa [prefixWord, tailWord_7293966, baseEnd_7293966] using wordTrace_append hprefix tailTrace_7293966
  have hstable : (prefixWord ++ tailWord_7293966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293966).length < 2 ^ (prefixWord ++ tailWord_7293966).sum := by decide
  have hdescent : baseEnd_7293966 < baseStart_7293966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7293983 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_7293983 : Nat := 118140960795 + 7293983 * 2 ^ 59
def prefixEnd_7293983 : Nat := 4983230072969 + 3 ^ 40 * 7293983 * 2
def baseEnd_7293983 : Nat := 3745319164723440991668089

theorem tailTrace_7293983 : CollatzResearch.WordTrace tailWord_7293983 prefixEnd_7293983 3745319164723440991668089 := by
  unfold tailWord_7293983
  simp only [CollatzResearch.WordTrace]
  refine ⟨266033415534152778965222603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177355610356101852643481735 266033415534152778965222603)
  ·
    refine ⟨399050123301229168447833905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266033415534152778965222603 399050123301229168447833905)
    ·
      refine ⟨299287592475921876335875429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399050123301229168447833905 299287592475921876335875429)
      ·
        refine ⟨56116423589235351812976643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299287592475921876335875429 56116423589235351812976643)
        ·
          refine ⟨84174635383853027719464965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56116423589235351812976643 84174635383853027719464965)
          ·
            refine ⟨15782744134472442697399681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84174635383853027719464965 15782744134472442697399681)
            ·
              refine ⟨11837058100854332023049761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15782744134472442697399681 11837058100854332023049761)
              ·
                refine ⟨8877793575640749017287321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837058100854332023049761 8877793575640749017287321)
                ·
                  refine ⟨6658345181730561762965491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8877793575640749017287321 6658345181730561762965491)
                  ·
                    refine ⟨9987517772595842644448237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6658345181730561762965491 9987517772595842644448237)
                    ·
                      refine ⟨3745319164723440991668089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9987517772595842644448237 3745319164723440991668089)
                      ·
                        rfl

theorem cell23_7293983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_7293983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7293983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7293983 prefixEnd_7293983 := by exact prefixLift 7293983
  have htrace : WordTrace (prefixWord ++ tailWord_7293983) baseStart_7293983 baseEnd_7293983 := by
    simpa [prefixWord, tailWord_7293983, baseEnd_7293983] using wordTrace_append hprefix tailTrace_7293983
  have hstable : (prefixWord ++ tailWord_7293983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7293983).length < 2 ^ (prefixWord ++ tailWord_7293983).sum := by decide
  have hdescent : baseEnd_7293983 < baseStart_7293983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7293983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294079 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_7294079 : Nat := 118140960795 + 7294079 * 2 ^ 59
def prefixEnd_7294079 : Nat := 4983230072969 + 3 ^ 40 * 7294079 * 2
def baseEnd_7294079 : Nat := 3745368458866272616067647

theorem tailTrace_7294079 : CollatzResearch.WordTrace tailWord_7294079 prefixEnd_7294079 3745368458866272616067647 := by
  unfold tailWord_7294079
  simp only [CollatzResearch.WordTrace]
  refine ⟨266036916941804987360717291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177357944627869991573811527 266036916941804987360717291)
  ·
    refine ⟨399055375412707481041075937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266036916941804987360717291 399055375412707481041075937)
    ·
      refine ⟨299291531559530610780806953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399055375412707481041075937 299291531559530610780806953)
      ·
        refine ⟨224468648669647958085605215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299291531559530610780806953 224468648669647958085605215)
        ·
          refine ⟨336702973004471937128407823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224468648669647958085605215 336702973004471937128407823)
          ·
            refine ⟨505054459506707905692611735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336702973004471937128407823 505054459506707905692611735)
            ·
              refine ⟨757581689260061858538917603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505054459506707905692611735 757581689260061858538917603)
              ·
                refine ⟨1136372533890092787808376405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757581689260061858538917603 1136372533890092787808376405)
                ·
                  refine ⟨13316865631524524857129411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1136372533890092787808376405 13316865631524524857129411)
                  ·
                    refine ⟨19975298447286787285694117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13316865631524524857129411 19975298447286787285694117)
                    ·
                      refine ⟨3745368458866272616067647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19975298447286787285694117 3745368458866272616067647)
                      ·
                        rfl

theorem cell23_7294079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_7294079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294079 prefixEnd_7294079 := by exact prefixLift 7294079
  have htrace : WordTrace (prefixWord ++ tailWord_7294079) baseStart_7294079 baseEnd_7294079 := by
    simpa [prefixWord, tailWord_7294079, baseEnd_7294079] using wordTrace_append hprefix tailTrace_7294079
  have hstable : (prefixWord ++ tailWord_7294079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294079).length < 2 ^ (prefixWord ++ tailWord_7294079).sum := by decide
  have hdescent : baseEnd_7294079 < baseStart_7294079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294096 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2]
def baseStart_7294096 : Nat := 118140960795 + 7294096 * 2 ^ 59
def prefixEnd_7294096 : Nat := 4983230072969 + 3 ^ 40 * 7294096 * 2
def baseEnd_7294096 : Nat := 3745377188037399049555069

theorem tailTrace_7294096 : CollatzResearch.WordTrace tailWord_7294096 prefixEnd_7294096 3745377188037399049555069 := by
  unfold tailWord_7294096
  simp only [CollatzResearch.WordTrace]
  refine ⟨133018768491371699632043071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177358357988495599509390761 133018768491371699632043071)
  ·
    refine ⟨199528152737057549448064607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133018768491371699632043071 199528152737057549448064607)
    ·
      refine ⟨299292229105586324172096911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199528152737057549448064607 299292229105586324172096911)
      ·
        refine ⟨448938343658379486258145367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299292229105586324172096911 448938343658379486258145367)
        ·
          refine ⟨673407515487569229387218051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448938343658379486258145367 673407515487569229387218051)
          ·
            refine ⟨1010111273231353844080827077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673407515487569229387218051 1010111273231353844080827077)
            ·
              refine ⟨189395863730878845765155077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1010111273231353844080827077 189395863730878845765155077)
              ·
                refine ⟨35511724449539783580966577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189395863730878845765155077 35511724449539783580966577)
                ·
                  refine ⟨26633793337154837685724933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35511724449539783580966577 26633793337154837685724933)
                  ·
                    refine ⟨4993836250716532066073425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26633793337154837685724933 4993836250716532066073425)
                    ·
                      refine ⟨3745377188037399049555069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993836250716532066073425 3745377188037399049555069)
                      ·
                        rfl

theorem cell23_7294096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2].length) (baseStart_7294096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294096 prefixEnd_7294096 := by exact prefixLift 7294096
  have htrace : WordTrace (prefixWord ++ tailWord_7294096) baseStart_7294096 baseEnd_7294096 := by
    simpa [prefixWord, tailWord_7294096, baseEnd_7294096] using wordTrace_append hprefix tailTrace_7294096
  have hstable : (prefixWord ++ tailWord_7294096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294096).length < 2 ^ (prefixWord ++ tailWord_7294096).sum := by decide
  have hdescent : baseEnd_7294096 < baseStart_7294096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294190 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_7294190 : Nat := 118140960795 + 7294190 * 2 ^ 59
def prefixEnd_7294190 : Nat := 4983230072969 + 3 ^ 40 * 7294190 * 2
def baseEnd_7294190 : Nat := 3745425455218921681779637

theorem tailTrace_7294190 : CollatzResearch.WordTrace tailWord_7294190 prefixEnd_7294190 3745425455218921681779637 := by
  unfold tailWord_7294190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255120680550356664751003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177360643629601902212005349 33255120680550356664751003)
  ·
    refine ⟨49882681020825534997126505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33255120680550356664751003 49882681020825534997126505)
    ·
      refine ⟨37412010765619151247844879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49882681020825534997126505 37412010765619151247844879)
      ·
        refine ⟨56118016148428726871767319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37412010765619151247844879 56118016148428726871767319)
        ·
          refine ⟨84177024222643090307650979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56118016148428726871767319 84177024222643090307650979)
          ·
            refine ⟨126265536333964635461476469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84177024222643090307650979 126265536333964635461476469)
            ·
              refine ⟨11837394031309184574513419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126265536333964635461476469 11837394031309184574513419)
              ·
                refine ⟨17756091046963776861770129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11837394031309184574513419 17756091046963776861770129)
                ·
                  refine ⟨13317068285222832646327597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17756091046963776861770129 13317068285222832646327597)
                  ·
                    refine ⟨4993900606958562242372849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13317068285222832646327597 4993900606958562242372849)
                    ·
                      refine ⟨3745425455218921681779637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993900606958562242372849 3745425455218921681779637)
                      ·
                        rfl

theorem cell23_7294190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_7294190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294190 prefixEnd_7294190 := by exact prefixLift 7294190
  have htrace : WordTrace (prefixWord ++ tailWord_7294190) baseStart_7294190 baseEnd_7294190 := by
    simpa [prefixWord, tailWord_7294190, baseEnd_7294190] using wordTrace_append hprefix tailTrace_7294190
  have hstable : (prefixWord ++ tailWord_7294190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294190).length < 2 ^ (prefixWord ++ tailWord_7294190).sum := by decide
  have hdescent : baseEnd_7294190 < baseStart_7294190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294220 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_7294220 : Nat := 118140960795 + 7294220 * 2 ^ 59
def prefixEnd_7294220 : Nat := 4983230072969 + 3 ^ 40 * 7294220 * 2
def baseEnd_7294220 : Nat := 3745440859638556564404499

theorem tailTrace_7294220 : CollatzResearch.WordTrace tailWord_7294220 prefixEnd_7294220 3745440859638556564404499 := by
  unfold tailWord_7294220
  simp only [CollatzResearch.WordTrace]
  refine ⟨133021029817147084220800057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177361373089529445627733409 133021029817147084220800057)
  ·
    refine ⟨99765772362860313165600043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133021029817147084220800057 99765772362860313165600043)
    ·
      refine ⟨149648658544290469748400065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99765772362860313165600043 149648658544290469748400065)
      ·
        refine ⟨112236493908217852311300049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149648658544290469748400065 112236493908217852311300049)
        ·
          refine ⟨84177370431163389233475037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112236493908217852311300049 84177370431163389233475037)
          ·
            refine ⟨31566513911686270962553139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84177370431163389233475037 31566513911686270962553139)
            ·
              refine ⟨47349770867529406443829709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31566513911686270962553139 47349770867529406443829709)
              ·
                refine ⟨17756164075323527416436141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47349770867529406443829709 17756164075323527416436141)
                ·
                  refine ⟨6658561528246322781163553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17756164075323527416436141 6658561528246322781163553)
                  ·
                    refine ⟨4993921146184742085872665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658561528246322781163553 4993921146184742085872665)
                    ·
                      refine ⟨3745440859638556564404499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993921146184742085872665 3745440859638556564404499)
                      ·
                        rfl

theorem cell23_7294220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_7294220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294220 prefixEnd_7294220 := by exact prefixLift 7294220
  have htrace : WordTrace (prefixWord ++ tailWord_7294220) baseStart_7294220 baseEnd_7294220 := by
    simpa [prefixWord, tailWord_7294220, baseEnd_7294220] using wordTrace_append hprefix tailTrace_7294220
  have hstable : (prefixWord ++ tailWord_7294220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294220).length < 2 ^ (prefixWord ++ tailWord_7294220).sum := by decide
  have hdescent : baseEnd_7294220 < baseStart_7294220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294237 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7294237 : Nat := 118140960795 + 7294237 * 2 ^ 59
def prefixEnd_7294237 : Nat := 4983230072969 + 3 ^ 40 * 7294237 * 2
def baseEnd_7294237 : Nat := 3745449588809682997891921

theorem tailTrace_7294237 : CollatzResearch.WordTrace tailWord_7294237 prefixEnd_7294237 3745449588809682997891921 := by
  unfold tailWord_7294237
  simp only [CollatzResearch.WordTrace]
  refine ⟨266042679675232580344968965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177361786450155053563312643 266042679675232580344968965)
  ·
    refine ⟨49883002439106108814681681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266042679675232580344968965 49883002439106108814681681)
    ·
      refine ⟨37412251829329581611011261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49883002439106108814681681 37412251829329581611011261)
      ·
        refine ⟨14029594435998593104129223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37412251829329581611011261 14029594435998593104129223)
        ·
          refine ⟨21044391653997889656193835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14029594435998593104129223 21044391653997889656193835)
          ·
            refine ⟨31566587480996834484290753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21044391653997889656193835 31566587480996834484290753)
            ·
              refine ⟨23674940610747625863218065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31566587480996834484290753 23674940610747625863218065)
              ·
                refine ⟨17756205458060719397413549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23674940610747625863218065 17756205458060719397413549)
                ·
                  refine ⟨6658577046772769774030081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17756205458060719397413549 6658577046772769774030081)
                  ·
                    refine ⟨4993932785079577330522561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658577046772769774030081 4993932785079577330522561)
                    ·
                      refine ⟨3745449588809682997891921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4993932785079577330522561 3745449588809682997891921)
                      ·
                        rfl

theorem cell23_7294237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7294237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294237 prefixEnd_7294237 := by exact prefixLift 7294237
  have htrace : WordTrace (prefixWord ++ tailWord_7294237) baseStart_7294237 baseEnd_7294237 := by
    simpa [prefixWord, tailWord_7294237, baseEnd_7294237] using wordTrace_append hprefix tailTrace_7294237
  have hstable : (prefixWord ++ tailWord_7294237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294237).length < 2 ^ (prefixWord ++ tailWord_7294237).sum := by decide
  have hdescent : baseEnd_7294237 < baseStart_7294237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7294243 : List Nat := [1, 1, 1, 4, 2, 5, 2, 7]
def baseStart_7294243 : Nat := 118140960795 + 7294243 * 2 ^ 59
def prefixEnd_7294243 : Nat := 4983230072969 + 3 ^ 40 * 7294243 * 2
def baseEnd_7294243 : Nat := 138720469247911480533959

theorem tailTrace_7294243 : CollatzResearch.WordTrace tailWord_7294243 prefixEnd_7294243 138720469247911480533959 := by
  unfold tailWord_7294243
  simp only [CollatzResearch.WordTrace]
  refine ⟨266042898513210843369687383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177361932342140562246458255 266042898513210843369687383)
  ·
    refine ⟨399064347769816265054531075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266042898513210843369687383 399064347769816265054531075)
    ·
      refine ⟨598596521654724397581796613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399064347769816265054531075 598596521654724397581796613)
      ·
        refine ⟨112236847810260824546586865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598596521654724397581796613 112236847810260824546586865)
        ·
          refine ⟨84177635857695618409940149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112236847810260824546586865 84177635857695618409940149)
          ·
            refine ⟨7891653361658964225931889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84177635857695618409940149 7891653361658964225931889)
            ·
              refine ⟨5918740021244223169448917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7891653361658964225931889 5918740021244223169448917)
              ·
                refine ⟨138720469247911480533959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5918740021244223169448917 138720469247911480533959)
                ·
                  rfl

theorem cell23_7294243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 7].length) (baseStart_7294243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7294243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7294243 prefixEnd_7294243 := by exact prefixLift 7294243
  have htrace : WordTrace (prefixWord ++ tailWord_7294243) baseStart_7294243 baseEnd_7294243 := by
    simpa [prefixWord, tailWord_7294243, baseEnd_7294243] using wordTrace_append hprefix tailTrace_7294243
  have hstable : (prefixWord ++ tailWord_7294243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7294243).length < 2 ^ (prefixWord ++ tailWord_7294243).sum := by decide
  have hdescent : baseEnd_7294243 < baseStart_7294243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7294243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
