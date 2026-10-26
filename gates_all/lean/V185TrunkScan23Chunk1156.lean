import V185TrunkScan23Chunk1155

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6847490 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_6847490 : Nat := 118140960795 + 6847490 * 2 ^ 59
def prefixEnd_6847490 : Nat := 4983230072969 + 3 ^ 40 * 6847490 * 2
def baseEnd_6847490 : Nat := 390672627428391044175997

theorem tailTrace_6847490 : CollatzResearch.WordTrace tailWord_6847490 prefixEnd_6847490 390672627428391044175997 := by
  unfold tailWord_6847490
  simp only [CollatzResearch.WordTrace]
  refine ⟨62437119490680165757946981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166498985308480442021191949 62437119490680165757946981)
  ·
    refine ⟨11706959904502531079615059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62437119490680165757946981 11706959904502531079615059)
    ·
      refine ⟨17560439856753796619422589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11706959904502531079615059 17560439856753796619422589)
      ·
        refine ⟨6585164946282673732283471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17560439856753796619422589 6585164946282673732283471)
        ·
          refine ⟨9877747419424010598425207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585164946282673732283471 9877747419424010598425207)
          ·
            refine ⟨14816621129136015897637811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9877747419424010598425207 14816621129136015897637811)
            ·
              refine ⟨22224931693704023846456717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14816621129136015897637811 22224931693704023846456717)
              ·
                refine ⟨8334349385139008942421269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22224931693704023846456717 8334349385139008942421269)
                ·
                  refine ⟨390672627428391044175997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8334349385139008942421269 390672627428391044175997)
                  ·
                    rfl

theorem cell23_6847490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_6847490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847490 prefixEnd_6847490 := by exact prefixLift 6847490
  have htrace : WordTrace (prefixWord ++ tailWord_6847490) baseStart_6847490 baseEnd_6847490 := by
    simpa [prefixWord, tailWord_6847490, baseEnd_6847490] using wordTrace_append hprefix tailTrace_6847490
  have hstable : (prefixWord ++ tailWord_6847490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847490).length < 2 ^ (prefixWord ++ tailWord_6847490).sum := by decide
  have hdescent : baseEnd_6847490 < baseStart_6847490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847550 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6847550 : Nat := 118140960795 + 6847550 * 2 ^ 59
def prefixEnd_6847550 : Nat := 4983230072969 + 3 ^ 40 * 6847550 * 2
def baseEnd_6847550 : Nat := 1172028151898263054277899

theorem tailTrace_6847550 : CollatzResearch.WordTrace tailWord_6847550 prefixEnd_6847550 1172028151898263054277899 := by
  unfold tailWord_6847550
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218833292812911659871513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166500444228335528852648069 31218833292812911659871513)
  ·
    refine ⟨23414124969609683744903635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31218833292812911659871513 23414124969609683744903635)
    ·
      refine ⟨35121187454414525617355453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23414124969609683744903635 35121187454414525617355453)
      ·
        refine ⟨13170445295405447106508295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35121187454414525617355453 13170445295405447106508295)
        ·
          refine ⟨19755667943108170659762443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170445295405447106508295 19755667943108170659762443)
          ·
            refine ⟨29633501914662255989643665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755667943108170659762443 29633501914662255989643665)
            ·
              refine ⟨22225126435996691992232749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29633501914662255989643665 22225126435996691992232749)
              ·
                refine ⟨8334422413498759497087281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22225126435996691992232749 8334422413498759497087281)
                ·
                  refine ⟨6250816810124069622815461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8334422413498759497087281 6250816810124069622815461)
                  ·
                    refine ⟨1172028151898263054277899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250816810124069622815461 1172028151898263054277899)
                    ·
                      rfl

theorem cell23_6847550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6847550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847550 prefixEnd_6847550 := by exact prefixLift 6847550
  have htrace : WordTrace (prefixWord ++ tailWord_6847550) baseStart_6847550 baseEnd_6847550 := by
    simpa [prefixWord, tailWord_6847550, baseEnd_6847550] using wordTrace_append hprefix tailTrace_6847550
  have hstable : (prefixWord ++ tailWord_6847550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847550).length < 2 ^ (prefixWord ++ tailWord_6847550).sum := by decide
  have hdescent : baseEnd_6847550 < baseStart_6847550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847573 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6847573 : Nat := 118140960795 + 6847573 * 2 ^ 59
def prefixEnd_6847573 : Nat := 4983230072969 + 3 ^ 40 * 6847573 * 2
def baseEnd_6847573 : Nat := 3516096265749842572846091

theorem tailTrace_6847573 : CollatzResearch.WordTrace tailWord_6847573 prefixEnd_6847573 3516096265749842572846091 := by
  unfold tailWord_6847573
  simp only [CollatzResearch.WordTrace]
  refine ⟨249751505221419968207059373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166501003480946645471372915 249751505221419968207059373)
  ·
    refine ⟨93656814458032488077647265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249751505221419968207059373 93656814458032488077647265)
    ·
      refine ⟨70242610843524366058235449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93656814458032488077647265 70242610843524366058235449)
      ·
        refine ⟨52681958132643274543676587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70242610843524366058235449 52681958132643274543676587)
        ·
          refine ⟨79022937198964911815514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52681958132643274543676587 79022937198964911815514881)
          ·
            refine ⟨59267202899223683861636161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79022937198964911815514881 59267202899223683861636161)
            ·
              refine ⟨44450402174417762896227121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59267202899223683861636161 44450402174417762896227121)
              ·
                refine ⟨33337801630813322172170341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44450402174417762896227121 33337801630813322172170341)
                ·
                  refine ⟨6250837805777497907281939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33337801630813322172170341 6250837805777497907281939)
                  ·
                    refine ⟨9376256708666246860922909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250837805777497907281939 9376256708666246860922909)
                    ·
                      refine ⟨3516096265749842572846091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376256708666246860922909 3516096265749842572846091)
                      ·
                        rfl

theorem cell23_6847573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6847573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847573 prefixEnd_6847573 := by exact prefixLift 6847573
  have htrace : WordTrace (prefixWord ++ tailWord_6847573) baseStart_6847573 baseEnd_6847573 := by
    simpa [prefixWord, tailWord_6847573, baseEnd_6847573] using wordTrace_append hprefix tailTrace_6847573
  have hstable : (prefixWord ++ tailWord_6847573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847573).length < 2 ^ (prefixWord ++ tailWord_6847573).sum := by decide
  have hdescent : baseEnd_6847573 < baseStart_6847573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847614 : List Nat := [4, 2, 4, 1, 1, 2, 2, 7]
def baseStart_6847614 : Nat := 118140960795 + 6847614 * 2 ^ 59
def prefixEnd_6847614 : Nat := 4983230072969 + 3 ^ 40 * 6847614 * 2
def baseEnd_6847614 : Nat := 130226567350247293053089

theorem tailTrace_6847614 : CollatzResearch.WordTrace tailWord_6847614 prefixEnd_6847614 130226567350247293053089 := by
  unfold tailWord_6847614
  simp only [CollatzResearch.WordTrace]
  refine ⟨31219125076783929026162737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166502000409514288139534597 31219125076783929026162737)
  ·
    refine ⟨23414343807587946769622053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31219125076783929026162737 23414343807587946769622053)
    ·
      refine ⟨4390189463922740019304135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23414343807587946769622053 4390189463922740019304135)
      ·
        refine ⟨6585284195884110028956203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4390189463922740019304135 6585284195884110028956203)
        ·
          refine ⟨9877926293826165043434305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585284195884110028956203 9877926293826165043434305)
          ·
            refine ⟨7408444720369623782575729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9877926293826165043434305 7408444720369623782575729)
            ·
              refine ⟨5556333540277217836931797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7408444720369623782575729 5556333540277217836931797)
              ·
                refine ⟨130226567350247293053089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5556333540277217836931797 130226567350247293053089)
                ·
                  rfl

theorem cell23_6847614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_6847614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847614 prefixEnd_6847614 := by exact prefixLift 6847614
  have htrace : WordTrace (prefixWord ++ tailWord_6847614) baseStart_6847614 baseEnd_6847614 := by
    simpa [prefixWord, tailWord_6847614, baseEnd_6847614] using wordTrace_append hprefix tailTrace_6847614
  have hstable : (prefixWord ++ tailWord_6847614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847614).length < 2 ^ (prefixWord ++ tailWord_6847614).sum := by decide
  have hdescent : baseEnd_6847614 < baseStart_6847614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847616 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_6847616 : Nat := 118140960795 + 6847616 * 2 ^ 59
def prefixEnd_6847616 : Nat := 4983230072969 + 3 ^ 40 * 6847616 * 2
def baseEnd_6847616 : Nat := 3516118345417985904608393

theorem tailTrace_6847616 : CollatzResearch.WordTrace tailWord_6847616 prefixEnd_6847616 3516118345417985904608393 := by
  unfold tailWord_6847616
  simp only [CollatzResearch.WordTrace]
  refine ⟨124876536780132093275437351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166502049040176124367249801 124876536780132093275437351)
  ·
    refine ⟨187314805170198139913156027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124876536780132093275437351 187314805170198139913156027)
    ·
      refine ⟨280972207755297209869734041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187314805170198139913156027 280972207755297209869734041)
      ·
        refine ⟨210729155816472907402300531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280972207755297209869734041 210729155816472907402300531)
        ·
          refine ⟨316093733724709361103450797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210729155816472907402300531 316093733724709361103450797)
          ·
            refine ⟨118535150146766010413794049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316093733724709361103450797 118535150146766010413794049)
            ·
              refine ⟨88901362610074507810345537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118535150146766010413794049 88901362610074507810345537)
              ·
                refine ⟨66676021957555880857759153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88901362610074507810345537 66676021957555880857759153)
                ·
                  refine ⟨50007016468166910643319365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66676021957555880857759153 50007016468166910643319365)
                  ·
                    refine ⟨9376315587781295745622381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50007016468166910643319365 9376315587781295745622381)
                    ·
                      refine ⟨3516118345417985904608393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376315587781295745622381 3516118345417985904608393)
                      ·
                        rfl

theorem cell23_6847616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_6847616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847616 prefixEnd_6847616 := by exact prefixLift 6847616
  have htrace : WordTrace (prefixWord ++ tailWord_6847616) baseStart_6847616 baseEnd_6847616 := by
    simpa [prefixWord, tailWord_6847616, baseEnd_6847616] using wordTrace_append hprefix tailTrace_6847616
  have hstable : (prefixWord ++ tailWord_6847616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847616).length < 2 ^ (prefixWord ++ tailWord_6847616).sum := by decide
  have hdescent : baseEnd_6847616 < baseStart_6847616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847617 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6847617 : Nat := 118140960795 + 6847617 * 2 ^ 59
def prefixEnd_6847617 : Nat := 4983230072969 + 3 ^ 40 * 6847617 * 2
def baseEnd_6847617 : Nat := 3516118858898640400695889

theorem tailTrace_6847617 : CollatzResearch.WordTrace tailWord_6847617 prefixEnd_6847617 3516118858898640400695889 := by
  unfold tailWord_6847617
  simp only [CollatzResearch.WordTrace]
  refine ⟨249753110033260563721661105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166502073355507042481107403 249753110033260563721661105)
  ·
    refine ⟨187314832524945422791245829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249753110033260563721661105 187314832524945422791245829)
    ·
      refine ⟨35121531098427266773358593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187314832524945422791245829 35121531098427266773358593)
      ·
        refine ⟨26341148323820450080018945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35121531098427266773358593 26341148323820450080018945)
        ·
          refine ⟨19755861242865337560014209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26341148323820450080018945 19755861242865337560014209)
          ·
            refine ⟨14816895932149003170010657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19755861242865337560014209 14816895932149003170010657)
            ·
              refine ⟨11112671949111752377507993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14816895932149003170010657 11112671949111752377507993)
              ·
                refine ⟨8334503961833814283130995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11112671949111752377507993 8334503961833814283130995)
                ·
                  refine ⟨12501755942750721424696493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8334503961833814283130995 12501755942750721424696493)
                  ·
                    refine ⟨4688158478531520534261185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12501755942750721424696493 4688158478531520534261185)
                    ·
                      refine ⟨3516118858898640400695889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688158478531520534261185 3516118858898640400695889)
                      ·
                        rfl

theorem cell23_6847617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6847617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847617 prefixEnd_6847617 := by exact prefixLift 6847617
  have htrace : WordTrace (prefixWord ++ tailWord_6847617) baseStart_6847617 baseEnd_6847617 := by
    simpa [prefixWord, tailWord_6847617, baseEnd_6847617] using wordTrace_append hprefix tailTrace_6847617
  have hstable : (prefixWord ++ tailWord_6847617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847617).length < 2 ^ (prefixWord ++ tailWord_6847617).sum := by decide
  have hdescent : baseEnd_6847617 < baseStart_6847617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847653 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 7]
def baseStart_6847653 : Nat := 118140960795 + 6847653 * 2 ^ 59
def prefixEnd_6847653 : Nat := 4983230072969 + 3 ^ 40 * 6847653 * 2
def baseEnd_6847653 : Nat := 390681927133578028871747

theorem tailTrace_6847653 : CollatzResearch.WordTrace tailWord_6847653 prefixEnd_6847653 390681927133578028871747 := by
  unfold tailWord_6847653
  simp only [CollatzResearch.WordTrace]
  refine ⟨249754423061130141869971613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166502948707420094579981075 249754423061130141869971613)
  ·
    refine ⟨93657908647923803201239355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249754423061130141869971613 93657908647923803201239355)
    ·
      refine ⟨140486862971885704801859033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93657908647923803201239355 140486862971885704801859033)
      ·
        refine ⟨105365147228914278601394275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140486862971885704801859033 105365147228914278601394275)
        ·
          refine ⟨158047720843371417902091413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105365147228914278601394275 158047720843371417902091413)
          ·
            refine ⟨7408486914533035214160535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158047720843371417902091413 7408486914533035214160535)
            ·
              refine ⟨11112730371799552821240803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408486914533035214160535 11112730371799552821240803)
              ·
                refine ⟨16669095557699329231861205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11112730371799552821240803 16669095557699329231861205)
                ·
                  refine ⟨390681927133578028871747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16669095557699329231861205 390681927133578028871747)
                  ·
                    rfl

theorem cell23_6847653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_6847653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847653 prefixEnd_6847653 := by exact prefixLift 6847653
  have htrace : WordTrace (prefixWord ++ tailWord_6847653) baseStart_6847653 baseEnd_6847653 := by
    simpa [prefixWord, tailWord_6847653, baseEnd_6847653] using wordTrace_append hprefix tailTrace_6847653
  have hstable : (prefixWord ++ tailWord_6847653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847653).length < 2 ^ (prefixWord ++ tailWord_6847653).sum := by decide
  have hdescent : baseEnd_6847653 < baseStart_6847653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847703 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_6847703 : Nat := 118140960795 + 6847703 * 2 ^ 59
def prefixEnd_6847703 : Nat := 4983230072969 + 3 ^ 40 * 6847703 * 2
def baseEnd_6847703 : Nat := 3516163018234927064220493

theorem tailTrace_6847703 : CollatzResearch.WordTrace tailWord_6847703 prefixEnd_6847703 3516163018234927064220493 := by
  unfold tailWord_6847703
  simp only [CollatzResearch.WordTrace]
  refine ⟨249756246710949000409291763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166504164473966000272861175 249756246710949000409291763)
  ·
    refine ⟨374634370066423500613937645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249756246710949000409291763 374634370066423500613937645)
    ·
      refine ⟨140487888774908812730226617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374634370066423500613937645 140487888774908812730226617)
      ·
        refine ⟨105365916581181609547669963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140487888774908812730226617 105365916581181609547669963)
        ·
          refine ⟨158048874871772414321504945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105365916581181609547669963 158048874871772414321504945)
          ·
            refine ⟨118536656153829310741128709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158048874871772414321504945 118536656153829310741128709)
            ·
              refine ⟨22225623028842995763961633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118536656153829310741128709 22225623028842995763961633)
              ·
                refine ⟨16669217271632246822971225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22225623028842995763961633 16669217271632246822971225)
                ·
                  refine ⟨12501912953724185117228419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16669217271632246822971225 12501912953724185117228419)
                  ·
                    refine ⟨18752869430586277675842629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12501912953724185117228419 18752869430586277675842629)
                    ·
                      refine ⟨3516163018234927064220493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18752869430586277675842629 3516163018234927064220493)
                      ·
                        rfl

theorem cell23_6847703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_6847703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847703 prefixEnd_6847703 := by exact prefixLift 6847703
  have htrace : WordTrace (prefixWord ++ tailWord_6847703) baseStart_6847703 baseEnd_6847703 := by
    simpa [prefixWord, tailWord_6847703, baseEnd_6847703] using wordTrace_append hprefix tailTrace_6847703
  have hstable : (prefixWord ++ tailWord_6847703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847703).length < 2 ^ (prefixWord ++ tailWord_6847703).sum := by decide
  have hdescent : baseEnd_6847703 < baseStart_6847703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847704 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 5]
def baseStart_6847704 : Nat := 118140960795 + 6847704 * 2 ^ 59
def prefixEnd_6847704 : Nat := 4983230072969 + 3 ^ 40 * 6847704 * 2
def baseEnd_6847704 : Nat := 390684836857286840034221

theorem tailTrace_6847704 : CollatzResearch.WordTrace tailWord_6847704 prefixEnd_6847704 390684836857286840034221 := by
  unfold tailWord_6847704
  simp only [CollatzResearch.WordTrace]
  refine ⟨124878141591972688790039083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166504188789296918386718777 124878141591972688790039083)
  ·
    refine ⟨187317212387959033185058625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124878141591972688790039083 187317212387959033185058625)
    ·
      refine ⟨140487909290969274888793969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187317212387959033185058625 140487909290969274888793969)
      ·
        refine ⟨105365931968226956166595477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140487909290969274888793969 105365931968226956166595477)
        ·
          refine ⟨4939028061010638570309163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105365931968226956166595477 4939028061010638570309163)
          ·
            refine ⟨7408542091515957855463745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939028061010638570309163 7408542091515957855463745)
            ·
              refine ⟨5556406568636968391597809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7408542091515957855463745 5556406568636968391597809)
              ·
                refine ⟨4167304926477726293698357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556406568636968391597809 4167304926477726293698357)
                ·
                  refine ⟨390684836857286840034221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167304926477726293698357 390684836857286840034221)
                  ·
                    rfl

theorem cell23_6847704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 5].length) (baseStart_6847704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847704 prefixEnd_6847704 := by exact prefixLift 6847704
  have htrace : WordTrace (prefixWord ++ tailWord_6847704) baseStart_6847704 baseEnd_6847704 := by
    simpa [prefixWord, tailWord_6847704, baseEnd_6847704] using wordTrace_append hprefix tailTrace_6847704
  have hstable : (prefixWord ++ tailWord_6847704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847704).length < 2 ^ (prefixWord ++ tailWord_6847704).sum := by decide
  have hdescent : baseEnd_6847704 < baseStart_6847704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847706 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_6847706 : Nat := 118140960795 + 6847706 * 2 ^ 59
def prefixEnd_6847706 : Nat := 4983230072969 + 3 ^ 40 * 6847706 * 2
def baseEnd_6847706 : Nat := 3516164558676890552482979

theorem tailTrace_6847706 : CollatzResearch.WordTrace tailWord_6847706 prefixEnd_6847706 3516164558676890552482979 := by
  unfold tailWord_6847706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62439089032484532980412743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166504237419958754614433981 62439089032484532980412743)
  ·
    refine ⟨93658633548726799470619115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62439089032484532980412743 93658633548726799470619115)
    ·
      refine ⟨140487950323090199205928673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93658633548726799470619115 140487950323090199205928673)
      ·
        refine ⟨105365962742317649404446505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140487950323090199205928673 105365962742317649404446505)
        ·
          refine ⟨79024472056738237053334879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105365962742317649404446505 79024472056738237053334879)
          ·
            refine ⟨118536708085107355580002319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79024472056738237053334879 118536708085107355580002319)
            ·
              refine ⟨177805062127661033370003479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118536708085107355580002319 177805062127661033370003479)
              ·
                refine ⟨266707593191491550055005219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177805062127661033370003479 266707593191491550055005219)
                ·
                  refine ⟨400061389787237325082507829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266707593191491550055005219 400061389787237325082507829)
                  ·
                    refine ⟨37505755292553499226485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400061389787237325082507829 37505755292553499226485109)
                    ·
                      refine ⟨3516164558676890552482979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37505755292553499226485109 3516164558676890552482979)
                      ·
                        rfl

theorem cell23_6847706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_6847706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847706 prefixEnd_6847706 := by exact prefixLift 6847706
  have htrace : WordTrace (prefixWord ++ tailWord_6847706) baseStart_6847706 baseEnd_6847706 := by
    simpa [prefixWord, tailWord_6847706, baseEnd_6847706] using wordTrace_append hprefix tailTrace_6847706
  have hstable : (prefixWord ++ tailWord_6847706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847706).length < 2 ^ (prefixWord ++ tailWord_6847706).sum := by decide
  have hdescent : baseEnd_6847706 < baseStart_6847706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847720 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6847720 : Nat := 118140960795 + 6847720 * 2 ^ 59
def prefixEnd_6847720 : Nat := 4983230072969 + 3 ^ 40 * 6847720 * 2
def baseEnd_6847720 : Nat := 3516171747406053497707915

theorem tailTrace_6847720 : CollatzResearch.WordTrace tailWord_6847720 prefixEnd_6847720 3516171747406053497707915 := by
  unfold tailWord_6847720
  simp only [CollatzResearch.WordTrace]
  refine ⟨124878433375943706156330307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166504577834591608208440409 124878433375943706156330307)
  ·
    refine ⟨187317650063915559234495461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124878433375943706156330307 187317650063915559234495461)
    ·
      refine ⟨35122059386984167356467899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187317650063915559234495461 35122059386984167356467899)
      ·
        refine ⟨52683089080476251034701849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35122059386984167356467899 52683089080476251034701849)
        ·
          refine ⟨39512316810357188276026387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52683089080476251034701849 39512316810357188276026387)
          ·
            refine ⟨59268475215535782414039581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39512316810357188276026387 59268475215535782414039581)
            ·
              refine ⟨22225678205825918405264843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59268475215535782414039581 22225678205825918405264843)
              ·
                refine ⟨33338517308738877607897265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22225678205825918405264843 33338517308738877607897265)
                ·
                  refine ⟨25003887981554158205922949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33338517308738877607897265 25003887981554158205922949)
                  ·
                    refine ⟨4688228996541404663610553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25003887981554158205922949 4688228996541404663610553)
                    ·
                      refine ⟨3516171747406053497707915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688228996541404663610553 3516171747406053497707915)
                      ·
                        rfl

theorem cell23_6847720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6847720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847720 prefixEnd_6847720 := by exact prefixLift 6847720
  have htrace : WordTrace (prefixWord ++ tailWord_6847720) baseStart_6847720 baseEnd_6847720 := by
    simpa [prefixWord, tailWord_6847720, baseEnd_6847720] using wordTrace_append hprefix tailTrace_6847720
  have hstable : (prefixWord ++ tailWord_6847720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847720).length < 2 ^ (prefixWord ++ tailWord_6847720).sum := by decide
  have hdescent : baseEnd_6847720 < baseStart_6847720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847740 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_6847740 : Nat := 118140960795 + 6847740 * 2 ^ 59
def prefixEnd_6847740 : Nat := 4983230072969 + 3 ^ 40 * 6847740 * 2
def baseEnd_6847740 : Nat := 3516182017019143419457823

theorem tailTrace_6847740 : CollatzResearch.WordTrace tailWord_6847740 prefixEnd_6847740 3516182017019143419457823 := by
  unfold tailWord_6847740
  simp only [CollatzResearch.WordTrace]
  refine ⟨124878798105907477864194337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166505064141209970485592449 124878798105907477864194337)
  ·
    refine ⟨93659098579430608398145753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124878798105907477864194337 93659098579430608398145753)
    ·
      refine ⟨70244323934572956298609315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93659098579430608398145753 70244323934572956298609315)
      ·
        refine ⟨105366485901859434447913973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70244323934572956298609315 105366485901859434447913973)
        ·
          refine ⟨9878108053299321979491935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105366485901859434447913973 9878108053299321979491935)
          ·
            refine ⟨14817162079948982969237903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878108053299321979491935 14817162079948982969237903)
            ·
              refine ⟨22225743119923474453856855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817162079948982969237903 22225743119923474453856855)
              ·
                refine ⟨33338614679885211680785283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22225743119923474453856855 33338614679885211680785283)
                ·
                  refine ⟨50007922019827817521177925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33338614679885211680785283 50007922019827817521177925)
                  ·
                    refine ⟨9376485378717715785220861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50007922019827817521177925 9376485378717715785220861)
                    ·
                      refine ⟨3516182017019143419457823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376485378717715785220861 3516182017019143419457823)
                      ·
                        rfl

theorem cell23_6847740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_6847740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847740 prefixEnd_6847740 := by exact prefixLift 6847740
  have htrace : WordTrace (prefixWord ++ tailWord_6847740) baseStart_6847740 baseEnd_6847740 := by
    simpa [prefixWord, tailWord_6847740, baseEnd_6847740] using wordTrace_append hprefix tailTrace_6847740
  have hstable : (prefixWord ++ tailWord_6847740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847740).length < 2 ^ (prefixWord ++ tailWord_6847740).sum := by decide
  have hdescent : baseEnd_6847740 < baseStart_6847740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847747 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 1, 4]
def baseStart_6847747 : Nat := 118140960795 + 6847747 * 2 ^ 59
def prefixEnd_6847747 : Nat := 4983230072969 + 3 ^ 40 * 6847747 * 2
def baseEnd_6847747 : Nat := 1172061870461241630690097

theorem tailTrace_6847747 : CollatzResearch.WordTrace tailWord_6847747 prefixEnd_6847747 1172061870461241630690097 := by
  unfold tailWord_6847747
  simp only [CollatzResearch.WordTrace]
  refine ⟨249757851522789595923893495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166505234348526397282595663 249757851522789595923893495)
  ·
    refine ⟨374636777284184393885840243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249757851522789595923893495 374636777284184393885840243)
    ·
      refine ⟨561955165926276590828760365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374636777284184393885840243 561955165926276590828760365)
      ·
        refine ⟨210733187222353721560785137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561955165926276590828760365 210733187222353721560785137)
        ·
          refine ⟨158049890416765291170588853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210733187222353721560785137 158049890416765291170588853)
          ·
            refine ⟨14817177226571746047242705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158049890416765291170588853 14817177226571746047242705)
            ·
              refine ⟨11112882919928809535432029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14817177226571746047242705 11112882919928809535432029)
              ·
                refine ⟨4167331094973303575787011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112882919928809535432029 4167331094973303575787011)
                ·
                  refine ⟨6250996642459955363680517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167331094973303575787011 6250996642459955363680517)
                  ·
                    refine ⟨1172061870461241630690097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250996642459955363680517 1172061870461241630690097)
                    ·
                      rfl

theorem cell23_6847747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 4].length) (baseStart_6847747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847747 prefixEnd_6847747 := by exact prefixLift 6847747
  have htrace : WordTrace (prefixWord ++ tailWord_6847747) baseStart_6847747 baseEnd_6847747 := by
    simpa [prefixWord, tailWord_6847747, baseEnd_6847747] using wordTrace_append hprefix tailTrace_6847747
  have hstable : (prefixWord ++ tailWord_6847747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847747).length < 2 ^ (prefixWord ++ tailWord_6847747).sum := by decide
  have hdescent : baseEnd_6847747 < baseStart_6847747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847780 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_6847780 : Nat := 118140960795 + 6847780 * 2 ^ 59
def prefixEnd_6847780 : Nat := 4983230072969 + 3 ^ 40 * 6847780 * 2
def baseEnd_6847780 : Nat := 3516202556245323262957639

theorem tailTrace_6847780 : CollatzResearch.WordTrace tailWord_6847780 prefixEnd_6847780 3516202556245323262957639 := by
  unfold tailWord_6847780
  simp only [CollatzResearch.WordTrace]
  refine ⟨124879527565835021279922397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166506036754446695039896529 124879527565835021279922397)
  ·
    refine ⟨46829822837188132979970899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124879527565835021279922397 46829822837188132979970899)
    ·
      refine ⟨70244734255782199469956349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46829822837188132979970899 70244734255782199469956349)
      ·
        refine ⟨26341775345918324801233631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70244734255782199469956349 26341775345918324801233631)
        ·
          refine ⟨39512663018877487201850447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26341775345918324801233631 39512663018877487201850447)
          ·
            refine ⟨59268994528316230802775671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39512663018877487201850447 59268994528316230802775671)
            ·
              refine ⟨88903491792474346204163507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59268994528316230802775671 88903491792474346204163507)
              ·
                refine ⟨133355237688711519306245261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88903491792474346204163507 133355237688711519306245261)
                ·
                  refine ⟨50008214133266819739841973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133355237688711519306245261 50008214133266819739841973)
                  ·
                    refine ⟨4688270074993764350610185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50008214133266819739841973 4688270074993764350610185)
                    ·
                      refine ⟨3516202556245323262957639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688270074993764350610185 3516202556245323262957639)
                      ·
                        rfl

theorem cell23_6847780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_6847780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847780 prefixEnd_6847780 := by exact prefixLift 6847780
  have htrace : WordTrace (prefixWord ++ tailWord_6847780) baseStart_6847780 baseEnd_6847780 := by
    simpa [prefixWord, tailWord_6847780, baseEnd_6847780] using wordTrace_append hprefix tailTrace_6847780
  have hstable : (prefixWord ++ tailWord_6847780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847780).length < 2 ^ (prefixWord ++ tailWord_6847780).sum := by decide
  have hdescent : baseEnd_6847780 < baseStart_6847780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847798 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6847798 : Nat := 118140960795 + 6847798 * 2 ^ 59
def prefixEnd_6847798 : Nat := 4983230072969 + 3 ^ 40 * 6847798 * 2
def baseEnd_6847798 : Nat := 1172070599632368064177519

theorem tailTrace_6847798 : CollatzResearch.WordTrace tailWord_6847798 prefixEnd_6847798 1172070599632368064177519 := by
  unfold tailWord_6847798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609981977850301977125003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166506474430403221089333365 15609981977850301977125003)
  ·
    refine ⟨23414972966775452965687505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15609981977850301977125003 23414972966775452965687505)
    ·
      refine ⟨17561229725081589724265629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23414972966775452965687505 17561229725081589724265629)
      ·
        refine ⟨6585461146905596146599611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17561229725081589724265629 6585461146905596146599611)
        ·
          refine ⟨9878191720358394219899417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585461146905596146599611 9878191720358394219899417)
          ·
            refine ⟨7408643790268795664924563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9878191720358394219899417 7408643790268795664924563)
            ·
              refine ⟨11112965685403193497386845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408643790268795664924563 11112965685403193497386845)
              ·
                refine ⟨4167362132026197561520067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112965685403193497386845 4167362132026197561520067)
                ·
                  refine ⟨6251043198039296342280101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167362132026197561520067 6251043198039296342280101)
                  ·
                    refine ⟨1172070599632368064177519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251043198039296342280101 1172070599632368064177519)
                    ·
                      rfl

theorem cell23_6847798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6847798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847798 prefixEnd_6847798 := by exact prefixLift 6847798
  have htrace : WordTrace (prefixWord ++ tailWord_6847798) baseStart_6847798 baseEnd_6847798 := by
    simpa [prefixWord, tailWord_6847798, baseEnd_6847798] using wordTrace_append hprefix tailTrace_6847798
  have hstable : (prefixWord ++ tailWord_6847798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847798).length < 2 ^ (prefixWord ++ tailWord_6847798).sum := by decide
  have hdescent : baseEnd_6847798 < baseStart_6847798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847804 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_6847804 : Nat := 118140960795 + 6847804 * 2 ^ 59
def prefixEnd_6847804 : Nat := 4983230072969 + 3 ^ 40 * 6847804 * 2
def baseEnd_6847804 : Nat := 3516214879781031169057529

theorem tailTrace_6847804 : CollatzResearch.WordTrace tailWord_6847804 prefixEnd_6847804 3516214879781031169057529 := by
  unfold tailWord_6847804
  simp only [CollatzResearch.WordTrace]
  refine ⟨124879965241791547329359233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166506620322388729772478977 124879965241791547329359233)
  ·
    refine ⟨93659973931343660497019425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124879965241791547329359233 93659973931343660497019425)
    ·
      refine ⟨70244980448507745372764569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93659973931343660497019425 70244980448507745372764569)
      ·
        refine ⟨52683735336380809029573427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70244980448507745372764569 52683735336380809029573427)
        ·
          refine ⟨79025603004571213544360141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52683735336380809029573427 79025603004571213544360141)
          ·
            refine ⟨29634601126714205079135053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79025603004571213544360141 29634601126714205079135053)
            ·
              refine ⟨11112975422517826904675645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29634601126714205079135053 11112975422517826904675645)
              ·
                refine ⟨4167365783444185089253367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112975422517826904675645 4167365783444185089253367)
                ·
                  refine ⟨6251048675166277633880051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167365783444185089253367 6251048675166277633880051)
                  ·
                    refine ⟨9376573012749416450820077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6251048675166277633880051 9376573012749416450820077)
                    ·
                      refine ⟨3516214879781031169057529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376573012749416450820077 3516214879781031169057529)
                      ·
                        rfl

theorem cell23_6847804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_6847804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847804 prefixEnd_6847804 := by exact prefixLift 6847804
  have htrace : WordTrace (prefixWord ++ tailWord_6847804) baseStart_6847804 baseEnd_6847804 := by
    simpa [prefixWord, tailWord_6847804, baseEnd_6847804] using wordTrace_append hprefix tailTrace_6847804
  have hstable : (prefixWord ++ tailWord_6847804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847804).length < 2 ^ (prefixWord ++ tailWord_6847804).sum := by decide
  have hdescent : baseEnd_6847804 < baseStart_6847804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847820 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_6847820 : Nat := 118140960795 + 6847820 * 2 ^ 59
def prefixEnd_6847820 : Nat := 4983230072969 + 3 ^ 40 * 6847820 * 2
def baseEnd_6847820 : Nat := 1172074365157167702152485

theorem tailTrace_6847820 : CollatzResearch.WordTrace tailWord_6847820 prefixEnd_6847820 1172074365157167702152485 := by
  unfold tailWord_6847820
  simp only [CollatzResearch.WordTrace]
  refine ⟨124880257025762564695650457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166507009367683419594200609 124880257025762564695650457)
  ·
    refine ⟨93660192769321923521737843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124880257025762564695650457 93660192769321923521737843)
    ·
      refine ⟨140490289153982885282606765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93660192769321923521737843 140490289153982885282606765)
      ·
        refine ⟨52683858432743581980977537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140490289153982885282606765 52683858432743581980977537)
        ·
          refine ⟨39512893824557686485733153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52683858432743581980977537 39512893824557686485733153)
          ·
            refine ⟨29634670368418264864299865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39512893824557686485733153 29634670368418264864299865)
            ·
              refine ⟨22226002776313698648224899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29634670368418264864299865 22226002776313698648224899)
              ·
                refine ⟨33339004164470547972337349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22226002776313698648224899 33339004164470547972337349)
                ·
                  refine ⟨6251063280838227744813253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33339004164470547972337349 6251063280838227744813253)
                  ·
                    refine ⟨1172074365157167702152485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251063280838227744813253 1172074365157167702152485)
                    ·
                      rfl

theorem cell23_6847820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_6847820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847820 prefixEnd_6847820 := by exact prefixLift 6847820
  have htrace : WordTrace (prefixWord ++ tailWord_6847820) baseStart_6847820 baseEnd_6847820 := by
    simpa [prefixWord, tailWord_6847820, baseEnd_6847820] using wordTrace_append hprefix tailTrace_6847820
  have hstable : (prefixWord ++ tailWord_6847820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847820).length < 2 ^ (prefixWord ++ tailWord_6847820).sum := by decide
  have hdescent : baseEnd_6847820 < baseStart_6847820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847847 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_6847847 : Nat := 118140960795 + 6847847 * 2 ^ 59
def prefixEnd_6847847 : Nat := 4983230072969 + 3 ^ 40 * 6847847 * 2
def baseEnd_6847847 : Nat := 3516236959449174500819831

theorem tailTrace_6847847 : CollatzResearch.WordTrace tailWord_6847847 prefixEnd_6847847 3516236959449174500819831 := by
  unfold tailWord_6847847
  simp only [CollatzResearch.WordTrace]
  refine ⟨249761498822427313002533795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166507665881618208668355863 249761498822427313002533795)
  ·
    refine ⟨374642248233640969503800693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249761498822427313002533795 374642248233640969503800693)
    ·
      refine ⟨35122710771903840890981315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374642248233640969503800693 35122710771903840890981315)
      ·
        refine ⟨52684066157855761336471973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35122710771903840890981315 52684066157855761336471973)
        ·
          refine ⟨9878262404597955250588495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52684066157855761336471973 9878262404597955250588495)
          ·
            refine ⟨14817393606896932875882743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878262404597955250588495 14817393606896932875882743)
            ·
              refine ⟨22226090410345399313824115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817393606896932875882743 22226090410345399313824115)
              ·
                refine ⟨33339135615518098970736173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22226090410345399313824115 33339135615518098970736173)
                ·
                  refine ⟨12502175855819287114026065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33339135615518098970736173 12502175855819287114026065)
                  ·
                    refine ⟨9376631891864465335519549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12502175855819287114026065 9376631891864465335519549)
                    ·
                      refine ⟨3516236959449174500819831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376631891864465335519549 3516236959449174500819831)
                      ·
                        rfl

theorem cell23_6847847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_6847847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847847 prefixEnd_6847847 := by exact prefixLift 6847847
  have htrace : WordTrace (prefixWord ++ tailWord_6847847) baseStart_6847847 baseEnd_6847847 := by
    simpa [prefixWord, tailWord_6847847, baseEnd_6847847] using wordTrace_append hprefix tailTrace_6847847
  have hstable : (prefixWord ++ tailWord_6847847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847847).length < 2 ^ (prefixWord ++ tailWord_6847847).sum := by decide
  have hdescent : baseEnd_6847847 < baseStart_6847847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847877 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_6847877 : Nat := 118140960795 + 6847877 * 2 ^ 59
def prefixEnd_6847877 : Nat := 4983230072969 + 3 ^ 40 * 6847877 * 2
def baseEnd_6847877 : Nat := 3516252363868809383444693

theorem tailTrace_6847877 : CollatzResearch.WordTrace tailWord_6847877 prefixEnd_6847877 3516252363868809383444693 := by
  unfold tailWord_6847877
  simp only [CollatzResearch.WordTrace]
  refine ⟨249762593012318628126125885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166508395341545752084083923 249762593012318628126125885)
  ·
    refine ⟨93660972379619485547297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249762593012318628126125885 93660972379619485547297207)
    ·
      refine ⟨140491458569429228320945811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93660972379619485547297207 140491458569429228320945811)
      ·
        refine ⟨210737187854143842481418717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140491458569429228320945811 210737187854143842481418717)
        ·
          refine ⟨79026445445303940930532019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210737187854143842481418717 79026445445303940930532019)
          ·
            refine ⟨118539668167955911395798029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79026445445303940930532019 118539668167955911395798029)
            ·
              refine ⟨44452375562983466773424261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118539668167955911395798029 44452375562983466773424261)
              ·
                refine ⟨8334820418059400020017049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44452375562983466773424261 8334820418059400020017049)
                ·
                  refine ⟨6251115313544550015012787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8334820418059400020017049 6251115313544550015012787)
                  ·
                    refine ⟨9376672970316825022519181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6251115313544550015012787 9376672970316825022519181)
                    ·
                      refine ⟨3516252363868809383444693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376672970316825022519181 3516252363868809383444693)
                      ·
                        rfl

theorem cell23_6847877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_6847877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847877 prefixEnd_6847877 := by exact prefixLift 6847877
  have htrace : WordTrace (prefixWord ++ tailWord_6847877) baseStart_6847877 baseEnd_6847877 := by
    simpa [prefixWord, tailWord_6847877, baseEnd_6847877] using wordTrace_append hprefix tailTrace_6847877
  have hstable : (prefixWord ++ tailWord_6847877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847877).length < 2 ^ (prefixWord ++ tailWord_6847877).sum := by decide
  have hdescent : baseEnd_6847877 < baseStart_6847877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847883 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_6847883 : Nat := 118140960795 + 6847883 * 2 ^ 59
def prefixEnd_6847883 : Nat := 4983230072969 + 3 ^ 40 * 6847883 * 2
def baseEnd_6847883 : Nat := 3516255444752736359969665

theorem tailTrace_6847883 : CollatzResearch.WordTrace tailWord_6847883 prefixEnd_6847883 3516255444752736359969665 := by
  unfold tailWord_6847883
  simp only [CollatzResearch.WordTrace]
  refine ⟨249762811850296891150844303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166508541233531260767229535 249762811850296891150844303)
  ·
    refine ⟨374644217775445336726266455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249762811850296891150844303 374644217775445336726266455)
    ·
      refine ⟨561966326663168005089399683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374644217775445336726266455 561966326663168005089399683)
      ·
        refine ⟨842949489994752007634099525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561966326663168005089399683 842949489994752007634099525)
        ·
          refine ⟨158053029374016001431393661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 842949489994752007634099525 158053029374016001431393661)
          ·
            refine ⟨59269886015256000536772623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158053029374016001431393661 59269886015256000536772623)
            ·
              refine ⟨88904829022884000805158935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59269886015256000536772623 88904829022884000805158935)
              ·
                refine ⟨133357243534326001207738403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88904829022884000805158935 133357243534326001207738403)
                ·
                  refine ⟨200035865301489001811607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133357243534326001207738403 200035865301489001811607605)
                  ·
                    refine ⟨18753362372014593919838213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200035865301489001811607605 18753362372014593919838213)
                    ·
                      refine ⟨3516255444752736359969665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18753362372014593919838213 3516255444752736359969665)
                      ·
                        rfl

theorem cell23_6847883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_6847883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847883 prefixEnd_6847883 := by exact prefixLift 6847883
  have htrace : WordTrace (prefixWord ++ tailWord_6847883) baseStart_6847883 baseEnd_6847883 := by
    simpa [prefixWord, tailWord_6847883, baseEnd_6847883] using wordTrace_append hprefix tailTrace_6847883
  have hstable : (prefixWord ++ tailWord_6847883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847883).length < 2 ^ (prefixWord ++ tailWord_6847883).sum := by decide
  have hdescent : baseEnd_6847883 < baseStart_6847883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847893 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_6847893 : Nat := 118140960795 + 6847893 * 2 ^ 59
def prefixEnd_6847893 : Nat := 4983230072969 + 3 ^ 40 * 6847893 * 2
def baseEnd_6847893 : Nat := 1172086859853093773614873

theorem tailTrace_6847893 : CollatzResearch.WordTrace tailWord_6847893 prefixEnd_6847893 1172086859853093773614873 := by
  unfold tailWord_6847893
  simp only [CollatzResearch.WordTrace]
  refine ⟨249763176580260662858708333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166508784386840441905805555 249763176580260662858708333)
  ·
    refine ⟨93661191217597748572015625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249763176580260662858708333 93661191217597748572015625)
    ·
      refine ⟨70245893413198311429011719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93661191217597748572015625 70245893413198311429011719)
      ·
        refine ⟨105368840119797467143517579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70245893413198311429011719 105368840119797467143517579)
        ·
          refine ⟨158053260179696200715276369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105368840119797467143517579 158053260179696200715276369)
          ·
            refine ⟨118539945134772150536457277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158053260179696200715276369 118539945134772150536457277)
            ·
              refine ⟨44452479425539556451171479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118539945134772150536457277 44452479425539556451171479)
              ·
                refine ⟨66678719138309334676757219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44452479425539556451171479 66678719138309334676757219)
                ·
                  refine ⟨100018078707464002015135829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66678719138309334676757219 100018078707464002015135829)
                  ·
                    refine ⟨1172086859853093773614873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100018078707464002015135829 1172086859853093773614873)
                    ·
                      rfl

theorem cell23_6847893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_6847893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847893 prefixEnd_6847893 := by exact prefixLift 6847893
  have htrace : WordTrace (prefixWord ++ tailWord_6847893) baseStart_6847893 baseEnd_6847893 := by
    simpa [prefixWord, tailWord_6847893, baseEnd_6847893] using wordTrace_append hprefix tailTrace_6847893
  have hstable : (prefixWord ++ tailWord_6847893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847893).length < 2 ^ (prefixWord ++ tailWord_6847893).sum := by decide
  have hdescent : baseEnd_6847893 < baseStart_6847893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848024 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6848024 : Nat := 118140960795 + 6848024 * 2 ^ 59
def prefixEnd_6848024 : Nat := 4983230072969 + 3 ^ 40 * 6848024 * 2
def baseEnd_6848024 : Nat := 3516327845525020308306517

theorem tailTrace_6848024 : CollatzResearch.WordTrace tailWord_6848024 prefixEnd_6848024 3516327845525020308306517 := by
  unfold tailWord_6848024
  simp only [CollatzResearch.WordTrace]
  refine ⟨124883977271393036115863563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166511969695190714821151417 124883977271393036115863563)
  ·
    refine ⟨187325965907089554173795345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124883977271393036115863563 187325965907089554173795345)
    ·
      refine ⟨140494474430317165630346509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187325965907089554173795345 140494474430317165630346509)
      ·
        refine ⟨52685427911368937111379941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140494474430317165630346509 52685427911368937111379941)
        ·
          refine ⟨9878517733381675708383739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52685427911368937111379941 9878517733381675708383739)
          ·
            refine ⟨14817776600072513562575609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878517733381675708383739 14817776600072513562575609)
            ·
              refine ⟨11113332450054385171931707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14817776600072513562575609 11113332450054385171931707)
              ·
                refine ⟨16669998675081577757897561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11113332450054385171931707 16669998675081577757897561)
                ·
                  refine ⟨12502499006311183318423171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16669998675081577757897561 12502499006311183318423171)
                  ·
                    refine ⟨18753748509466774977634757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12502499006311183318423171 18753748509466774977634757)
                    ·
                      refine ⟨3516327845525020308306517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18753748509466774977634757 3516327845525020308306517)
                      ·
                        rfl

theorem cell23_6848024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6848024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848024 prefixEnd_6848024 := by exact prefixLift 6848024
  have htrace : WordTrace (prefixWord ++ tailWord_6848024) baseStart_6848024 baseEnd_6848024 := by
    simpa [prefixWord, tailWord_6848024, baseEnd_6848024] using wordTrace_append hprefix tailTrace_6848024
  have hstable : (prefixWord ++ tailWord_6848024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848024).length < 2 ^ (prefixWord ++ tailWord_6848024).sum := by decide
  have hdescent : baseEnd_6848024 < baseStart_6848024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848050 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6848050 : Nat := 118140960795 + 6848050 * 2 ^ 59
def prefixEnd_6848050 : Nat := 4983230072969 + 3 ^ 40 * 6848050 * 2
def baseEnd_6848050 : Nat := 3516341196022037206581397

theorem tailTrace_6848050 : CollatzResearch.WordTrace tailWord_6848050 prefixEnd_6848050 3516341196022037206581397 := by
  unfold tailWord_6848050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442225710172969668043401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166512601893794585781449069 62442225710172969668043401)
  ·
    refine ⟨46831669282629727251032551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62442225710172969668043401 46831669282629727251032551)
    ·
      refine ⟨70247503923944590876548827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46831669282629727251032551 70247503923944590876548827)
      ·
        refine ⟨105371255885916886314823241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70247503923944590876548827 105371255885916886314823241)
        ·
          refine ⟨79028441914437664736117431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105371255885916886314823241 79028441914437664736117431)
          ·
            refine ⟨118542662871656497104176147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79028441914437664736117431 118542662871656497104176147)
            ·
              refine ⟨177813994307484745656264221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118542662871656497104176147 177813994307484745656264221)
              ·
                refine ⟨66680247865306779621099083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177813994307484745656264221 66680247865306779621099083)
                ·
                  refine ⟨100020371797960169431648625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66680247865306779621099083 100020371797960169431648625)
                  ·
                    refine ⟨75015278848470127073736469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100020371797960169431648625 75015278848470127073736469)
                    ·
                      refine ⟨3516341196022037206581397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75015278848470127073736469 3516341196022037206581397)
                      ·
                        rfl

theorem cell23_6848050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6848050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848050 prefixEnd_6848050 := by exact prefixLift 6848050
  have htrace : WordTrace (prefixWord ++ tailWord_6848050) baseStart_6848050 baseEnd_6848050 := by
    simpa [prefixWord, tailWord_6848050, baseEnd_6848050] using wordTrace_append hprefix tailTrace_6848050
  have hstable : (prefixWord ++ tailWord_6848050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848050).length < 2 ^ (prefixWord ++ tailWord_6848050).sum := by decide
  have hdescent : baseEnd_6848050 < baseStart_6848050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848051 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 1, 4]
def baseStart_6848051 : Nat := 118140960795 + 6848051 * 2 ^ 59
def prefixEnd_6848051 : Nat := 4983230072969 + 3 ^ 40 * 6848051 * 2
def baseEnd_6848051 : Nat := 1172113903167563900889631

theorem tailTrace_6848051 : CollatzResearch.WordTrace tailWord_6848051 prefixEnd_6848051 1172113903167563900889631 := by
  unfold tailWord_6848051
  simp only [CollatzResearch.WordTrace]
  refine ⟨249768939313688255842960007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166512626209125503895306671 249768939313688255842960007)
  ·
    refine ⟨374653408970532383764440011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249768939313688255842960007 374653408970532383764440011)
    ·
      refine ⟨561980113455798575646660017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374653408970532383764440011 561980113455798575646660017)
      ·
        refine ⟨421485085091848931734995013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561980113455798575646660017 421485085091848931734995013)
        ·
          refine ⟨79028453454721674700311565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421485085091848931734995013 79028453454721674700311565)
          ·
            refine ⟨29635670045520628012616837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79028453454721674700311565 29635670045520628012616837)
            ·
              refine ⟨5556688133535117752365657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29635670045520628012616837 5556688133535117752365657)
              ·
                refine ⟨4167516100151338314274243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556688133535117752365657 4167516100151338314274243)
                ·
                  refine ⟨6251274150227007471411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167516100151338314274243 6251274150227007471411365)
                  ·
                    refine ⟨1172113903167563900889631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251274150227007471411365 1172113903167563900889631)
                    ·
                      rfl

theorem cell23_6848051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 4].length) (baseStart_6848051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848051 prefixEnd_6848051 := by exact prefixLift 6848051
  have htrace : WordTrace (prefixWord ++ tailWord_6848051) baseStart_6848051 baseEnd_6848051 := by
    simpa [prefixWord, tailWord_6848051, baseEnd_6848051] using wordTrace_append hprefix tailTrace_6848051
  have hstable : (prefixWord ++ tailWord_6848051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848051).length < 2 ^ (prefixWord ++ tailWord_6848051).sum := by decide
  have hdescent : baseEnd_6848051 < baseStart_6848051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848074 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_6848074 : Nat := 118140960795 + 6848074 * 2 ^ 59
def prefixEnd_6848074 : Nat := 4983230072969 + 3 ^ 40 * 6848074 * 2
def baseEnd_6848074 : Nat := 3516353519557745112681287

theorem tailTrace_6848074 : CollatzResearch.WordTrace tailWord_6848074 prefixEnd_6848074 3516353519557745112681287 := by
  unfold tailWord_6848074
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442444548151232692761819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166513185461736620514031517 62442444548151232692761819)
  ·
    refine ⟨93663666822226849039142729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62442444548151232692761819 93663666822226849039142729)
    ·
      refine ⟨70247750116670136779357047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93663666822226849039142729 70247750116670136779357047)
      ·
        refine ⟨105371625175005205169035571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70247750116670136779357047 105371625175005205169035571)
        ·
          refine ⟨158057437762507807753553357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105371625175005205169035571 158057437762507807753553357)
          ·
            refine ⟨59271539160940427907582509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158057437762507807753553357 59271539160940427907582509)
            ·
              refine ⟨22226827185352660465343441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59271539160940427907582509 22226827185352660465343441)
              ·
                refine ⟨16670120389014495349007581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22226827185352660465343441 16670120389014495349007581)
                ·
                  refine ⟨6251295145880435755877843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16670120389014495349007581 6251295145880435755877843)
                  ·
                    refine ⟨9376942718820653633816765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6251295145880435755877843 9376942718820653633816765)
                    ·
                      refine ⟨3516353519557745112681287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9376942718820653633816765 3516353519557745112681287)
                      ·
                        rfl

theorem cell23_6848074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_6848074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848074 prefixEnd_6848074 := by exact prefixLift 6848074
  have htrace : WordTrace (prefixWord ++ tailWord_6848074) baseStart_6848074 baseEnd_6848074 := by
    simpa [prefixWord, tailWord_6848074, baseEnd_6848074] using wordTrace_append hprefix tailTrace_6848074
  have hstable : (prefixWord ++ tailWord_6848074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848074).length < 2 ^ (prefixWord ++ tailWord_6848074).sum := by decide
  have hdescent : baseEnd_6848074 < baseStart_6848074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848084 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_6848084 : Nat := 118140960795 + 6848084 * 2 ^ 59
def prefixEnd_6848084 : Nat := 4983230072969 + 3 ^ 40 * 6848084 * 2
def baseEnd_6848084 : Nat := 3516358654364290073556241

theorem tailTrace_6848084 : CollatzResearch.WordTrace tailWord_6848084 prefixEnd_6848084 3516358654364290073556241 := by
  unfold tailWord_6848084
  simp only [CollatzResearch.WordTrace]
  refine ⟨124885071461284351239455653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166513428615045801652607537 124885071461284351239455653)
  ·
    refine ⟨23415950898990815857397935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124885071461284351239455653 23415950898990815857397935)
    ·
      refine ⟨35123926348486223786096903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23415950898990815857397935 35123926348486223786096903)
      ·
        refine ⟨52685889522729335679145355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35123926348486223786096903 52685889522729335679145355)
        ·
          refine ⟨79028834284094003518718033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52685889522729335679145355 79028834284094003518718033)
          ·
            refine ⟨59271625713070502639038525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79028834284094003518718033 59271625713070502639038525)
            ·
              refine ⟨22226859642401438489639447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59271625713070502639038525 22226859642401438489639447)
              ·
                refine ⟨33340289463602157734459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22226859642401438489639447 33340289463602157734459171)
                ·
                  refine ⟨50010434195403236601688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33340289463602157734459171 50010434195403236601688757)
                  ·
                    refine ⟨4688478205819053431408321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50010434195403236601688757 4688478205819053431408321)
                    ·
                      refine ⟨3516358654364290073556241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688478205819053431408321 3516358654364290073556241)
                      ·
                        rfl

theorem cell23_6848084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_6848084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848084 prefixEnd_6848084 := by exact prefixLift 6848084
  have htrace : WordTrace (prefixWord ++ tailWord_6848084) baseStart_6848084 baseEnd_6848084 := by
    simpa [prefixWord, tailWord_6848084, baseEnd_6848084] using wordTrace_append hprefix tailTrace_6848084
  have hstable : (prefixWord ++ tailWord_6848084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848084).length < 2 ^ (prefixWord ++ tailWord_6848084).sum := by decide
  have hdescent : baseEnd_6848084 < baseStart_6848084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848137 : List Nat := [1, 2, 1, 1, 4, 1, 6, 7]
def baseStart_6848137 : Nat := 118140960795 + 6848137 * 2 ^ 59
def prefixEnd_6848137 : Nat := 4983230072969 + 3 ^ 40 * 6848137 * 2
def baseEnd_6848137 : Nat := 130236513660702902451611

theorem tailTrace_6848137 : CollatzResearch.WordTrace tailWord_6848137 prefixEnd_6848137 130236513660702902451611 := by
  unfold tailWord_6848137
  simp only [CollatzResearch.WordTrace]
  refine ⟨249772075991376692530590665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166514717327584461687060443 249772075991376692530590665)
  ·
    refine ⟨187329056993532519397942999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249772075991376692530590665 187329056993532519397942999)
    ·
      refine ⟨280993585490298779096914499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187329056993532519397942999 280993585490298779096914499)
      ·
        refine ⟨421490378235448168645371749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280993585490298779096914499 421490378235448168645371749)
        ·
          refine ⟨79029445919146531621007203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421490378235448168645371749 79029445919146531621007203)
          ·
            refine ⟨118544168878719797431510805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79029445919146531621007203 118544168878719797431510805)
            ·
              refine ⟨5556757916189990504602069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118544168878719797431510805 5556757916189990504602069)
              ·
                refine ⟨130236513660702902451611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5556757916189990504602069 130236513660702902451611)
                ·
                  rfl

theorem cell23_6848137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 7].length) (baseStart_6848137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848137 prefixEnd_6848137 := by exact prefixLift 6848137
  have htrace : WordTrace (prefixWord ++ tailWord_6848137) baseStart_6848137 baseEnd_6848137 := by
    simpa [prefixWord, tailWord_6848137, baseEnd_6848137] using wordTrace_append hprefix tailTrace_6848137
  have hstable : (prefixWord ++ tailWord_6848137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848137).length < 2 ^ (prefixWord ++ tailWord_6848137).sum := by decide
  have hdescent : baseEnd_6848137 < baseStart_6848137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848198 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6848198 : Nat := 118140960795 + 6848198 * 2 ^ 59
def prefixEnd_6848198 : Nat := 4983230072969 + 3 ^ 40 * 6848198 * 2
def baseEnd_6848198 : Nat := 3516417191158902627530717

theorem tailTrace_6848198 : CollatzResearch.WordTrace tailWord_6848198 prefixEnd_6848198 3516417191158902627530717 := by
  unfold tailWord_6848198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805446901379865623392539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166516200562770466632374165 7805446901379865623392539)
  ·
    refine ⟨11708170352069798435088809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7805446901379865623392539 11708170352069798435088809)
    ·
      refine ⟨8781127764052348826316607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11708170352069798435088809 8781127764052348826316607)
      ·
        refine ⟨13171691646078523239474911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781127764052348826316607 13171691646078523239474911)
        ·
          refine ⟨19757537469117784859212367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13171691646078523239474911 19757537469117784859212367)
          ·
            refine ⟨29636306203676677288818551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19757537469117784859212367 29636306203676677288818551)
            ·
              refine ⟨44454459305515015933227827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29636306203676677288818551 44454459305515015933227827)
              ·
                refine ⟨66681688958272523899841741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44454459305515015933227827 66681688958272523899841741)
                ·
                  refine ⟨25005633359352196462440653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66681688958272523899841741 25005633359352196462440653)
                  ·
                    refine ⟨9377112509757073673415245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25005633359352196462440653 9377112509757073673415245)
                    ·
                      refine ⟨3516417191158902627530717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9377112509757073673415245 3516417191158902627530717)
                      ·
                        rfl

theorem cell23_6848198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6848198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848198 prefixEnd_6848198 := by exact prefixLift 6848198
  have htrace : WordTrace (prefixWord ++ tailWord_6848198) baseStart_6848198 baseEnd_6848198 := by
    simpa [prefixWord, tailWord_6848198, baseEnd_6848198] using wordTrace_append hprefix tailTrace_6848198
  have hstable : (prefixWord ++ tailWord_6848198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848198).length < 2 ^ (prefixWord ++ tailWord_6848198).sum := by decide
  have hdescent : baseEnd_6848198 < baseStart_6848198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848207 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_6848207 : Nat := 118140960795 + 6848207 * 2 ^ 59
def prefixEnd_6848207 : Nat := 4983230072969 + 3 ^ 40 * 6848207 * 2
def baseEnd_6848207 : Nat := 3516421812484793092318175

theorem tailTrace_6848207 : CollatzResearch.WordTrace tailWord_6848207 prefixEnd_6848207 3516421812484793092318175 := by
  unfold tailWord_6848207
  simp only [CollatzResearch.WordTrace]
  refine ⟨249774629101123094485638875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166516419400748729657092583 249774629101123094485638875)
  ·
    refine ⟨374661943651684641728458313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249774629101123094485638875 374661943651684641728458313)
    ·
      refine ⟨280996457738763481296343735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374661943651684641728458313 280996457738763481296343735)
      ·
        refine ⟨421494686608145221944515603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280996457738763481296343735 421494686608145221944515603)
        ·
          refine ⟨632242029912217832916773405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421494686608145221944515603 632242029912217832916773405)
          ·
            refine ⟨237090761217081687343790027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632242029912217832916773405 237090761217081687343790027)
            ·
              refine ⟨355636141825622531015685041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237090761217081687343790027 355636141825622531015685041)
              ·
                refine ⟨266727106369216898261763781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355636141825622531015685041 266727106369216898261763781)
                ·
                  refine ⟨50011332444228168424080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266727106369216898261763781 50011332444228168424080709)
                  ·
                    refine ⟨9377124833292781579515133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50011332444228168424080709 9377124833292781579515133)
                    ·
                      refine ⟨3516421812484793092318175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9377124833292781579515133 3516421812484793092318175)
                      ·
                        rfl

theorem cell23_6848207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_6848207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848207 prefixEnd_6848207 := by exact prefixLift 6848207
  have htrace : WordTrace (prefixWord ++ tailWord_6848207) baseStart_6848207 baseEnd_6848207 := by
    simpa [prefixWord, tailWord_6848207, baseEnd_6848207] using wordTrace_append hprefix tailTrace_6848207
  have hstable : (prefixWord ++ tailWord_6848207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848207).length < 2 ^ (prefixWord ++ tailWord_6848207).sum := by decide
  have hdescent : baseEnd_6848207 < baseStart_6848207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848231 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6848231 : Nat := 118140960795 + 6848231 * 2 ^ 59
def prefixEnd_6848231 : Nat := 4983230072969 + 3 ^ 40 * 6848231 * 2
def baseEnd_6848231 : Nat := 1172144712006833666139355

theorem tailTrace_6848231 : CollatzResearch.WordTrace tailWord_6848231 prefixEnd_6848231 1172144712006833666139355 := by
  unfold tailWord_6848231
  simp only [CollatzResearch.WordTrace]
  refine ⟨249775504453036146584512547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166517002968690764389675031 249775504453036146584512547)
  ·
    refine ⟨374663256679554219876768821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249775504453036146584512547 374663256679554219876768821)
    ·
      refine ⟨35124680313708208113447077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374663256679554219876768821 35124680313708208113447077)
      ·
        refine ⟨6585877558820289021271327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35124680313708208113447077 6585877558820289021271327)
        ·
          refine ⟨9878816338230433531906991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585877558820289021271327 9878816338230433531906991)
          ·
            refine ⟨14818224507345650297860487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878816338230433531906991 14818224507345650297860487)
            ·
              refine ⟨22227336761018475446790731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14818224507345650297860487 22227336761018475446790731)
              ·
                refine ⟨33341005141527713170186097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22227336761018475446790731 33341005141527713170186097)
                ·
                  refine ⟨25005753856145784877639573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33341005141527713170186097 25005753856145784877639573)
                  ·
                    refine ⟨1172144712006833666139355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25005753856145784877639573 1172144712006833666139355)
                    ·
                      rfl

theorem cell23_6848231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6848231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848231 prefixEnd_6848231 := by exact prefixLift 6848231
  have htrace : WordTrace (prefixWord ++ tailWord_6848231) baseStart_6848231 baseEnd_6848231 := by
    simpa [prefixWord, tailWord_6848231, baseEnd_6848231] using wordTrace_append hprefix tailTrace_6848231
  have hstable : (prefixWord ++ tailWord_6848231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848231).length < 2 ^ (prefixWord ++ tailWord_6848231).sum := by decide
  have hdescent : baseEnd_6848231 < baseStart_6848231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848238 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_6848238 : Nat := 118140960795 + 6848238 * 2 ^ 59
def prefixEnd_6848238 : Nat := 4983230072969 + 3 ^ 40 * 6848238 * 2
def baseEnd_6848238 : Nat := 3516437730385082471030533

theorem tailTrace_6848238 : CollatzResearch.WordTrace tailWord_6848238 prefixEnd_6848238 3516437730385082471030533 := by
  unfold tailWord_6848238
  simp only [CollatzResearch.WordTrace]
  refine ⟨31221969970501348347502171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166517173176007191186678245 31221969970501348347502171)
  ·
    refine ⟨46832954955752022521253257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31221969970501348347502171 46832954955752022521253257)
    ·
      refine ⟨35124716216814016890939943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46832954955752022521253257 35124716216814016890939943)
      ·
        refine ⟨52687074325221025336409915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35124716216814016890939943 52687074325221025336409915)
        ·
          refine ⟨79030611487831538004614873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52687074325221025336409915 79030611487831538004614873)
          ·
            refine ⟨59272958615873653503461155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79030611487831538004614873 59272958615873653503461155)
            ·
              refine ⟨88909437923810480255191733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59272958615873653503461155 88909437923810480255191733)
              ·
                refine ⟨8335259805357232523924225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88909437923810480255191733 8335259805357232523924225)
                ·
                  refine ⟨6251444854017924392943169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8335259805357232523924225 6251444854017924392943169)
                  ·
                    refine ⟨4688583640513443294707377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6251444854017924392943169 4688583640513443294707377)
                    ·
                      refine ⟨3516437730385082471030533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688583640513443294707377 3516437730385082471030533)
                      ·
                        rfl

theorem cell23_6848238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_6848238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848238 prefixEnd_6848238 := by exact prefixLift 6848238
  have htrace : WordTrace (prefixWord ++ tailWord_6848238) baseStart_6848238 baseEnd_6848238 := by
    simpa [prefixWord, tailWord_6848238, baseEnd_6848238] using wordTrace_append hprefix tailTrace_6848238
  have hstable : (prefixWord ++ tailWord_6848238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848238).length < 2 ^ (prefixWord ++ tailWord_6848238).sum := by decide
  have hdescent : baseEnd_6848238 < baseStart_6848238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848267 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_6848267 : Nat := 118140960795 + 6848267 * 2 ^ 59
def prefixEnd_6848267 : Nat := 4983230072969 + 3 ^ 40 * 6848267 * 2
def baseEnd_6848267 : Nat := 3516452621324062857567899

theorem tailTrace_6848267 : CollatzResearch.WordTrace tailWord_6848267 prefixEnd_6848267 3516452621324062857567899 := by
  unfold tailWord_6848267
  simp only [CollatzResearch.WordTrace]
  refine ⟨249776817480905724732823055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166517878320603816488548703 249776817480905724732823055)
  ·
    refine ⟨374665226221358587099234583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249776817480905724732823055 374665226221358587099234583)
    ·
      refine ⟨561997839332037880648851875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374665226221358587099234583 561997839332037880648851875)
      ·
        refine ⟨842996758998056820973277813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561997839332037880648851875 842996758998056820973277813)
        ·
          refine ⟨79030946156067826966244795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 842996758998056820973277813 79030946156067826966244795)
          ·
            refine ⟨118546419234101740449367193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79030946156067826966244795 118546419234101740449367193)
            ·
              refine ⟨88909814425576305337025395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118546419234101740449367193 88909814425576305337025395)
              ·
                refine ⟨133364721638364458005538093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88909814425576305337025395 133364721638364458005538093)
                ·
                  refine ⟨50011770614386671752076785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133364721638364458005538093 50011770614386671752076785)
                  ·
                    refine ⟨37508827960790003814057589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50011770614386671752076785 37508827960790003814057589)
                    ·
                      refine ⟨3516452621324062857567899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37508827960790003814057589 3516452621324062857567899)
                      ·
                        rfl

theorem cell23_6848267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_6848267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848267 prefixEnd_6848267 := by exact prefixLift 6848267
  have htrace : WordTrace (prefixWord ++ tailWord_6848267) baseStart_6848267 baseEnd_6848267 := by
    simpa [prefixWord, tailWord_6848267, baseEnd_6848267] using wordTrace_append hprefix tailTrace_6848267
  have hstable : (prefixWord ++ tailWord_6848267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848267).length < 2 ^ (prefixWord ++ tailWord_6848267).sum := by decide
  have hdescent : baseEnd_6848267 < baseStart_6848267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848338 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_6848338 : Nat := 118140960795 + 6848338 * 2 ^ 59
def prefixEnd_6848338 : Nat := 4983230072969 + 3 ^ 40 * 6848338 * 2
def baseEnd_6848338 : Nat := 1172163026150177359926691

theorem tailTrace_6848338 : CollatzResearch.WordTrace tailWord_6848338 prefixEnd_6848338 1172163026150177359926691 := by
  unfold tailWord_6848338
  simp only [CollatzResearch.WordTrace]
  refine ⟨62444851765912125964664417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166519604709099002572438445 62444851765912125964664417)
  ·
    refine ⟨46833638824434094473498313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62444851765912125964664417 46833638824434094473498313)
    ·
      refine ⟨35125229118325570855123735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46833638824434094473498313 35125229118325570855123735)
      ·
        refine ⟨52687843677488356282685603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35125229118325570855123735 52687843677488356282685603)
        ·
          refine ⟨79031765516232534424028405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52687843677488356282685603 79031765516232534424028405)
          ·
            refine ⟨7409228017146800102252663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79031765516232534424028405 7409228017146800102252663)
            ·
              refine ⟨11113842025720200153378995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409228017146800102252663 11113842025720200153378995)
              ·
                refine ⟨16670763038580300230068493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11113842025720200153378995 16670763038580300230068493)
                ·
                  refine ⟨6251536139467612586275685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16670763038580300230068493 6251536139467612586275685)
                  ·
                    refine ⟨1172163026150177359926691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251536139467612586275685 1172163026150177359926691)
                    ·
                      rfl

theorem cell23_6848338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_6848338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848338 prefixEnd_6848338 := by exact prefixLift 6848338
  have htrace : WordTrace (prefixWord ++ tailWord_6848338) baseStart_6848338 baseEnd_6848338 := by
    simpa [prefixWord, tailWord_6848338, baseEnd_6848338] using wordTrace_append hprefix tailTrace_6848338
  have hstable : (prefixWord ++ tailWord_6848338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848338).length < 2 ^ (prefixWord ++ tailWord_6848338).sum := by decide
  have hdescent : baseEnd_6848338 < baseStart_6848338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848351 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 6]
def baseStart_6848351 : Nat := 118140960795 + 6848351 * 2 ^ 59
def prefixEnd_6848351 : Nat := 4983230072969 + 3 ^ 40 * 6848351 * 2
def baseEnd_6848351 : Nat := 390721750411004503213057

theorem tailTrace_6848351 : CollatzResearch.WordTrace tailWord_6848351 prefixEnd_6848351 390721750411004503213057 := by
  unfold tailWord_6848351
  simp only [CollatzResearch.WordTrace]
  refine ⟨249779881212601407078880907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166519920808400938052587271 249779881212601407078880907)
  ·
    refine ⟨374669821818902110618321361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249779881212601407078880907 374669821818902110618321361)
    ·
      refine ⟨281002366364176582963741021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374669821818902110618321361 281002366364176582963741021)
      ·
        refine ⟨105375887386566218611402883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281002366364176582963741021 105375887386566218611402883)
        ·
          refine ⟨158063831079849327917104325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105375887386566218611402883 158063831079849327917104325)
          ·
            refine ⟨29636968327471748984457061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158063831079849327917104325 29636968327471748984457061)
            ·
              refine ⟨5556931561400952934585699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29636968327471748984457061 5556931561400952934585699)
              ·
                refine ⟨8335397342101429401878549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5556931561400952934585699 8335397342101429401878549)
                ·
                  refine ⟨390721750411004503213057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8335397342101429401878549 390721750411004503213057)
                  ·
                    rfl

theorem cell23_6848351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 6].length) (baseStart_6848351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848351 prefixEnd_6848351 := by exact prefixLift 6848351
  have htrace : WordTrace (prefixWord ++ tailWord_6848351) baseStart_6848351 baseEnd_6848351 := by
    simpa [prefixWord, tailWord_6848351, baseEnd_6848351] using wordTrace_append hprefix tailTrace_6848351
  have hstable : (prefixWord ++ tailWord_6848351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848351).length < 2 ^ (prefixWord ++ tailWord_6848351).sum := by decide
  have hdescent : baseEnd_6848351 < baseStart_6848351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848361 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_6848361 : Nat := 118140960795 + 6848361 * 2 ^ 59
def prefixEnd_6848361 : Nat := 4983230072969 + 3 ^ 40 * 6848361 * 2
def baseEnd_6848361 : Nat := 3516500888505585489792467

theorem tailTrace_6848361 : CollatzResearch.WordTrace tailWord_6848361 prefixEnd_6848361 3516500888505585489792467 := by
  unfold tailWord_6848361
  simp only [CollatzResearch.WordTrace]
  refine ⟨249780245942565178786744937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166520163961710119191163291 249780245942565178786744937)
  ·
    refine ⟨187335184456923884090058703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249780245942565178786744937 187335184456923884090058703)
    ·
      refine ⟨281002776685385826135088055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187335184456923884090058703 281002776685385826135088055)
      ·
        refine ⟨421504165028078739202632083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281002776685385826135088055 421504165028078739202632083)
        ·
          refine ⟨632256247542118108803948125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421504165028078739202632083 632256247542118108803948125)
          ·
            refine ⟨237096092828294290801480547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632256247542118108803948125 237096092828294290801480547)
            ·
              refine ⟨355644139242441436202220821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237096092828294290801480547 355644139242441436202220821)
              ·
                refine ⟨16670819026989442321979101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355644139242441436202220821 16670819026989442321979101)
                ·
                  refine ⟨6251557135121040870742163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16670819026989442321979101 6251557135121040870742163)
                  ·
                    refine ⟨9377335702681561306113245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6251557135121040870742163 9377335702681561306113245)
                    ·
                      refine ⟨3516500888505585489792467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9377335702681561306113245 3516500888505585489792467)
                      ·
                        rfl

theorem cell23_6848361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_6848361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848361 prefixEnd_6848361 := by exact prefixLift 6848361
  have htrace : WordTrace (prefixWord ++ tailWord_6848361) baseStart_6848361 baseEnd_6848361 := by
    simpa [prefixWord, tailWord_6848361, baseEnd_6848361] using wordTrace_append hprefix tailTrace_6848361
  have hstable : (prefixWord ++ tailWord_6848361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848361).length < 2 ^ (prefixWord ++ tailWord_6848361).sum := by decide
  have hdescent : baseEnd_6848361 < baseStart_6848361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848388 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6848388 : Nat := 118140960795 + 6848388 * 2 ^ 59
def prefixEnd_6848388 : Nat := 4983230072969 + 3 ^ 40 * 6848388 * 2
def baseEnd_6848388 : Nat := 3516514752483256884154843

theorem tailTrace_6848388 : CollatzResearch.WordTrace tailWord_6848388 prefixEnd_6848388 3516514752483256884154843 := by
  unfold tailWord_6848388
  simp only [CollatzResearch.WordTrace]
  refine ⟨124890615356733681198988909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166520820475644908265318545 124890615356733681198988909)
  ·
    refine ⟨46833980758775130449620841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124890615356733681198988909 46833980758775130449620841)
    ·
      refine ⟨35125485569081347837215631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46833980758775130449620841 35125485569081347837215631)
      ·
        refine ⟨52688228353622021755823447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35125485569081347837215631 52688228353622021755823447)
        ·
          refine ⟨79032342530433032633735171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52688228353622021755823447 79032342530433032633735171)
          ·
            refine ⟨118548513795649548950602757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79032342530433032633735171 118548513795649548950602757)
            ·
              refine ⟨22227846336684290428238017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118548513795649548950602757 22227846336684290428238017)
              ·
                refine ⟨16670884752513217821178513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22227846336684290428238017 16670884752513217821178513)
                ·
                  refine ⟨12503163564384913365883885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16670884752513217821178513 12503163564384913365883885)
                  ·
                    refine ⟨4688686336644342512206457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12503163564384913365883885 4688686336644342512206457)
                    ·
                      refine ⟨3516514752483256884154843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688686336644342512206457 3516514752483256884154843)
                      ·
                        rfl

theorem cell23_6848388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6848388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848388 prefixEnd_6848388 := by exact prefixLift 6848388
  have htrace : WordTrace (prefixWord ++ tailWord_6848388) baseStart_6848388 baseEnd_6848388 := by
    simpa [prefixWord, tailWord_6848388, baseEnd_6848388] using wordTrace_append hprefix tailTrace_6848388
  have hstable : (prefixWord ++ tailWord_6848388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848388).length < 2 ^ (prefixWord ++ tailWord_6848388).sum := by decide
  have hdescent : baseEnd_6848388 < baseStart_6848388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848445 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6848445 : Nat := 118140960795 + 6848445 * 2 ^ 59
def prefixEnd_6848445 : Nat := 4983230072969 + 3 ^ 40 * 6848445 * 2
def baseEnd_6848445 : Nat := 1172181340293521053714027

theorem tailTrace_6848445 : CollatzResearch.WordTrace tailWord_6848445 prefixEnd_6848445 1172181340293521053714027 := by
  unfold tailWord_6848445
  simp only [CollatzResearch.WordTrace]
  refine ⟨249783309674260861132802789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166522206449507240755201859 249783309674260861132802789)
  ·
    refine ⟨46834370563923911462400523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249783309674260861132802789 46834370563923911462400523)
    ·
      refine ⟨70251555845885867193600785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46834370563923911462400523 70251555845885867193600785)
      ·
        refine ⟨52688666884414400395200589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70251555845885867193600785 52688666884414400395200589)
        ·
          refine ⟨19758250081655400148200221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52688666884414400395200589 19758250081655400148200221)
          ·
            refine ⟨7409343780620775055575083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19758250081655400148200221 7409343780620775055575083)
            ·
              refine ⟨11114015670931162583362625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409343780620775055575083 11114015670931162583362625)
              ·
                refine ⟨8335511753198371937521969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11114015670931162583362625 8335511753198371937521969)
                ·
                  refine ⟨6251633814898778953141477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8335511753198371937521969 6251633814898778953141477)
                  ·
                    refine ⟨1172181340293521053714027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251633814898778953141477 1172181340293521053714027)
                    ·
                      rfl

theorem cell23_6848445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6848445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848445 prefixEnd_6848445 := by exact prefixLift 6848445
  have htrace : WordTrace (prefixWord ++ tailWord_6848445) baseStart_6848445 baseEnd_6848445 := by
    simpa [prefixWord, tailWord_6848445, baseEnd_6848445] using wordTrace_append hprefix tailTrace_6848445
  have hstable : (prefixWord ++ tailWord_6848445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848445).length < 2 ^ (prefixWord ++ tailWord_6848445).sum := by decide
  have hdescent : baseEnd_6848445 < baseStart_6848445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848565 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 5]
def baseStart_6848565 : Nat := 118140960795 + 6848565 * 2 ^ 59
def prefixEnd_6848565 : Nat := 4983230072969 + 3 ^ 40 * 6848565 * 2
def baseEnd_6848565 : Nat := 390733959839900299071281

theorem tailTrace_6848565 : CollatzResearch.WordTrace tailWord_6848565 prefixEnd_6848565 390733959839900299071281 := by
  unfold tailWord_6848565
  simp only [CollatzResearch.WordTrace]
  refine ⟨249787686433826121627171149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166525124289217414418114099 249787686433826121627171149)
  ·
    refine ⟨93670382412684795610189181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249787686433826121627171149 93670382412684795610189181)
    ·
      refine ⟨35126393404756798353820943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93670382412684795610189181 35126393404756798353820943)
      ·
        refine ⟨52689590107135197530731415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35126393404756798353820943 52689590107135197530731415)
        ·
          refine ⟨79034385160702796296097123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52689590107135197530731415 79034385160702796296097123)
          ·
            refine ⟨118551577741054194444145685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79034385160702796296097123 118551577741054194444145685)
            ·
              refine ⟨5557105206611915364569329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118551577741054194444145685 5557105206611915364569329)
              ·
                refine ⟨4167828904958936523426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557105206611915364569329 4167828904958936523426997)
                ·
                  refine ⟨390733959839900299071281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167828904958936523426997 390733959839900299071281)
                  ·
                    rfl

theorem cell23_6848565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_6848565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848565 prefixEnd_6848565 := by exact prefixLift 6848565
  have htrace : WordTrace (prefixWord ++ tailWord_6848565) baseStart_6848565 baseEnd_6848565 := by
    simpa [prefixWord, tailWord_6848565, baseEnd_6848565] using wordTrace_append hprefix tailTrace_6848565
  have hstable : (prefixWord ++ tailWord_6848565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848565).length < 2 ^ (prefixWord ++ tailWord_6848565).sum := by decide
  have hdescent : baseEnd_6848565 < baseStart_6848565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848581 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_6848581 : Nat := 118140960795 + 6848581 * 2 ^ 59
def prefixEnd_6848581 : Nat := 4983230072969 + 3 ^ 40 * 6848581 * 2
def baseEnd_6848581 : Nat := 3516613854249574629041455

theorem tailTrace_6848581 : CollatzResearch.WordTrace tailWord_6848581 prefixEnd_6848581 3516613854249574629041455 := by
  unfold tailWord_6848581
  simp only [CollatzResearch.WordTrace]
  refine ⟨249788270001768156359753597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166525513334512104239835731 249788270001768156359753597)
  ·
    refine ⟨93670601250663058634907599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249788270001768156359753597 93670601250663058634907599)
    ·
      refine ⟨140505901875994587952361399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93670601250663058634907599 140505901875994587952361399)
      ·
        refine ⟨210758852813991881928542099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140505901875994587952361399 210758852813991881928542099)
        ·
          refine ⟨316138279220987822892813149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210758852813991881928542099 316138279220987822892813149)
          ·
            refine ⟨118551854707870433584804931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316138279220987822892813149 118551854707870433584804931)
            ·
              refine ⟨177827782061805650377207397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118551854707870433584804931 177827782061805650377207397)
              ·
                refine ⟨33342709136588559445726387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177827782061805650377207397 33342709136588559445726387)
                ·
                  refine ⟨50014063704882839168589581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33342709136588559445726387 50014063704882839168589581)
                  ·
                    refine ⟨18755273889331064688221093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50014063704882839168589581 18755273889331064688221093)
                    ·
                      refine ⟨3516613854249574629041455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18755273889331064688221093 3516613854249574629041455)
                      ·
                        rfl

theorem cell23_6848581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_6848581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848581 prefixEnd_6848581 := by exact prefixLift 6848581
  have htrace : WordTrace (prefixWord ++ tailWord_6848581) baseStart_6848581 baseEnd_6848581 := by
    simpa [prefixWord, tailWord_6848581, baseEnd_6848581] using wordTrace_append hprefix tailTrace_6848581
  have hstable : (prefixWord ++ tailWord_6848581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848581).length < 2 ^ (prefixWord ++ tailWord_6848581).sum := by decide
  have hdescent : baseEnd_6848581 < baseStart_6848581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848611 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6848611 : Nat := 118140960795 + 6848611 * 2 ^ 59
def prefixEnd_6848611 : Nat := 4983230072969 + 3 ^ 40 * 6848611 * 2
def baseEnd_6848611 : Nat := 3516629258669209511666317

theorem tailTrace_6848611 : CollatzResearch.WordTrace tailWord_6848611 prefixEnd_6848611 3516629258669209511666317 := by
  unfold tailWord_6848611
  simp only [CollatzResearch.WordTrace]
  refine ⟨249789364191659471483345687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166526242794439647655563791 249789364191659471483345687)
  ·
    refine ⟨374684046287489207225018531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249789364191659471483345687 374684046287489207225018531)
    ·
      refine ⟨562026069431233810837527797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374684046287489207225018531 562026069431233810837527797)
      ·
        refine ⟨52689944009178169766018231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 562026069431233810837527797 52689944009178169766018231)
        ·
          refine ⟨79034916013767254649027347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52689944009178169766018231 79034916013767254649027347)
          ·
            refine ⟨118552374020650881973541021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79034916013767254649027347 118552374020650881973541021)
            ·
              refine ⟨44457140257744080740077883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118552374020650881973541021 44457140257744080740077883)
              ·
                refine ⟨66685710386616121110116825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44457140257744080740077883 66685710386616121110116825)
                ·
                  refine ⟨50014282789962090832587619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66685710386616121110116825 50014282789962090832587619)
                  ·
                    refine ⟨75021424184943136248881429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50014282789962090832587619 75021424184943136248881429)
                    ·
                      refine ⟨3516629258669209511666317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75021424184943136248881429 3516629258669209511666317)
                      ·
                        rfl

theorem cell23_6848611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6848611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848611 prefixEnd_6848611 := by exact prefixLift 6848611
  have htrace : WordTrace (prefixWord ++ tailWord_6848611) baseStart_6848611 baseEnd_6848611 := by
    simpa [prefixWord, tailWord_6848611, baseEnd_6848611] using wordTrace_append hprefix tailTrace_6848611
  have hstable : (prefixWord ++ tailWord_6848611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848611).length < 2 ^ (prefixWord ++ tailWord_6848611).sum := by decide
  have hdescent : baseEnd_6848611 < baseStart_6848611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848625 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 1, 4]
def baseStart_6848625 : Nat := 118140960795 + 6848625 * 2 ^ 59
def prefixEnd_6848625 : Nat := 4983230072969 + 3 ^ 40 * 6848625 * 2
def baseEnd_6848625 : Nat := 1172212149132790818963751

theorem tailTrace_6848625 : CollatzResearch.WordTrace tailWord_6848625 prefixEnd_6848625 1172212149132790818963751 := by
  unfold tailWord_6848625
  simp only [CollatzResearch.WordTrace]
  refine ⟨249789874813608751874355329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166526583209072501249570219 249789874813608751874355329)
  ·
    refine ⟨187342406110206563905766497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249789874813608751874355329 187342406110206563905766497)
    ·
      refine ⟨140506804582654922929324873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187342406110206563905766497 140506804582654922929324873)
      ·
        refine ⟨105380103436991192196993655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140506804582654922929324873 105380103436991192196993655)
        ·
          refine ⟨158070155155486788295490483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105380103436991192196993655 158070155155486788295490483)
          ·
            refine ⟨237105232733230182443235725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158070155155486788295490483 237105232733230182443235725)
            ·
              refine ⟨88914462274961318416213397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237105232733230182443235725 88914462274961318416213397)
              ·
                refine ⟨4167865419138811800760003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88914462274961318416213397 4167865419138811800760003)
                ·
                  refine ⟨6251798128708217701140005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167865419138811800760003 6251798128708217701140005)
                  ·
                    refine ⟨1172212149132790818963751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251798128708217701140005 1172212149132790818963751)
                    ·
                      rfl

theorem cell23_6848625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_6848625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848625 prefixEnd_6848625 := by exact prefixLift 6848625
  have htrace : WordTrace (prefixWord ++ tailWord_6848625) baseStart_6848625 baseEnd_6848625 := by
    simpa [prefixWord, tailWord_6848625, baseEnd_6848625] using wordTrace_append hprefix tailTrace_6848625
  have hstable : (prefixWord ++ tailWord_6848625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848625).length < 2 ^ (prefixWord ++ tailWord_6848625).sum := by decide
  have hdescent : baseEnd_6848625 < baseStart_6848625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848689 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 6]
def baseStart_6848689 : Nat := 118140960795 + 6848689 * 2 ^ 59
def prefixEnd_6848689 : Nat := 4983230072969 + 3 ^ 40 * 6848689 * 2
def baseEnd_6848689 : Nat := 390741034462251134054551

theorem tailTrace_6848689 : CollatzResearch.WordTrace tailWord_6848689 prefixEnd_6848689 390741034462251134054551 := by
  unfold tailWord_6848689
  simp only [CollatzResearch.WordTrace]
  refine ⟨249792209085376890804685121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166528139390251260536456747 249792209085376890804685121)
  ·
    refine ⟨187344156814032668103513841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249792209085376890804685121 187344156814032668103513841)
    ·
      refine ⟨140508117610524501077635381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187344156814032668103513841 140508117610524501077635381)
      ·
        refine ⟨13172636025986671976028317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140508117610524501077635381 13172636025986671976028317)
        ·
          refine ⟨4939738509745001991010619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13172636025986671976028317 4939738509745001991010619)
          ·
            refine ⟨7409607764617502986515929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939738509745001991010619 7409607764617502986515929)
            ·
              refine ⟨5557205823463127239886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409607764617502986515929 5557205823463127239886947)
              ·
                refine ⟨8335808735194690859830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557205823463127239886947 8335808735194690859830421)
                ·
                  refine ⟨390741034462251134054551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8335808735194690859830421 390741034462251134054551)
                  ·
                    rfl

theorem cell23_6848689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_6848689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848689 prefixEnd_6848689 := by exact prefixLift 6848689
  have htrace : WordTrace (prefixWord ++ tailWord_6848689) baseStart_6848689 baseEnd_6848689 := by
    simpa [prefixWord, tailWord_6848689, baseEnd_6848689] using wordTrace_append hprefix tailTrace_6848689
  have hstable : (prefixWord ++ tailWord_6848689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848689).length < 2 ^ (prefixWord ++ tailWord_6848689).sum := by decide
  have hdescent : baseEnd_6848689 < baseStart_6848689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848733 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6848733 : Nat := 118140960795 + 6848733 * 2 ^ 59
def prefixEnd_6848733 : Nat := 4983230072969 + 3 ^ 40 * 6848733 * 2
def baseEnd_6848733 : Nat := 3516691903309058034340757

theorem tailTrace_6848733 : CollatzResearch.WordTrace tailWord_6848733 prefixEnd_6848733 3516691903309058034340757 := by
  unfold tailWord_6848733
  simp only [CollatzResearch.WordTrace]
  refine ⟨249793813897217486319286853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166529209264811657546191235 249793813897217486319286853)
  ·
    refine ⟨46836340105728278684866285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249793813897217486319286853 46836340105728278684866285)
    ·
      refine ⟨17563627539648104506824857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46836340105728278684866285 17563627539648104506824857)
      ·
        refine ⟨13172720654736078380118643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17563627539648104506824857 13172720654736078380118643)
        ·
          refine ⟨19759080982104117570177965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172720654736078380118643 19759080982104117570177965)
          ·
            refine ⟨7409655368289044088816737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759080982104117570177965 7409655368289044088816737)
            ·
              refine ⟨5557241526216783066612553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409655368289044088816737 5557241526216783066612553)
              ·
                refine ⟨4167931144662587299959415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557241526216783066612553 4167931144662587299959415)
                ·
                  refine ⟨6251896716993880949939123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167931144662587299959415 6251896716993880949939123)
                  ·
                    refine ⟨9377845075490821424908685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6251896716993880949939123 9377845075490821424908685)
                    ·
                      refine ⟨3516691903309058034340757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9377845075490821424908685 3516691903309058034340757)
                      ·
                        rfl

theorem cell23_6848733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6848733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848733 prefixEnd_6848733 := by exact prefixLift 6848733
  have htrace : WordTrace (prefixWord ++ tailWord_6848733) baseStart_6848733 baseEnd_6848733 := by
    simpa [prefixWord, tailWord_6848733, baseEnd_6848733] using wordTrace_append hprefix tailTrace_6848733
  have hstable : (prefixWord ++ tailWord_6848733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848733).length < 2 ^ (prefixWord ++ tailWord_6848733).sum := by decide
  have hdescent : baseEnd_6848733 < baseStart_6848733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848755 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3]
def baseStart_6848755 : Nat := 118140960795 + 6848755 * 2 ^ 59
def prefixEnd_6848755 : Nat := 4983230072969 + 3 ^ 40 * 6848755 * 2
def baseEnd_6848755 : Nat := 3516703199883456948265655

theorem tailTrace_6848755 : CollatzResearch.WordTrace tailWord_6848755 prefixEnd_6848755 3516703199883456948265655 := by
  unfold tailWord_6848755
  simp only [CollatzResearch.WordTrace]
  refine ⟨249794616303137784076587719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166529744202091856051058479 249794616303137784076587719)
  ·
    refine ⟨374691924454706676114881579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249794616303137784076587719 374691924454706676114881579)
    ·
      refine ⟨562037886682060014172322369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374691924454706676114881579 562037886682060014172322369)
      ·
        refine ⟨421528415011545010629241777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562037886682060014172322369 421528415011545010629241777)
        ·
          refine ⟨316146311258658757971931333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421528415011545010629241777 316146311258658757971931333)
          ·
            refine ⟨59277433360998517119737125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316146311258658757971931333 59277433360998517119737125)
            ·
              refine ⟨11114518755187221959950711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59277433360998517119737125 11114518755187221959950711)
              ·
                refine ⟨16671778132780832939926067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114518755187221959950711 16671778132780832939926067)
                ·
                  refine ⟨25007667199171249409889101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16671778132780832939926067 25007667199171249409889101)
                  ·
                    refine ⟨9377875199689218528708413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25007667199171249409889101 9377875199689218528708413)
                    ·
                      refine ⟨3516703199883456948265655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9377875199689218528708413 3516703199883456948265655)
                      ·
                        rfl

theorem cell23_6848755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_6848755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848755 prefixEnd_6848755 := by exact prefixLift 6848755
  have htrace : WordTrace (prefixWord ++ tailWord_6848755) baseStart_6848755 baseEnd_6848755 := by
    simpa [prefixWord, tailWord_6848755, baseEnd_6848755] using wordTrace_append hprefix tailTrace_6848755
  have hstable : (prefixWord ++ tailWord_6848755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848755).length < 2 ^ (prefixWord ++ tailWord_6848755).sum := by decide
  have hdescent : baseEnd_6848755 < baseStart_6848755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848795 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 4, 2]
def baseStart_6848795 : Nat := 118140960795 + 6848795 * 2 ^ 59
def prefixEnd_6848795 : Nat := 4983230072969 + 3 ^ 40 * 6848795 * 2
def baseEnd_6848795 : Nat := 3516723739109636791765471

theorem tailTrace_6848795 : CollatzResearch.WordTrace tailWord_6848795 prefixEnd_6848795 3516723739109636791765471 := by
  unfold tailWord_6848795
  simp only [CollatzResearch.WordTrace]
  refine ⟨249796075222992870908043839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166530716815328580605362559 249796075222992870908043839)
  ·
    refine ⟨374694112834489306362065759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249796075222992870908043839 374694112834489306362065759)
    ·
      refine ⟨562041169251733959543098639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374694112834489306362065759 562041169251733959543098639)
      ·
        refine ⟨843061753877600939314647959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562041169251733959543098639 843061753877600939314647959)
        ·
          refine ⟨1264592630816401408971971939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843061753877600939314647959 1264592630816401408971971939)
          ·
            refine ⟨1896888946224602113457957909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264592630816401408971971939 1896888946224602113457957909)
            ·
              refine ⟨88916669354278224068341777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1896888946224602113457957909 88916669354278224068341777)
              ·
                refine ⟨66687502015708668051256333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88916669354278224068341777 66687502015708668051256333)
                ·
                  refine ⟨25007813255890750519221125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66687502015708668051256333 25007813255890750519221125)
                  ·
                    refine ⟨4688964985479515722353961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25007813255890750519221125 4688964985479515722353961)
                    ·
                      refine ⟨3516723739109636791765471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688964985479515722353961 3516723739109636791765471)
                      ·
                        rfl

theorem cell23_6848795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4, 2].length) (baseStart_6848795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848795 prefixEnd_6848795 := by exact prefixLift 6848795
  have htrace : WordTrace (prefixWord ++ tailWord_6848795) baseStart_6848795 baseEnd_6848795 := by
    simpa [prefixWord, tailWord_6848795, baseEnd_6848795] using wordTrace_append hprefix tailTrace_6848795
  have hstable : (prefixWord ++ tailWord_6848795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848795).length < 2 ^ (prefixWord ++ tailWord_6848795).sum := by decide
  have hdescent : baseEnd_6848795 < baseStart_6848795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848812 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_6848812 : Nat := 118140960795 + 6848812 * 2 ^ 59
def prefixEnd_6848812 : Nat := 4983230072969 + 3 ^ 40 * 6848812 * 2
def baseEnd_6848812 : Nat := 3516732468280763225252893

theorem tailTrace_6848812 : CollatzResearch.WordTrace tailWord_6848812 prefixEnd_6848812 3516732468280763225252893 := by
  unfold tailWord_6848812
  simp only [CollatzResearch.WordTrace]
  refine ⟨124898347631965641405706345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166531130175954188540941793 124898347631965641405706345)
  ·
    refine ⟨93673760723974231054279759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124898347631965641405706345 93673760723974231054279759)
    ·
      refine ⟨140510641085961346581419639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93673760723974231054279759 140510641085961346581419639)
      ·
        refine ⟨210765961628942019872129459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140510641085961346581419639 210765961628942019872129459)
        ·
          refine ⟨316148942443413029808194189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210765961628942019872129459 316148942443413029808194189)
          ·
            refine ⟨118555853416279886178072821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316148942443413029808194189 118555853416279886178072821)
            ·
              refine ⟨11114611257776239329194327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118555853416279886178072821 11114611257776239329194327)
              ·
                refine ⟨16671916886664358993791491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114611257776239329194327 16671916886664358993791491)
                ·
                  refine ⟨25007875329996538490687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16671916886664358993791491 25007875329996538490687237)
                  ·
                    refine ⟨4688976624374350967003857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25007875329996538490687237 4688976624374350967003857)
                    ·
                      refine ⟨3516732468280763225252893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688976624374350967003857 3516732468280763225252893)
                      ·
                        rfl

theorem cell23_6848812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_6848812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848812 prefixEnd_6848812 := by exact prefixLift 6848812
  have htrace : WordTrace (prefixWord ++ tailWord_6848812) baseStart_6848812 baseEnd_6848812 := by
    simpa [prefixWord, tailWord_6848812, baseEnd_6848812] using wordTrace_append hprefix tailTrace_6848812
  have hstable : (prefixWord ++ tailWord_6848812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848812).length < 2 ^ (prefixWord ++ tailWord_6848812).sum := by decide
  have hdescent : baseEnd_6848812 < baseStart_6848812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848852 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 7]
def baseStart_6848852 : Nat := 118140960795 + 6848852 * 2 ^ 59
def prefixEnd_6848852 : Nat := 4983230072969 + 3 ^ 40 * 6848852 * 2
def baseEnd_6848852 : Nat := 390750334167438118750301

theorem tailTrace_6848852 : CollatzResearch.WordTrace tailWord_6848852 prefixEnd_6848852 390750334167438118750301 := by
  unfold tailWord_6848852
  simp only [CollatzResearch.WordTrace]
  refine ⟨124899077091893184821434405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166532102789190913095245873 124899077091893184821434405)
  ·
    refine ⟨23418576954729972154018951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124899077091893184821434405 23418576954729972154018951)
    ·
      refine ⟨35127865432094958231028427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23418576954729972154018951 35127865432094958231028427)
      ·
        refine ⟨52691798148142437346542641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35127865432094958231028427 52691798148142437346542641)
        ·
          refine ⟨39518848611106828009906981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52691798148142437346542641 39518848611106828009906981)
          ·
            refine ⟨7409784114582530251857559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39518848611106828009906981 7409784114582530251857559)
            ·
              refine ⟨11114676171873795377786339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409784114582530251857559 11114676171873795377786339)
              ·
                refine ⟨16672014257810693066679509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114676171873795377786339 16672014257810693066679509)
                ·
                  refine ⟨390750334167438118750301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16672014257810693066679509 390750334167438118750301)
                  ·
                    rfl

theorem cell23_6848852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_6848852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848852 prefixEnd_6848852 := by exact prefixLift 6848852
  have htrace : WordTrace (prefixWord ++ tailWord_6848852) baseStart_6848852 baseEnd_6848852 := by
    simpa [prefixWord, tailWord_6848852, baseEnd_6848852] using wordTrace_append hprefix tailTrace_6848852
  have hstable : (prefixWord ++ tailWord_6848852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848852).length < 2 ^ (prefixWord ++ tailWord_6848852).sum := by decide
  have hdescent : baseEnd_6848852 < baseStart_6848852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848882 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_6848882 : Nat := 118140960795 + 6848882 * 2 ^ 59
def prefixEnd_6848882 : Nat := 4983230072969 + 3 ^ 40 * 6848882 * 2
def baseEnd_6848882 : Nat := 1172256137308859317125857

theorem tailTrace_6848882 : CollatzResearch.WordTrace tailWord_6848882 prefixEnd_6848882 1172256137308859317125857 := by
  unfold tailWord_6848882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449812093419421191615225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166532832249118456510973933 62449812093419421191615225)
  ·
    refine ⟨46837359070064565893711419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62449812093419421191615225 46837359070064565893711419)
    ·
      refine ⟨70256038605096848840567129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46837359070064565893711419 70256038605096848840567129)
      ·
        refine ⟨52692028953822636630425347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70256038605096848840567129 52692028953822636630425347)
        ·
          refine ⟨79038043430733954945638021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52692028953822636630425347 79038043430733954945638021)
          ·
            refine ⟨14819633143262616552307129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79038043430733954945638021 14819633143262616552307129)
            ·
              refine ⟨11114724857446962414230347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14819633143262616552307129 11114724857446962414230347)
              ·
                refine ⟨16672087286170443621345521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114724857446962414230347 16672087286170443621345521)
                ·
                  refine ⟨12504065464627832716009141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16672087286170443621345521 12504065464627832716009141)
                  ·
                    refine ⟨1172256137308859317125857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12504065464627832716009141 1172256137308859317125857)
                    ·
                      rfl

theorem cell23_6848882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_6848882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848882 prefixEnd_6848882 := by exact prefixLift 6848882
  have htrace : WordTrace (prefixWord ++ tailWord_6848882) baseStart_6848882 baseEnd_6848882 := by
    simpa [prefixWord, tailWord_6848882, baseEnd_6848882] using wordTrace_append hprefix tailTrace_6848882
  have hstable : (prefixWord ++ tailWord_6848882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848882).length < 2 ^ (prefixWord ++ tailWord_6848882).sum := by decide
  have hdescent : baseEnd_6848882 < baseStart_6848882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_6848888 : Nat := 118140960795 + 6848888 * 2 ^ 59
def prefixEnd_6848888 : Nat := 4983230072969 + 3 ^ 40 * 6848888 * 2
def baseEnd_6848888 : Nat := 3516771492810504927902543

theorem tailTrace_6848888 : CollatzResearch.WordTrace tailWord_6848888 prefixEnd_6848888 3516771492810504927902543 := by
  unfold tailWord_6848888
  simp only [CollatzResearch.WordTrace]
  refine ⟨124899733605827973895589659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166532978141103965194119545 124899733605827973895589659)
  ·
    refine ⟨187349600408741960843384489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124899733605827973895589659 187349600408741960843384489)
    ·
      refine ⟨140512200306556470632538367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187349600408741960843384489 140512200306556470632538367)
      ·
        refine ⟨210768300459834705948807551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140512200306556470632538367 210768300459834705948807551)
        ·
          refine ⟨316152450689752058923211327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210768300459834705948807551 316152450689752058923211327)
          ·
            refine ⟨474228676034628088384816991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316152450689752058923211327 474228676034628088384816991)
            ·
              refine ⟨711343014051942132577225487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474228676034628088384816991 711343014051942132577225487)
              ·
                refine ⟨1067014521077913198865838231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711343014051942132577225487 1067014521077913198865838231)
                ·
                  refine ⟨1600521781616869798298757347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067014521077913198865838231 1600521781616869798298757347)
                  ·
                    refine ⟨2400782672425304697448136021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1600521781616869798298757347 2400782672425304697448136021)
                    ·
                      refine ⟨3516771492810504927902543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2400782672425304697448136021 3516771492810504927902543)
                      ·
                        rfl

theorem cell23_6848888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_6848888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848888 prefixEnd_6848888 := by exact prefixLift 6848888
  have htrace : WordTrace (prefixWord ++ tailWord_6848888) baseStart_6848888 baseEnd_6848888 := by
    simpa [prefixWord, tailWord_6848888, baseEnd_6848888] using wordTrace_append hprefix tailTrace_6848888
  have hstable : (prefixWord ++ tailWord_6848888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848888).length < 2 ^ (prefixWord ++ tailWord_6848888).sum := by decide
  have hdescent : baseEnd_6848888 < baseStart_6848888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848895 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 5, 4]
def baseStart_6848895 : Nat := 118140960795 + 6848895 * 2 ^ 59
def prefixEnd_6848895 : Nat := 4983230072969 + 3 ^ 40 * 6848895 * 2
def baseEnd_6848895 : Nat := 1172258362391695466838337

theorem tailTrace_6848895 : CollatzResearch.WordTrace tailWord_6848895 prefixEnd_6848895 1172258362391695466838337 := by
  unfold tailWord_6848895
  simp only [CollatzResearch.WordTrace]
  refine ⟨249799722522630587986684139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166533148348420391991122759 249799722522630587986684139)
  ·
    refine ⟨374699583783945881980026209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249799722522630587986684139 374699583783945881980026209)
    ·
      refine ⟨281024687837959411485019657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374699583783945881980026209 281024687837959411485019657)
      ·
        refine ⟨210768515878469558613764743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281024687837959411485019657 210768515878469558613764743)
        ·
          refine ⟨316152773817704337920647115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210768515878469558613764743 316152773817704337920647115)
          ·
            refine ⟨474229160726556506880970673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316152773817704337920647115 474229160726556506880970673)
            ·
              refine ⟨355671870544917380160728005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474229160726556506880970673 355671870544917380160728005)
              ·
                refine ⟨66688475727172008780136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355671870544917380160728005 66688475727172008780136501)
                ·
                  refine ⟨6252044599422375823137797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66688475727172008780136501 6252044599422375823137797)
                  ·
                    refine ⟨1172258362391695466838337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252044599422375823137797 1172258362391695466838337)
                    ·
                      rfl

theorem cell23_6848895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_6848895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848895 prefixEnd_6848895 := by exact prefixLift 6848895
  have htrace : WordTrace (prefixWord ++ tailWord_6848895) baseStart_6848895 baseEnd_6848895 := by
    simpa [prefixWord, tailWord_6848895, baseEnd_6848895] using wordTrace_append hprefix tailTrace_6848895
  have hstable : (prefixWord ++ tailWord_6848895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848895).length < 2 ^ (prefixWord ++ tailWord_6848895).sum := by decide
  have hdescent : baseEnd_6848895 < baseStart_6848895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848936 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6848936 : Nat := 118140960795 + 6848936 * 2 ^ 59
def prefixEnd_6848936 : Nat := 4983230072969 + 3 ^ 40 * 6848936 * 2
def baseEnd_6848936 : Nat := 3516796139881920740102323

theorem tailTrace_6848936 : CollatzResearch.WordTrace tailWord_6848936 prefixEnd_6848936 3516796139881920740102323 := by
  unfold tailWord_6848936
  simp only [CollatzResearch.WordTrace]
  refine ⟨124900608957741025994463331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166534145276988034659284441 124900608957741025994463331)
  ·
    refine ⟨187350913436611538991694997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124900608957741025994463331 187350913436611538991694997)
    ·
      refine ⟨8782074067341165890235703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187350913436611538991694997 8782074067341165890235703)
      ·
        refine ⟨13173111101011748835353555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782074067341165890235703 13173111101011748835353555)
        ·
          refine ⟨19759666651517623253030333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13173111101011748835353555 19759666651517623253030333)
          ·
            refine ⟨7409874994319108719886375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759666651517623253030333 7409874994319108719886375)
            ·
              refine ⟨11114812491478663079829563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409874994319108719886375 11114812491478663079829563)
              ·
                refine ⟨16672218737217994619744345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114812491478663079829563 16672218737217994619744345)
                ·
                  refine ⟨12504164052913495964808259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16672218737217994619744345 12504164052913495964808259)
                  ·
                    refine ⟨18756246079370243947212389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12504164052913495964808259 18756246079370243947212389)
                    ·
                      refine ⟨3516796139881920740102323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18756246079370243947212389 3516796139881920740102323)
                      ·
                        rfl

theorem cell23_6848936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6848936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848936 prefixEnd_6848936 := by exact prefixLift 6848936
  have htrace : WordTrace (prefixWord ++ tailWord_6848936) baseStart_6848936 baseEnd_6848936 := by
    simpa [prefixWord, tailWord_6848936, baseEnd_6848936] using wordTrace_append hprefix tailTrace_6848936
  have hstable : (prefixWord ++ tailWord_6848936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848936).length < 2 ^ (prefixWord ++ tailWord_6848936).sum := by decide
  have hdescent : baseEnd_6848936 < baseStart_6848936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848952 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_6848952 : Nat := 118140960795 + 6848952 * 2 ^ 59
def prefixEnd_6848952 : Nat := 4983230072969 + 3 ^ 40 * 6848952 * 2
def baseEnd_6848952 : Nat := 3516804355572392677502249

theorem tailTrace_6848952 : CollatzResearch.WordTrace tailWord_6848952 prefixEnd_6848952 3516804355572392677502249 := by
  unfold tailWord_6848952
  simp only [CollatzResearch.WordTrace]
  refine ⟨124900900741712043360754555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166534534322282724481006073 124900900741712043360754555)
  ·
    refine ⟨187351351112568065041131833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124900900741712043360754555 187351351112568065041131833)
    ·
      refine ⟨140513513334426048780848875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187351351112568065041131833 140513513334426048780848875)
      ·
        refine ⟨210770270001639073171273313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140513513334426048780848875 210770270001639073171273313)
        ·
          refine ⟨158077702501229304878454985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210770270001639073171273313 158077702501229304878454985)
          ·
            refine ⟨118558276875921978658841239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158077702501229304878454985 118558276875921978658841239)
            ·
              refine ⟨177837415313882967988261859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118558276875921978658841239 177837415313882967988261859)
              ·
                refine ⟨266756122970824451982392789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177837415313882967988261859 266756122970824451982392789)
                ·
                  refine ⟨6252096632128698093337331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266756122970824451982392789 6252096632128698093337331)
                  ·
                    refine ⟨9378144948193047140005997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252096632128698093337331 9378144948193047140005997)
                    ·
                      refine ⟨3516804355572392677502249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378144948193047140005997 3516804355572392677502249)
                      ·
                        rfl

theorem cell23_6848952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_6848952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848952 prefixEnd_6848952 := by exact prefixLift 6848952
  have htrace : WordTrace (prefixWord ++ tailWord_6848952) baseStart_6848952 baseEnd_6848952 := by
    simpa [prefixWord, tailWord_6848952, baseEnd_6848952] using wordTrace_append hprefix tailTrace_6848952
  have hstable : (prefixWord ++ tailWord_6848952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848952).length < 2 ^ (prefixWord ++ tailWord_6848952).sum := by decide
  have hdescent : baseEnd_6848952 < baseStart_6848952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848989 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6848989 : Nat := 118140960795 + 6848989 * 2 ^ 59
def prefixEnd_6848989 : Nat := 4983230072969 + 3 ^ 40 * 6848989 * 2
def baseEnd_6848989 : Nat := 1172274451452203010913193

theorem tailTrace_6848989 : CollatzResearch.WordTrace tailWord_6848989 prefixEnd_6848989 1172274451452203010913193 := by
  unfold tailWord_6848989
  simp only [CollatzResearch.WordTrace]
  refine ⟨249803150984290042040606021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166535433989526694693737347 249803150984290042040606021)
  ·
    refine ⟨46838090809554382882613629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249803150984290042040606021 46838090809554382882613629)
    ·
      refine ⟨17564284053582893580980111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46838090809554382882613629 17564284053582893580980111)
      ·
        refine ⟨26346426080374340371470167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17564284053582893580980111 26346426080374340371470167)
        ·
          refine ⟨39519639120561510557205251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26346426080374340371470167 39519639120561510557205251)
          ·
            refine ⟨59279458680842265835807877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39519639120561510557205251 59279458680842265835807877)
            ·
              refine ⟨11114898502657924844213977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59279458680842265835807877 11114898502657924844213977)
              ·
                refine ⟨8336173876993443633160483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11114898502657924844213977 8336173876993443633160483)
                ·
                  refine ⟨12504260815490165449740725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336173876993443633160483 12504260815490165449740725)
                  ·
                    refine ⟨1172274451452203010913193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12504260815490165449740725 1172274451452203010913193)
                    ·
                      rfl

theorem cell23_6848989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6848989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848989 prefixEnd_6848989 := by exact prefixLift 6848989
  have htrace : WordTrace (prefixWord ++ tailWord_6848989) baseStart_6848989 baseEnd_6848989 := by
    simpa [prefixWord, tailWord_6848989, baseEnd_6848989] using wordTrace_append hprefix tailTrace_6848989
  have hstable : (prefixWord ++ tailWord_6848989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848989).length < 2 ^ (prefixWord ++ tailWord_6848989).sum := by decide
  have hdescent : baseEnd_6848989 < baseStart_6848989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848992 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2]
def baseStart_6848992 : Nat := 118140960795 + 6848992 * 2 ^ 59
def prefixEnd_6848992 : Nat := 4983230072969 + 3 ^ 40 * 6848992 * 2
def baseEnd_6848992 : Nat := 3516824894798572521002065

theorem tailTrace_6848992 : CollatzResearch.WordTrace tailWord_6848992 prefixEnd_6848992 3516824894798572521002065 := by
  unfold tailWord_6848992
  simp only [CollatzResearch.WordTrace]
  refine ⟨124901630201639586776482615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166535506935519449035310153 124901630201639586776482615)
  ·
    refine ⟨187352445302459380164723923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124901630201639586776482615 187352445302459380164723923)
    ·
      refine ⟨281028667953689070247085885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187352445302459380164723923 281028667953689070247085885)
      ·
        refine ⟨105385750482633401342657207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281028667953689070247085885 105385750482633401342657207)
        ·
          refine ⟨158078625723950102013985811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105385750482633401342657207 158078625723950102013985811)
          ·
            refine ⟨237117938585925153020978717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158078625723950102013985811 237117938585925153020978717)
            ·
              refine ⟨88919226969721932382867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237117938585925153020978717 88919226969721932382867019)
              ·
                refine ⟨133378840454582898574300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88919226969721932382867019 133378840454582898574300529)
                ·
                  refine ⟨100034130340937173930725397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133378840454582898574300529 100034130340937173930725397)
                  ·
                    refine ⟨4689099859731430028002753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100034130340937173930725397 4689099859731430028002753)
                    ·
                      refine ⟨3516824894798572521002065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689099859731430028002753 3516824894798572521002065)
                      ·
                        rfl

theorem cell23_6848992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_6848992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6848992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6848992 prefixEnd_6848992 := by exact prefixLift 6848992
  have htrace : WordTrace (prefixWord ++ tailWord_6848992) baseStart_6848992 baseEnd_6848992 := by
    simpa [prefixWord, tailWord_6848992, baseEnd_6848992] using wordTrace_append hprefix tailTrace_6848992
  have hstable : (prefixWord ++ tailWord_6848992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848992).length < 2 ^ (prefixWord ++ tailWord_6848992).sum := by decide
  have hdescent : baseEnd_6848992 < baseStart_6848992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849013 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6849013 : Nat := 118140960795 + 6849013 * 2 ^ 59
def prefixEnd_6849013 : Nat := 4983230072969 + 3 ^ 40 * 6849013 * 2
def baseEnd_6849013 : Nat := 3516835677892316938839469

theorem tailTrace_6849013 : CollatzResearch.WordTrace tailWord_6849013 prefixEnd_6849013 3516835677892316938839469 := by
  unfold tailWord_6849013
  simp only [CollatzResearch.WordTrace]
  refine ⟨249804026336203094139479693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166536017557468729426319795 249804026336203094139479693)
  ·
    refine ⟨93676509876076160302304885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249804026336203094139479693 93676509876076160302304885)
    ·
      refine ⟨8782172800882140028341083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93676509876076160302304885 8782172800882140028341083)
      ·
        refine ⟨13173259201323210042511625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782172800882140028341083 13173259201323210042511625)
        ·
          refine ⟨9879944400992407531883719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13173259201323210042511625 9879944400992407531883719)
          ·
            refine ⟨14819916601488611297825579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879944400992407531883719 14819916601488611297825579)
            ·
              refine ⟨22229874902232916946738369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14819916601488611297825579 22229874902232916946738369)
              ·
                refine ⟨16672406176674687710053777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22229874902232916946738369 16672406176674687710053777)
                ·
                  refine ⟨12504304632506015782540333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16672406176674687710053777 12504304632506015782540333)
                  ·
                    refine ⟨4689114237189755918452625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12504304632506015782540333 4689114237189755918452625)
                    ·
                      refine ⟨3516835677892316938839469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689114237189755918452625 3516835677892316938839469)
                      ·
                        rfl

theorem cell23_6849013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6849013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849013 prefixEnd_6849013 := by exact prefixLift 6849013
  have htrace : WordTrace (prefixWord ++ tailWord_6849013) baseStart_6849013 baseEnd_6849013 := by
    simpa [prefixWord, tailWord_6849013, baseEnd_6849013] using wordTrace_append hprefix tailTrace_6849013
  have hstable : (prefixWord ++ tailWord_6849013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849013).length < 2 ^ (prefixWord ++ tailWord_6849013).sum := by decide
  have hdescent : baseEnd_6849013 < baseStart_6849013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849036 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_6849036 : Nat := 118140960795 + 6849036 * 2 ^ 59
def prefixEnd_6849036 : Nat := 4983230072969 + 3 ^ 40 * 6849036 * 2
def baseEnd_6849036 : Nat := 1172282495982456782950621

theorem tailTrace_6849036 : CollatzResearch.WordTrace tailWord_6849036 prefixEnd_6849036 1172282495982456782950621 := by
  unfold tailWord_6849036
  simp only [CollatzResearch.WordTrace]
  refine ⟨124902432607559884533783481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166536576810079846045044641 124902432607559884533783481)
  ·
    refine ⟨93676824455669913400337611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124902432607559884533783481 93676824455669913400337611)
    ·
      refine ⟨140515236683504870100506417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93676824455669913400337611 140515236683504870100506417)
      ·
        refine ⟨105386427512628652575379813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140515236683504870100506417 105386427512628652575379813)
        ·
          refine ⟨19759955158617872357883715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105386427512628652575379813 19759955158617872357883715)
          ·
            refine ⟨29639932737926808536825573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19759955158617872357883715 29639932737926808536825573)
            ·
              refine ⟨5557487388361276600654795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29639932737926808536825573 5557487388361276600654795)
              ·
                refine ⟨8336231082541914900982193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557487388361276600654795 8336231082541914900982193)
                ·
                  refine ⟨6252173311906436175736645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336231082541914900982193 6252173311906436175736645)
                  ·
                    refine ⟨1172282495982456782950621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252173311906436175736645 1172282495982456782950621)
                    ·
                      rfl

theorem cell23_6849036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_6849036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849036 prefixEnd_6849036 := by exact prefixLift 6849036
  have htrace : WordTrace (prefixWord ++ tailWord_6849036) baseStart_6849036 baseEnd_6849036 := by
    simpa [prefixWord, tailWord_6849036, baseEnd_6849036] using wordTrace_append hprefix tailTrace_6849036
  have hstable : (prefixWord ++ tailWord_6849036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849036).length < 2 ^ (prefixWord ++ tailWord_6849036).sum := by decide
  have hdescent : baseEnd_6849036 < baseStart_6849036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849059 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3]
def baseStart_6849059 : Nat := 118140960795 + 6849059 * 2 ^ 59
def prefixEnd_6849059 : Nat := 4983230072969 + 3 ^ 40 * 6849059 * 2
def baseEnd_6849059 : Nat := 3516859298002423758864257

theorem tailTrace_6849059 : CollatzResearch.WordTrace tailWord_6849059 prefixEnd_6849059 3516859298002423758864257 := by
  unfold tailWord_6849059
  simp only [CollatzResearch.WordTrace]
  refine ⟨249805704094036443995654231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166537136062690962663769487 249805704094036443995654231)
  ·
    refine ⟨374708556141054665993481347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249805704094036443995654231 374708556141054665993481347)
    ·
      refine ⟨562062834211581998990222021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374708556141054665993481347 562062834211581998990222021)
      ·
        refine ⟨105386781414671624810666629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 562062834211581998990222021 105386781414671624810666629)
        ·
          refine ⟨19760021515250929651999993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105386781414671624810666629 19760021515250929651999993)
          ·
            refine ⟨14820016136438197238999995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19760021515250929651999993 14820016136438197238999995)
            ·
              refine ⟨22230024204657295858499993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14820016136438197238999995 22230024204657295858499993)
              ·
                refine ⟨16672518153492971893874995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22230024204657295858499993 16672518153492971893874995)
                ·
                  refine ⟨25008777230239457840812493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16672518153492971893874995 25008777230239457840812493)
                  ·
                    refine ⟨9378291461339796690304685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25008777230239457840812493 9378291461339796690304685)
                    ·
                      refine ⟨3516859298002423758864257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378291461339796690304685 3516859298002423758864257)
                      ·
                        rfl

theorem cell23_6849059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_6849059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849059 prefixEnd_6849059 := by exact prefixLift 6849059
  have htrace : WordTrace (prefixWord ++ tailWord_6849059) baseStart_6849059 baseEnd_6849059 := by
    simpa [prefixWord, tailWord_6849059, baseEnd_6849059] using wordTrace_append hprefix tailTrace_6849059
  have hstable : (prefixWord ++ tailWord_6849059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849059).length < 2 ^ (prefixWord ++ tailWord_6849059).sum := by decide
  have hdescent : baseEnd_6849059 < baseStart_6849059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849063 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6849063 : Nat := 118140960795 + 6849063 * 2 ^ 59
def prefixEnd_6849063 : Nat := 4983230072969 + 3 ^ 40 * 6849063 * 2
def baseEnd_6849063 : Nat := 3516861351925041743214239

theorem tailTrace_6849063 : CollatzResearch.WordTrace tailWord_6849063 prefixEnd_6849063 3516861351925041743214239 := by
  unfold tailWord_6849063
  simp only [CollatzResearch.WordTrace]
  refine ⟨249805849986021952678799843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166537233324014635119199895 249805849986021952678799843)
  ·
    refine ⟨374708774979032929018199765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249805849986021952678799843 374708774979032929018199765)
    ·
      refine ⟨8782236913571084273864057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 374708774979032929018199765 8782236913571084273864057)
      ·
        refine ⟨6586677685178313205398043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8782236913571084273864057 6586677685178313205398043)
        ·
          refine ⟨9880016527767469808097065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586677685178313205398043 9880016527767469808097065)
          ·
            refine ⟨7410012395825602356072799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9880016527767469808097065 7410012395825602356072799)
            ·
              refine ⟨11115018593738403534109199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410012395825602356072799 11115018593738403534109199)
              ·
                refine ⟨16672527890607605301163799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11115018593738403534109199 16672527890607605301163799)
                ·
                  refine ⟨25008791835911407951745699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16672527890607605301163799 25008791835911407951745699)
                  ·
                    refine ⟨37513187753867111927618549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25008791835911407951745699 37513187753867111927618549)
                    ·
                      refine ⟨3516861351925041743214239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37513187753867111927618549 3516861351925041743214239)
                      ·
                        rfl

theorem cell23_6849063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6849063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849063 prefixEnd_6849063 := by exact prefixLift 6849063
  have htrace : WordTrace (prefixWord ++ tailWord_6849063) baseStart_6849063 baseEnd_6849063 := by
    simpa [prefixWord, tailWord_6849063, baseEnd_6849063] using wordTrace_append hprefix tailTrace_6849063
  have hstable : (prefixWord ++ tailWord_6849063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849063).length < 2 ^ (prefixWord ++ tailWord_6849063).sum := by decide
  have hdescent : baseEnd_6849063 < baseStart_6849063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849082 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_6849082 : Nat := 118140960795 + 6849082 * 2 ^ 59
def prefixEnd_6849082 : Nat := 4983230072969 + 3 ^ 40 * 6849082 * 2
def baseEnd_6849082 : Nat := 3516871108057477168876651

theorem tailTrace_6849082 : CollatzResearch.WordTrace tailWord_6849082 prefixEnd_6849082 3516871108057477168876651 := by
  unfold tailWord_6849082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451635743238279730935375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166537695315302079282494333 62451635743238279730935375)
  ·
    refine ⟨93677453614857419596403063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451635743238279730935375 93677453614857419596403063)
    ·
      refine ⟨140516180422286129394604595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93677453614857419596403063 140516180422286129394604595)
      ·
        refine ⟨210774270633429194091906893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140516180422286129394604595 210774270633429194091906893)
        ·
          refine ⟨79040351487535947784465085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210774270633429194091906893 79040351487535947784465085)
          ·
            refine ⟨29640131807825980419174407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79040351487535947784465085 29640131807825980419174407)
            ·
              refine ⟨44460197711738970628761611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29640131807825980419174407 44460197711738970628761611)
              ·
                refine ⟨66690296567608455943142417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44460197711738970628761611 66690296567608455943142417)
                ·
                  refine ⟨50017722425706341957356813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66690296567608455943142417 50017722425706341957356813)
                  ·
                    refine ⟨18756645909639878234008805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50017722425706341957356813 18756645909639878234008805)
                    ·
                      refine ⟨3516871108057477168876651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18756645909639878234008805 3516871108057477168876651)
                      ·
                        rfl

theorem cell23_6849082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_6849082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849082 prefixEnd_6849082 := by exact prefixLift 6849082
  have htrace : WordTrace (prefixWord ++ tailWord_6849082) baseStart_6849082 baseEnd_6849082 := by
    simpa [prefixWord, tailWord_6849082, baseEnd_6849082] using wordTrace_append hprefix tailTrace_6849082
  have hstable : (prefixWord ++ tailWord_6849082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849082).length < 2 ^ (prefixWord ++ tailWord_6849082).sum := by decide
  have hdescent : baseEnd_6849082 < baseStart_6849082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849099 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 4, 2]
def baseStart_6849099 : Nat := 118140960795 + 6849099 * 2 ^ 59
def prefixEnd_6849099 : Nat := 4983230072969 + 3 ^ 40 * 6849099 * 2
def baseEnd_6849099 : Nat := 3516879837228603602364073

theorem tailTrace_6849099 : CollatzResearch.WordTrace tailWord_6849099 prefixEnd_6849099 3516879837228603602364073 := by
  unfold tailWord_6849099
  simp only [CollatzResearch.WordTrace]
  refine ⟨249807163013891530827110351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166538108675927687218073567 249807163013891530827110351)
  ·
    refine ⟨374710744520837296240665527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249807163013891530827110351 374710744520837296240665527)
    ·
      refine ⟨562066116781255944360998291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374710744520837296240665527 562066116781255944360998291)
      ·
        refine ⟨843099175171883916541497437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562066116781255944360998291 843099175171883916541497437)
        ·
          refine ⟨316162190689456468703061539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 843099175171883916541497437 316162190689456468703061539)
          ·
            refine ⟨474243286034184703054592309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316162190689456468703061539 474243286034184703054592309)
            ·
              refine ⟨44460308065704815911368029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 474243286034184703054592309 44460308065704815911368029)
              ·
                refine ⟨16672615524639305966763011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44460308065704815911368029 16672615524639305966763011)
                ·
                  refine ⟨25008923286958958950144517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16672615524639305966763011 25008923286958958950144517)
                  ·
                    refine ⟨4689173116304804803152097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25008923286958958950144517 4689173116304804803152097)
                    ·
                      refine ⟨3516879837228603602364073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689173116304804803152097 3516879837228603602364073)
                      ·
                        rfl

theorem cell23_6849099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4, 2].length) (baseStart_6849099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849099 prefixEnd_6849099 := by exact prefixLift 6849099
  have htrace : WordTrace (prefixWord ++ tailWord_6849099) baseStart_6849099 baseEnd_6849099 := by
    simpa [prefixWord, tailWord_6849099, baseEnd_6849099] using wordTrace_append hprefix tailTrace_6849099
  have hstable : (prefixWord ++ tailWord_6849099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849099).length < 2 ^ (prefixWord ++ tailWord_6849099).sum := by decide
  have hdescent : baseEnd_6849099 < baseStart_6849099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849102 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6849102 : Nat := 118140960795 + 6849102 * 2 ^ 59
def prefixEnd_6849102 : Nat := 4983230072969 + 3 ^ 40 * 6849102 * 2
def baseEnd_6849102 : Nat := 3516881377670567090626559

theorem tailTrace_6849102 : CollatzResearch.WordTrace tailWord_6849102 prefixEnd_6849102 3516881377670567090626559 := by
  unfold tailWord_6849102
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225909054110082792433695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166538181621920441559646373 31225909054110082792433695)
  ·
    refine ⟨46838863581165124188650543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31225909054110082792433695 46838863581165124188650543)
    ·
      refine ⟨70258295371747686282975815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46838863581165124188650543 70258295371747686282975815)
      ·
        refine ⟨105387443057621529424463723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70258295371747686282975815 105387443057621529424463723)
        ·
          refine ⟨158081164586432294136695585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105387443057621529424463723 158081164586432294136695585)
          ·
            refine ⟨118560873439824220602521689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158081164586432294136695585 118560873439824220602521689)
            ·
              refine ⟨88920655079868165451891267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118560873439824220602521689 88920655079868165451891267)
              ·
                refine ⟨133380982619802248177836901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88920655079868165451891267 133380982619802248177836901)
                ·
                  refine ⟨25008934241212921533344419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133380982619802248177836901 25008934241212921533344419)
                  ·
                    refine ⟨37513401361819382300016629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25008934241212921533344419 37513401361819382300016629)
                    ·
                      refine ⟨3516881377670567090626559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37513401361819382300016629 3516881377670567090626559)
                      ·
                        rfl

theorem cell23_6849102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6849102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849102 prefixEnd_6849102 := by exact prefixLift 6849102
  have htrace : WordTrace (prefixWord ++ tailWord_6849102) baseStart_6849102 baseEnd_6849102 := by
    simpa [prefixWord, tailWord_6849102, baseEnd_6849102] using wordTrace_append hprefix tailTrace_6849102
  have hstable : (prefixWord ++ tailWord_6849102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849102).length < 2 ^ (prefixWord ++ tailWord_6849102).sum := by decide
  have hdescent : baseEnd_6849102 < baseStart_6849102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849133 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_6849133 : Nat := 118140960795 + 6849133 * 2 ^ 59
def prefixEnd_6849133 : Nat := 4983230072969 + 3 ^ 40 * 6849133 * 2
def baseEnd_6849133 : Nat := 3516897295570856469338917

theorem tailTrace_6849133 : CollatzResearch.WordTrace tailWord_6849133 prefixEnd_6849133 3516897295570856469338917 := by
  unfold tailWord_6849133
  simp only [CollatzResearch.WordTrace]
  refine ⟨249808403095768354633848053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166538935397178903089232035 249808403095768354633848053)
  ·
    refine ⟨23419537790228283246923255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249808403095768354633848053 23419537790228283246923255)
    ·
      refine ⟨35129306685342424870384883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23419537790228283246923255 35129306685342424870384883)
      ·
        refine ⟨52693960028013637305577325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35129306685342424870384883 52693960028013637305577325)
        ·
          refine ⟨19760235010505113989591497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52693960028013637305577325 19760235010505113989591497)
          ·
            refine ⟨14820176257878835492193623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19760235010505113989591497 14820176257878835492193623)
            ·
              refine ⟨22230264386818253238290435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14820176257878835492193623 22230264386818253238290435)
              ·
                refine ⟨33345396580227379857435653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22230264386818253238290435 33345396580227379857435653)
                ·
                  refine ⟨6252261858792633723269185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33345396580227379857435653 6252261858792633723269185)
                  ·
                    refine ⟨4689196394094475292451889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252261858792633723269185 4689196394094475292451889)
                    ·
                      refine ⟨3516897295570856469338917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689196394094475292451889 3516897295570856469338917)
                      ·
                        rfl

theorem cell23_6849133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_6849133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849133 prefixEnd_6849133 := by exact prefixLift 6849133
  have htrace : WordTrace (prefixWord ++ tailWord_6849133) baseStart_6849133 baseEnd_6849133 := by
    simpa [prefixWord, tailWord_6849133, baseEnd_6849133] using wordTrace_append hprefix tailTrace_6849133
  have hstable : (prefixWord ++ tailWord_6849133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849133).length < 2 ^ (prefixWord ++ tailWord_6849133).sum := by decide
  have hdescent : baseEnd_6849133 < baseStart_6849133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849152 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_6849152 : Nat := 118140960795 + 6849152 * 2 ^ 59
def prefixEnd_6849152 : Nat := 4983230072969 + 3 ^ 40 * 6849152 * 2
def baseEnd_6849152 : Nat := 1172302350567763965000443

theorem tailTrace_6849152 : CollatzResearch.WordTrace tailWord_6849152 prefixEnd_6849152 1172302350567763965000443 := by
  unfold tailWord_6849152
  simp only [CollatzResearch.WordTrace]
  refine ⟨124904548041349760439394855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166539397388466347252526473 124904548041349760439394855)
  ·
    refine ⟨187356822062024640659092283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124904548041349760439394855 187356822062024640659092283)
    ·
      refine ⟨281035233093036960988638425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187356822062024640659092283 281035233093036960988638425)
      ·
        refine ⟨210776424819777720741478819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281035233093036960988638425 210776424819777720741478819)
        ·
          refine ⟨316164637229666581112218229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210776424819777720741478819 316164637229666581112218229)
          ·
            refine ⟨29640434740281241979270459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316164637229666581112218229 29640434740281241979270459)
            ·
              refine ⟨44460652110421862968905689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29640434740281241979270459 44460652110421862968905689)
              ·
                refine ⟨33345489082816397226679267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44460652110421862968905689 33345489082816397226679267)
                ·
                  refine ⟨50018233624224595840018901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33345489082816397226679267 50018233624224595840018901)
                  ·
                    refine ⟨1172302350567763965000443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50018233624224595840018901 1172302350567763965000443)
                    ·
                      rfl

theorem cell23_6849152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_6849152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849152 prefixEnd_6849152 := by exact prefixLift 6849152
  have htrace : WordTrace (prefixWord ++ tailWord_6849152) baseStart_6849152 baseEnd_6849152 := by
    simpa [prefixWord, tailWord_6849152, baseEnd_6849152] using wordTrace_append hprefix tailTrace_6849152
  have hstable : (prefixWord ++ tailWord_6849152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849152).length < 2 ^ (prefixWord ++ tailWord_6849152).sum := by decide
  have hdescent : baseEnd_6849152 < baseStart_6849152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849154 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6849154 : Nat := 118140960795 + 6849154 * 2 ^ 59
def prefixEnd_6849154 : Nat := 4983230072969 + 3 ^ 40 * 6849154 * 2
def baseEnd_6849154 : Nat := 3516908078664600887176321

theorem tailTrace_6849154 : CollatzResearch.WordTrace tailWord_6849154 prefixEnd_6849154 3516908078664600887176321 := by
  unfold tailWord_6849154
  simp only [CollatzResearch.WordTrace]
  refine ⟨62452292257173068805090629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166539446019128183480241677 62452292257173068805090629)
  ·
    refine ⟨11709804798219950400954493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62452292257173068805090629 11709804798219950400954493)
    ·
      refine ⟨4391176799332481400357935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11709804798219950400954493 4391176799332481400357935)
      ·
        refine ⟨6586765198998722100536903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391176799332481400357935 6586765198998722100536903)
        ·
          refine ⟨9880147798498083150805355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586765198998722100536903 9880147798498083150805355)
          ·
            refine ⟨14820221697747124726208033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880147798498083150805355 14820221697747124726208033)
            ·
              refine ⟨11115166273310343544656025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14820221697747124726208033 11115166273310343544656025)
              ·
                refine ⟨8336374704982757658492019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115166273310343544656025 8336374704982757658492019)
                ·
                  refine ⟨12504562057474136487738029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336374704982757658492019 12504562057474136487738029)
                  ·
                    refine ⟨4689210771552801182901761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12504562057474136487738029 4689210771552801182901761)
                    ·
                      refine ⟨3516908078664600887176321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689210771552801182901761 3516908078664600887176321)
                      ·
                        rfl

theorem cell23_6849154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6849154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849154 prefixEnd_6849154 := by exact prefixLift 6849154
  have htrace : WordTrace (prefixWord ++ tailWord_6849154) baseStart_6849154 baseEnd_6849154 := by
    simpa [prefixWord, tailWord_6849154, baseEnd_6849154] using wordTrace_append hprefix tailTrace_6849154
  have hstable : (prefixWord ++ tailWord_6849154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849154).length < 2 ^ (prefixWord ++ tailWord_6849154).sum := by decide
  have hdescent : baseEnd_6849154 < baseStart_6849154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849209 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6849209 : Nat := 118140960795 + 6849209 * 2 ^ 59
def prefixEnd_6849209 : Nat := 4983230072969 + 3 ^ 40 * 6849209 * 2
def baseEnd_6849209 : Nat := 3516936320100598171988567

theorem tailTrace_6849209 : CollatzResearch.WordTrace tailWord_6849209 prefixEnd_6849209 3516936320100598171988567 := by
  unfold tailWord_6849209
  simp only [CollatzResearch.WordTrace]
  refine ⟨249811175043493019613614681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166540783362328679742409787 249811175043493019613614681)
  ·
    refine ⟨187358381282619764710211011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249811175043493019613614681 187358381282619764710211011)
    ·
      refine ⟨281037571923929647065316517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187358381282619764710211011 281037571923929647065316517)
      ·
        refine ⟨52694544735736808824746847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281037571923929647065316517 52694544735736808824746847)
        ·
          refine ⟨79041817103605213237120271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52694544735736808824746847 79041817103605213237120271)
          ·
            refine ⟨118562725655407819855680407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79041817103605213237120271 118562725655407819855680407)
            ·
              refine ⟨177844088483111729783520611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118562725655407819855680407 177844088483111729783520611)
              ·
                refine ⟨266766132724667594675280917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177844088483111729783520611 266766132724667594675280917)
                ·
                  refine ⟨12504662471468793500403793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266766132724667594675280917 12504662471468793500403793)
                  ·
                    refine ⟨9378496853601595125302845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12504662471468793500403793 9378496853601595125302845)
                    ·
                      refine ⟨3516936320100598171988567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378496853601595125302845 3516936320100598171988567)
                      ·
                        rfl

theorem cell23_6849209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6849209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849209 prefixEnd_6849209 := by exact prefixLift 6849209
  have htrace : WordTrace (prefixWord ++ tailWord_6849209) baseStart_6849209 baseEnd_6849209 := by
    simpa [prefixWord, tailWord_6849209, baseEnd_6849209] using wordTrace_append hprefix tailTrace_6849209
  have hstable : (prefixWord ++ tailWord_6849209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849209).length < 2 ^ (prefixWord ++ tailWord_6849209).sum := by decide
  have hdescent : baseEnd_6849209 < baseStart_6849209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849226 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_6849226 : Nat := 118140960795 + 6849226 * 2 ^ 59
def prefixEnd_6849226 : Nat := 4983230072969 + 3 ^ 40 * 6849226 * 2
def baseEnd_6849226 : Nat := 3516945049271724605475989

theorem tailTrace_6849226 : CollatzResearch.WordTrace tailWord_6849226 prefixEnd_6849226 3516945049271724605475989 := by
  unfold tailWord_6849226
  simp only [CollatzResearch.WordTrace]
  refine ⟨62452948771107857879245883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166541196722954287677989021 62452948771107857879245883)
  ·
    refine ⟨93679423156661786818868825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62452948771107857879245883 93679423156661786818868825)
    ·
      refine ⟨70259567367496340114151619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93679423156661786818868825 70259567367496340114151619)
      ·
        refine ⟨105389351051244510171227429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70259567367496340114151619 105389351051244510171227429)
        ·
          refine ⟨19760503322108345657105143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105389351051244510171227429 19760503322108345657105143)
          ·
            refine ⟨29640754983162518485657715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760503322108345657105143 29640754983162518485657715)
            ·
              refine ⟨44461132474743777728486573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29640754983162518485657715 44461132474743777728486573)
              ·
                refine ⟨16672924678028916648182465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44461132474743777728486573 16672924678028916648182465)
                ·
                  refine ⟨12504693508521687486136849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16672924678028916648182465 12504693508521687486136849)
                  ·
                    refine ⟨9378520131391265614602637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12504693508521687486136849 9378520131391265614602637)
                    ·
                      refine ⟨3516945049271724605475989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378520131391265614602637 3516945049271724605475989)
                      ·
                        rfl

theorem cell23_6849226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_6849226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849226 prefixEnd_6849226 := by exact prefixLift 6849226
  have htrace : WordTrace (prefixWord ++ tailWord_6849226) baseStart_6849226 baseEnd_6849226 := by
    simpa [prefixWord, tailWord_6849226, baseEnd_6849226] using wordTrace_append hprefix tailTrace_6849226
  have hstable : (prefixWord ++ tailWord_6849226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849226).length < 2 ^ (prefixWord ++ tailWord_6849226).sum := by decide
  have hdescent : baseEnd_6849226 < baseStart_6849226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849289 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_6849289 : Nat := 118140960795 + 6849289 * 2 ^ 59
def prefixEnd_6849289 : Nat := 4983230072969 + 3 ^ 40 * 6849289 * 2
def baseEnd_6849289 : Nat := 1172325799517652619662733

theorem tailTrace_6849289 : CollatzResearch.WordTrace tailWord_6849289 prefixEnd_6849289 1172325799517652619662733 := by
  unfold tailWord_6849289
  simp only [CollatzResearch.WordTrace]
  refine ⟨249814092883203193276526921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166542728588802128851017947 249814092883203193276526921)
  ·
    refine ⟨187360569662402394957395191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249814092883203193276526921 187360569662402394957395191)
    ·
      refine ⟨281040854493603592436092787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187360569662402394957395191 281040854493603592436092787)
      ·
        refine ⟨421561281740405388654139181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281040854493603592436092787 421561281740405388654139181)
        ·
          refine ⟨158085480652652020745302193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421561281740405388654139181 158085480652652020745302193)
          ·
            refine ⟨118564110489489015558976645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158085480652652020745302193 118564110489489015558976645)
            ·
              refine ⟨22230770716779190417308121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118564110489489015558976645 22230770716779190417308121)
              ·
                refine ⟨16673078037584392812981091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22230770716779190417308121 16673078037584392812981091)
                ·
                  refine ⟨25009617056376589219471637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16673078037584392812981091 25009617056376589219471637)
                  ·
                    refine ⟨1172325799517652619662733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25009617056376589219471637 1172325799517652619662733)
                    ·
                      rfl

theorem cell23_6849289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_6849289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849289 prefixEnd_6849289 := by exact prefixLift 6849289
  have htrace : WordTrace (prefixWord ++ tailWord_6849289) baseStart_6849289 baseEnd_6849289 := by
    simpa [prefixWord, tailWord_6849289, baseEnd_6849289] using wordTrace_append hprefix tailTrace_6849289
  have hstable : (prefixWord ++ tailWord_6849289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849289).length < 2 ^ (prefixWord ++ tailWord_6849289).sum := by decide
  have hdescent : baseEnd_6849289 < baseStart_6849289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849290 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_6849290 : Nat := 118140960795 + 6849290 * 2 ^ 59
def prefixEnd_6849290 : Nat := 4983230072969 + 3 ^ 40 * 6849290 * 2
def baseEnd_6849290 : Nat := 3516977912033612355075695

theorem tailTrace_6849290 : CollatzResearch.WordTrace tailWord_6849290 prefixEnd_6849290 3516977912033612355075695 := by
  unfold tailWord_6849290
  simp only [CollatzResearch.WordTrace]
  refine ⟨62453532339049892611828331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166542752904133046964875549 62453532339049892611828331)
  ·
    refine ⟨93680298508574838917742497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62453532339049892611828331 93680298508574838917742497)
    ·
      refine ⟨70260223881431129188306873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93680298508574838917742497 70260223881431129188306873)
      ·
        refine ⟨52695167911073346891230155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70260223881431129188306873 52695167911073346891230155)
        ·
          refine ⟨79042751866610020336845233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52695167911073346891230155 79042751866610020336845233)
          ·
            refine ⟨59282063899957515252633925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79042751866610020336845233 59282063899957515252633925)
            ·
              refine ⟨11115386981242034109868861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59282063899957515252633925 11115386981242034109868861)
              ·
                refine ⟨4168270117965762791200823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11115386981242034109868861 4168270117965762791200823)
                ·
                  refine ⟨6252405176948644186801235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168270117965762791200823 6252405176948644186801235)
                  ·
                    refine ⟨9378607765422966280201853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252405176948644186801235 9378607765422966280201853)
                    ·
                      refine ⟨3516977912033612355075695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378607765422966280201853 3516977912033612355075695)
                      ·
                        rfl

theorem cell23_6849290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_6849290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849290 prefixEnd_6849290 := by exact prefixLift 6849290
  have htrace : WordTrace (prefixWord ++ tailWord_6849290) baseStart_6849290 baseEnd_6849290 := by
    simpa [prefixWord, tailWord_6849290, baseEnd_6849290] using wordTrace_append hprefix tailTrace_6849290
  have hstable : (prefixWord ++ tailWord_6849290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849290).length < 2 ^ (prefixWord ++ tailWord_6849290).sum := by decide
  have hdescent : baseEnd_6849290 < baseStart_6849290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849299 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_6849299 : Nat := 118140960795 + 6849299 * 2 ^ 59
def prefixEnd_6849299 : Nat := 4983230072969 + 3 ^ 40 * 6849299 * 2
def baseEnd_6849299 : Nat := 3516982533359502819863153

theorem tailTrace_6849299 : CollatzResearch.WordTrace tailWord_6849299 prefixEnd_6849299 3516982533359502819863153 := by
  unfold tailWord_6849299
  simp only [CollatzResearch.WordTrace]
  refine ⟨249814457613166964984390951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166542971742111309989593967 249814457613166964984390951)
  ·
    refine ⟨374721686419750447476586427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249814457613166964984390951 374721686419750447476586427)
    ·
      refine ⟨562082529629625671214879641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374721686419750447476586427 562082529629625671214879641)
      ·
        refine ⟨421561897222219253411159731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562082529629625671214879641 421561897222219253411159731)
        ·
          refine ⟨632342845833328880116739597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421561897222219253411159731 632342845833328880116739597)
          ·
            refine ⟨237128567187498330043777349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632342845833328880116739597 237128567187498330043777349)
            ·
              refine ⟨44461606347655936883208253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237128567187498330043777349 44461606347655936883208253)
              ·
                refine ⟨16673102380370976331203095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44461606347655936883208253 16673102380370976331203095)
                ·
                  refine ⟨25009653570556464496804643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16673102380370976331203095 25009653570556464496804643)
                  ·
                    refine ⟨37514480355834696745206965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25009653570556464496804643 37514480355834696745206965)
                    ·
                      refine ⟨3516982533359502819863153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37514480355834696745206965 3516982533359502819863153)
                      ·
                        rfl

theorem cell23_6849299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_6849299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849299 prefixEnd_6849299 := by exact prefixLift 6849299
  have htrace : WordTrace (prefixWord ++ tailWord_6849299) baseStart_6849299 baseEnd_6849299 := by
    simpa [prefixWord, tailWord_6849299, baseEnd_6849299] using wordTrace_append hprefix tailTrace_6849299
  have hstable : (prefixWord ++ tailWord_6849299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849299).length < 2 ^ (prefixWord ++ tailWord_6849299).sum := by decide
  have hdescent : baseEnd_6849299 < baseStart_6849299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849306 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_6849306 : Nat := 118140960795 + 6849306 * 2 ^ 59
def prefixEnd_6849306 : Nat := 4983230072969 + 3 ^ 40 * 6849306 * 2
def baseEnd_6849306 : Nat := 1172328709241361430825207

theorem tailTrace_6849306 : CollatzResearch.WordTrace tailWord_6849306 prefixEnd_6849306 1172328709241361430825207 := by
  unfold tailWord_6849306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62453678231035401294973943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166543141949427736786597181 62453678231035401294973943)
  ·
    refine ⟨93680517346553101942460915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62453678231035401294973943 93680517346553101942460915)
    ·
      refine ⟨140520776019829652913691373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93680517346553101942460915 140520776019829652913691373)
      ·
        refine ⟨52695291007436119842634265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140520776019829652913691373 52695291007436119842634265)
        ·
          refine ⟨39521468255577089881975699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52695291007436119842634265 39521468255577089881975699)
          ·
            refine ⟨59282202383365634822963549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39521468255577089881975699 59282202383365634822963549)
            ·
              refine ⟨22230825893762113058611331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59282202383365634822963549 22230825893762113058611331)
              ·
                refine ⟨33346238840643169587916997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22230825893762113058611331 33346238840643169587916997)
                ·
                  refine ⟨6252419782620594297734437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33346238840643169587916997 6252419782620594297734437)
                  ·
                    refine ⟨1172328709241361430825207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252419782620594297734437 1172328709241361430825207)
                    ·
                      rfl

theorem cell23_6849306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_6849306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849306 prefixEnd_6849306 := by exact prefixLift 6849306
  have htrace : WordTrace (prefixWord ++ tailWord_6849306) baseStart_6849306 baseEnd_6849306 := by
    simpa [prefixWord, tailWord_6849306, baseEnd_6849306] using wordTrace_append hprefix tailTrace_6849306
  have hstable : (prefixWord ++ tailWord_6849306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849306).length < 2 ^ (prefixWord ++ tailWord_6849306).sum := by decide
  have hdescent : baseEnd_6849306 < baseStart_6849306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849333 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_6849333 : Nat := 118140960795 + 6849333 * 2 ^ 59
def prefixEnd_6849333 : Nat := 4983230072969 + 3 ^ 40 * 6849333 * 2
def baseEnd_6849333 : Nat := 3516999991701755686837997

theorem tailTrace_6849333 : CollatzResearch.WordTrace tailWord_6849333 prefixEnd_6849333 3516999991701755686837997 := by
  unfold tailWord_6849333
  simp only [CollatzResearch.WordTrace]
  refine ⟨249815697695043788791128653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166543798463362525860752435 249815697695043788791128653)
  ·
    refine ⟨93680886635641420796673245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249815697695043788791128653 93680886635641420796673245)
    ·
      refine ⟨35130332488365532798752467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93680886635641420796673245 35130332488365532798752467)
      ·
        refine ⟨52695498732548299198128701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35130332488365532798752467 52695498732548299198128701)
        ·
          refine ⟨19760812024705612199298263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52695498732548299198128701 19760812024705612199298263)
          ·
            refine ⟨29641218037058418298947395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760812024705612199298263 29641218037058418298947395)
            ·
              refine ⟨44461827055587627448421093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29641218037058418298947395 44461827055587627448421093)
              ·
                refine ⟨8336592572922680146578955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44461827055587627448421093 8336592572922680146578955)
                ·
                  refine ⟨12504888859384020219868433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336592572922680146578955 12504888859384020219868433)
                  ·
                    refine ⟨9378666644538015164901325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12504888859384020219868433 9378666644538015164901325)
                    ·
                      refine ⟨3516999991701755686837997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378666644538015164901325 3516999991701755686837997)
                      ·
                        rfl

theorem cell23_6849333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_6849333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849333 prefixEnd_6849333 := by exact prefixLift 6849333
  have htrace : WordTrace (prefixWord ++ tailWord_6849333) baseStart_6849333 baseEnd_6849333 := by
    simpa [prefixWord, tailWord_6849333, baseEnd_6849333] using wordTrace_append hprefix tailTrace_6849333
  have hstable : (prefixWord ++ tailWord_6849333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849333).length < 2 ^ (prefixWord ++ tailWord_6849333).sum := by decide
  have hdescent : baseEnd_6849333 < baseStart_6849333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849364 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_6849364 : Nat := 118140960795 + 6849364 * 2 ^ 59
def prefixEnd_6849364 : Nat := 4983230072969 + 3 ^ 40 * 6849364 * 2
def baseEnd_6849364 : Nat := 3517015909602045065550355

theorem tailTrace_6849364 : CollatzResearch.WordTrace tailWord_6849364 prefixEnd_6849364 3517015909602045065550355 := by
  unfold tailWord_6849364
  simp only [CollatzResearch.WordTrace]
  refine ⟨124908414178965740542753573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166544552238620987390338097 124908414178965740542753573)
  ·
    refine ⟨23420327658556076351766295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124908414178965740542753573 23420327658556076351766295)
    ·
      refine ⟨35130491487834114527649443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23420327658556076351766295 35130491487834114527649443)
      ·
        refine ⟨52695737231751171791474165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35130491487834114527649443 52695737231751171791474165)
        ·
          refine ⟨4940225365476672355450703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52695737231751171791474165 4940225365476672355450703)
          ·
            refine ⟨7410338048215008533176055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940225365476672355450703 7410338048215008533176055)
            ·
              refine ⟨11115507072322512799764083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410338048215008533176055 11115507072322512799764083)
              ·
                refine ⟨16673260608483769199646125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11115507072322512799764083 16673260608483769199646125)
                ·
                  refine ⟨6252472728181413449867297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16673260608483769199646125 6252472728181413449867297)
                  ·
                    refine ⟨4689354546136060087400473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252472728181413449867297 4689354546136060087400473)
                    ·
                      refine ⟨3517015909602045065550355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689354546136060087400473 3517015909602045065550355)
                      ·
                        rfl

theorem cell23_6849364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_6849364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849364 prefixEnd_6849364 := by exact prefixLift 6849364
  have htrace : WordTrace (prefixWord ++ tailWord_6849364) baseStart_6849364 baseEnd_6849364 := by
    simpa [prefixWord, tailWord_6849364, baseEnd_6849364] using wordTrace_append hprefix tailTrace_6849364
  have hstable : (prefixWord ++ tailWord_6849364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849364).length < 2 ^ (prefixWord ++ tailWord_6849364).sum := by decide
  have hdescent : baseEnd_6849364 < baseStart_6849364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849380 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_6849380 : Nat := 118140960795 + 6849380 * 2 ^ 59
def prefixEnd_6849380 : Nat := 4983230072969 + 3 ^ 40 * 6849380 * 2
def baseEnd_6849380 : Nat := 3517024125292517002950281

theorem tailTrace_6849380 : CollatzResearch.WordTrace tailWord_6849380 prefixEnd_6849380 3517024125292517002950281 := by
  unfold tailWord_6849380
  simp only [CollatzResearch.WordTrace]
  refine ⟨124908705962936757909044797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166544941283915677212059729 124908705962936757909044797)
  ·
    refine ⟨46840764736101284215891799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124908705962936757909044797 46840764736101284215891799)
    ·
      refine ⟨70261147104151926323837699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46840764736101284215891799 70261147104151926323837699)
      ·
        refine ⟨105391720656227889485756549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70261147104151926323837699 105391720656227889485756549)
        ·
          refine ⟨19760947623042729278579353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105391720656227889485756549 19760947623042729278579353)
          ·
            refine ⟨14820710717282046958934515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19760947623042729278579353 14820710717282046958934515)
            ·
              refine ⟨22231066075923070438401773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14820710717282046958934515 22231066075923070438401773)
              ·
                refine ⟨8336649778471151414400665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22231066075923070438401773 8336649778471151414400665)
                ·
                  refine ⟨6252487333853363560800499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336649778471151414400665 6252487333853363560800499)
                  ·
                    refine ⟨9378731000780045341200749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252487333853363560800499 9378731000780045341200749)
                    ·
                      refine ⟨3517024125292517002950281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9378731000780045341200749 3517024125292517002950281)
                      ·
                        rfl

theorem cell23_6849380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_6849380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849380 prefixEnd_6849380 := by exact prefixLift 6849380
  have htrace : WordTrace (prefixWord ++ tailWord_6849380) baseStart_6849380 baseEnd_6849380 := by
    simpa [prefixWord, tailWord_6849380, baseEnd_6849380] using wordTrace_append hprefix tailTrace_6849380
  have hstable : (prefixWord ++ tailWord_6849380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849380).length < 2 ^ (prefixWord ++ tailWord_6849380).sum := by decide
  have hdescent : baseEnd_6849380 < baseStart_6849380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849403 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 6, 2, 2]
def baseStart_6849403 : Nat := 118140960795 + 6849403 * 2 ^ 59
def prefixEnd_6849403 : Nat := 4983230072969 + 3 ^ 40 * 6849403 * 2
def baseEnd_6849403 : Nat := 3517035935347570412962675

theorem tailTrace_6849403 : CollatzResearch.WordTrace tailWord_6849403 prefixEnd_6849403 3517035935347570412962675 := by
  unfold tailWord_6849403
  simp only [CollatzResearch.WordTrace]
  refine ⟨249818250804790190746176863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166545500536526793830784575 249818250804790190746176863)
  ·
    refine ⟨374727376207185286119265295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249818250804790190746176863 374727376207185286119265295)
    ·
      refine ⟨562091064310777929178897943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374727376207185286119265295 562091064310777929178897943)
      ·
        refine ⟨843136596466166893768346915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562091064310777929178897943 843136596466166893768346915)
        ·
          refine ⟨1264704894699250340652520373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843136596466166893768346915 1264704894699250340652520373)
          ·
            refine ⟨118566083878054719436173785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1264704894699250340652520373 118566083878054719436173785)
            ·
              refine ⟨88924562908541039577130339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118566083878054719436173785 88924562908541039577130339)
              ·
                refine ⟨133386844362811559365695509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88924562908541039577130339 133386844362811559365695509)
                ·
                  refine ⟨6252508329506791845266977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133386844362811559365695509 6252508329506791845266977)
                  ·
                    refine ⟨4689381247130093883950233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252508329506791845266977 4689381247130093883950233)
                    ·
                      refine ⟨3517035935347570412962675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689381247130093883950233 3517035935347570412962675)
                      ·
                        rfl

theorem cell23_6849403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2, 2].length) (baseStart_6849403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849403 prefixEnd_6849403 := by exact prefixLift 6849403
  have htrace : WordTrace (prefixWord ++ tailWord_6849403) baseStart_6849403 baseEnd_6849403 := by
    simpa [prefixWord, tailWord_6849403, baseEnd_6849403] using wordTrace_append hprefix tailTrace_6849403
  have hstable : (prefixWord ++ tailWord_6849403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849403).length < 2 ^ (prefixWord ++ tailWord_6849403).sum := by decide
  have hdescent : baseEnd_6849403 < baseStart_6849403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849419 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_6849419 : Nat := 118140960795 + 6849419 * 2 ^ 59
def prefixEnd_6849419 : Nat := 4983230072969 + 3 ^ 40 * 6849419 * 2
def baseEnd_6849419 : Nat := 3517044151038042350362601

theorem tailTrace_6849419 : CollatzResearch.WordTrace tailWord_6849419 prefixEnd_6849419 3517044151038042350362601 := by
  unfold tailWord_6849419
  simp only [CollatzResearch.WordTrace]
  refine ⟨249818834372732225478759311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166545889581821483652506207 249818834372732225478759311)
  ·
    refine ⟨374728251559098338218138967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249818834372732225478759311 374728251559098338218138967)
    ·
      refine ⟨562092377338647507327208451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374728251559098338218138967 562092377338647507327208451)
      ·
        refine ⟨843138566007971260990812677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562092377338647507327208451 843138566007971260990812677)
        ·
          refine ⟨158088481126494611435777377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 843138566007971260990812677 158088481126494611435777377)
          ·
            refine ⟨118566360844870958576833033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158088481126494611435777377 118566360844870958576833033)
            ·
              refine ⟨88924770633653218932624775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118566360844870958576833033 88924770633653218932624775)
              ·
                refine ⟨133387155950479828398937163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88924770633653218932624775 133387155950479828398937163)
                ·
                  refine ⟨200080733925719742598405745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133387155950479828398937163 200080733925719742598405745)
                  ·
                    refine ⟨150060550444289806948804309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200080733925719742598405745 150060550444289806948804309)
                    ·
                      refine ⟨3517044151038042350362601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150060550444289806948804309 3517044151038042350362601)
                      ·
                        rfl

theorem cell23_6849419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_6849419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849419 prefixEnd_6849419 := by exact prefixLift 6849419
  have htrace : WordTrace (prefixWord ++ tailWord_6849419) baseStart_6849419 baseEnd_6849419 := by
    simpa [prefixWord, tailWord_6849419, baseEnd_6849419] using wordTrace_append hprefix tailTrace_6849419
  have hstable : (prefixWord ++ tailWord_6849419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849419).length < 2 ^ (prefixWord ++ tailWord_6849419).sum := by decide
  have hdescent : baseEnd_6849419 < baseStart_6849419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849420 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_6849420 : Nat := 118140960795 + 6849420 * 2 ^ 59
def prefixEnd_6849420 : Nat := 4983230072969 + 3 ^ 40 * 6849420 * 2
def baseEnd_6849420 : Nat := 3517044664518696846450097

theorem tailTrace_6849420 : CollatzResearch.WordTrace tailWord_6849420 prefixEnd_6849420 3517044664518696846450097 := by
  unfold tailWord_6849420
  simp only [CollatzResearch.WordTrace]
  refine ⟨124909435422864301324772857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166545913897152401766363809 124909435422864301324772857)
  ·
    refine ⟨93682076567148225993579643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124909435422864301324772857 93682076567148225993579643)
    ·
      refine ⟨140523114850722338990369465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93682076567148225993579643 140523114850722338990369465)
      ·
        refine ⟨105392336138041754242777099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140523114850722338990369465 105392336138041754242777099)
        ·
          refine ⟨158088504207062631364165649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105392336138041754242777099 158088504207062631364165649)
          ·
            refine ⟨118566378155296973523124237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158088504207062631364165649 118566378155296973523124237)
            ·
              refine ⟨44462391808236365071171589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118566378155296973523124237 44462391808236365071171589)
              ·
                refine ⟨8336698464044318450844673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44462391808236365071171589 8336698464044318450844673)
                ·
                  refine ⟨6252523848033238838133505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336698464044318450844673 6252523848033238838133505)
                  ·
                    refine ⟨4689392886024929128600129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252523848033238838133505 4689392886024929128600129)
                    ·
                      refine ⟨3517044664518696846450097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689392886024929128600129 3517044664518696846450097)
                      ·
                        rfl

theorem cell23_6849420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_6849420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849420 prefixEnd_6849420 := by exact prefixLift 6849420
  have htrace : WordTrace (prefixWord ++ tailWord_6849420) baseStart_6849420 baseEnd_6849420 := by
    simpa [prefixWord, tailWord_6849420, baseEnd_6849420] using wordTrace_append hprefix tailTrace_6849420
  have hstable : (prefixWord ++ tailWord_6849420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849420).length < 2 ^ (prefixWord ++ tailWord_6849420).sum := by decide
  have hdescent : baseEnd_6849420 < baseStart_6849420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849430 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6849430 : Nat := 118140960795 + 6849430 * 2 ^ 59
def prefixEnd_6849430 : Nat := 4983230072969 + 3 ^ 40 * 6849430 * 2
def baseEnd_6849430 : Nat := 1172349933108413935775017

theorem tailTrace_6849430 : CollatzResearch.WordTrace tailWord_6849430 prefixEnd_6849430 1172349933108413935775017 := by
  unfold tailWord_6849430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15613702223480773397338109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166546157050461582904939829 15613702223480773397338109)
  ·
    refine ⟨5855138333805290024001791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15613702223480773397338109 5855138333805290024001791)
    ·
      refine ⟨8782707500707935036002687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855138333805290024001791 8782707500707935036002687)
      ·
        refine ⟨13174061251061902554004031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782707500707935036002687 13174061251061902554004031)
        ·
          refine ⟨19761091876592853831006047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174061251061902554004031 19761091876592853831006047)
          ·
            refine ⟨29641637814889280746509071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19761091876592853831006047 29641637814889280746509071)
            ·
              refine ⟨44462456722333921119763607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29641637814889280746509071 44462456722333921119763607)
              ·
                refine ⟨66693685083500881679645411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44462456722333921119763607 66693685083500881679645411)
                ·
                  refine ⟨100040527625251322519468117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66693685083500881679645411 100040527625251322519468117)
                  ·
                    refine ⟨1172349933108413935775017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100040527625251322519468117 1172349933108413935775017)
                    ·
                      rfl

theorem cell23_6849430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6849430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849430 prefixEnd_6849430 := by exact prefixLift 6849430
  have htrace : WordTrace (prefixWord ++ tailWord_6849430) baseStart_6849430 baseEnd_6849430 := by
    simpa [prefixWord, tailWord_6849430, baseEnd_6849430] using wordTrace_append hprefix tailTrace_6849430
  have hstable : (prefixWord ++ tailWord_6849430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849430).length < 2 ^ (prefixWord ++ tailWord_6849430).sum := by decide
  have hdescent : baseEnd_6849430 < baseStart_6849430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849550 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_6849550 : Nat := 118140960795 + 6849550 * 2 ^ 59
def prefixEnd_6849550 : Nat := 4983230072969 + 3 ^ 40 * 6849550 * 2
def baseEnd_6849550 : Nat := 390790157444864593091611

theorem tailTrace_6849550 : CollatzResearch.WordTrace tailWord_6849550 prefixEnd_6849550 390790157444864593091611 := by
  unfold tailWord_6849550
  simp only [CollatzResearch.WordTrace]
  refine ⟨31227951541907204356472263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166549074890171756567852069 31227951541907204356472263)
  ·
    refine ⟨46841927312860806534708395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31227951541907204356472263 46841927312860806534708395)
    ·
      refine ⟨70262890969291209802062593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841927312860806534708395 70262890969291209802062593)
      ·
        refine ⟨52697168226968407351546945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70262890969291209802062593 52697168226968407351546945)
        ·
          refine ⟨39522876170226305513660209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52697168226968407351546945 39522876170226305513660209)
          ·
            refine ⟨29642157127669729135245157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39522876170226305513660209 29642157127669729135245157)
            ·
              refine ⟨5557904461438074212858467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29642157127669729135245157 5557904461438074212858467)
              ·
                refine ⟨8336856692157111319287701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557904461438074212858467 8336856692157111319287701)
                ·
                  refine ⟨390790157444864593091611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8336856692157111319287701 390790157444864593091611)
                  ·
                    rfl

theorem cell23_6849550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_6849550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849550 prefixEnd_6849550 := by exact prefixLift 6849550
  have htrace : WordTrace (prefixWord ++ tailWord_6849550) baseStart_6849550 baseEnd_6849550 := by
    simpa [prefixWord, tailWord_6849550, baseEnd_6849550] using wordTrace_append hprefix tailTrace_6849550
  have hstable : (prefixWord ++ tailWord_6849550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849550).length < 2 ^ (prefixWord ++ tailWord_6849550).sum := by decide
  have hdescent : baseEnd_6849550 < baseStart_6849550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849553 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_6849553 : Nat := 118140960795 + 6849553 * 2 ^ 59
def prefixEnd_6849553 : Nat := 4983230072969 + 3 ^ 40 * 6849553 * 2
def baseEnd_6849553 : Nat := 3517112957445744826086985

theorem tailTrace_6849553 : CollatzResearch.WordTrace tailWord_6849553 prefixEnd_6849553 3517112957445744826086985 := by
  unfold tailWord_6849553
  simp only [CollatzResearch.WordTrace]
  refine ⟨249823721754246766364137313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166549147836164510909424875 249823721754246766364137313)
  ·
    refine ⟨187367791315685074773102985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249823721754246766364137313 187367791315685074773102985)
    ·
      refine ⟨140525843486763806079827239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187367791315685074773102985 140525843486763806079827239)
      ·
        refine ⟨210788765230145709119740859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140525843486763806079827239 210788765230145709119740859)
        ·
          refine ⟨316183147845218563679611289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210788765230145709119740859 316183147845218563679611289)
          ·
            refine ⟨237137360883913922759708467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316183147845218563679611289 237137360883913922759708467)
            ·
              refine ⟨355706041325870884139562701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237137360883913922759708467 355706041325870884139562701)
              ·
                refine ⟨133389765497201581552336013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355706041325870884139562701 133389765497201581552336013)
                ·
                  refine ⟨50021162061450593082126005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133389765497201581552336013 50021162061450593082126005)
                  ·
                    refine ⟨4689483943260993101449313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50021162061450593082126005 4689483943260993101449313)
                    ·
                      refine ⟨3517112957445744826086985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689483943260993101449313 3517112957445744826086985)
                      ·
                        rfl

theorem cell23_6849553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_6849553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849553 prefixEnd_6849553 := by exact prefixLift 6849553
  have htrace : WordTrace (prefixWord ++ tailWord_6849553) baseStart_6849553 baseEnd_6849553 := by
    simpa [prefixWord, tailWord_6849553, baseEnd_6849553] using wordTrace_append hprefix tailTrace_6849553
  have hstable : (prefixWord ++ tailWord_6849553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849553).length < 2 ^ (prefixWord ++ tailWord_6849553).sum := by decide
  have hdescent : baseEnd_6849553 < baseStart_6849553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849580 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_6849580 : Nat := 118140960795 + 6849580 * 2 ^ 59
def prefixEnd_6849580 : Nat := 4983230072969 + 3 ^ 40 * 6849580 * 2
def baseEnd_6849580 : Nat := 1172375607141138740149787

theorem tailTrace_6849580 : CollatzResearch.WordTrace tailWord_6849580 prefixEnd_6849580 1172375607141138740149787 := by
  unfold tailWord_6849580
  simp only [CollatzResearch.WordTrace]
  refine ⟨124912353262574474987685097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166549804350099299983580129 124912353262574474987685097)
  ·
    refine ⟨93684264946930856240763823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124912353262574474987685097 93684264946930856240763823)
    ·
      refine ⟨140526397420396284361145735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93684264946930856240763823 140526397420396284361145735)
      ·
        refine ⟨210789596130594426541718603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140526397420396284361145735 210789596130594426541718603)
        ·
          refine ⟨316184394195891639812577905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210789596130594426541718603 316184394195891639812577905)
          ·
            refine ⟨237138295646918729859433429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316184394195891639812577905 237138295646918729859433429)
            ·
              refine ⟨5557928804224657731080471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237138295646918729859433429 5557928804224657731080471)
              ·
                refine ⟨8336893206336986596620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557928804224657731080471 8336893206336986596620707)
                ·
                  refine ⟨12505339809505479894931061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336893206336986596620707 12505339809505479894931061)
                  ·
                    refine ⟨1172375607141138740149787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12505339809505479894931061 1172375607141138740149787)
                    ·
                      rfl

theorem cell23_6849580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_6849580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849580 prefixEnd_6849580 := by exact prefixLift 6849580
  have htrace : WordTrace (prefixWord ++ tailWord_6849580) baseStart_6849580 baseEnd_6849580 := by
    simpa [prefixWord, tailWord_6849580, baseEnd_6849580] using wordTrace_append hprefix tailTrace_6849580
  have hstable : (prefixWord ++ tailWord_6849580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849580).length < 2 ^ (prefixWord ++ tailWord_6849580).sum := by decide
  have hdescent : baseEnd_6849580 < baseStart_6849580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849583 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 6, 2]
def baseStart_6849583 : Nat := 118140960795 + 6849583 * 2 ^ 59
def prefixEnd_6849583 : Nat := 4983230072969 + 3 ^ 40 * 6849583 * 2
def baseEnd_6849583 : Nat := 3517128361865379708711847

theorem tailTrace_6849583 : CollatzResearch.WordTrace tailWord_6849583 prefixEnd_6849583 3517128361865379708711847 := by
  unfold tailWord_6849583
  simp only [CollatzResearch.WordTrace]
  refine ⟨249824815944138081487729403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166549877296092054325152935 249824815944138081487729403)
  ·
    refine ⟨374737223916207122231594105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249824815944138081487729403 374737223916207122231594105)
    ·
      refine ⟨281052917937155341673695579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374737223916207122231594105 281052917937155341673695579)
      ·
        refine ⟨421579376905733012510543369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281052917937155341673695579 421579376905733012510543369)
        ·
          refine ⟨316184532679299759382907527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421579376905733012510543369 316184532679299759382907527)
          ·
            refine ⟨474276799018949639074361291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316184532679299759382907527 474276799018949639074361291)
            ·
              refine ⟨711415198528424458611541937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474276799018949639074361291 711415198528424458611541937)
              ·
                refine ⟨533561398896318343958656453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711415198528424458611541937 533561398896318343958656453)
                ·
                  refine ⟨100042762293059689492248085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533561398896318343958656453 100042762293059689492248085)
                  ·
                    refine ⟨4689504482487172944949129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100042762293059689492248085 4689504482487172944949129)
                    ·
                      refine ⟨3517128361865379708711847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689504482487172944949129 3517128361865379708711847)
                      ·
                        rfl

theorem cell23_6849583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6, 2].length) (baseStart_6849583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849583 prefixEnd_6849583 := by exact prefixLift 6849583
  have htrace : WordTrace (prefixWord ++ tailWord_6849583) baseStart_6849583 baseEnd_6849583 := by
    simpa [prefixWord, tailWord_6849583, baseEnd_6849583] using wordTrace_append hprefix tailTrace_6849583
  have hstable : (prefixWord ++ tailWord_6849583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849583).length < 2 ^ (prefixWord ++ tailWord_6849583).sum := by decide
  have hdescent : baseEnd_6849583 < baseStart_6849583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849594 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_6849594 : Nat := 118140960795 + 6849594 * 2 ^ 59
def prefixEnd_6849594 : Nat := 4983230072969 + 3 ^ 40 * 6849594 * 2
def baseEnd_6849594 : Nat := 3517134010152579165674297

theorem tailTrace_6849594 : CollatzResearch.WordTrace tailWord_6849594 prefixEnd_6849594 3517134010152579165674297 := by
  unfold tailWord_6849594
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456304286774557591594959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166550144764732153577586557 62456304286774557591594959)
  ·
    refine ⟨93684456430161836387392439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62456304286774557591594959 93684456430161836387392439)
    ·
      refine ⟨140526684645242754581088659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93684456430161836387392439 140526684645242754581088659)
      ·
        refine ⟨210790026967864131871632989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140526684645242754581088659 210790026967864131871632989)
        ·
          refine ⟨79046260112949049451862371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210790026967864131871632989 79046260112949049451862371)
          ·
            refine ⟨118569390169423574177793557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79046260112949049451862371 118569390169423574177793557)
            ·
              refine ⟨5557940164191730039584073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118569390169423574177793557 5557940164191730039584073)
              ·
                refine ⟨4168455123143797529688055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557940164191730039584073 4168455123143797529688055)
                ·
                  refine ⟨6252682684715696294532083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168455123143797529688055 6252682684715696294532083)
                  ·
                    refine ⟨9379024027073544441798125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252682684715696294532083 9379024027073544441798125)
                    ·
                      refine ⟨3517134010152579165674297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379024027073544441798125 3517134010152579165674297)
                      ·
                        rfl

theorem cell23_6849594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_6849594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849594 prefixEnd_6849594 := by exact prefixLift 6849594
  have htrace : WordTrace (prefixWord ++ tailWord_6849594) baseStart_6849594 baseEnd_6849594 := by
    simpa [prefixWord, tailWord_6849594, baseEnd_6849594] using wordTrace_append hprefix tailTrace_6849594
  have hstable : (prefixWord ++ tailWord_6849594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849594).length < 2 ^ (prefixWord ++ tailWord_6849594).sum := by decide
  have hdescent : baseEnd_6849594 < baseStart_6849594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849603 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3]
def baseStart_6849603 : Nat := 118140960795 + 6849603 * 2 ^ 59
def prefixEnd_6849603 : Nat := 4983230072969 + 3 ^ 40 * 6849603 * 2
def baseEnd_6849603 : Nat := 3517138631478469630461755

theorem tailTrace_6849603 : CollatzResearch.WordTrace tailWord_6849603 prefixEnd_6849603 3517138631478469630461755 := by
  unfold tailWord_6849603
  simp only [CollatzResearch.WordTrace]
  refine ⟨249825545404065624903457463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166550363602710416602304975 249825545404065624903457463)
  ·
    refine ⟨374738318106098437355186195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249825545404065624903457463 374738318106098437355186195)
    ·
      refine ⟨562107477159147656032779293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374738318106098437355186195 562107477159147656032779293)
      ·
        refine ⟨210790303934680371012292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562107477159147656032779293 210790303934680371012292235)
        ·
          refine ⟨316185455902020556518438353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210790303934680371012292235 316185455902020556518438353)
          ·
            refine ⟨237139091926515417388828765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316185455902020556518438353 237139091926515417388828765)
            ·
              refine ⟨88927159472443281520810787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237139091926515417388828765 88927159472443281520810787)
              ·
                refine ⟨133390739208664922281216181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88927159472443281520810787 133390739208664922281216181)
                ·
                  refine ⟨12505381800812336463864017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133390739208664922281216181 12505381800812336463864017)
                  ·
                    refine ⟨9379036350609252347898013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12505381800812336463864017 9379036350609252347898013)
                    ·
                      refine ⟨3517138631478469630461755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379036350609252347898013 3517138631478469630461755)
                      ·
                        rfl

theorem cell23_6849603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_6849603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849603 prefixEnd_6849603 := by exact prefixLift 6849603
  have htrace : WordTrace (prefixWord ++ tailWord_6849603) baseStart_6849603 baseEnd_6849603 := by
    simpa [prefixWord, tailWord_6849603, baseEnd_6849603] using wordTrace_append hprefix tailTrace_6849603
  have hstable : (prefixWord ++ tailWord_6849603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849603).length < 2 ^ (prefixWord ++ tailWord_6849603).sum := by decide
  have hdescent : baseEnd_6849603 < baseStart_6849603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849610 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_6849610 : Nat := 118140960795 + 6849610 * 2 ^ 59
def prefixEnd_6849610 : Nat := 4983230072969 + 3 ^ 40 * 6849610 * 2
def baseEnd_6849610 : Nat := 1172380741947683701024741

theorem tailTrace_6849610 : CollatzResearch.WordTrace tailWord_6849610 prefixEnd_6849610 1172380741947683701024741 := by
  unfold tailWord_6849610
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456450178760066274740571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166550533810026843399308189 62456450178760066274740571)
  ·
    refine ⟨93684675268140099412110857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62456450178760066274740571 93684675268140099412110857)
    ·
      refine ⟨70263506451105074559083143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93684675268140099412110857 70263506451105074559083143)
      ·
        refine ⟨105395259676657611838624715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70263506451105074559083143 105395259676657611838624715)
        ·
          refine ⟨158092889514986417757937073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105395259676657611838624715 158092889514986417757937073)
          ·
            refine ⟨118569667136239813318452805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158092889514986417757937073 118569667136239813318452805)
            ·
              refine ⟨22231812588044964997209901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118569667136239813318452805 22231812588044964997209901)
              ·
                refine ⟨8336929720516861873953713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22231812588044964997209901 8336929720516861873953713)
                ·
                  refine ⟨6252697290387646405465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336929720516861873953713 6252697290387646405465285)
                  ·
                    refine ⟨1172380741947683701024741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252697290387646405465285 1172380741947683701024741)
                    ·
                      rfl

theorem cell23_6849610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_6849610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849610 prefixEnd_6849610 := by exact prefixLift 6849610
  have htrace : WordTrace (prefixWord ++ tailWord_6849610) baseStart_6849610 baseEnd_6849610 := by
    simpa [prefixWord, tailWord_6849610, baseEnd_6849610] using wordTrace_append hprefix tailTrace_6849610
  have hstable : (prefixWord ++ tailWord_6849610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849610).length < 2 ^ (prefixWord ++ tailWord_6849610).sum := by decide
  have hdescent : baseEnd_6849610 < baseStart_6849610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_6849616 : Nat := 118140960795 + 6849616 * 2 ^ 59
def prefixEnd_6849616 : Nat := 4983230072969 + 3 ^ 40 * 6849616 * 2
def baseEnd_6849616 : Nat := 3517145306726978079599195

theorem tailTrace_6849616 : CollatzResearch.WordTrace tailWord_6849616 prefixEnd_6849616 3517145306726978079599195 := by
  unfold tailWord_6849616
  simp only [CollatzResearch.WordTrace]
  refine ⟨124913009776509264061840351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166550679702012352082453801 124913009776509264061840351)
  ·
    refine ⟨187369514664763896092760527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124913009776509264061840351 187369514664763896092760527)
    ·
      refine ⟨281054271997145844139140791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187369514664763896092760527 281054271997145844139140791)
      ·
        refine ⟨421581407995718766208711187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281054271997145844139140791 421581407995718766208711187)
        ·
          refine ⟨632372111993578149313066781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421581407995718766208711187 632372111993578149313066781)
          ·
            refine ⟨237139541997591805992400043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632372111993578149313066781 237139541997591805992400043)
            ·
              refine ⟨355709312996387708988600065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237139541997591805992400043 355709312996387708988600065)
              ·
                refine ⟨266781984747290781741450049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355709312996387708988600065 266781984747290781741450049)
                ·
                  refine ⟨200086488560468086306087537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266781984747290781741450049 200086488560468086306087537)
                  ·
                    refine ⟨150064866420351064729565653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200086488560468086306087537 150064866420351064729565653)
                    ·
                      refine ⟨3517145306726978079599195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150064866420351064729565653 3517145306726978079599195)
                      ·
                        rfl

theorem cell23_6849616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_6849616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849616 prefixEnd_6849616 := by exact prefixLift 6849616
  have htrace : WordTrace (prefixWord ++ tailWord_6849616) baseStart_6849616 baseEnd_6849616 := by
    simpa [prefixWord, tailWord_6849616, baseEnd_6849616] using wordTrace_append hprefix tailTrace_6849616
  have hstable : (prefixWord ++ tailWord_6849616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849616).length < 2 ^ (prefixWord ++ tailWord_6849616).sum := by decide
  have hdescent : baseEnd_6849616 < baseStart_6849616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849620 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_6849620 : Nat := 118140960795 + 6849620 * 2 ^ 59
def prefixEnd_6849620 : Nat := 4983230072969 + 3 ^ 40 * 6849620 * 2
def baseEnd_6849620 : Nat := 3517147360649596063949177

theorem tailTrace_6849620 : CollatzResearch.WordTrace tailWord_6849620 prefixEnd_6849620 3517147360649596063949177 := by
  unfold tailWord_6849620
  simp only [CollatzResearch.WordTrace]
  refine ⟨124913082722502018403413157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166550776963336024537884209 124913082722502018403413157)
  ·
    refine ⟨23421203010469128450639967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124913082722502018403413157 23421203010469128450639967)
    ·
      refine ⟨35131804515703692675959951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23421203010469128450639967 35131804515703692675959951)
      ·
        refine ⟨52697706773555539013939927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35131804515703692675959951 52697706773555539013939927)
        ·
          refine ⟨79046560160333308520909891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52697706773555539013939927 79046560160333308520909891)
          ·
            refine ⟨118569840240499962781364837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79046560160333308520909891 118569840240499962781364837)
            ·
              refine ⟨22231845045093743021505907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118569840240499962781364837 22231845045093743021505907)
              ·
                refine ⟨33347767567640614532258861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22231845045093743021505907 33347767567640614532258861)
                ·
                  refine ⟨12505412837865230449597073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33347767567640614532258861 12505412837865230449597073)
                  ·
                    refine ⟨9379059628398922837197805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12505412837865230449597073 9379059628398922837197805)
                    ·
                      refine ⟨3517147360649596063949177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379059628398922837197805 3517147360649596063949177)
                      ·
                        rfl

theorem cell23_6849620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_6849620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849620 prefixEnd_6849620 := by exact prefixLift 6849620
  have htrace : WordTrace (prefixWord ++ tailWord_6849620) baseStart_6849620 baseEnd_6849620 := by
    simpa [prefixWord, tailWord_6849620, baseEnd_6849620] using wordTrace_append hprefix tailTrace_6849620
  have hstable : (prefixWord ++ tailWord_6849620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849620).length < 2 ^ (prefixWord ++ tailWord_6849620).sum := by decide
  have hdescent : baseEnd_6849620 < baseStart_6849620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849634 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6849634 : Nat := 118140960795 + 6849634 * 2 ^ 59
def prefixEnd_6849634 : Nat := 4983230072969 + 3 ^ 40 * 6849634 * 2
def baseEnd_6849634 : Nat := 3517154549378759009174113

theorem tailTrace_6849634 : CollatzResearch.WordTrace tailWord_6849634 prefixEnd_6849634 3517154549378759009174113 := by
  unfold tailWord_6849634
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456669016738329299458989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166551117377968878131890637 62456669016738329299458989)
  ·
    refine ⟨23421250881276873487297121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62456669016738329299458989 23421250881276873487297121)
    ·
      refine ⟨17565938160957655115472841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23421250881276873487297121 17565938160957655115472841)
      ·
        refine ⟨13174453620718241336604631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17565938160957655115472841 13174453620718241336604631)
        ·
          refine ⟨19761680431077362004906947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174453620718241336604631 19761680431077362004906947)
          ·
            refine ⟨29642520646616043007360421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19761680431077362004906947 29642520646616043007360421)
            ·
              refine ⟨5557972621240508063880079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29642520646616043007360421 5557972621240508063880079)
              ·
                refine ⟨8336958931860762095820119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557972621240508063880079 8336958931860762095820119)
                ·
                  refine ⟨12505438397791143143730179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336958931860762095820119 12505438397791143143730179)
                  ·
                    refine ⟨18758157596686714715595269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12505438397791143143730179 18758157596686714715595269)
                    ·
                      refine ⟨3517154549378759009174113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18758157596686714715595269 3517154549378759009174113)
                      ·
                        rfl

theorem cell23_6849634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6849634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849634 prefixEnd_6849634 := by exact prefixLift 6849634
  have htrace : WordTrace (prefixWord ++ tailWord_6849634) baseStart_6849634 baseEnd_6849634 := by
    simpa [prefixWord, tailWord_6849634, baseEnd_6849634] using wordTrace_append hprefix tailTrace_6849634
  have hstable : (prefixWord ++ tailWord_6849634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849634).length < 2 ^ (prefixWord ++ tailWord_6849634).sum := by decide
  have hdescent : baseEnd_6849634 < baseStart_6849634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849640 : List Nat := [2, 1, 4, 4, 1, 1, 10]
def baseStart_6849640 : Nat := 118140960795 + 6849640 * 2 ^ 59
def prefixEnd_6849640 : Nat := 4983230072969 + 3 ^ 40 * 6849640 * 2
def baseEnd_6849640 : Nat := 43421699139045505996285

theorem tailTrace_6849640 : CollatzResearch.WordTrace tailWord_6849640 prefixEnd_6849640 43421699139045505996285 := by
  unfold tailWord_6849640
  simp only [CollatzResearch.WordTrace]
  refine ⟨124913447452465790111277187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166551263269954386815036249 124913447452465790111277187)
  ·
    refine ⟨187370171178698685166915781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124913447452465790111277187 187370171178698685166915781)
    ·
      refine ⟨35131907096006003468796709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187370171178698685166915781 35131907096006003468796709)
      ·
        refine ⟨6587232580501125650399383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35131907096006003468796709 6587232580501125650399383)
        ·
          refine ⟨9880848870751688475599075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587232580501125650399383 9880848870751688475599075)
          ·
            refine ⟨14821273306127532713398613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880848870751688475599075 14821273306127532713398613)
            ·
              refine ⟨43421699139045505996285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14821273306127532713398613 43421699139045505996285)
              ·
                rfl

theorem cell23_6849640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 10].length) (baseStart_6849640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849640 prefixEnd_6849640 := by exact prefixLift 6849640
  have htrace : WordTrace (prefixWord ++ tailWord_6849640) baseStart_6849640 baseEnd_6849640 := by
    simpa [prefixWord, tailWord_6849640, baseEnd_6849640] using wordTrace_append hprefix tailTrace_6849640
  have hstable : (prefixWord ++ tailWord_6849640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849640).length < 2 ^ (prefixWord ++ tailWord_6849640).sum := by decide
  have hdescent : baseEnd_6849640 < baseStart_6849640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849718 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6849718 : Nat := 118140960795 + 6849718 * 2 ^ 59
def prefixEnd_6849718 : Nat := 4983230072969 + 3 ^ 40 * 6849718 * 2
def baseEnd_6849718 : Nat := 3517197681753736680523727

theorem tailTrace_6849718 : CollatzResearch.WordTrace tailWord_6849718 prefixEnd_6849718 3517197681753736680523727 := by
  unfold tailWord_6849718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614358737415562471493363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166553159865765999695929205 15614358737415562471493363)
  ·
    refine ⟨23421538106123343707240045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15614358737415562471493363 23421538106123343707240045)
    ·
      refine ⟨8783076789796253890215017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23421538106123343707240045 8783076789796253890215017)
      ·
        refine ⟨6587307592347190417661263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8783076789796253890215017 6587307592347190417661263)
        ·
          refine ⟨9880961388520785626491895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587307592347190417661263 9880961388520785626491895)
          ·
            refine ⟨14821442082781178439737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880961388520785626491895 14821442082781178439737843)
            ·
              refine ⟨22232163124171767659606765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14821442082781178439737843 22232163124171767659606765)
              ·
                refine ⟨8337061171564412872352537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22232163124171767659606765 8337061171564412872352537)
                ·
                  refine ⟨6252795878673309654264403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337061171564412872352537 6252795878673309654264403)
                  ·
                    refine ⟨9379193818009964481396605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252795878673309654264403 9379193818009964481396605)
                    ·
                      refine ⟨3517197681753736680523727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379193818009964481396605 3517197681753736680523727)
                      ·
                        rfl

theorem cell23_6849718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6849718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849718 prefixEnd_6849718 := by exact prefixLift 6849718
  have htrace : WordTrace (prefixWord ++ tailWord_6849718) baseStart_6849718 baseEnd_6849718 := by
    simpa [prefixWord, tailWord_6849718, baseEnd_6849718] using wordTrace_append hprefix tailTrace_6849718
  have hstable : (prefixWord ++ tailWord_6849718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849718).length < 2 ^ (prefixWord ++ tailWord_6849718).sum := by decide
  have hdescent : baseEnd_6849718 < baseStart_6849718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849760 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_6849760 : Nat := 118140960795 + 6849760 * 2 ^ 59
def prefixEnd_6849760 : Nat := 4983230072969 + 3 ^ 40 * 6849760 * 2
def baseEnd_6849760 : Nat := 1172406415980408505399511

theorem tailTrace_6849760 : CollatzResearch.WordTrace tailWord_6849760 prefixEnd_6849760 1172406415980408505399511 := by
  unfold tailWord_6849760
  simp only [CollatzResearch.WordTrace]
  refine ⟨124915635832248420358461367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166554181109664560477948489 124915635832248420358461367)
  ·
    refine ⟨187373453748372630537692051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124915635832248420358461367 187373453748372630537692051)
    ·
      refine ⟨281060180622558945806538077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187373453748372630537692051 281060180622558945806538077)
      ·
        refine ⟨105397567733459604677451779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281060180622558945806538077 105397567733459604677451779)
        ·
          refine ⟨158096351600189407016177669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105397567733459604677451779 158096351600189407016177669)
          ·
            refine ⟨29643065925035513815533313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158096351600189407016177669 29643065925035513815533313)
            ·
              refine ⟨22232299443776635361649985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29643065925035513815533313 22232299443776635361649985)
              ·
                refine ⟨16674224582832476521237489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22232299443776635361649985 16674224582832476521237489)
                ·
                  refine ⟨12505668437124357390928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16674224582832476521237489 12505668437124357390928117)
                  ·
                    refine ⟨1172406415980408505399511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12505668437124357390928117 1172406415980408505399511)
                    ·
                      rfl

theorem cell23_6849760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_6849760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849760 prefixEnd_6849760 := by exact prefixLift 6849760
  have htrace : WordTrace (prefixWord ++ tailWord_6849760) baseStart_6849760 baseEnd_6849760 := by
    simpa [prefixWord, tailWord_6849760, baseEnd_6849760] using wordTrace_append hprefix tailTrace_6849760
  have hstable : (prefixWord ++ tailWord_6849760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849760).length < 2 ^ (prefixWord ++ tailWord_6849760).sum := by decide
  have hdescent : baseEnd_6849760 < baseStart_6849760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849770 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_6849770 : Nat := 118140960795 + 6849770 * 2 ^ 59
def prefixEnd_6849770 : Nat := 4983230072969 + 3 ^ 40 * 6849770 * 2
def baseEnd_6849770 : Nat := 3517224382747770477073487

theorem tailTrace_6849770 : CollatzResearch.WordTrace tailWord_6849770 prefixEnd_6849770 3517224382747770477073487 := by
  unfold tailWord_6849770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62457909098615153106196691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166554424262973741616524509 62457909098615153106196691)
  ·
    refine ⟨93686863647922729659295037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62457909098615153106196691 93686863647922729659295037)
    ·
      refine ⟨35132573867971023622235639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93686863647922729659295037 35132573867971023622235639)
      ·
        refine ⟨52698860801956535433353459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35132573867971023622235639 52698860801956535433353459)
        ·
          refine ⟨79048291202934803150030189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52698860801956535433353459 79048291202934803150030189)
          ·
            refine ⟨29643109201100551181261321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79048291202934803150030189 29643109201100551181261321)
            ·
              refine ⟨22232331900825413385945991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29643109201100551181261321 22232331900825413385945991)
              ·
                refine ⟨33348497851238120078918987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22232331900825413385945991 33348497851238120078918987)
                ·
                  refine ⟨50022746776857180118378481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33348497851238120078918987 50022746776857180118378481)
                  ·
                    refine ⟨37517060082642885088783861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50022746776857180118378481 37517060082642885088783861)
                    ·
                      refine ⟨3517224382747770477073487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37517060082642885088783861 3517224382747770477073487)
                      ·
                        rfl

theorem cell23_6849770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_6849770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849770 prefixEnd_6849770 := by exact prefixLift 6849770
  have htrace : WordTrace (prefixWord ++ tailWord_6849770) baseStart_6849770 baseEnd_6849770 := by
    simpa [prefixWord, tailWord_6849770, baseEnd_6849770] using wordTrace_append hprefix tailTrace_6849770
  have hstable : (prefixWord ++ tailWord_6849770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849770).length < 2 ^ (prefixWord ++ tailWord_6849770).sum := by decide
  have hdescent : baseEnd_6849770 < baseStart_6849770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849783 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_6849783 : Nat := 118140960795 + 6849783 * 2 ^ 59
def prefixEnd_6849783 : Nat := 4983230072969 + 3 ^ 40 * 6849783 * 2
def baseEnd_6849783 : Nat := 3517231057996278926210927

theorem tailTrace_6849783 : CollatzResearch.WordTrace tailWord_6849783 prefixEnd_6849783 3517231057996278926210927 := by
  unfold tailWord_6849783
  simp only [CollatzResearch.WordTrace]
  refine ⟨249832110543413515645010003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166554740362275677096673335 249832110543413515645010003)
  ·
    refine ⟨374748165815120273467515005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249832110543413515645010003 374748165815120273467515005)
    ·
      refine ⟨140530562180670102550318127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374748165815120273467515005 140530562180670102550318127)
      ·
        refine ⟨210795843271005153825477191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140530562180670102550318127 210795843271005153825477191)
        ·
          refine ⟨316193764906507730738215787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210795843271005153825477191 316193764906507730738215787)
          ·
            refine ⟨474290647359761596107323681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316193764906507730738215787 474290647359761596107323681)
            ·
              refine ⟨355717985519821197080492761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474290647359761596107323681 355717985519821197080492761)
              ·
                refine ⟨266788489139865897810369571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355717985519821197080492761 266788489139865897810369571)
                ·
                  refine ⟨400182733709798846715554357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266788489139865897810369571 400182733709798846715554357)
                  ·
                    refine ⟨37517131285293641879583221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400182733709798846715554357 37517131285293641879583221)
                    ·
                      refine ⟨3517231057996278926210927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37517131285293641879583221 3517231057996278926210927)
                      ·
                        rfl

theorem cell23_6849783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_6849783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849783 prefixEnd_6849783 := by exact prefixLift 6849783
  have htrace : WordTrace (prefixWord ++ tailWord_6849783) baseStart_6849783 baseEnd_6849783 := by
    simpa [prefixWord, tailWord_6849783, baseEnd_6849783] using wordTrace_append hprefix tailTrace_6849783
  have hstable : (prefixWord ++ tailWord_6849783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849783).length < 2 ^ (prefixWord ++ tailWord_6849783).sum := by decide
  have hdescent : baseEnd_6849783 < baseStart_6849783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849824 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_6849824 : Nat := 118140960795 + 6849824 * 2 ^ 59
def prefixEnd_6849824 : Nat := 4983230072969 + 3 ^ 40 * 6849824 * 2
def baseEnd_6849824 : Nat := 1172417370234371088599413

theorem tailTrace_6849824 : CollatzResearch.WordTrace tailWord_6849824 prefixEnd_6849824 1172417370234371088599413 := by
  unfold tailWord_6849824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124916802968132489823626263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166555737290843319764835017 124916802968132489823626263)
  ·
    refine ⟨187375204452198734735439395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124916802968132489823626263 187375204452198734735439395)
    ·
      refine ⟨281062806678298102103159093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187375204452198734735439395 281062806678298102103159093)
      ·
        refine ⟨26349638126090447072171165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281062806678298102103159093 26349638126090447072171165)
        ·
          refine ⟨9881114297283917652064187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26349638126090447072171165 9881114297283917652064187)
          ·
            refine ⟨14821671445925876478096281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881114297283917652064187 14821671445925876478096281)
            ·
              refine ⟨11116253584444407358572211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14821671445925876478096281 11116253584444407358572211)
              ·
                refine ⟨16674380376666611037858317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116253584444407358572211 16674380376666611037858317)
                ·
                  refine ⟨6252892641249979139196869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16674380376666611037858317 6252892641249979139196869)
                  ·
                    refine ⟨1172417370234371088599413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252892641249979139196869 1172417370234371088599413)
                    ·
                      rfl

theorem cell23_6849824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_6849824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849824 prefixEnd_6849824 := by exact prefixLift 6849824
  have htrace : WordTrace (prefixWord ++ tailWord_6849824) baseStart_6849824 baseEnd_6849824 := by
    simpa [prefixWord, tailWord_6849824, baseEnd_6849824] using wordTrace_append hprefix tailTrace_6849824
  have hstable : (prefixWord ++ tailWord_6849824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849824).length < 2 ^ (prefixWord ++ tailWord_6849824).sum := by decide
  have hdescent : baseEnd_6849824 < baseStart_6849824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849904 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2]
def baseStart_6849904 : Nat := 118140960795 + 6849904 * 2 ^ 59
def prefixEnd_6849904 : Nat := 4983230072969 + 3 ^ 40 * 6849904 * 2
def baseEnd_6849904 : Nat := 3517293189155472952797871

theorem tailTrace_6849904 : CollatzResearch.WordTrace tailWord_6849904 prefixEnd_6849904 3517293189155472952797871 := by
  unfold tailWord_6849904
  simp only [CollatzResearch.WordTrace]
  refine ⟨124918261887987576655082383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166557682517316768873443177 124918261887987576655082383)
  ·
    refine ⟨187377392831981364982623575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124918261887987576655082383 187377392831981364982623575)
    ·
      refine ⟨281066089247972047473935363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187377392831981364982623575 281066089247972047473935363)
      ·
        refine ⟨421599133871958071210903045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281066089247972047473935363 421599133871958071210903045)
        ·
          refine ⟨79049837600992138352044321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421599133871958071210903045 79049837600992138352044321)
          ·
            refine ⟨59287378200744103764033241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79049837600992138352044321 59287378200744103764033241)
            ·
              refine ⟨44465533650558077823024931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59287378200744103764033241 44465533650558077823024931)
              ·
                refine ⟨66698300475837116734537397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44465533650558077823024931 66698300475837116734537397)
                ·
                  refine ⟨6252965669609729693862881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66698300475837116734537397 6252965669609729693862881)
                  ·
                    refine ⟨4689724252207297270397161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252965669609729693862881 4689724252207297270397161)
                    ·
                      refine ⟨3517293189155472952797871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689724252207297270397161 3517293189155472952797871)
                      ·
                        rfl

theorem cell23_6849904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2].length) (baseStart_6849904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849904 prefixEnd_6849904 := by exact prefixLift 6849904
  have htrace : WordTrace (prefixWord ++ tailWord_6849904) baseStart_6849904 baseEnd_6849904 := by
    simpa [prefixWord, tailWord_6849904, baseEnd_6849904] using wordTrace_append hprefix tailTrace_6849904
  have hstable : (prefixWord ++ tailWord_6849904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849904).length < 2 ^ (prefixWord ++ tailWord_6849904).sum := by decide
  have hdescent : baseEnd_6849904 < baseStart_6849904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849917 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6849917 : Nat := 118140960795 + 6849917 * 2 ^ 59
def prefixEnd_6849917 : Nat := 4983230072969 + 3 ^ 40 * 6849917 * 2
def baseEnd_6849917 : Nat := 3517299864403981401935311

theorem tailTrace_6849917 : CollatzResearch.WordTrace tailWord_6849917 prefixEnd_6849917 3517299864403981401935311 := by
  unfold tailWord_6849917
  simp only [CollatzResearch.WordTrace]
  refine ⟨249836997924928056530388005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166557998616618704353592003 249836997924928056530388005)
  ·
    refine ⟨46844437110924010599447751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249836997924928056530388005 46844437110924010599447751)
    ·
      refine ⟨70266655666386015899171627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844437110924010599447751 70266655666386015899171627)
      ·
        refine ⟨105399983499579023848757441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70266655666386015899171627 105399983499579023848757441)
        ·
          refine ⟨79049987624684267886568081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105399983499579023848757441 79049987624684267886568081)
          ·
            refine ⟨59287490718513200914926061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79049987624684267886568081 59287490718513200914926061)
            ·
              refine ⟨22232809019442450343097273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59287490718513200914926061 22232809019442450343097273)
              ·
                refine ⟨16674606764581837757322955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22232809019442450343097273 16674606764581837757322955)
                ·
                  refine ⟨25011910146872756635984433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16674606764581837757322955 25011910146872756635984433)
                  ·
                    refine ⟨18758932610154567476988325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25011910146872756635984433 18758932610154567476988325)
                    ·
                      refine ⟨3517299864403981401935311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18758932610154567476988325 3517299864403981401935311)
                      ·
                        rfl

theorem cell23_6849917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6849917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849917 prefixEnd_6849917 := by exact prefixLift 6849917
  have htrace : WordTrace (prefixWord ++ tailWord_6849917) baseStart_6849917 baseEnd_6849917 := by
    simpa [prefixWord, tailWord_6849917, baseEnd_6849917] using wordTrace_append hprefix tailTrace_6849917
  have hstable : (prefixWord ++ tailWord_6849917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849917).length < 2 ^ (prefixWord ++ tailWord_6849917).sum := by decide
  have hdescent : baseEnd_6849917 < baseStart_6849917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849924 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6849924 : Nat := 118140960795 + 6849924 * 2 ^ 59
def prefixEnd_6849924 : Nat := 4983230072969 + 3 ^ 40 * 6849924 * 2
def baseEnd_6849924 : Nat := 3517303458768562874547779

theorem tailTrace_6849924 : CollatzResearch.WordTrace tailWord_6849924 prefixEnd_6849924 3517303458768562874547779 := by
  unfold tailWord_6849924
  simp only [CollatzResearch.WordTrace]
  refine ⟨124918626617951348362946413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166558168823935131150595217 124918626617951348362946413)
  ·
    refine ⟨46844484981731755636104905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124918626617951348362946413 46844484981731755636104905)
    ·
      refine ⟨35133363736298816727078679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46844484981731755636104905 35133363736298816727078679)
      ·
        refine ⟨52700045604448225090618019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35133363736298816727078679 52700045604448225090618019)
        ·
          refine ⟨79050068406672337635927029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52700045604448225090618019 79050068406672337635927029)
          ·
            refine ⟨7410943913125531653368159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79050068406672337635927029 7410943913125531653368159)
            ·
              refine ⟨11116415869688297480052239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410943913125531653368159 11116415869688297480052239)
              ·
                refine ⟨16674623804532446220078359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116415869688297480052239 16674623804532446220078359)
                ·
                  refine ⟨25011935706798669330117539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16674623804532446220078359 25011935706798669330117539)
                  ·
                    refine ⟨37517903560198003995176309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25011935706798669330117539 37517903560198003995176309)
                    ·
                      refine ⟨3517303458768562874547779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37517903560198003995176309 3517303458768562874547779)
                      ·
                        rfl

theorem cell23_6849924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6849924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849924 prefixEnd_6849924 := by exact prefixLift 6849924
  have htrace : WordTrace (prefixWord ++ tailWord_6849924) baseStart_6849924 baseEnd_6849924 := by
    simpa [prefixWord, tailWord_6849924, baseEnd_6849924] using wordTrace_append hprefix tailTrace_6849924
  have hstable : (prefixWord ++ tailWord_6849924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849924).length < 2 ^ (prefixWord ++ tailWord_6849924).sum := by decide
  have hdescent : baseEnd_6849924 < baseStart_6849924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849944 : List Nat := [2, 1, 2, 5, 2, 2, 1, 8]
def baseStart_6849944 : Nat := 118140960795 + 6849944 * 2 ^ 59
def prefixEnd_6849944 : Nat := 4983230072969 + 3 ^ 40 * 6849944 * 2
def baseEnd_6849944 : Nat := 130270878828950103566581

theorem tailTrace_6849944 : CollatzResearch.WordTrace tailWord_6849944 prefixEnd_6849944 130270878828950103566581 := by
  unfold tailWord_6849944
  simp only [CollatzResearch.WordTrace]
  refine ⟨124918991347915120070810443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166558655130553493427747257 124918991347915120070810443)
  ·
    refine ⟨187378487021872680106215665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124918991347915120070810443 187378487021872680106215665)
    ·
      refine ⟨140533865266404510079661749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187378487021872680106215665 140533865266404510079661749)
      ·
        refine ⟨13175049868725422819968289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140533865266404510079661749 13175049868725422819968289)
        ·
          refine ⟨9881287401544067114976217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13175049868725422819968289 9881287401544067114976217)
          ·
            refine ⟨7410965551158050336232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881287401544067114976217 7410965551158050336232163)
            ·
              refine ⟨11116448326737075504348245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410965551158050336232163 11116448326737075504348245)
              ·
                refine ⟨130270878828950103566581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11116448326737075504348245 130270878828950103566581)
                ·
                  rfl

theorem cell23_6849944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 8].length) (baseStart_6849944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849944 prefixEnd_6849944 := by exact prefixLift 6849944
  have htrace : WordTrace (prefixWord ++ tailWord_6849944) baseStart_6849944 baseEnd_6849944 := by
    simpa [prefixWord, tailWord_6849944, baseEnd_6849944] using wordTrace_append hprefix tailTrace_6849944
  have hstable : (prefixWord ++ tailWord_6849944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849944).length < 2 ^ (prefixWord ++ tailWord_6849944).sum := by decide
  have hdescent : baseEnd_6849944 < baseStart_6849944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849954 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6849954 : Nat := 118140960795 + 6849954 * 2 ^ 59
def prefixEnd_6849954 : Nat := 4983230072969 + 3 ^ 40 * 6849954 * 2
def baseEnd_6849954 : Nat := 3517318863188197757172641

theorem tailTrace_6849954 : CollatzResearch.WordTrace tailWord_6849954 prefixEnd_6849954 3517318863188197757172641 := by
  unfold tailWord_6849954
  simp only [CollatzResearch.WordTrace]
  refine ⟨62459586856448502962371229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166558898283862674566323277 62459586856448502962371229)
  ·
    refine ⟨23422345071168188610889211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62459586856448502962371229 23422345071168188610889211)
    ·
      refine ⟨35133517606752282916333817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23422345071168188610889211 35133517606752282916333817)
      ·
        refine ⟨26350138205064212187250363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35133517606752282916333817 26350138205064212187250363)
        ·
          refine ⟨39525207307596318280875545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26350138205064212187250363 39525207307596318280875545)
          ·
            refine ⟨29643905480697238710656659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39525207307596318280875545 29643905480697238710656659)
            ·
              refine ⟨44465858221045858065984989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29643905480697238710656659 44465858221045858065984989)
              ·
                refine ⟨16674696832892196774744371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44465858221045858065984989 16674696832892196774744371)
                ·
                  refine ⟨25012045249338295162116557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16674696832892196774744371 25012045249338295162116557)
                  ·
                    refine ⟨9379516968501860685793709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25012045249338295162116557 9379516968501860685793709)
                    ·
                      refine ⟨3517318863188197757172641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379516968501860685793709 3517318863188197757172641)
                      ·
                        rfl

theorem cell23_6849954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6849954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849954 prefixEnd_6849954 := by exact prefixLift 6849954
  have htrace : WordTrace (prefixWord ++ tailWord_6849954) baseStart_6849954 baseEnd_6849954 := by
    simpa [prefixWord, tailWord_6849954, baseEnd_6849954] using wordTrace_append hprefix tailTrace_6849954
  have hstable : (prefixWord ++ tailWord_6849954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849954).length < 2 ^ (prefixWord ++ tailWord_6849954).sum := by decide
  have hdescent : baseEnd_6849954 < baseStart_6849954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849964 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_6849964 : Nat := 118140960795 + 6849964 * 2 ^ 59
def prefixEnd_6849964 : Nat := 4983230072969 + 3 ^ 40 * 6849964 * 2
def baseEnd_6849964 : Nat := 3517323997994742718047595

theorem tailTrace_6849964 : CollatzResearch.WordTrace tailWord_6849964 prefixEnd_6849964 3517323997994742718047595 := by
  unfold tailWord_6849964
  simp only [CollatzResearch.WordTrace]
  refine ⟨124919356077878891778674473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166559141437171855704899297 124919356077878891778674473)
  ·
    refine ⟨93689517058409168834005855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124919356077878891778674473 93689517058409168834005855)
    ·
      refine ⟨140534275587613753251008783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93689517058409168834005855 140534275587613753251008783)
      ·
        refine ⟨210801413381420629876513175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140534275587613753251008783 210801413381420629876513175)
        ·
          refine ⟨316202120072130944814769763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210801413381420629876513175 316202120072130944814769763)
          ·
            refine ⟨474303180108196417222154645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316202120072130944814769763 474303180108196417222154645)
            ·
              refine ⟨22232961567571707057288499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474303180108196417222154645 22232961567571707057288499)
              ·
                refine ⟨33349442351357560585932749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22232961567571707057288499 33349442351357560585932749)
                ·
                  refine ⟨12506040881759085219724781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33349442351357560585932749 12506040881759085219724781)
                  ·
                    refine ⟨4689765330659656957396793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12506040881759085219724781 4689765330659656957396793)
                    ·
                      refine ⟨3517323997994742718047595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689765330659656957396793 3517323997994742718047595)
                      ·
                        rfl

theorem cell23_6849964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_6849964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849964 prefixEnd_6849964 := by exact prefixLift 6849964
  have htrace : WordTrace (prefixWord ++ tailWord_6849964) baseStart_6849964 baseEnd_6849964 := by
    simpa [prefixWord, tailWord_6849964, baseEnd_6849964] using wordTrace_append hprefix tailTrace_6849964
  have hstable : (prefixWord ++ tailWord_6849964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849964).length < 2 ^ (prefixWord ++ tailWord_6849964).sum := by decide
  have hdescent : baseEnd_6849964 < baseStart_6849964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849981 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6849981 : Nat := 118140960795 + 6849981 * 2 ^ 59
def prefixEnd_6849981 : Nat := 4983230072969 + 3 ^ 40 * 6849981 * 2
def baseEnd_6849981 : Nat := 3517332727165869151535017

theorem tailTrace_6849981 : CollatzResearch.WordTrace tailWord_6849981 prefixEnd_6849981 3517332727165869151535017 := by
  unfold tailWord_6849981
  simp only [CollatzResearch.WordTrace]
  refine ⟨249839332196696195460717797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166559554797797463640478531 249839332196696195460717797)
  ·
    refine ⟨46844874786880536648884587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249839332196696195460717797 46844874786880536648884587)
    ·
      refine ⟨70267312180320804973326881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844874786880536648884587 70267312180320804973326881)
      ·
        refine ⟨52700484135240603729995161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70267312180320804973326881 52700484135240603729995161)
        ·
          refine ⟨39525363101430452797496371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52700484135240603729995161 39525363101430452797496371)
          ·
            refine ⟨59288044652145679196244557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39525363101430452797496371 59288044652145679196244557)
            ·
              refine ⟨22233016744554629698591709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59288044652145679196244557 22233016744554629698591709)
              ·
                refine ⟨8337381279207986136971891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22233016744554629698591709 8337381279207986136971891)
                ·
                  refine ⟨12506071918811979205457837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8337381279207986136971891 12506071918811979205457837)
                  ·
                    refine ⟨4689776969554492202046689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12506071918811979205457837 4689776969554492202046689)
                    ·
                      refine ⟨3517332727165869151535017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689776969554492202046689 3517332727165869151535017)
                      ·
                        rfl

theorem cell23_6849981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6849981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849981 prefixEnd_6849981 := by exact prefixLift 6849981
  have htrace : WordTrace (prefixWord ++ tailWord_6849981) baseStart_6849981 baseEnd_6849981 := by
    simpa [prefixWord, tailWord_6849981, baseEnd_6849981] using wordTrace_append hprefix tailTrace_6849981
  have hstable : (prefixWord ++ tailWord_6849981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849981).length < 2 ^ (prefixWord ++ tailWord_6849981).sum := by decide
  have hdescent : baseEnd_6849981 < baseStart_6849981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6849988 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6849988 : Nat := 118140960795 + 6849988 * 2 ^ 59
def prefixEnd_6849988 : Nat := 4983230072969 + 3 ^ 40 * 6849988 * 2
def baseEnd_6849988 : Nat := 3517336321530450624147485

theorem tailTrace_6849988 : CollatzResearch.WordTrace tailWord_6849988 prefixEnd_6849988 3517336321530450624147485 := by
  unfold tailWord_6849988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124919793753835417828111309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166559725005113890437481745 124919793753835417828111309)
  ·
    refine ⟨46844922657688281685541741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124919793753835417828111309 46844922657688281685541741)
    ·
      refine ⟨17566845996633105632078153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46844922657688281685541741 17566845996633105632078153)
      ·
        refine ⟨13175134497474829224058615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17566845996633105632078153 13175134497474829224058615)
        ·
          refine ⟨19762701746212243836087923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175134497474829224058615 19762701746212243836087923)
          ·
            refine ⟨29644052619318365754131885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762701746212243836087923 29644052619318365754131885)
            ·
              refine ⟨11116519732244387157799457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29644052619318365754131885 11116519732244387157799457)
              ·
                refine ⟨8337389799183290368349593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116519732244387157799457 8337389799183290368349593)
                ·
                  refine ⟨6253042349387467776262195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337389799183290368349593 6253042349387467776262195)
                  ·
                    refine ⟨9379563524081201664393293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6253042349387467776262195 9379563524081201664393293)
                    ·
                      refine ⟨3517336321530450624147485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379563524081201664393293 3517336321530450624147485)
                      ·
                        rfl

theorem cell23_6849988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6849988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6849988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6849988 prefixEnd_6849988 := by exact prefixLift 6849988
  have htrace : WordTrace (prefixWord ++ tailWord_6849988) baseStart_6849988 baseEnd_6849988 := by
    simpa [prefixWord, tailWord_6849988, baseEnd_6849988] using wordTrace_append hprefix tailTrace_6849988
  have hstable : (prefixWord ++ tailWord_6849988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6849988).length < 2 ^ (prefixWord ++ tailWord_6849988).sum := by decide
  have hdescent : baseEnd_6849988 < baseStart_6849988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6849988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850000 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 11]
def baseStart_6850000 : Nat := 118140960795 + 6850000 * 2 ^ 59
def prefixEnd_6850000 : Nat := 4983230072969 + 3 ^ 40 * 6850000 * 2
def baseEnd_6850000 : Nat := 390815831477589397466381

theorem tailTrace_6850000 : CollatzResearch.WordTrace tailWord_6850000 prefixEnd_6850000 390815831477589397466381 := by
  unfold tailWord_6850000
  simp only [CollatzResearch.WordTrace]
  refine ⟨124920012591813680852829727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166560016789084907803772969 124920012591813680852829727)
  ·
    refine ⟨187380018887720521279244591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124920012591813680852829727 187380018887720521279244591)
    ·
      refine ⟨281070028331580781918866887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187380018887720521279244591 281070028331580781918866887)
      ·
        refine ⟨421605042497371172878300331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281070028331580781918866887 421605042497371172878300331)
        ·
          refine ⟨632407563746056759317450497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421605042497371172878300331 632407563746056759317450497)
          ·
            refine ⟨474305672809542569488087873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632407563746056759317450497 474305672809542569488087873)
            ·
              refine ⟨355729254607156927116065905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474305672809542569488087873 355729254607156927116065905)
              ·
                refine ⟨266796940955367695337049429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355729254607156927116065905 266796940955367695337049429)
                ·
                  refine ⟨390815831477589397466381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 266796940955367695337049429 390815831477589397466381)
                  ·
                    rfl

theorem cell23_6850000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_6850000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850000 prefixEnd_6850000 := by exact prefixLift 6850000
  have htrace : WordTrace (prefixWord ++ tailWord_6850000) baseStart_6850000 baseEnd_6850000 := by
    simpa [prefixWord, tailWord_6850000, baseEnd_6850000] using wordTrace_append hprefix tailTrace_6850000
  have hstable : (prefixWord ++ tailWord_6850000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850000).length < 2 ^ (prefixWord ++ tailWord_6850000).sum := by decide
  have hdescent : baseEnd_6850000 < baseStart_6850000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850017 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 7]
def baseStart_6850017 : Nat := 118140960795 + 6850017 * 2 ^ 59
def prefixEnd_6850017 : Nat := 4983230072969 + 3 ^ 40 * 6850017 * 2
def baseEnd_6850017 : Nat := 390816801385492334520539

theorem tailTrace_6850017 : CollatzResearch.WordTrace tailWord_6850017 prefixEnd_6850017 390816801385492334520539 := by
  unfold tailWord_6850017
  simp only [CollatzResearch.WordTrace]
  refine ⟨249840645224565773609028305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166560430149710515739352203 249840645224565773609028305)
  ·
    refine ⟨187380483918424330206771229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249840645224565773609028305 187380483918424330206771229)
    ·
      refine ⟨70267681469409123827539211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187380483918424330206771229 70267681469409123827539211)
      ·
        refine ⟨105401522204113685741308817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70267681469409123827539211 105401522204113685741308817)
        ·
          refine ⟨79051141653085264305981613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105401522204113685741308817 79051141653085264305981613)
          ·
            refine ⟨29644178119906974114743105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79051141653085264305981613 29644178119906974114743105)
            ·
              refine ⟨22233133589930230586057329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29644178119906974114743105 22233133589930230586057329)
              ·
                refine ⟨16674850192447672939542997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22233133589930230586057329 16674850192447672939542997)
                ·
                  refine ⟨390816801385492334520539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16674850192447672939542997 390816801385492334520539)
                  ·
                    rfl

theorem cell23_6850017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_6850017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850017 prefixEnd_6850017 := by exact prefixLift 6850017
  have htrace : WordTrace (prefixWord ++ tailWord_6850017) baseStart_6850017 baseEnd_6850017 := by
    simpa [prefixWord, tailWord_6850017, baseEnd_6850017] using wordTrace_append hprefix tailTrace_6850017
  have hstable : (prefixWord ++ tailWord_6850017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850017).length < 2 ^ (prefixWord ++ tailWord_6850017).sum := by decide
  have hdescent : baseEnd_6850017 < baseStart_6850017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850027 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3]
def baseStart_6850027 : Nat := 118140960795 + 6850027 * 2 ^ 59
def prefixEnd_6850027 : Nat := 4983230072969 + 3 ^ 40 * 6850027 * 2
def baseEnd_6850027 : Nat := 3517356347275975971559805

theorem tailTrace_6850027 : CollatzResearch.WordTrace tailWord_6850027 prefixEnd_6850027 3517356347275975971559805 := by
  unfold tailWord_6850027
  simp only [CollatzResearch.WordTrace]
  refine ⟨249841009954529545316892335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166560673303019696877928223 249841009954529545316892335)
  ·
    refine ⟨374761514931794317975338503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249841009954529545316892335 374761514931794317975338503)
    ·
      refine ⟨562142272397691476963007755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374761514931794317975338503 562142272397691476963007755)
      ·
        refine ⟨843213408596537215444511633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562142272397691476963007755 843213408596537215444511633)
        ·
          refine ⟨632410056447402911583383725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843213408596537215444511633 632410056447402911583383725)
          ·
            refine ⟨237153771167776091843768897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632410056447402911583383725 237153771167776091843768897)
            ·
              refine ⟨177865328375832068882826673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237153771167776091843768897 177865328375832068882826673)
              ·
                refine ⟨133398996281874051662120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177865328375832068882826673 133398996281874051662120005)
                ·
                  refine ⟨25012311802851384686647501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133398996281874051662120005 25012311802851384686647501)
                  ·
                    refine ⟨9379616926069269257492813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25012311802851384686647501 9379616926069269257492813)
                    ·
                      refine ⟨3517356347275975971559805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379616926069269257492813 3517356347275975971559805)
                      ·
                        rfl

theorem cell23_6850027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].length) (baseStart_6850027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850027 prefixEnd_6850027 := by exact prefixLift 6850027
  have htrace : WordTrace (prefixWord ++ tailWord_6850027) baseStart_6850027 baseEnd_6850027 := by
    simpa [prefixWord, tailWord_6850027, baseEnd_6850027] using wordTrace_append hprefix tailTrace_6850027
  have hstable : (prefixWord ++ tailWord_6850027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850027).length < 2 ^ (prefixWord ++ tailWord_6850027).sum := by decide
  have hdescent : baseEnd_6850027 < baseStart_6850027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850057 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_6850057 : Nat := 118140960795 + 6850057 * 2 ^ 59
def prefixEnd_6850057 : Nat := 4983230072969 + 3 ^ 40 * 6850057 * 2
def baseEnd_6850057 : Nat := 3517371751695610854184667

theorem tailTrace_6850057 : CollatzResearch.WordTrace tailWord_6850057 prefixEnd_6850057 3517371751695610854184667 := by
  unfold tailWord_6850057
  simp only [CollatzResearch.WordTrace]
  refine ⟨249842104144420860440484425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166561402762947240293656283 249842104144420860440484425)
  ·
    refine ⟨187381578108315645330363319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249842104144420860440484425 187381578108315645330363319)
    ·
      refine ⟨281072367162473467995544979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187381578108315645330363319 281072367162473467995544979)
      ·
        refine ⟨421608550743710201993317469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281072367162473467995544979 421608550743710201993317469)
        ·
          refine ⟨158103206528891325747494051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421608550743710201993317469 158103206528891325747494051)
          ·
            refine ⟨237154809793336988621241077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158103206528891325747494051 237154809793336988621241077)
            ·
              refine ⟨22233263418125342683241351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237154809793336988621241077 22233263418125342683241351)
              ·
                refine ⟨33349895127188014024862027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22233263418125342683241351 33349895127188014024862027)
                ·
                  refine ⟨50024842690782021037293041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33349895127188014024862027 50024842690782021037293041)
                  ·
                    refine ⟨37518632018086515777969781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50024842690782021037293041 37518632018086515777969781)
                    ·
                      refine ⟨3517371751695610854184667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37518632018086515777969781 3517371751695610854184667)
                      ·
                        rfl

theorem cell23_6850057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_6850057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850057 prefixEnd_6850057 := by exact prefixLift 6850057
  have htrace : WordTrace (prefixWord ++ tailWord_6850057) baseStart_6850057 baseEnd_6850057 := by
    simpa [prefixWord, tailWord_6850057, baseEnd_6850057] using wordTrace_append hprefix tailTrace_6850057
  have hstable : (prefixWord ++ tailWord_6850057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850057).length < 2 ^ (prefixWord ++ tailWord_6850057).sum := by decide
  have hdescent : baseEnd_6850057 < baseStart_6850057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850062 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6850062 : Nat := 118140960795 + 6850062 * 2 ^ 59
def prefixEnd_6850062 : Nat := 4983230072969 + 3 ^ 40 * 6850062 * 2
def baseEnd_6850062 : Nat := 3517374319098883334622145

theorem tailTrace_6850062 : CollatzResearch.WordTrace tailWord_6850062 prefixEnd_6850062 3517374319098883334622145 := by
  unfold tailWord_6850062
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230285813675343286802055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166561524339601830862944293 31230285813675343286802055)
  ·
    refine ⟨46845428720513014930203083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31230285813675343286802055 46845428720513014930203083)
    ·
      refine ⟨70268143080769522395304625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845428720513014930203083 70268143080769522395304625)
      ·
        refine ⟨52701107310577141796478469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70268143080769522395304625 52701107310577141796478469)
        ·
          refine ⟨9881457620733214086839713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52701107310577141796478469 9881457620733214086839713)
          ·
            refine ⟨7411093215549910565129785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881457620733214086839713 7411093215549910565129785)
            ·
              refine ⟨5558319911662432923847339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411093215549910565129785 5558319911662432923847339)
              ·
                refine ⟨8337479867493649385771009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558319911662432923847339 8337479867493649385771009)
                ·
                  refine ⟨6253109900620237039328257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337479867493649385771009 6253109900620237039328257)
                  ·
                    refine ⟨4689832425465177779496193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253109900620237039328257 4689832425465177779496193)
                    ·
                      refine ⟨3517374319098883334622145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689832425465177779496193 3517374319098883334622145)
                      ·
                        rfl

theorem cell23_6850062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6850062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850062 prefixEnd_6850062 := by exact prefixLift 6850062
  have htrace : WordTrace (prefixWord ++ tailWord_6850062) baseStart_6850062 baseEnd_6850062 := by
    simpa [prefixWord, tailWord_6850062, baseEnd_6850062] using wordTrace_append hprefix tailTrace_6850062
  have hstable : (prefixWord ++ tailWord_6850062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850062).length < 2 ^ (prefixWord ++ tailWord_6850062).sum := by decide
  have hdescent : baseEnd_6850062 < baseStart_6850062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850097 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_6850097 : Nat := 118140960795 + 6850097 * 2 ^ 59
def prefixEnd_6850097 : Nat := 4983230072969 + 3 ^ 40 * 6850097 * 2
def baseEnd_6850097 : Nat := 3517392290921790697684483

theorem tailTrace_6850097 : CollatzResearch.WordTrace tailWord_6850097 prefixEnd_6850097 3517392290921790697684483 := by
  unfold tailWord_6850097
  simp only [CollatzResearch.WordTrace]
  refine ⟨249843563064275947271940545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166562375376183964847960363 249843563064275947271940545)
  ·
    refine ⟨187382672298206960453955409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249843563064275947271940545 187382672298206960453955409)
    ·
      refine ⟨140537004223655220340466557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187382672298206960453955409 140537004223655220340466557)
      ·
        refine ⟨52701376583870707627674959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140537004223655220340466557 52701376583870707627674959)
        ·
          refine ⟨79052064875806061441512439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52701376583870707627674959 79052064875806061441512439)
          ·
            refine ⟨118578097313709092162268659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79052064875806061441512439 118578097313709092162268659)
            ·
              refine ⟨177867145970563638243402989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118578097313709092162268659 177867145970563638243402989)
              ·
                refine ⟨66700179738961364341276121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177867145970563638243402989 66700179738961364341276121)
                ·
                  refine ⟨50025134804221023255957091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66700179738961364341276121 50025134804221023255957091)
                  ·
                    refine ⟨75037702206331534883935637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50025134804221023255957091 75037702206331534883935637)
                    ·
                      refine ⟨3517392290921790697684483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75037702206331534883935637 3517392290921790697684483)
                      ·
                        rfl

theorem cell23_6850097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_6850097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850097 prefixEnd_6850097 := by exact prefixLift 6850097
  have htrace : WordTrace (prefixWord ++ tailWord_6850097) baseStart_6850097 baseEnd_6850097 := by
    simpa [prefixWord, tailWord_6850097, baseEnd_6850097] using wordTrace_append hprefix tailTrace_6850097
  have hstable : (prefixWord ++ tailWord_6850097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850097).length < 2 ^ (prefixWord ++ tailWord_6850097).sum := by decide
  have hdescent : baseEnd_6850097 < baseStart_6850097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850102 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6850102 : Nat := 118140960795 + 6850102 * 2 ^ 59
def prefixEnd_6850102 : Nat := 4983230072969 + 3 ^ 40 * 6850102 * 2
def baseEnd_6850102 : Nat := 390821650925007019791329

theorem tailTrace_6850102 : CollatzResearch.WordTrace tailWord_6850102 prefixEnd_6850102 390821650925007019791329 := by
  unfold tailWord_6850102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15615234089328614570367035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166562496952838555417248373 15615234089328614570367035)
  ·
    refine ⟨23422851133992921855550553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15615234089328614570367035 23422851133992921855550553)
    ·
      refine ⟨17567138350494691391662915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23422851133992921855550553 17567138350494691391662915)
      ·
        refine ⟨26350707525742037087494373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17567138350494691391662915 26350707525742037087494373)
        ·
          refine ⟨4940757661076631953905195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26350707525742037087494373 4940757661076631953905195)
          ·
            refine ⟨7411136491614947930857793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940757661076631953905195 7411136491614947930857793)
            ·
              refine ⟨5558352368711210948143345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411136491614947930857793 5558352368711210948143345)
              ·
                refine ⟨4168764276533408211107509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558352368711210948143345 4168764276533408211107509)
                ·
                  refine ⟨390821650925007019791329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168764276533408211107509 390821650925007019791329)
                  ·
                    rfl

theorem cell23_6850102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6850102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850102 prefixEnd_6850102 := by exact prefixLift 6850102
  have htrace : WordTrace (prefixWord ++ tailWord_6850102) baseStart_6850102 baseEnd_6850102 := by
    simpa [prefixWord, tailWord_6850102, baseEnd_6850102] using wordTrace_append hprefix tailTrace_6850102
  have hstable : (prefixWord ++ tailWord_6850102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850102).length < 2 ^ (prefixWord ++ tailWord_6850102).sum := by decide
  have hdescent : baseEnd_6850102 < baseStart_6850102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850124 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 6]
def baseStart_6850124 : Nat := 118140960795 + 6850124 * 2 ^ 59
def prefixEnd_6850124 : Nat := 4983230072969 + 3 ^ 40 * 6850124 * 2
def baseEnd_6850124 : Nat := 390822906099940232449651

theorem tailTrace_6850124 : CollatzResearch.WordTrace tailWord_6850124 prefixEnd_6850124 390822906099940232449651 := by
  unfold tailWord_6850124
  simp only [CollatzResearch.WordTrace]
  refine ⟨124922273917589065441586713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166563031890118753922115617 124922273917589065441586713)
  ·
    refine ⟨93691705438191799081190035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124922273917589065441586713 93691705438191799081190035)
    ·
      refine ⟨140537558157287698621785053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93691705438191799081190035 140537558157287698621785053)
      ·
        refine ⟨52701584308982886983169395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140537558157287698621785053 52701584308982886983169395)
        ·
          refine ⟨79052376463474330474754093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52701584308982886983169395 79052376463474330474754093)
          ·
            refine ⟨29644641173802873928032785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79052376463474330474754093 29644641173802873928032785)
            ·
              refine ⟨22233480880352155446024589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29644641173802873928032785 22233480880352155446024589)
              ·
                refine ⟨8337555330132058292259221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22233480880352155446024589 8337555330132058292259221)
                ·
                  refine ⟨390822906099940232449651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8337555330132058292259221 390822906099940232449651)
                  ·
                    rfl

theorem cell23_6850124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_6850124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850124 prefixEnd_6850124 := by exact prefixLift 6850124
  have htrace : WordTrace (prefixWord ++ tailWord_6850124) baseStart_6850124 baseEnd_6850124 := by
    simpa [prefixWord, tailWord_6850124, baseEnd_6850124] using wordTrace_append hprefix tailTrace_6850124
  have hstable : (prefixWord ++ tailWord_6850124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850124).length < 2 ^ (prefixWord ++ tailWord_6850124).sum := by decide
  have hdescent : baseEnd_6850124 < baseStart_6850124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850158 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_6850158 : Nat := 118140960795 + 6850158 * 2 ^ 59
def prefixEnd_6850158 : Nat := 4983230072969 + 3 ^ 40 * 6850158 * 2
def baseEnd_6850158 : Nat := 390824845915746106557967

theorem tailTrace_6850158 : CollatzResearch.WordTrace tailWord_6850158 prefixEnd_6850158 390824845915746106557967 := by
  unfold tailWord_6850158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230723489631869336238891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166563858611369969793274085 31230723489631869336238891)
  ·
    refine ⟨46846085234447804004358337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31230723489631869336238891 46846085234447804004358337)
    ·
      refine ⟨35134563925835853003268753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46846085234447804004358337 35134563925835853003268753)
      ·
        refine ⟨26350922944376889752451565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35134563925835853003268753 26350922944376889752451565)
        ·
          refine ⟨9881596104141333657169337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26350922944376889752451565 9881596104141333657169337)
          ·
            refine ⟨7411197078106000242877003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881596104141333657169337 7411197078106000242877003)
            ·
              refine ⟨11116795617159000364315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411197078106000242877003 11116795617159000364315505)
              ·
                refine ⟨8337596712869250273236629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116795617159000364315505 8337596712869250273236629)
                ·
                  refine ⟨390824845915746106557967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8337596712869250273236629 390824845915746106557967)
                  ·
                    rfl

theorem cell23_6850158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_6850158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850158 prefixEnd_6850158 := by exact prefixLift 6850158
  have htrace : WordTrace (prefixWord ++ tailWord_6850158) baseStart_6850158 baseEnd_6850158 := by
    simpa [prefixWord, tailWord_6850158, baseEnd_6850158] using wordTrace_append hprefix tailTrace_6850158
  have hstable : (prefixWord ++ tailWord_6850158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850158).length < 2 ^ (prefixWord ++ tailWord_6850158).sum := by decide
  have hdescent : baseEnd_6850158 < baseStart_6850158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850161 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_6850161 : Nat := 118140960795 + 6850161 * 2 ^ 59
def prefixEnd_6850161 : Nat := 4983230072969 + 3 ^ 40 * 6850161 * 2
def baseEnd_6850161 : Nat := 3517425153683678447284189

theorem tailTrace_6850161 : CollatzResearch.WordTrace tailWord_6850161 prefixEnd_6850161 3517425153683678447284189 := by
  unfold tailWord_6850161
  simp only [CollatzResearch.WordTrace]
  refine ⟨249845897336044086202270337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166563931557362724134846891 249845897336044086202270337)
  ·
    refine ⟨187384423002033064651702753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249845897336044086202270337 187384423002033064651702753)
    ·
      refine ⟨140538317251524798488777065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187384423002033064651702753 140538317251524798488777065)
      ·
        refine ⟨105403737938643598866582799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140538317251524798488777065 105403737938643598866582799)
        ·
          refine ⟨158105606907965398299874199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105403737938643598866582799 158105606907965398299874199)
          ·
            refine ⟨237158410361948097449811299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158105606907965398299874199 237158410361948097449811299)
            ·
              refine ⟨355737615542922146174716949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237158410361948097449811299 355737615542922146174716949)
              ·
                refine ⟨16675200728574475601939857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355737615542922146174716949 16675200728574475601939857)
                ·
                  refine ⟨12506400546430856701454893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16675200728574475601939857 12506400546430856701454893)
                  ·
                    refine ⟨4689900204911571263045585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12506400546430856701454893 4689900204911571263045585)
                    ·
                      refine ⟨3517425153683678447284189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689900204911571263045585 3517425153683678447284189)
                      ·
                        rfl

theorem cell23_6850161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_6850161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850161 prefixEnd_6850161 := by exact prefixLift 6850161
  have htrace : WordTrace (prefixWord ++ tailWord_6850161) baseStart_6850161 baseEnd_6850161 := by
    simpa [prefixWord, tailWord_6850161, baseEnd_6850161] using wordTrace_append hprefix tailTrace_6850161
  have hstable : (prefixWord ++ tailWord_6850161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850161).length < 2 ^ (prefixWord ++ tailWord_6850161).sum := by decide
  have hdescent : baseEnd_6850161 < baseStart_6850161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850211 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 3]
def baseStart_6850211 : Nat := 118140960795 + 6850211 * 2 ^ 59
def prefixEnd_6850211 : Nat := 4983230072969 + 3 ^ 40 * 6850211 * 2
def baseEnd_6850211 : Nat := 3517450827716403251658959

theorem tailTrace_6850211 : CollatzResearch.WordTrace tailWord_6850211 prefixEnd_6850211 3517450827716403251658959 := by
  unfold tailWord_6850211
  simp only [CollatzResearch.WordTrace]
  refine ⟨249847720985862944741590487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166565147323908629827726991 249847720985862944741590487)
  ·
    refine ⟨374771581478794417112385731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249847720985862944741590487 374771581478794417112385731)
    ·
      refine ⟨562157372218191625668578597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374771581478794417112385731 562157372218191625668578597)
      ·
        refine ⟨105404507290910929812858487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 562157372218191625668578597 105404507290910929812858487)
        ·
          refine ⟨158106760936366394719287731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105404507290910929812858487 158106760936366394719287731)
          ·
            refine ⟨237160141404549592078931597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158106760936366394719287731 237160141404549592078931597)
            ·
              refine ⟨88935053026706097029599349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237160141404549592078931597 88935053026706097029599349)
              ·
                refine ⟨8337661221253696596524939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88935053026706097029599349 8337661221253696596524939)
                ·
                  refine ⟨12506491831880544894787409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8337661221253696596524939 12506491831880544894787409)
                  ·
                    refine ⟨9379868873910408671090557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12506491831880544894787409 9379868873910408671090557)
                    ·
                      refine ⟨3517450827716403251658959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379868873910408671090557 3517450827716403251658959)
                      ·
                        rfl

theorem cell23_6850211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_6850211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850211 prefixEnd_6850211 := by exact prefixLift 6850211
  have htrace : WordTrace (prefixWord ++ tailWord_6850211) baseStart_6850211 baseEnd_6850211 := by
    simpa [prefixWord, tailWord_6850211, baseEnd_6850211] using wordTrace_append hprefix tailTrace_6850211
  have hstable : (prefixWord ++ tailWord_6850211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850211).length < 2 ^ (prefixWord ++ tailWord_6850211).sum := by decide
  have hdescent : baseEnd_6850211 < baseStart_6850211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850242 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6850242 : Nat := 118140960795 + 6850242 * 2 ^ 59
def prefixEnd_6850242 : Nat := 4983230072969 + 3 ^ 40 * 6850242 * 2
def baseEnd_6850242 : Nat := 3517466745616692630371317

theorem tailTrace_6850242 : CollatzResearch.WordTrace tailWord_6850242 prefixEnd_6850242 3517466745616692630371317 := by
  unfold tailWord_6850242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62462212912187659258992245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166565901099167091357312653 62462212912187659258992245)
  ·
    refine ⟨5855832460517593055530523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62462212912187659258992245 5855832460517593055530523)
    ·
      refine ⟨8783748690776389583295785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855832460517593055530523 8783748690776389583295785)
      ·
        refine ⟨6587811518082292187471839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8783748690776389583295785 6587811518082292187471839)
        ·
          refine ⟨9881717277123438281207759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587811518082292187471839 9881717277123438281207759)
          ·
            refine ⟨14822575915685157421811639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881717277123438281207759 14822575915685157421811639)
            ·
              refine ⟨22233863873527736132717459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14822575915685157421811639 22233863873527736132717459)
              ·
                refine ⟨33350795810291604199076189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22233863873527736132717459 33350795810291604199076189)
                ·
                  refine ⟨12506548428859351574653571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33350795810291604199076189 12506548428859351574653571)
                  ·
                    refine ⟨18759822643289027361980357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12506548428859351574653571 18759822643289027361980357)
                    ·
                      refine ⟨3517466745616692630371317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18759822643289027361980357 3517466745616692630371317)
                      ·
                        rfl

theorem cell23_6850242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6850242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850242 prefixEnd_6850242 := by exact prefixLift 6850242
  have htrace : WordTrace (prefixWord ++ tailWord_6850242) baseStart_6850242 baseEnd_6850242 := by
    simpa [prefixWord, tailWord_6850242, baseEnd_6850242] using wordTrace_append hprefix tailTrace_6850242
  have hstable : (prefixWord ++ tailWord_6850242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850242).length < 2 ^ (prefixWord ++ tailWord_6850242).sum := by decide
  have hdescent : baseEnd_6850242 < baseStart_6850242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850258 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6850258 : Nat := 118140960795 + 6850258 * 2 ^ 59
def prefixEnd_6850258 : Nat := 4983230072969 + 3 ^ 40 * 6850258 * 2
def baseEnd_6850258 : Nat := 3517474961307164567771243

theorem tailTrace_6850258 : CollatzResearch.WordTrace tailWord_6850258 prefixEnd_6850258 3517474961307164567771243 := by
  unfold tailWord_6850258
  simp only [CollatzResearch.WordTrace]
  refine ⟨62462358804173167942137857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166566290144461781179034285 62462358804173167942137857)
  ·
    refine ⟨46846769103129875956603393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62462358804173167942137857 46846769103129875956603393)
    ·
      refine ⟨35135076827347406967452545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46846769103129875956603393 35135076827347406967452545)
      ·
        refine ⟨26351307620510555225589409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35135076827347406967452545 26351307620510555225589409)
        ·
          refine ⟨19763480715382916419192057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26351307620510555225589409 19763480715382916419192057)
          ·
            refine ⟨14822610536537187314394043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19763480715382916419192057 14822610536537187314394043)
            ·
              refine ⟨22233915804805780971591065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14822610536537187314394043 22233915804805780971591065)
              ·
                refine ⟨16675436853604335728693299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22233915804805780971591065 16675436853604335728693299)
                ·
                  refine ⟨25013155280406503593039949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16675436853604335728693299 25013155280406503593039949)
                  ·
                    refine ⟨9379933230152438847389981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25013155280406503593039949 9379933230152438847389981)
                    ·
                      refine ⟨3517474961307164567771243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379933230152438847389981 3517474961307164567771243)
                      ·
                        rfl

theorem cell23_6850258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6850258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850258 prefixEnd_6850258 := by exact prefixLift 6850258
  have htrace : WordTrace (prefixWord ++ tailWord_6850258) baseStart_6850258 baseEnd_6850258 := by
    simpa [prefixWord, tailWord_6850258, baseEnd_6850258] using wordTrace_append hprefix tailTrace_6850258
  have hstable : (prefixWord ++ tailWord_6850258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850258).length < 2 ^ (prefixWord ++ tailWord_6850258).sum := by decide
  have hdescent : baseEnd_6850258 < baseStart_6850258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850262 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6850262 : Nat := 118140960795 + 6850262 * 2 ^ 59
def prefixEnd_6850262 : Nat := 4983230072969 + 3 ^ 40 * 6850262 * 2
def baseEnd_6850262 : Nat := 3517477015229782552121225

theorem tailTrace_6850262 : CollatzResearch.WordTrace tailWord_6850262 prefixEnd_6850262 3517477015229782552121225 := by
  unfold tailWord_6850262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15615598819292386278231065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166566387405785453634464693 15615598819292386278231065)
  ·
    refine ⟨11711699114469289708673299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15615598819292386278231065 11711699114469289708673299)
    ·
      refine ⟨17567548671703934563009949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711699114469289708673299 17567548671703934563009949)
      ·
        refine ⟨6587830751888975461128731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17567548671703934563009949 6587830751888975461128731)
        ·
          refine ⟨9881746127833463191693097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587830751888975461128731 9881746127833463191693097)
          ·
            refine ⟨7411309595875097393769823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881746127833463191693097 7411309595875097393769823)
            ·
              refine ⟨11116964393812646090654735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411309595875097393769823 11116964393812646090654735)
              ·
                refine ⟨16675446590718969135982103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116964393812646090654735 16675446590718969135982103)
                ·
                  refine ⟨25013169886078453703973155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16675446590718969135982103 25013169886078453703973155)
                  ·
                    refine ⟨37519754829117680555959733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25013169886078453703973155 37519754829117680555959733)
                    ·
                      refine ⟨3517477015229782552121225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37519754829117680555959733 3517477015229782552121225)
                      ·
                        rfl

theorem cell23_6850262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6850262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850262 prefixEnd_6850262 := by exact prefixLift 6850262
  have htrace : WordTrace (prefixWord ++ tailWord_6850262) baseStart_6850262 baseEnd_6850262 := by
    simpa [prefixWord, tailWord_6850262, baseEnd_6850262] using wordTrace_append hprefix tailTrace_6850262
  have hstable : (prefixWord ++ tailWord_6850262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850262).length < 2 ^ (prefixWord ++ tailWord_6850262).sum := by decide
  have hdescent : baseEnd_6850262 < baseStart_6850262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 4, 2]
def baseStart_6850281 : Nat := 118140960795 + 6850281 * 2 ^ 59
def prefixEnd_6850281 : Nat := 4983230072969 + 3 ^ 40 * 6850281 * 2
def baseEnd_6850281 : Nat := 3517486771362217977783637

theorem tailTrace_6850281 : CollatzResearch.WordTrace tailWord_6850281 prefixEnd_6850281 3517486771362217977783637 := by
  unfold tailWord_6850281
  simp only [CollatzResearch.WordTrace]
  refine ⟨249850274095609346696638697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166566849397072897797759131 249850274095609346696638697)
  ·
    refine ⟨187387705571707010022479023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249850274095609346696638697 187387705571707010022479023)
    ·
      refine ⟨281081558357560515033718535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187387705571707010022479023 281081558357560515033718535)
      ·
        refine ⟨421622337536340772550577803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281081558357560515033718535 421622337536340772550577803)
        ·
          refine ⟨632433506304511158825866705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421622337536340772550577803 632433506304511158825866705)
          ·
            refine ⟨474325129728383369119400029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632433506304511158825866705 474325129728383369119400029)
            ·
              refine ⟨177871923648143763419775011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474325129728383369119400029 177871923648143763419775011)
              ·
                refine ⟨266807885472215645129662517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177871923648143763419775011 266807885472215645129662517)
                ·
                  refine ⟨25013239263020216730905861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266807885472215645129662517 25013239263020216730905861)
                  ·
                    refine ⟨4689982361816290637044849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25013239263020216730905861 4689982361816290637044849)
                    ·
                      refine ⟨3517486771362217977783637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689982361816290637044849 3517486771362217977783637)
                      ·
                        rfl

theorem cell23_6850281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4, 2].length) (baseStart_6850281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850281 prefixEnd_6850281 := by exact prefixLift 6850281
  have htrace : WordTrace (prefixWord ++ tailWord_6850281) baseStart_6850281 baseEnd_6850281 := by
    simpa [prefixWord, tailWord_6850281, baseEnd_6850281] using wordTrace_append hprefix tailTrace_6850281
  have hstable : (prefixWord ++ tailWord_6850281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850281).length < 2 ^ (prefixWord ++ tailWord_6850281).sum := by decide
  have hdescent : baseEnd_6850281 < baseStart_6850281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850284 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_6850284 : Nat := 118140960795 + 6850284 * 2 ^ 59
def prefixEnd_6850284 : Nat := 4983230072969 + 3 ^ 40 * 6850284 * 2
def baseEnd_6850284 : Nat := 3517488311804181466046123

theorem tailTrace_6850284 : CollatzResearch.WordTrace tailWord_6850284 prefixEnd_6850284 3517488311804181466046123 := by
  unfold tailWord_6850284
  simp only [CollatzResearch.WordTrace]
  refine ⟨124925191757299239104498953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166566922343065652139331937 124925191757299239104498953)
  ·
    refine ⟨93693893817974429328374215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124925191757299239104498953 93693893817974429328374215)
    ·
      refine ⟨140540840726961643992561323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93693893817974429328374215 140540840726961643992561323)
      ·
        refine ⟨210811261090442465988841985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140540840726961643992561323 210811261090442465988841985)
        ·
          refine ⟨158108445817831849491631489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210811261090442465988841985 158108445817831849491631489)
          ·
            refine ⟨118581334363373887118723617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158108445817831849491631489 118581334363373887118723617)
            ·
              refine ⟨88936000772530415339042713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118581334363373887118723617 88936000772530415339042713)
              ·
                refine ⟨66702000579397811504282035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88936000772530415339042713 66702000579397811504282035)
                ·
                  refine ⟨100053000869096717256423053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66702000579397811504282035 100053000869096717256423053)
                  ·
                    refine ⟨37519875325911268971158645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100053000869096717256423053 37519875325911268971158645)
                    ·
                      refine ⟨3517488311804181466046123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37519875325911268971158645 3517488311804181466046123)
                      ·
                        rfl

theorem cell23_6850284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_6850284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850284 prefixEnd_6850284 := by exact prefixLift 6850284
  have htrace : WordTrace (prefixWord ++ tailWord_6850284) baseStart_6850284 baseEnd_6850284 := by
    simpa [prefixWord, tailWord_6850284, baseEnd_6850284] using wordTrace_append hprefix tailTrace_6850284
  have hstable : (prefixWord ++ tailWord_6850284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850284).length < 2 ^ (prefixWord ++ tailWord_6850284).sum := by decide
  have hdescent : baseEnd_6850284 < baseStart_6850284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850292 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6850292 : Nat := 118140960795 + 6850292 * 2 ^ 59
def prefixEnd_6850292 : Nat := 4983230072969 + 3 ^ 40 * 6850292 * 2
def baseEnd_6850292 : Nat := 3517492419649417434746087

theorem tailTrace_6850292 : CollatzResearch.WordTrace tailWord_6850292 prefixEnd_6850292 3517492419649417434746087 := by
  unfold tailWord_6850292
  simp only [CollatzResearch.WordTrace]
  refine ⟨124925337649284747787644565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166567116865712997050192753 124925337649284747787644565)
  ·
    refine ⟨5855875202310222552545839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124925337649284747787644565 5855875202310222552545839)
    ·
      refine ⟨8783812803465333828818759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855875202310222552545839 8783812803465333828818759)
      ·
        refine ⟨13175719205198000743228139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8783812803465333828818759 13175719205198000743228139)
        ·
          refine ⟨19763578807797001114842209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175719205198000743228139 19763578807797001114842209)
          ·
            refine ⟨14822684105847750836131657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19763578807797001114842209 14822684105847750836131657)
            ·
              refine ⟨11117013079385813127098743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14822684105847750836131657 11117013079385813127098743)
              ·
                refine ⟨16675519619078719690648115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11117013079385813127098743 16675519619078719690648115)
                ·
                  refine ⟨25013279428618079535972173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16675519619078719690648115 25013279428618079535972173)
                  ·
                    refine ⟨9379979785731779825989565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25013279428618079535972173 9379979785731779825989565)
                    ·
                      refine ⟨3517492419649417434746087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9379979785731779825989565 3517492419649417434746087)
                      ·
                        rfl

theorem cell23_6850292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6850292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850292 prefixEnd_6850292 := by exact prefixLift 6850292
  have htrace : WordTrace (prefixWord ++ tailWord_6850292) baseStart_6850292 baseEnd_6850292 := by
    simpa [prefixWord, tailWord_6850292, baseEnd_6850292] using wordTrace_append hprefix tailTrace_6850292
  have hstable : (prefixWord ++ tailWord_6850292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850292).length < 2 ^ (prefixWord ++ tailWord_6850292).sum := by decide
  have hdescent : baseEnd_6850292 < baseStart_6850292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850298 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_6850298 : Nat := 118140960795 + 6850298 * 2 ^ 59
def prefixEnd_6850298 : Nat := 4983230072969 + 3 ^ 40 * 6850298 * 2
def baseEnd_6850298 : Nat := 3517495500533344411271059

theorem tailTrace_6850298 : CollatzResearch.WordTrace tailWord_6850298 prefixEnd_6850298 3517495500533344411271059 := by
  unfold tailWord_6850298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62462723534136939650001887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166567262757698505733338365 62462723534136939650001887)
  ·
    refine ⟨93694085301205409475002831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62462723534136939650001887 93694085301205409475002831)
    ·
      refine ⟨140541127951808114212504247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93694085301205409475002831 140541127951808114212504247)
      ·
        refine ⟨210811691927712171318756371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140541127951808114212504247 210811691927712171318756371)
        ·
          refine ⟨316217537891568256978134557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210811691927712171318756371 316217537891568256978134557)
          ·
            refine ⟨118581576709338096366800459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316217537891568256978134557 118581576709338096366800459)
            ·
              refine ⟨177872365064007144550200689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118581576709338096366800459 177872365064007144550200689)
              ·
                refine ⟨133404273798005358412650517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177872365064007144550200689 133404273798005358412650517)
                ·
                  refine ⟨6253325334281501175592993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133404273798005358412650517 6253325334281501175592993)
                  ·
                    refine ⟨4689994000711125881694745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253325334281501175592993 4689994000711125881694745)
                    ·
                      refine ⟨3517495500533344411271059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4689994000711125881694745 3517495500533344411271059)
                      ·
                        rfl

theorem cell23_6850298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_6850298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850298 prefixEnd_6850298 := by exact prefixLift 6850298
  have htrace : WordTrace (prefixWord ++ tailWord_6850298) baseStart_6850298 baseEnd_6850298 := by
    simpa [prefixWord, tailWord_6850298, baseEnd_6850298] using wordTrace_append hprefix tailTrace_6850298
  have hstable : (prefixWord ++ tailWord_6850298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850298).length < 2 ^ (prefixWord ++ tailWord_6850298).sum := by decide
  have hdescent : baseEnd_6850298 < baseStart_6850298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850304 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 7]
def baseStart_6850304 : Nat := 118140960795 + 6850304 * 2 ^ 59
def prefixEnd_6850304 : Nat := 4983230072969 + 3 ^ 40 * 6850304 * 2
def baseEnd_6850304 : Nat := 390833175713030154199559

theorem tailTrace_6850304 : CollatzResearch.WordTrace tailWord_6850304 prefixEnd_6850304 390833175713030154199559 := by
  unfold tailWord_6850304
  simp only [CollatzResearch.WordTrace]
  refine ⟨124925556487263010812362983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166567408649684014416483977 124925556487263010812362983)
  ·
    refine ⟨187388334730894516218544475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124925556487263010812362983 187388334730894516218544475)
    ·
      refine ⟨281082502096341774327816713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187388334730894516218544475 281082502096341774327816713)
      ·
        refine ⟨210811876572256330745862535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281082502096341774327816713 210811876572256330745862535)
        ·
          refine ⟨316217814858384496118793803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210811876572256330745862535 316217814858384496118793803)
          ·
            refine ⟨474326722287576744178190705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316217814858384496118793803 474326722287576744178190705)
            ·
              refine ⟨355745041715682558133643029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474326722287576744178190705 355745041715682558133643029)
              ·
                refine ⟨16675548830422619912514517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355745041715682558133643029 16675548830422619912514517)
                ·
                  refine ⟨390833175713030154199559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16675548830422619912514517 390833175713030154199559)
                  ·
                    rfl

theorem cell23_6850304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_6850304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850304 prefixEnd_6850304 := by exact prefixLift 6850304
  have htrace : WordTrace (prefixWord ++ tailWord_6850304) baseStart_6850304 baseEnd_6850304 := by
    simpa [prefixWord, tailWord_6850304, baseEnd_6850304] using wordTrace_append hprefix tailTrace_6850304
  have hstable : (prefixWord ++ tailWord_6850304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850304).length < 2 ^ (prefixWord ++ tailWord_6850304).sum := by decide
  have hdescent : baseEnd_6850304 < baseStart_6850304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850310 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6850310 : Nat := 118140960795 + 6850310 * 2 ^ 59
def prefixEnd_6850310 : Nat := 4983230072969 + 3 ^ 40 * 6850310 * 2
def baseEnd_6850310 : Nat := 3517501662301198364321005

theorem tailTrace_6850310 : CollatzResearch.WordTrace tailWord_6850310 prefixEnd_6850310 3517501662301198364321005 := by
  unfold tailWord_6850310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807854119140758895295137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166567554541669523099629589 7807854119140758895295137)
  ·
    refine ⟨5855890589355569171471353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7807854119140758895295137 5855890589355569171471353)
    ·
      refine ⟨4391917942016676878603515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855890589355569171471353 4391917942016676878603515)
      ·
        refine ⟨6587876913025015317905273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391917942016676878603515 6587876913025015317905273)
        ·
          refine ⟨4940907684768761488428955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6587876913025015317905273 4940907684768761488428955)
          ·
            refine ⟨7411361527153142232643433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940907684768761488428955 7411361527153142232643433)
            ·
              refine ⟨5558521145364856674482575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411361527153142232643433 5558521145364856674482575)
              ·
                refine ⟨8337781718047285011723863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558521145364856674482575 8337781718047285011723863)
                ·
                  refine ⟨12506672577070927517585795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8337781718047285011723863 12506672577070927517585795)
                  ·
                    refine ⟨18760008865606391276378693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12506672577070927517585795 18760008865606391276378693)
                    ·
                      refine ⟨3517501662301198364321005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18760008865606391276378693 3517501662301198364321005)
                      ·
                        rfl

theorem cell23_6850310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6850310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850310 prefixEnd_6850310 := by exact prefixLift 6850310
  have htrace : WordTrace (prefixWord ++ tailWord_6850310) baseStart_6850310 baseEnd_6850310 := by
    simpa [prefixWord, tailWord_6850310, baseEnd_6850310] using wordTrace_append hprefix tailTrace_6850310
  have hstable : (prefixWord ++ tailWord_6850310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850310).length < 2 ^ (prefixWord ++ tailWord_6850310).sum := by decide
  have hdescent : baseEnd_6850310 < baseStart_6850310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850338 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_6850338 : Nat := 118140960795 + 6850338 * 2 ^ 59
def prefixEnd_6850338 : Nat := 4983230072969 + 3 ^ 40 * 6850338 * 2
def baseEnd_6850338 : Nat := 390835115528836028307875

theorem tailTrace_6850338 : CollatzResearch.WordTrace tailWord_6850338 prefixEnd_6850338 390835115528836028307875 := by
  unfold tailWord_6850338
  simp only [CollatzResearch.WordTrace]
  refine ⟨62463088264100711357865917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166568235370935230287642445 62463088264100711357865917)
  ·
    refine ⟨23423658099037766759199719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62463088264100711357865917 23423658099037766759199719)
    ·
      refine ⟨35135487148556650138799579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23423658099037766759199719 35135487148556650138799579)
      ·
        refine ⟨52703230722834975208199369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35135487148556650138799579 52703230722834975208199369)
        ·
          refine ⟨39527423042126231406149527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52703230722834975208199369 39527423042126231406149527)
          ·
            refine ⟨59291134563189347109224291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39527423042126231406149527 59291134563189347109224291)
            ·
              refine ⟨88936701844784020663836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59291134563189347109224291 88936701844784020663836437)
              ·
                refine ⟨4168907898974250968617333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88936701844784020663836437 4168907898974250968617333)
                ·
                  refine ⟨390835115528836028307875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168907898974250968617333 390835115528836028307875)
                  ·
                    rfl

theorem cell23_6850338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_6850338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850338 prefixEnd_6850338 := by exact prefixLift 6850338
  have htrace : WordTrace (prefixWord ++ tailWord_6850338) baseStart_6850338 baseEnd_6850338 := by
    simpa [prefixWord, tailWord_6850338, baseEnd_6850338] using wordTrace_append hprefix tailTrace_6850338
  have hstable : (prefixWord ++ tailWord_6850338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850338).length < 2 ^ (prefixWord ++ tailWord_6850338).sum := by decide
  have hdescent : baseEnd_6850338 < baseStart_6850338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850371 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_6850371 : Nat := 118140960795 + 6850371 * 2 ^ 59
def prefixEnd_6850371 : Nat := 4983230072969 + 3 ^ 40 * 6850371 * 2
def baseEnd_6850371 : Nat := 3517532984621122625658223

theorem tailTrace_6850371 : CollatzResearch.WordTrace tailWord_6850371 prefixEnd_6850371 3517532984621122625658223 := by
  unfold tailWord_6850371
  simp only [CollatzResearch.WordTrace]
  refine ⟨249853556665283292067414967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166569037776855528044943311 249853556665283292067414967)
  ·
    refine ⟨374780334997924938101122451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249853556665283292067414967 374780334997924938101122451)
    ·
      refine ⟨562170502496887407151683677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374780334997924938101122451 562170502496887407151683677)
      ·
        refine ⟨210813938436332777681881379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562170502496887407151683677 210813938436332777681881379)
        ·
          refine ⟨316220907654499166522822069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210813938436332777681881379 316220907654499166522822069)
          ·
            refine ⟨29645710092609296861514569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316220907654499166522822069 29645710092609296861514569)
            ·
              refine ⟨22234282569456972646135927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29645710092609296861514569 22234282569456972646135927)
              ·
                refine ⟨33351423854185458969203891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22234282569456972646135927 33351423854185458969203891)
                ·
                  refine ⟨50027135781278188453805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33351423854185458969203891 50027135781278188453805837)
                  ·
                    refine ⟨18760175917979320670177189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50027135781278188453805837 18760175917979320670177189)
                    ·
                      refine ⟨3517532984621122625658223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18760175917979320670177189 3517532984621122625658223)
                      ·
                        rfl

theorem cell23_6850371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_6850371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850371 prefixEnd_6850371 := by exact prefixLift 6850371
  have htrace : WordTrace (prefixWord ++ tailWord_6850371) baseStart_6850371 baseEnd_6850371 := by
    simpa [prefixWord, tailWord_6850371, baseEnd_6850371] using wordTrace_append hprefix tailTrace_6850371
  have hstable : (prefixWord ++ tailWord_6850371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850371).length < 2 ^ (prefixWord ++ tailWord_6850371).sum := by decide
  have hdescent : baseEnd_6850371 < baseStart_6850371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850388 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_6850388 : Nat := 118140960795 + 6850388 * 2 ^ 59
def prefixEnd_6850388 : Nat := 4983230072969 + 3 ^ 40 * 6850388 * 2
def baseEnd_6850388 : Nat := 3517541713792249059145645

theorem tailTrace_6850388 : CollatzResearch.WordTrace tailWord_6850388 prefixEnd_6850388 3517541713792249059145645 := by
  unfold tailWord_6850388
  simp only [CollatzResearch.WordTrace]
  refine ⟨124927088353110851985391909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166569451137481135980522545 124927088353110851985391909)
  ·
    refine ⟨23423829066208284747260983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124927088353110851985391909 23423829066208284747260983)
    ·
      refine ⟨35135743599312427120891475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23423829066208284747260983 35135743599312427120891475)
      ·
        refine ⟨52703615398968640681337213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35135743599312427120891475 52703615398968640681337213)
        ·
          refine ⟨19763855774613240255501455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52703615398968640681337213 19763855774613240255501455)
          ·
            refine ⟨29645783661919860383252183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19763855774613240255501455 29645783661919860383252183)
            ·
              refine ⟨44468675492879790574878275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29645783661919860383252183 44468675492879790574878275)
              ·
                refine ⟨66703013239319685862317413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44468675492879790574878275 66703013239319685862317413)
                ·
                  refine ⟨12506814982372441099184515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66703013239319685862317413 12506814982372441099184515)
                  ·
                    refine ⟨18760222473558661648776773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12506814982372441099184515 18760222473558661648776773)
                    ·
                      refine ⟨3517541713792249059145645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18760222473558661648776773 3517541713792249059145645)
                      ·
                        rfl

theorem cell23_6850388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_6850388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850388 prefixEnd_6850388 := by exact prefixLift 6850388
  have htrace : WordTrace (prefixWord ++ tailWord_6850388) baseStart_6850388 baseEnd_6850388 := by
    simpa [prefixWord, tailWord_6850388, baseEnd_6850388] using wordTrace_append hprefix tailTrace_6850388
  have hstable : (prefixWord ++ tailWord_6850388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850388).length < 2 ^ (prefixWord ++ tailWord_6850388).sum := by decide
  have hdescent : baseEnd_6850388 < baseStart_6850388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850408 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6850408 : Nat := 118140960795 + 6850408 * 2 ^ 59
def prefixEnd_6850408 : Nat := 4983230072969 + 3 ^ 40 * 6850408 * 2
def baseEnd_6850408 : Nat := 3517551983405338980895553

theorem tailTrace_6850408 : CollatzResearch.WordTrace tailWord_6850408 prefixEnd_6850408 3517551983405338980895553 := by
  unfold tailWord_6850408
  simp only [CollatzResearch.WordTrace]
  refine ⟨124927453083074623693255939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166569937444099498257674585 124927453083074623693255939)
  ·
    refine ⟨187391179624611935539883909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124927453083074623693255939 187391179624611935539883909)
    ·
      refine ⟨35135846179614737913728233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187391179624611935539883909 35135846179614737913728233)
      ·
        refine ⟨26351884634711053435296175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35135846179614737913728233 26351884634711053435296175)
        ·
          refine ⟨39527826952066580152944263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26351884634711053435296175 39527826952066580152944263)
          ·
            refine ⟨59291740428099870229416395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39527826952066580152944263 59291740428099870229416395)
            ·
              refine ⟨88937610642149805344124593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59291740428099870229416395 88937610642149805344124593)
              ·
                refine ⟨66703207981612354008093445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88937610642149805344124593 66703207981612354008093445)
                ·
                  refine ⟨12506851496552316376517521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66703207981612354008093445 12506851496552316376517521)
                  ·
                    refine ⟨9380138622414237282388141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12506851496552316376517521 9380138622414237282388141)
                    ·
                      refine ⟨3517551983405338980895553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9380138622414237282388141 3517551983405338980895553)
                      ·
                        rfl

theorem cell23_6850408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6850408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850408 prefixEnd_6850408 := by exact prefixLift 6850408
  have htrace : WordTrace (prefixWord ++ tailWord_6850408) baseStart_6850408 baseEnd_6850408 := by
    simpa [prefixWord, tailWord_6850408, baseEnd_6850408] using wordTrace_append hprefix tailTrace_6850408
  have hstable : (prefixWord ++ tailWord_6850408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850408).length < 2 ^ (prefixWord ++ tailWord_6850408).sum := by decide
  have hdescent : baseEnd_6850408 < baseStart_6850408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850422 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6850422 : Nat := 118140960795 + 6850422 * 2 ^ 59
def prefixEnd_6850422 : Nat := 4983230072969 + 3 ^ 40 * 6850422 * 2
def baseEnd_6850422 : Nat := 3517559172134501926120489

theorem tailTrace_6850422 : CollatzResearch.WordTrace tailWord_6850422 prefixEnd_6850422 3517559172134501926120489 := by
  unfold tailWord_6850422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15615963549256157986095095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166570277858732351851681013 15615963549256157986095095)
  ·
    refine ⟨23423945323884236979142643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15615963549256157986095095 23423945323884236979142643)
    ·
      refine ⟨35135917985826355468713965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23423945323884236979142643 35135917985826355468713965)
      ·
        refine ⟨13175969244684883300767737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35135917985826355468713965 13175969244684883300767737)
        ·
          refine ⟨9881976933513662475575803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13175969244684883300767737 9881976933513662475575803)
          ·
            refine ⟨14822965400270493713363705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881976933513662475575803 14822965400270493713363705)
            ·
              refine ⟨11117224050202870285022779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14822965400270493713363705 11117224050202870285022779)
              ·
                refine ⟨16675836075304305427534169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11117224050202870285022779 16675836075304305427534169)
                ·
                  refine ⟨12506877056478229070650627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16675836075304305427534169 12506877056478229070650627)
                  ·
                    refine ⟨18760315584717343605975941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12506877056478229070650627 18760315584717343605975941)
                    ·
                      refine ⟨3517559172134501926120489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18760315584717343605975941 3517559172134501926120489)
                      ·
                        rfl

theorem cell23_6850422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6850422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850422 prefixEnd_6850422 := by exact prefixLift 6850422
  have htrace : WordTrace (prefixWord ++ tailWord_6850422) baseStart_6850422 baseEnd_6850422 := by
    simpa [prefixWord, tailWord_6850422, baseEnd_6850422] using wordTrace_append hprefix tailTrace_6850422
  have hstable : (prefixWord ++ tailWord_6850422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850422).length < 2 ^ (prefixWord ++ tailWord_6850422).sum := by decide
  have hdescent : baseEnd_6850422 < baseStart_6850422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850458 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_6850458 : Nat := 118140960795 + 6850458 * 2 ^ 59
def prefixEnd_6850458 : Nat := 4983230072969 + 3 ^ 40 * 6850458 * 2
def baseEnd_6850458 : Nat := 1172525885812687928423441

theorem tailTrace_6850458 : CollatzResearch.WordTrace tailWord_6850458 prefixEnd_6850458 1172525885812687928423441 := by
  unfold tailWord_6850458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62464182453992026481458007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166571153210645403950554685 62464182453992026481458007)
  ·
    refine ⟨93696273680988039722187011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62464182453992026481458007 93696273680988039722187011)
    ·
      refine ⟨140544410521482059583280517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93696273680988039722187011 140544410521482059583280517)
      ·
        refine ⟨26352076972777886171865097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140544410521482059583280517 26352076972777886171865097)
        ·
          refine ⟨19764057729583414628898823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26352076972777886171865097 19764057729583414628898823)
          ·
            refine ⟨29646086594375121943348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19764057729583414628898823 29646086594375121943348235)
            ·
              refine ⟨44469129891562682915022353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29646086594375121943348235 44469129891562682915022353)
              ·
                refine ⟨33351847418672012186266765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44469129891562682915022353 33351847418672012186266765)
                ·
                  refine ⟨12506942782002004569850037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33351847418672012186266765 12506942782002004569850037)
                  ·
                    refine ⟨1172525885812687928423441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12506942782002004569850037 1172525885812687928423441)
                    ·
                      rfl

theorem cell23_6850458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_6850458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850458 prefixEnd_6850458 := by exact prefixLift 6850458
  have htrace : WordTrace (prefixWord ++ tailWord_6850458) baseStart_6850458 baseEnd_6850458 := by
    simpa [prefixWord, tailWord_6850458, baseEnd_6850458] using wordTrace_append hprefix tailTrace_6850458
  have hstable : (prefixWord ++ tailWord_6850458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850458).length < 2 ^ (prefixWord ++ tailWord_6850458).sum := by decide
  have hdescent : baseEnd_6850458 < baseStart_6850458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850488 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_6850488 : Nat := 118140960795 + 6850488 * 2 ^ 59
def prefixEnd_6850488 : Nat := 4983230072969 + 3 ^ 40 * 6850488 * 2
def baseEnd_6850488 : Nat := 1172531020619232889298395

theorem tailTrace_6850488 : CollatzResearch.WordTrace tailWord_6850488 prefixEnd_6850488 1172531020619232889298395 := by
  unfold tailWord_6850488
  simp only [CollatzResearch.WordTrace]
  refine ⟨124928912002929710524712059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166571882670572947366282745 124928912002929710524712059)
  ·
    refine ⟨187393368004394565787068089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124928912002929710524712059 187393368004394565787068089)
    ·
      refine ⟨140545026003295924340301067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187393368004394565787068089 140545026003295924340301067)
      ·
        refine ⟨210817539004943886510451601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140545026003295924340301067 210817539004943886510451601)
        ·
          refine ⟨158113154253707914882838701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210817539004943886510451601 158113154253707914882838701)
          ·
            refine ⟨59292432845140468081064513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158113154253707914882838701 59292432845140468081064513)
            ·
              refine ⟨44469324633855351060798385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59292432845140468081064513 44469324633855351060798385)
              ·
                refine ⟨33351993475391513295598789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44469324633855351060798385 33351993475391513295598789)
                ·
                  refine ⟨6253498776635908742924773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33351993475391513295598789 6253498776635908742924773)
                  ·
                    refine ⟨1172531020619232889298395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6253498776635908742924773 1172531020619232889298395)
                    ·
                      rfl

theorem cell23_6850488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_6850488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850488 prefixEnd_6850488 := by exact prefixLift 6850488
  have htrace : WordTrace (prefixWord ++ tailWord_6850488) baseStart_6850488 baseEnd_6850488 := by
    simpa [prefixWord, tailWord_6850488, baseEnd_6850488] using wordTrace_append hprefix tailTrace_6850488
  have hstable : (prefixWord ++ tailWord_6850488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850488).length < 2 ^ (prefixWord ++ tailWord_6850488).sum := by decide
  have hdescent : baseEnd_6850488 < baseStart_6850488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850492 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_6850492 : Nat := 118140960795 + 6850492 * 2 ^ 59
def prefixEnd_6850492 : Nat := 4983230072969 + 3 ^ 40 * 6850492 * 2
def baseEnd_6850492 : Nat := 1172531705260105550748389

theorem tailTrace_6850492 : CollatzResearch.WordTrace tailWord_6850492 prefixEnd_6850492 1172531705260105550748389 := by
  unfold tailWord_6850492
  simp only [CollatzResearch.WordTrace]
  refine ⟨124928984948922464866284865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166571979931896619821713153 124928984948922464866284865)
  ·
    refine ⟨93696738711691848649713649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124928984948922464866284865 93696738711691848649713649)
    ·
      refine ⟨70272554033768886487285237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93696738711691848649713649 70272554033768886487285237)
      ·
        refine ⟨6588051940665833108182991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70272554033768886487285237 6588051940665833108182991)
        ·
          refine ⟨9882077910998749662274487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588051940665833108182991 9882077910998749662274487)
          ·
            refine ⟨14823116866498124493411731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882077910998749662274487 14823116866498124493411731)
            ·
              refine ⟨22234675299747186740117597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14823116866498124493411731 22234675299747186740117597)
              ·
                refine ⟨8338003237405195027544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22234675299747186740117597 8338003237405195027544099)
                ·
                  refine ⟨12507004856107792541316149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338003237405195027544099 12507004856107792541316149)
                  ·
                    refine ⟨1172531705260105550748389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12507004856107792541316149 1172531705260105550748389)
                    ·
                      rfl

theorem cell23_6850492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_6850492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850492 prefixEnd_6850492 := by exact prefixLift 6850492
  have htrace : WordTrace (prefixWord ++ tailWord_6850492) baseStart_6850492 baseEnd_6850492 := by
    simpa [prefixWord, tailWord_6850492, baseEnd_6850492] using wordTrace_append hprefix tailTrace_6850492
  have hstable : (prefixWord ++ tailWord_6850492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850492).length < 2 ^ (prefixWord ++ tailWord_6850492).sum := by decide
  have hdescent : baseEnd_6850492 < baseStart_6850492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850495 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 5, 2, 2]
def baseStart_6850495 : Nat := 118140960795 + 6850495 * 2 ^ 59
def prefixEnd_6850495 : Nat := 4983230072969 + 3 ^ 40 * 6850495 * 2
def baseEnd_6850495 : Nat := 3517596656222280140507653

theorem tailTrace_6850495 : CollatzResearch.WordTrace tailWord_6850495 prefixEnd_6850495 3517596656222280140507653 := by
  unfold tailWord_6850495
  simp only [CollatzResearch.WordTrace]
  refine ⟨249858079316834061244928939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166572052877889374163285959 249858079316834061244928939)
  ·
    refine ⟨374787118975251091867393409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249858079316834061244928939 374787118975251091867393409)
    ·
      refine ⟨281090339231438318900545057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374787118975251091867393409 281090339231438318900545057)
      ·
        refine ⟨210817754423578739175408793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281090339231438318900545057 210817754423578739175408793)
        ·
          refine ⟨158113315817684054381556595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210817754423578739175408793 158113315817684054381556595)
          ·
            refine ⟨237169973726526081572334893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158113315817684054381556595 237169973726526081572334893)
            ·
              refine ⟨88938740147447280589625585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237169973726526081572334893 88938740147447280589625585)
              ·
                refine ⟨66704055110585460442219189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88938740147447280589625585 66704055110585460442219189)
                ·
                  refine ⟨6253505166617386916458049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66704055110585460442219189 6253505166617386916458049)
                  ·
                    refine ⟨4690128874963040187343537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253505166617386916458049 4690128874963040187343537)
                    ·
                      refine ⟨3517596656222280140507653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690128874963040187343537 3517596656222280140507653)
                      ·
                        rfl

theorem cell23_6850495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_6850495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850495 prefixEnd_6850495 := by exact prefixLift 6850495
  have htrace : WordTrace (prefixWord ++ tailWord_6850495) baseStart_6850495 baseEnd_6850495 := by
    simpa [prefixWord, tailWord_6850495, baseEnd_6850495] using wordTrace_append hprefix tailTrace_6850495
  have hstable : (prefixWord ++ tailWord_6850495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850495).length < 2 ^ (prefixWord ++ tailWord_6850495).sum := by decide
  have hdescent : baseEnd_6850495 < baseStart_6850495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850522 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_6850522 : Nat := 118140960795 + 6850522 * 2 ^ 59
def prefixEnd_6850522 : Nat := 4983230072969 + 3 ^ 40 * 6850522 * 2
def baseEnd_6850522 : Nat := 1172536840066650511623343

theorem tailTrace_6850522 : CollatzResearch.WordTrace tailWord_6850522 prefixEnd_6850522 1172536840066650511623343 := by
  unfold tailWord_6850522
  simp only [CollatzResearch.WordTrace]
  refine ⟨62464766021934061214040455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166572709391824163237441213 62464766021934061214040455)
  ·
    refine ⟨93697149032901091821060683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62464766021934061214040455 93697149032901091821060683)
    ·
      refine ⟨140545723549351637731591025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93697149032901091821060683 140545723549351637731591025)
      ·
        refine ⟨105409292662013728298693269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140545723549351637731591025 105409292662013728298693269)
        ·
          refine ⟨4941060593531893514001247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105409292662013728298693269 4941060593531893514001247)
          ·
            refine ⟨7411590890297840271001871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941060593531893514001247 7411590890297840271001871)
            ·
              refine ⟨11117386335446760406502807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411590890297840271001871 11117386335446760406502807)
              ·
                refine ⟨16676079503170140609754211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11117386335446760406502807 16676079503170140609754211)
                ·
                  refine ⟨25014119254755210914631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16676079503170140609754211 25014119254755210914631317)
                  ·
                    refine ⟨1172536840066650511623343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25014119254755210914631317 1172536840066650511623343)
                    ·
                      rfl

theorem cell23_6850522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_6850522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850522 prefixEnd_6850522 := by exact prefixLift 6850522
  have htrace : WordTrace (prefixWord ++ tailWord_6850522) baseStart_6850522 baseEnd_6850522 := by
    simpa [prefixWord, tailWord_6850522, baseEnd_6850522] using wordTrace_append hprefix tailTrace_6850522
  have hstable : (prefixWord ++ tailWord_6850522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850522).length < 2 ^ (prefixWord ++ tailWord_6850522).sum := by decide
  have hdescent : baseEnd_6850522 < baseStart_6850522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850525 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6850525 : Nat := 118140960795 + 6850525 * 2 ^ 59
def prefixEnd_6850525 : Nat := 4983230072969 + 3 ^ 40 * 6850525 * 2
def baseEnd_6850525 : Nat := 3517612060641915023132515

theorem tailTrace_6850525 : CollatzResearch.WordTrace tailWord_6850525 prefixEnd_6850525 3517612060641915023132515 := by
  unfold tailWord_6850525
  simp only [CollatzResearch.WordTrace]
  refine ⟨249859173506725376368521029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166572782337816917579014019 249859173506725376368521029)
  ·
    refine ⟨46848595032511008069097693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249859173506725376368521029 46848595032511008069097693)
    ·
      refine ⟨17568223137191628025911635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46848595032511008069097693 17568223137191628025911635)
      ·
        refine ⟨26352334705787442038867453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17568223137191628025911635 26352334705787442038867453)
        ·
          refine ⟨9882125514670290764575295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26352334705787442038867453 9882125514670290764575295)
          ·
            refine ⟨14823188272005436146862943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882125514670290764575295 14823188272005436146862943)
            ·
              refine ⟨22234782408008154220294415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14823188272005436146862943 22234782408008154220294415)
              ·
                refine ⟨33352173612012231330441623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22234782408008154220294415 33352173612012231330441623)
                ·
                  refine ⟨50028260418018346995662435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33352173612012231330441623 50028260418018346995662435)
                  ·
                    refine ⟨75042390627027520493493653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50028260418018346995662435 75042390627027520493493653)
                    ·
                      refine ⟨3517612060641915023132515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75042390627027520493493653 3517612060641915023132515)
                      ·
                        rfl

theorem cell23_6850525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6850525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850525 prefixEnd_6850525 := by exact prefixLift 6850525
  have htrace : WordTrace (prefixWord ++ tailWord_6850525) baseStart_6850525 baseEnd_6850525 := by
    simpa [prefixWord, tailWord_6850525, baseEnd_6850525] using wordTrace_append hprefix tailTrace_6850525
  have hstable : (prefixWord ++ tailWord_6850525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850525).length < 2 ^ (prefixWord ++ tailWord_6850525).sum := by decide
  have hdescent : baseEnd_6850525 < baseStart_6850525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850551 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_6850551 : Nat := 118140960795 + 6850551 * 2 ^ 59
def prefixEnd_6850551 : Nat := 4983230072969 + 3 ^ 40 * 6850551 * 2
def baseEnd_6850551 : Nat := 3517625411138931921407395

theorem tailTrace_6850551 : CollatzResearch.WordTrace tailWord_6850551 prefixEnd_6850551 3517625411138931921407395 := by
  unfold tailWord_6850551
  simp only [CollatzResearch.WordTrace]
  refine ⟨249860121804631182808967507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166573414536420788539311671 249860121804631182808967507)
  ·
    refine ⟨374790182706946774213451261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249860121804631182808967507 374790182706946774213451261)
    ·
      refine ⟨140546318515105040330044223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374790182706946774213451261 140546318515105040330044223)
      ·
        refine ⟨210819477772657560495066335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140546318515105040330044223 210819477772657560495066335)
        ·
          refine ⟨316229216658986340742599503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210819477772657560495066335 316229216658986340742599503)
          ·
            refine ⟨474343824988479511113899255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316229216658986340742599503 474343824988479511113899255)
            ·
              refine ⟨711515737482719266670848883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474343824988479511113899255 711515737482719266670848883)
              ·
                refine ⟨1067273606224078900006273325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711515737482719266670848883 1067273606224078900006273325)
                ·
                  refine ⟨400227602334029587502352497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067273606224078900006273325 400227602334029587502352497)
                  ·
                    refine ⟨300170701750522190626764373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 400227602334029587502352497 300170701750522190626764373)
                    ·
                      refine ⟨3517625411138931921407395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 300170701750522190626764373 3517625411138931921407395)
                      ·
                        rfl

theorem cell23_6850551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_6850551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850551 prefixEnd_6850551 := by exact prefixLift 6850551
  have htrace : WordTrace (prefixWord ++ tailWord_6850551) baseStart_6850551 baseEnd_6850551 := by
    simpa [prefixWord, tailWord_6850551, baseEnd_6850551] using wordTrace_append hprefix tailTrace_6850551
  have hstable : (prefixWord ++ tailWord_6850551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850551).length < 2 ^ (prefixWord ++ tailWord_6850551).sum := by decide
  have hdescent : baseEnd_6850551 < baseStart_6850551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850568 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6850568 : Nat := 118140960795 + 6850568 * 2 ^ 59
def prefixEnd_6850568 : Nat := 4983230072969 + 3 ^ 40 * 6850568 * 2
def baseEnd_6850568 : Nat := 3517634140310058354894817

theorem tailTrace_6850568 : CollatzResearch.WordTrace tailWord_6850568 prefixEnd_6850568 3517634140310058354894817 := by
  unfold tailWord_6850568
  simp only [CollatzResearch.WordTrace]
  refine ⟨124930370922784797356168179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166573827897046396474890905 124930370922784797356168179)
  ·
    refine ⟨187395556384177196034252269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124930370922784797356168179 187395556384177196034252269)
    ·
      refine ⟨70273333644066448512844601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187395556384177196034252269 70273333644066448512844601)
      ·
        refine ⟨52705000233049836384633451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70273333644066448512844601 52705000233049836384633451)
        ·
          refine ⟨79057500349574754576950177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52705000233049836384633451 79057500349574754576950177)
          ·
            refine ⟨59293125262181065932712633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79057500349574754576950177 59293125262181065932712633)
            ·
              refine ⟨44469843946635799449534475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59293125262181065932712633 44469843946635799449534475)
              ·
                refine ⟨66704765919953699174301713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44469843946635799449534475 66704765919953699174301713)
                ·
                  refine ⟨50028574439965274380726285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66704765919953699174301713 50028574439965274380726285)
                  ·
                    refine ⟨18760715414986977892772357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50028574439965274380726285 18760715414986977892772357)
                    ·
                      refine ⟨3517634140310058354894817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18760715414986977892772357 3517634140310058354894817)
                      ·
                        rfl

theorem cell23_6850568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6850568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850568 prefixEnd_6850568 := by exact prefixLift 6850568
  have htrace : WordTrace (prefixWord ++ tailWord_6850568) baseStart_6850568 baseEnd_6850568 := by
    simpa [prefixWord, tailWord_6850568, baseEnd_6850568] using wordTrace_append hprefix tailTrace_6850568
  have hstable : (prefixWord ++ tailWord_6850568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850568).length < 2 ^ (prefixWord ++ tailWord_6850568).sum := by decide
  have hdescent : baseEnd_6850568 < baseStart_6850568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850585 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 4, 2]
def baseStart_6850585 : Nat := 118140960795 + 6850585 * 2 ^ 59
def prefixEnd_6850585 : Nat := 4983230072969 + 3 ^ 40 * 6850585 * 2
def baseEnd_6850585 : Nat := 3517642869481184788382239

theorem tailTrace_6850585 : CollatzResearch.WordTrace tailWord_6850585 prefixEnd_6850585 3517642869481184788382239 := by
  unfold tailWord_6850585
  simp only [CollatzResearch.WordTrace]
  refine ⟨249861361886508006615705209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166574241257672004410470139 249861361886508006615705209)
  ·
    refine ⟨187396021414881004961778907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249861361886508006615705209 187396021414881004961778907)
    ·
      refine ⟨281094032122321507442668361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187396021414881004961778907 281094032122321507442668361)
      ·
        refine ⟨210820524091741130582001271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281094032122321507442668361 210820524091741130582001271)
        ·
          refine ⟨316230786137611695873001907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210820524091741130582001271 316230786137611695873001907)
          ·
            refine ⟨474346179206417543809502861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316230786137611695873001907 474346179206417543809502861)
            ·
              refine ⟨177879817202406578928563573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474346179206417543809502861 177879817202406578928563573)
              ·
                refine ⟨16676232862725616774552835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177879817202406578928563573 16676232862725616774552835)
                ·
                  refine ⟨25014349294088425161829253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16676232862725616774552835 25014349294088425161829253)
                  ·
                    refine ⟨4690190492641579717842985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25014349294088425161829253 4690190492641579717842985)
                    ·
                      refine ⟨3517642869481184788382239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690190492641579717842985 3517642869481184788382239)
                      ·
                        rfl

theorem cell23_6850585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_6850585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850585 prefixEnd_6850585 := by exact prefixLift 6850585
  have htrace : WordTrace (prefixWord ++ tailWord_6850585) baseStart_6850585 baseEnd_6850585 := by
    simpa [prefixWord, tailWord_6850585, baseEnd_6850585] using wordTrace_append hprefix tailTrace_6850585
  have hstable : (prefixWord ++ tailWord_6850585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850585).length < 2 ^ (prefixWord ++ tailWord_6850585).sum := by decide
  have hdescent : baseEnd_6850585 < baseStart_6850585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850589 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_6850589 : Nat := 118140960795 + 6850589 * 2 ^ 59
def prefixEnd_6850589 : Nat := 4983230072969 + 3 ^ 40 * 6850589 * 2
def baseEnd_6850589 : Nat := 3517644923403802772732221

theorem tailTrace_6850589 : CollatzResearch.WordTrace tailWord_6850589 prefixEnd_6850589 3517644923403802772732221 := by
  unfold tailWord_6850589
  simp only [CollatzResearch.WordTrace]
  refine ⟨249861507778493515298850821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166574338518995676865900547 249861507778493515298850821)
  ·
    refine ⟨46849032708467534118534529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249861507778493515298850821 46849032708467534118534529)
    ·
      refine ⟨35136774531350650588900897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46849032708467534118534529 35136774531350650588900897)
      ·
        refine ⟨26352580898512987941675673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35136774531350650588900897 26352580898512987941675673)
        ·
          refine ⟨19764435673884740956256755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26352580898512987941675673 19764435673884740956256755)
          ·
            refine ⟨29646653510827111434385133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19764435673884740956256755 29646653510827111434385133)
            ·
              refine ⟨11117495066560166787894425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29646653510827111434385133 11117495066560166787894425)
              ·
                refine ⟨8338121299920125090920819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11117495066560166787894425 8338121299920125090920819)
                ·
                  refine ⟨12507181949880187636381229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338121299920125090920819 12507181949880187636381229)
                  ·
                    refine ⟨4690193231205070363642961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12507181949880187636381229 4690193231205070363642961)
                    ·
                      refine ⟨3517644923403802772732221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690193231205070363642961 3517644923403802772732221)
                      ·
                        rfl

theorem cell23_6850589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_6850589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850589 prefixEnd_6850589 := by exact prefixLift 6850589
  have htrace : WordTrace (prefixWord ++ tailWord_6850589) baseStart_6850589 baseEnd_6850589 := by
    simpa [prefixWord, tailWord_6850589, baseEnd_6850589] using wordTrace_append hprefix tailTrace_6850589
  have hstable : (prefixWord ++ tailWord_6850589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850589).length < 2 ^ (prefixWord ++ tailWord_6850589).sum := by decide
  have hdescent : baseEnd_6850589 < baseStart_6850589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850602 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6850602 : Nat := 118140960795 + 6850602 * 2 ^ 59
def prefixEnd_6850602 : Nat := 4983230072969 + 3 ^ 40 * 6850602 * 2
def baseEnd_6850602 : Nat := 3517651598652311221869661

theorem tailTrace_6850602 : CollatzResearch.WordTrace tailWord_6850602 prefixEnd_6850602 3517651598652311221869661 := by
  unfold tailWord_6850602
  simp only [CollatzResearch.WordTrace]
  refine ⟨62465495481861604629768515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166574654618297612346049373 62465495481861604629768515)
  ·
    refine ⟨93698243222792406944652773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62465495481861604629768515 93698243222792406944652773)
    ·
      refine ⟨17568420604273576302122395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93698243222792406944652773 17568420604273576302122395)
      ·
        refine ⟨26352630906410364453183593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17568420604273576302122395 26352630906410364453183593)
        ·
          refine ⟨19764473179807773339887695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26352630906410364453183593 19764473179807773339887695)
          ·
            refine ⟨29646709769711660009831543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19764473179807773339887695 29646709769711660009831543)
            ·
              refine ⟨44470064654567490014747315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29646709769711660009831543 44470064654567490014747315)
              ·
                refine ⟨66705096981851235022120973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44470064654567490014747315 66705096981851235022120973)
                ·
                  refine ⟨25014411368194213133295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66705096981851235022120973 25014411368194213133295365)
                  ·
                    refine ⟨4690202131536414962492881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25014411368194213133295365 4690202131536414962492881)
                    ·
                      refine ⟨3517651598652311221869661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690202131536414962492881 3517651598652311221869661)
                      ·
                        rfl

theorem cell23_6850602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6850602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850602 prefixEnd_6850602 := by exact prefixLift 6850602
  have htrace : WordTrace (prefixWord ++ tailWord_6850602) baseStart_6850602 baseEnd_6850602 := by
    simpa [prefixWord, tailWord_6850602, baseEnd_6850602] using wordTrace_append hprefix tailTrace_6850602
  have hstable : (prefixWord ++ tailWord_6850602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850602).length < 2 ^ (prefixWord ++ tailWord_6850602).sum := by decide
  have hdescent : baseEnd_6850602 < baseStart_6850602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850606 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6850606 : Nat := 118140960795 + 6850606 * 2 ^ 59
def prefixEnd_6850606 : Nat := 4983230072969 + 3 ^ 40 * 6850606 * 2
def baseEnd_6850606 : Nat := 3517653652574929206219643

theorem tailTrace_6850606 : CollatzResearch.WordTrace tailWord_6850606 prefixEnd_6850606 3517653652574929206219643 := by
  unfold tailWord_6850606
  simp only [CollatzResearch.WordTrace]
  refine ⟨31232765977428990900277459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166574751879621284801479781 31232765977428990900277459)
  ·
    refine ⟨46849148966143486350416189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31232765977428990900277459 46849148966143486350416189)
    ·
      refine ⟨17568430862303807381406071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46849148966143486350416189 17568430862303807381406071)
      ·
        refine ⟨26352646293455711072109107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17568430862303807381406071 26352646293455711072109107)
        ·
          refine ⟨39528969440183566608163661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26352646293455711072109107 39528969440183566608163661)
          ·
            refine ⟨14823363540068837478061373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39528969440183566608163661 14823363540068837478061373)
            ·
              refine ⟨5558761327525814054273015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14823363540068837478061373 5558761327525814054273015)
              ·
                refine ⟨8338141991288721081409523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558761327525814054273015 8338141991288721081409523)
                ·
                  refine ⟨12507212986933081622114285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338141991288721081409523 12507212986933081622114285)
                  ·
                    refine ⟨4690204870099905608292857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12507212986933081622114285 4690204870099905608292857)
                    ·
                      refine ⟨3517653652574929206219643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690204870099905608292857 3517653652574929206219643)
                      ·
                        rfl

theorem cell23_6850606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6850606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850606 prefixEnd_6850606 := by exact prefixLift 6850606
  have htrace : WordTrace (prefixWord ++ tailWord_6850606) baseStart_6850606 baseEnd_6850606 := by
    simpa [prefixWord, tailWord_6850606, baseEnd_6850606] using wordTrace_append hprefix tailTrace_6850606
  have hstable : (prefixWord ++ tailWord_6850606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850606).length < 2 ^ (prefixWord ++ tailWord_6850606).sum := by decide
  have hdescent : baseEnd_6850606 < baseStart_6850606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850688 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_6850688 : Nat := 118140960795 + 6850688 * 2 ^ 59
def prefixEnd_6850688 : Nat := 4983230072969 + 3 ^ 40 * 6850688 * 2
def baseEnd_6850688 : Nat := 3517695757988597885394265

theorem tailTrace_6850688 : CollatzResearch.WordTrace tailWord_6850688 prefixEnd_6850688 3517695757988597885394265 := by
  unfold tailWord_6850688
  simp only [CollatzResearch.WordTrace]
  refine ⟨124932559302567427603352359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166576745736756570137803145 124932559302567427603352359)
  ·
    refine ⟨187398838953851141405028539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124932559302567427603352359 187398838953851141405028539)
    ·
      refine ⟨281098258430776712107542809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187398838953851141405028539 281098258430776712107542809)
      ·
        refine ⟨210823693823082534080657107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281098258430776712107542809 210823693823082534080657107)
        ·
          refine ⟨316235540734623801120985661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210823693823082534080657107 316235540734623801120985661)
          ·
            refine ⟨118588327775483925420369623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316235540734623801120985661 118588327775483925420369623)
            ·
              refine ⟨177882491663225888130554435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118588327775483925420369623 177882491663225888130554435)
              ·
                refine ⟨266823737494838832195831653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177882491663225888130554435 266823737494838832195831653)
                ·
                  refine ⟨50029450780282281036718435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266823737494838832195831653 50029450780282281036718435)
                  ·
                    refine ⟨75044176170423421555077653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50029450780282281036718435 75044176170423421555077653)
                    ·
                      refine ⟨3517695757988597885394265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75044176170423421555077653 3517695757988597885394265)
                      ·
                        rfl

theorem cell23_6850688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_6850688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850688 prefixEnd_6850688 := by exact prefixLift 6850688
  have htrace : WordTrace (prefixWord ++ tailWord_6850688) baseStart_6850688 baseEnd_6850688 := by
    simpa [prefixWord, tailWord_6850688, baseEnd_6850688] using wordTrace_append hprefix tailTrace_6850688
  have hstable : (prefixWord ++ tailWord_6850688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850688).length < 2 ^ (prefixWord ++ tailWord_6850688).sum := by decide
  have hdescent : baseEnd_6850688 < baseStart_6850688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850692 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6850692 : Nat := 118140960795 + 6850692 * 2 ^ 59
def prefixEnd_6850692 : Nat := 4983230072969 + 3 ^ 40 * 6850692 * 2
def baseEnd_6850692 : Nat := 3517697811911215869744247

theorem tailTrace_6850692 : CollatzResearch.WordTrace tailWord_6850692 prefixEnd_6850692 3517697811911215869744247 := by
  unfold tailWord_6850692
  simp only [CollatzResearch.WordTrace]
  refine ⟨124932632248560181944925165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166576842998080242593233553 124932632248560181944925165)
  ·
    refine ⟨46849737093210068229346937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124932632248560181944925165 46849737093210068229346937)
    ·
      refine ⟨35137302819907551172010203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46849737093210068229346937 35137302819907551172010203)
      ·
        refine ⟨52705954229861326758015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35137302819907551172010203 52705954229861326758015305)
        ·
          refine ⟨39529465672395995068511479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52705954229861326758015305 39529465672395995068511479)
          ·
            refine ⟨59294198508593992602767219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39529465672395995068511479 59294198508593992602767219)
            ·
              refine ⟨88941297762890988904150829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59294198508593992602767219 88941297762890988904150829)
              ·
                refine ⟨33352986661084120839056561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88941297762890988904150829 33352986661084120839056561)
                ·
                  refine ⟨25014739995813090629292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33352986661084120839056561 25014739995813090629292421)
                  ·
                    refine ⟨4690263749214954492992329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25014739995813090629292421 4690263749214954492992329)
                    ·
                      refine ⟨3517697811911215869744247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690263749214954492992329 3517697811911215869744247)
                      ·
                        rfl

theorem cell23_6850692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6850692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850692 prefixEnd_6850692 := by exact prefixLift 6850692
  have htrace : WordTrace (prefixWord ++ tailWord_6850692) baseStart_6850692 baseEnd_6850692 := by
    simpa [prefixWord, tailWord_6850692, baseEnd_6850692] using wordTrace_append hprefix tailTrace_6850692
  have hstable : (prefixWord ++ tailWord_6850692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850692).length < 2 ^ (prefixWord ++ tailWord_6850692).sum := by decide
  have hdescent : baseEnd_6850692 < baseStart_6850692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850695 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_6850695 : Nat := 118140960795 + 6850695 * 2 ^ 59
def prefixEnd_6850695 : Nat := 4983230072969 + 3 ^ 40 * 6850695 * 2
def baseEnd_6850695 : Nat := 3517699352353179358006733

theorem tailTrace_6850695 : CollatzResearch.WordTrace tailWord_6850695 prefixEnd_6850695 3517699352353179358006733 := by
  unfold tailWord_6850695
  simp only [CollatzResearch.WordTrace]
  refine ⟨249865373916109495402209539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166576915944072996934806359 249865373916109495402209539)
  ·
    refine ⟨374798060874164243103314309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249865373916109495402209539 374798060874164243103314309)
    ·
      refine ⟨70274636413905795581871433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374798060874164243103314309 70274636413905795581871433)
      ·
        refine ⟨52705977310429346686403575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70274636413905795581871433 52705977310429346686403575)
        ·
          refine ⟨79058965965644020029605363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52705977310429346686403575 79058965965644020029605363)
          ·
            refine ⟨118588448948466030044408045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79058965965644020029605363 118588448948466030044408045)
            ·
              refine ⟨44470668355674761266653017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118588448948466030044408045 44470668355674761266653017)
              ·
                refine ⟨33353001266756070949989763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44470668355674761266653017 33353001266756070949989763)
                ·
                  refine ⟨50029501900134106424984645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33353001266756070949989763 50029501900134106424984645)
                  ·
                    refine ⟨9380531606275144954684621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50029501900134106424984645 9380531606275144954684621)
                    ·
                      refine ⟨3517699352353179358006733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9380531606275144954684621 3517699352353179358006733)
                      ·
                        rfl

theorem cell23_6850695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_6850695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850695 prefixEnd_6850695 := by exact prefixLift 6850695
  have htrace : WordTrace (prefixWord ++ tailWord_6850695) baseStart_6850695 baseEnd_6850695 := by
    simpa [prefixWord, tailWord_6850695, baseEnd_6850695] using wordTrace_append hprefix tailTrace_6850695
  have hstable : (prefixWord ++ tailWord_6850695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850695).length < 2 ^ (prefixWord ++ tailWord_6850695).sum := by decide
  have hdescent : baseEnd_6850695 < baseStart_6850695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850745 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_6850745 : Nat := 118140960795 + 6850745 * 2 ^ 59
def prefixEnd_6850745 : Nat := 4983230072969 + 3 ^ 40 * 6850745 * 2
def baseEnd_6850745 : Nat := 1172575008795301387460501

theorem tailTrace_6850745 : CollatzResearch.WordTrace tailWord_6850745 prefixEnd_6850745 1172575008795301387460501 := by
  unfold tailWord_6850745
  simp only [CollatzResearch.WordTrace]
  refine ⟨249867197565928353941529689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166578131710618902627686459 249867197565928353941529689)
  ·
    refine ⟨187400398174446265456147267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249867197565928353941529689 187400398174446265456147267)
    ·
      refine ⟨281100597261669398184220901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187400398174446265456147267 281100597261669398184220901)
      ·
        refine ⟨52706361986563012159541419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281100597261669398184220901 52706361986563012159541419)
        ·
          refine ⟨79059542979844518239312129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52706361986563012159541419 79059542979844518239312129)
          ·
            refine ⟨59294657234883388679484097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79059542979844518239312129 59294657234883388679484097)
            ·
              refine ⟨44470992926162541509613073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59294657234883388679484097 44470992926162541509613073)
              ·
                refine ⟨33353244694621906132209805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44470992926162541509613073 33353244694621906132209805)
                ·
                  refine ⟨12507466760483214799578677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33353244694621906132209805 12507466760483214799578677)
                  ·
                    refine ⟨1172575008795301387460501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12507466760483214799578677 1172575008795301387460501)
                    ·
                      rfl

theorem cell23_6850745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_6850745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850745 prefixEnd_6850745 := by exact prefixLift 6850745
  have htrace : WordTrace (prefixWord ++ tailWord_6850745) baseStart_6850745 baseEnd_6850745 := by
    simpa [prefixWord, tailWord_6850745, baseEnd_6850745] using wordTrace_append hprefix tailTrace_6850745
  have hstable : (prefixWord ++ tailWord_6850745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850745).length < 2 ^ (prefixWord ++ tailWord_6850745).sum := by decide
  have hdescent : baseEnd_6850745 < baseStart_6850745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850795 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_6850795 : Nat := 118140960795 + 6850795 * 2 ^ 59
def prefixEnd_6850795 : Nat := 4983230072969 + 3 ^ 40 * 6850795 * 2
def baseEnd_6850795 : Nat := 3517750700418628966756273

theorem tailTrace_6850795 : CollatzResearch.WordTrace tailWord_6850795 prefixEnd_6850795 3517750700418628966756273 := by
  unfold tailWord_6850795
  simp only [CollatzResearch.WordTrace]
  refine ⟨249869021215747212480849839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166579347477164808320566559 249869021215747212480849839)
  ·
    refine ⟨374803531823620818721274759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249869021215747212480849839 374803531823620818721274759)
    ·
      refine ⟨562205297735431228081912139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374803531823620818721274759 562205297735431228081912139)
      ·
        refine ⟨843307946603146842122868209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562205297735431228081912139 843307946603146842122868209)
        ·
          refine ⟨632480959952360131592151157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843307946603146842122868209 632480959952360131592151157)
          ·
            refine ⟨59295089995533762336764171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 632480959952360131592151157 59295089995533762336764171)
            ·
              refine ⟨88942634993300643505146257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59295089995533762336764171 88942634993300643505146257)
              ·
                refine ⟨66706976244975482628859693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88942634993300643505146257 66706976244975482628859693)
                ·
                  refine ⟨25015116091865805985822385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66706976244975482628859693 25015116091865805985822385)
                  ·
                    refine ⟨18761337068899354489366789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25015116091865805985822385 18761337068899354489366789)
                    ·
                      refine ⟨3517750700418628966756273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18761337068899354489366789 3517750700418628966756273)
                      ·
                        rfl

theorem cell23_6850795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_6850795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850795 prefixEnd_6850795 := by exact prefixLift 6850795
  have htrace : WordTrace (prefixWord ++ tailWord_6850795) baseStart_6850795 baseEnd_6850795 := by
    simpa [prefixWord, tailWord_6850795, baseEnd_6850795] using wordTrace_append hprefix tailTrace_6850795
  have hstable : (prefixWord ++ tailWord_6850795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850795).length < 2 ^ (prefixWord ++ tailWord_6850795).sum := by decide
  have hdescent : baseEnd_6850795 < baseStart_6850795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850812 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_6850812 : Nat := 118140960795 + 6850812 * 2 ^ 59
def prefixEnd_6850812 : Nat := 4983230072969 + 3 ^ 40 * 6850812 * 2
def baseEnd_6850812 : Nat := 3517759429589755400243695

theorem tailTrace_6850812 : CollatzResearch.WordTrace tailWord_6850812 prefixEnd_6850812 3517759429589755400243695 := by
  unfold tailWord_6850812
  simp only [CollatzResearch.WordTrace]
  refine ⟨124934820628342812192109345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166579760837790416256145793 124934820628342812192109345)
  ·
    refine ⟨93701115471257109144082009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124934820628342812192109345 93701115471257109144082009)
    ·
      refine ⟨70275836603442831858061507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93701115471257109144082009 70275836603442831858061507)
      ·
        refine ⟨105413754905164247787092261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70275836603442831858061507 105413754905164247787092261)
        ·
          refine ⟨19765079044718296460079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105413754905164247787092261 19765079044718296460079799)
          ·
            refine ⟨29647618567077444690119699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19765079044718296460079799 29647618567077444690119699)
            ·
              refine ⟨44471427850616167035179549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29647618567077444690119699 44471427850616167035179549)
              ·
                refine ⟨16676785443981062638192331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44471427850616167035179549 16676785443981062638192331)
                ·
                  refine ⟨25015178165971593957288497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16676785443981062638192331 25015178165971593957288497)
                  ·
                    refine ⟨18761383624478695467966373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25015178165971593957288497 18761383624478695467966373)
                    ·
                      refine ⟨3517759429589755400243695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18761383624478695467966373 3517759429589755400243695)
                      ·
                        rfl

theorem cell23_6850812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_6850812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850812 prefixEnd_6850812 := by exact prefixLift 6850812
  have htrace : WordTrace (prefixWord ++ tailWord_6850812) baseStart_6850812 baseEnd_6850812 := by
    simpa [prefixWord, tailWord_6850812, baseEnd_6850812] using wordTrace_append hprefix tailTrace_6850812
  have hstable : (prefixWord ++ tailWord_6850812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850812).length < 2 ^ (prefixWord ++ tailWord_6850812).sum := by decide
  have hdescent : baseEnd_6850812 < baseStart_6850812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850833 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_6850833 : Nat := 118140960795 + 6850833 * 2 ^ 59
def prefixEnd_6850833 : Nat := 4983230072969 + 3 ^ 40 * 6850833 * 2
def baseEnd_6850833 : Nat := 3517770212683499818081099

theorem tailTrace_6850833 : CollatzResearch.WordTrace tailWord_6850833 prefixEnd_6850833 3517770212683499818081099 := by
  unfold tailWord_6850833
  simp only [CollatzResearch.WordTrace]
  refine ⟨249870407189609544970733153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166580271459739696647155435 249870407189609544970733153)
  ·
    refine ⟨187402805392207158728049865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249870407189609544970733153 187402805392207158728049865)
    ·
      refine ⟨140552104044155369046037399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187402805392207158728049865 140552104044155369046037399)
      ·
        refine ⟨210828156066233053569056099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140552104044155369046037399 210828156066233053569056099)
        ·
          refine ⟨316242234099349580353584149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210828156066233053569056099 316242234099349580353584149)
          ·
            refine ⟨14823854723407011579074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316242234099349580353584149 14823854723407011579074257)
            ·
              refine ⟨11117891042555258684305693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14823854723407011579074257 11117891042555258684305693)
              ·
                refine ⟨4169209140958222006614635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11117891042555258684305693 4169209140958222006614635)
                ·
                  refine ⟨6253813711437333009921953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169209140958222006614635 6253813711437333009921953)
                  ·
                    refine ⟨4690360283577999757441465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253813711437333009921953 4690360283577999757441465)
                    ·
                      refine ⟨3517770212683499818081099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690360283577999757441465 3517770212683499818081099)
                      ·
                        rfl

theorem cell23_6850833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_6850833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850833 prefixEnd_6850833 := by exact prefixLift 6850833
  have htrace : WordTrace (prefixWord ++ tailWord_6850833) baseStart_6850833 baseEnd_6850833 := by
    simpa [prefixWord, tailWord_6850833, baseEnd_6850833] using wordTrace_append hprefix tailTrace_6850833
  have hstable : (prefixWord ++ tailWord_6850833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850833).length < 2 ^ (prefixWord ++ tailWord_6850833).sum := by decide
  have hdescent : baseEnd_6850833 < baseStart_6850833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850866 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_6850866 : Nat := 118140960795 + 6850866 * 2 ^ 59
def prefixEnd_6850866 : Nat := 4983230072969 + 3 ^ 40 * 6850866 * 2
def baseEnd_6850866 : Nat := 3517787157545098188968447

theorem tailTrace_6850866 : CollatzResearch.WordTrace tailWord_6850866 prefixEnd_6850866 3517787157545098188968447 := by
  unfold tailWord_6850866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467902699622497901671113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166581073865659994404456301 62467902699622497901671113)
  ·
    refine ⟨46850927024716873426253335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62467902699622497901671113 46850927024716873426253335)
    ·
      refine ⟨70276390537075310139380003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46850927024716873426253335 70276390537075310139380003)
      ·
        refine ⟨105414585805612965209070005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70276390537075310139380003 105414585805612965209070005)
        ·
          refine ⟨9882617419276215488350313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105414585805612965209070005 9882617419276215488350313)
          ·
            refine ⟨7411963064457161616262735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9882617419276215488350313 7411963064457161616262735)
            ·
              refine ⟨11117944596685742424394103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411963064457161616262735 11117944596685742424394103)
              ·
                refine ⟨16676916895028613636591155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11117944596685742424394103 16676916895028613636591155)
                ·
                  refine ⟨25015375342542920454886733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16676916895028613636591155 25015375342542920454886733)
                  ·
                    refine ⟨9380765753453595170582525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25015375342542920454886733 9380765753453595170582525)
                    ·
                      refine ⟨3517787157545098188968447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9380765753453595170582525 3517787157545098188968447)
                      ·
                        rfl

theorem cell23_6850866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_6850866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850866 prefixEnd_6850866 := by exact prefixLift 6850866
  have htrace : WordTrace (prefixWord ++ tailWord_6850866) baseStart_6850866 baseEnd_6850866 := by
    simpa [prefixWord, tailWord_6850866, baseEnd_6850866] using wordTrace_append hprefix tailTrace_6850866
  have hstable : (prefixWord ++ tailWord_6850866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850866).length < 2 ^ (prefixWord ++ tailWord_6850866).sum := by decide
  have hdescent : baseEnd_6850866 < baseStart_6850866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850876 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_6850876 : Nat := 118140960795 + 6850876 * 2 ^ 59
def prefixEnd_6850876 : Nat := 4983230072969 + 3 ^ 40 * 6850876 * 2
def baseEnd_6850876 : Nat := 3517792292351643149843401

theorem tailTrace_6850876 : CollatzResearch.WordTrace tailWord_6850876 prefixEnd_6850876 3517792292351643149843401 := by
  unfold tailWord_6850876
  simp only [CollatzResearch.WordTrace]
  refine ⟨124935987764226881657274241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166581317018969175543032321 124935987764226881657274241)
  ·
    refine ⟨93701990823170161242955681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124935987764226881657274241 93701990823170161242955681)
    ·
      refine ⟨70276493117377620932216761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93701990823170161242955681 70276493117377620932216761)
      ·
        refine ⟨52707369838033215699162571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70276493117377620932216761 52707369838033215699162571)
        ·
          refine ⟨79061054757049823548743857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52707369838033215699162571 79061054757049823548743857)
          ·
            refine ⟨59295791067787367661557893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79061054757049823548743857 59295791067787367661557893)
            ·
              refine ⟨11117960825210131436542105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59295791067787367661557893 11117960825210131436542105)
              ·
                refine ⟨8338470618907598577406579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11117960825210131436542105 8338470618907598577406579)
                ·
                  refine ⟨12507705928361397866109869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338470618907598577406579 12507705928361397866109869)
                  ·
                    refine ⟨4690389723135524199791201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12507705928361397866109869 4690389723135524199791201)
                    ·
                      refine ⟨3517792292351643149843401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690389723135524199791201 3517792292351643149843401)
                      ·
                        rfl

theorem cell23_6850876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_6850876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850876 prefixEnd_6850876 := by exact prefixLift 6850876
  have htrace : WordTrace (prefixWord ++ tailWord_6850876) baseStart_6850876 baseEnd_6850876 := by
    simpa [prefixWord, tailWord_6850876, baseEnd_6850876] using wordTrace_append hprefix tailTrace_6850876
  have hstable : (prefixWord ++ tailWord_6850876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850876).length < 2 ^ (prefixWord ++ tailWord_6850876).sum := by decide
  have hdescent : baseEnd_6850876 < baseStart_6850876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850884 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6850884 : Nat := 118140960795 + 6850884 * 2 ^ 59
def prefixEnd_6850884 : Nat := 4983230072969 + 3 ^ 40 * 6850884 * 2
def baseEnd_6850884 : Nat := 3517796400196879118543365

theorem tailTrace_6850884 : CollatzResearch.WordTrace tailWord_6850884 prefixEnd_6850884 3517796400196879118543365 := by
  unfold tailWord_6850884
  simp only [CollatzResearch.WordTrace]
  refine ⟨124936133656212390340419853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166581511541616520453893137 124936133656212390340419853)
  ·
    refine ⟨46851050121079646377657445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124936133656212390340419853 46851050121079646377657445)
    ·
      refine ⟨8784571897702433695810771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46851050121079646377657445 8784571897702433695810771)
      ·
        refine ⟨13176857846553650543716157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8784571897702433695810771 13176857846553650543716157)
        ·
          refine ⟨4941321692457618953893559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13176857846553650543716157 4941321692457618953893559)
          ·
            refine ⟨7411982538686428430840339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941321692457618953893559 7411982538686428430840339)
            ·
              refine ⟨11117973808029642646260509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411982538686428430840339 11117973808029642646260509)
              ·
                refine ⟨4169240178011115992347691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11117973808029642646260509 4169240178011115992347691)
                ·
                  refine ⟨6253860267016673988521537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169240178011115992347691 6253860267016673988521537)
                  ·
                    refine ⟨4690395200262505491391153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253860267016673988521537 4690395200262505491391153)
                    ·
                      refine ⟨3517796400196879118543365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690395200262505491391153 3517796400196879118543365)
                      ·
                        rfl

theorem cell23_6850884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6850884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850884 prefixEnd_6850884 := by exact prefixLift 6850884
  have htrace : WordTrace (prefixWord ++ tailWord_6850884) baseStart_6850884 baseEnd_6850884 := by
    simpa [prefixWord, tailWord_6850884, baseEnd_6850884] using wordTrace_append hprefix tailTrace_6850884
  have hstable : (prefixWord ++ tailWord_6850884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850884).length < 2 ^ (prefixWord ++ tailWord_6850884).sum := by decide
  have hdescent : baseEnd_6850884 < baseStart_6850884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850892 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6850892 : Nat := 118140960795 + 6850892 * 2 ^ 59
def prefixEnd_6850892 : Nat := 4983230072969 + 3 ^ 40 * 6850892 * 2
def baseEnd_6850892 : Nat := 3517800508042115087243327

theorem tailTrace_6850892 : CollatzResearch.WordTrace tailWord_6850892 prefixEnd_6850892 3517800508042115087243327 := by
  unfold tailWord_6850892
  simp only [CollatzResearch.WordTrace]
  refine ⟨124936279548197899023565465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166581706064263865364753953 124936279548197899023565465)
  ·
    refine ⟨93702209661148424267674099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124936279548197899023565465 93702209661148424267674099)
    ·
      refine ⟨140553314491722636401511149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93702209661148424267674099 140553314491722636401511149)
      ·
        refine ⟨52707492934395988650566681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140553314491722636401511149 52707492934395988650566681)
        ·
          refine ⟨39530619700796991487925011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52707492934395988650566681 39530619700796991487925011)
          ·
            refine ⟨59295929551195487231887517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39530619700796991487925011 59295929551195487231887517)
            ·
              refine ⟨22235973581698307711957819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59295929551195487231887517 22235973581698307711957819)
              ·
                refine ⟨33353960372547461567936729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22235973581698307711957819 33353960372547461567936729)
                ·
                  refine ⟨25015470279410596175952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33353960372547461567936729 25015470279410596175952547)
                  ·
                    refine ⟨37523205419115894263928821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25015470279410596175952547 37523205419115894263928821)
                    ·
                      refine ⟨3517800508042115087243327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37523205419115894263928821 3517800508042115087243327)
                      ·
                        rfl

theorem cell23_6850892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6850892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850892 prefixEnd_6850892 := by exact prefixLift 6850892
  have htrace : WordTrace (prefixWord ++ tailWord_6850892) baseStart_6850892 baseEnd_6850892 := by
    simpa [prefixWord, tailWord_6850892, baseEnd_6850892] using wordTrace_append hprefix tailTrace_6850892
  have hstable : (prefixWord ++ tailWord_6850892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850892).length < 2 ^ (prefixWord ++ tailWord_6850892).sum := by decide
  have hdescent : baseEnd_6850892 < baseStart_6850892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6850905 : Nat := 118140960795 + 6850905 * 2 ^ 59
def prefixEnd_6850905 : Nat := 4983230072969 + 3 ^ 40 * 6850905 * 2
def baseEnd_6850905 : Nat := 3517807183290623536380767

theorem tailTrace_6850905 : CollatzResearch.WordTrace tailWord_6850905 prefixEnd_6850905 3517807183290623536380767 := by
  unfold tailWord_6850905
  simp only [CollatzResearch.WordTrace]
  refine ⟨249873033245348701267354169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166582022163565800844902779 249873033245348701267354169)
  ·
    refine ⟨187404774934011525950515627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249873033245348701267354169 187404774934011525950515627)
    ·
      refine ⟨281107162401017288925773441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187404774934011525950515627 281107162401017288925773441)
      ·
        refine ⟨210830371800762966694330081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281107162401017288925773441 210830371800762966694330081)
        ·
          refine ⟨158122778850572225020747561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210830371800762966694330081 158122778850572225020747561)
          ·
            refine ⟨118592084137929168765560671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158122778850572225020747561 118592084137929168765560671)
            ·
              refine ⟨177888126206893753148341007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118592084137929168765560671 177888126206893753148341007)
              ·
                refine ⟨266832189310340629722511511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177888126206893753148341007 266832189310340629722511511)
                ·
                  refine ⟨400248283965510944583767267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266832189310340629722511511 400248283965510944583767267)
                  ·
                    refine ⟨600372425948266416875650901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 400248283965510944583767267 600372425948266416875650901)
                    ·
                      refine ⟨3517807183290623536380767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 600372425948266416875650901 3517807183290623536380767)
                      ·
                        rfl

theorem cell23_6850905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6850905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850905 prefixEnd_6850905 := by exact prefixLift 6850905
  have htrace : WordTrace (prefixWord ++ tailWord_6850905) baseStart_6850905 baseEnd_6850905 := by
    simpa [prefixWord, tailWord_6850905, baseEnd_6850905] using wordTrace_append hprefix tailTrace_6850905
  have hstable : (prefixWord ++ tailWord_6850905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850905).length < 2 ^ (prefixWord ++ tailWord_6850905).sum := by decide
  have hdescent : baseEnd_6850905 < baseStart_6850905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850906 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_6850906 : Nat := 118140960795 + 6850906 * 2 ^ 59
def prefixEnd_6850906 : Nat := 4983230072969 + 3 ^ 40 * 6850906 * 2
def baseEnd_6850906 : Nat := 3517807696771278032468263

theorem tailTrace_6850906 : CollatzResearch.WordTrace tailWord_6850906 prefixEnd_6850906 3517807696771278032468263 := by
  unfold tailWord_6850906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62468267429586269609535143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166582046478896718958760381 62468267429586269609535143)
  ·
    refine ⟨93702401144379404414302715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62468267429586269609535143 93702401144379404414302715)
    ·
      refine ⟨140553601716569106621454073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93702401144379404414302715 140553601716569106621454073)
      ·
        refine ⟨105415201287426829966090555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140553601716569106621454073 105415201287426829966090555)
        ·
          refine ⟨158122801931140244949135833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105415201287426829966090555 158122801931140244949135833)
          ·
            refine ⟨118592101448355183711851875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158122801931140244949135833 118592101448355183711851875)
            ·
              refine ⟨177888152172532775567777813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118592101448355183711851875 177888152172532775567777813)
              ·
                refine ⟨8338507133087473854739585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177888152172532775567777813 8338507133087473854739585)
                ·
                  refine ⟨6253880349815605391054689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8338507133087473854739585 6253880349815605391054689)
                  ·
                    refine ⟨4690410262361704043291017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253880349815605391054689 4690410262361704043291017)
                    ·
                      refine ⟨3517807696771278032468263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690410262361704043291017 3517807696771278032468263)
                      ·
                        rfl

theorem cell23_6850906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_6850906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850906 prefixEnd_6850906 := by exact prefixLift 6850906
  have htrace : WordTrace (prefixWord ++ tailWord_6850906) baseStart_6850906 baseEnd_6850906 := by
    simpa [prefixWord, tailWord_6850906, baseEnd_6850906] using wordTrace_append hprefix tailTrace_6850906
  have hstable : (prefixWord ++ tailWord_6850906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850906).length < 2 ^ (prefixWord ++ tailWord_6850906).sum := by decide
  have hdescent : baseEnd_6850906 < baseStart_6850906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850952 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6850952 : Nat := 118140960795 + 6850952 * 2 ^ 59
def prefixEnd_6850952 : Nat := 4983230072969 + 3 ^ 40 * 6850952 * 2
def baseEnd_6850952 : Nat := 3517831316881384852493051

theorem tailTrace_6850952 : CollatzResearch.WordTrace tailWord_6850952 prefixEnd_6850952 3517831316881384852493051 := by
  unfold tailWord_6850952
  simp only [CollatzResearch.WordTrace]
  refine ⟨124937373738089214147157555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166583164984118952196210073 124937373738089214147157555)
  ·
    refine ⟨187406060607133821220736333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124937373738089214147157555 187406060607133821220736333)
    ·
      refine ⟨70277272727675182957776125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187406060607133821220736333 70277272727675182957776125)
      ·
        refine ⟨26353977272878193609166047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70277272727675182957776125 26353977272878193609166047)
        ·
          refine ⟨39530965909317290413749071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26353977272878193609166047 39530965909317290413749071)
          ·
            refine ⟨59296448863975935620623607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39530965909317290413749071 59296448863975935620623607)
            ·
              refine ⟨88944673295963903430935411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59296448863975935620623607 88944673295963903430935411)
              ·
                refine ⟨133417009943945855146403117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88944673295963903430935411 133417009943945855146403117)
                ·
                  refine ⟨50031378728979695679901169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133417009943945855146403117 50031378728979695679901169)
                  ·
                    refine ⟨37523534046734771759925877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50031378728979695679901169 37523534046734771759925877)
                    ·
                      refine ⟨3517831316881384852493051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37523534046734771759925877 3517831316881384852493051)
                      ·
                        rfl

theorem cell23_6850952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6850952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850952 prefixEnd_6850952 := by exact prefixLift 6850952
  have htrace : WordTrace (prefixWord ++ tailWord_6850952) baseStart_6850952 baseEnd_6850952 := by
    simpa [prefixWord, tailWord_6850952, baseEnd_6850952] using wordTrace_append hprefix tailTrace_6850952
  have hstable : (prefixWord ++ tailWord_6850952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850952).length < 2 ^ (prefixWord ++ tailWord_6850952).sum := by decide
  have hdescent : baseEnd_6850952 < baseStart_6850952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850979 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 6, 2]
def baseStart_6850979 : Nat := 118140960795 + 6850979 * 2 ^ 59
def prefixEnd_6850979 : Nat := 4983230072969 + 3 ^ 40 * 6850979 * 2
def baseEnd_6850979 : Nat := 3517845180859056246855427

theorem tailTrace_6850979 : CollatzResearch.WordTrace tailWord_6850979 prefixEnd_6850979 3517845180859056246855427 := by
  unfold tailWord_6850979
  simp only [CollatzResearch.WordTrace]
  refine ⟨249875732247080611905547991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166583821498053741270365327 249875732247080611905547991)
  ·
    refine ⟨374813598370620917858321987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249875732247080611905547991 374813598370620917858321987)
    ·
      refine ⟨562220397555931376787482981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374813598370620917858321987 562220397555931376787482981)
      ·
        refine ⟨105416324541737133147653059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 562220397555931376787482981 105416324541737133147653059)
        ·
          refine ⟨158124486812605699721479589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105416324541737133147653059 158124486812605699721479589)
          ·
            refine ⟨29648341277363568697777423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158124486812605699721479589 29648341277363568697777423)
            ·
              refine ⟨44472511916045353046666135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29648341277363568697777423 44472511916045353046666135)
              ·
                refine ⟨66708767874068029569999203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44472511916045353046666135 66708767874068029569999203)
                ·
                  refine ⟨100063151811102044354998805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66708767874068029569999203 100063151811102044354998805)
                  ·
                    refine ⟨4690460241145408329140569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100063151811102044354998805 4690460241145408329140569)
                    ·
                      refine ⟨3517845180859056246855427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690460241145408329140569 3517845180859056246855427)
                      ·
                        rfl

theorem cell23_6850979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_6850979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850979 prefixEnd_6850979 := by exact prefixLift 6850979
  have htrace : WordTrace (prefixWord ++ tailWord_6850979) baseStart_6850979 baseEnd_6850979 := by
    simpa [prefixWord, tailWord_6850979, baseEnd_6850979] using wordTrace_append hprefix tailTrace_6850979
  have hstable : (prefixWord ++ tailWord_6850979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850979).length < 2 ^ (prefixWord ++ tailWord_6850979).sum := by decide
  have hdescent : baseEnd_6850979 < baseStart_6850979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6850999 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_6850999 : Nat := 118140960795 + 6850999 * 2 ^ 59
def prefixEnd_6850999 : Nat := 4983230072969 + 3 ^ 40 * 6850999 * 2
def baseEnd_6850999 : Nat := 3517855450472146168605335

theorem tailTrace_6850999 : CollatzResearch.WordTrace tailWord_6850999 prefixEnd_6850999 3517855450472146168605335 := by
  unfold tailWord_6850999
  simp only [CollatzResearch.WordTrace]
  refine ⟨249876461707008155321276051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166584307804672103547517367 249876461707008155321276051)
  ·
    refine ⟨374814692560512232981914077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249876461707008155321276051 374814692560512232981914077)
    ·
      refine ⟨140555509710192087368217779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374814692560512232981914077 140555509710192087368217779)
      ·
        refine ⟨210833264565288131052326669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140555509710192087368217779 210833264565288131052326669)
        ·
          refine ⟨79062474211983049144622501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210833264565288131052326669 79062474211983049144622501)
          ·
            refine ⟨14824213914746821714616719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79062474211983049144622501 14824213914746821714616719)
            ·
              refine ⟨22236320872120232571925079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14824213914746821714616719 22236320872120232571925079)
              ·
                refine ⟨33354481308180348857887619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22236320872120232571925079 33354481308180348857887619)
                ·
                  refine ⟨50031721962270523286831429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33354481308180348857887619 50031721962270523286831429)
                  ·
                    refine ⟨9380947867925723116280893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50031721962270523286831429 9380947867925723116280893)
                    ·
                      refine ⟨3517855450472146168605335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9380947867925723116280893 3517855450472146168605335)
                      ·
                        rfl

theorem cell23_6850999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_6850999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6850999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6850999 prefixEnd_6850999 := by exact prefixLift 6850999
  have htrace : WordTrace (prefixWord ++ tailWord_6850999) baseStart_6850999 baseEnd_6850999 := by
    simpa [prefixWord, tailWord_6850999, baseEnd_6850999] using wordTrace_append hprefix tailTrace_6850999
  have hstable : (prefixWord ++ tailWord_6850999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6850999).length < 2 ^ (prefixWord ++ tailWord_6850999).sum := by decide
  have hdescent : baseEnd_6850999 < baseStart_6850999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6850999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851056 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2]
def baseStart_6851056 : Nat := 118140960795 + 6851056 * 2 ^ 59
def prefixEnd_6851056 : Nat := 4983230072969 + 3 ^ 40 * 6851056 * 2
def baseEnd_6851056 : Nat := 3517884718869452445592573

theorem tailTrace_6851056 : CollatzResearch.WordTrace tailWord_6851056 prefixEnd_6851056 3517884718869452445592573 := by
  unfold tailWord_6851056
  simp only [CollatzResearch.WordTrace]
  refine ⟨124939270333900827028050511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166585693778534436037400681 124939270333900827028050511)
  ·
    refine ⟨187408905500851240542075767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124939270333900827028050511 187408905500851240542075767)
    ·
      refine ⟨281113358251276860813113651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187408905500851240542075767 281113358251276860813113651)
      ·
        refine ⟨421670037376915291219670477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281113358251276860813113651 421670037376915291219670477)
        ·
          refine ⟨158126264016343234207376429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421670037376915291219670477 158126264016343234207376429)
          ·
            refine ⟨59297349006128712827766161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158126264016343234207376429 59297349006128712827766161)
            ·
              refine ⟨44473011754596534620824621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59297349006128712827766161 44473011754596534620824621)
              ·
                refine ⟨16677379407973700482809233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44473011754596534620824621 16677379407973700482809233)
                ·
                  refine ⟨12508034555980275362106925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16677379407973700482809233 12508034555980275362106925)
                  ·
                    refine ⟨4690512958492603260790097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12508034555980275362106925 4690512958492603260790097)
                    ·
                      refine ⟨3517884718869452445592573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690512958492603260790097 3517884718869452445592573)
                      ·
                        rfl

theorem cell23_6851056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2].length) (baseStart_6851056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851056 prefixEnd_6851056 := by exact prefixLift 6851056
  have htrace : WordTrace (prefixWord ++ tailWord_6851056) baseStart_6851056 baseEnd_6851056 := by
    simpa [prefixWord, tailWord_6851056, baseEnd_6851056] using wordTrace_append hprefix tailTrace_6851056
  have hstable : (prefixWord ++ tailWord_6851056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851056).length < 2 ^ (prefixWord ++ tailWord_6851056).sum := by decide
  have hdescent : baseEnd_6851056 < baseStart_6851056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851073 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_6851073 : Nat := 118140960795 + 6851073 * 2 ^ 59
def prefixEnd_6851073 : Nat := 4983230072969 + 3 ^ 40 * 6851073 * 2
def baseEnd_6851073 : Nat := 3517893448040578879079995

theorem tailTrace_6851073 : CollatzResearch.WordTrace tailWord_6851073 prefixEnd_6851073 3517893448040578879079995 := by
  unfold tailWord_6851073
  simp only [CollatzResearch.WordTrace]
  refine ⟨249879160708740065959469873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166586107139160043972979915 249879160708740065959469873)
  ·
    refine ⟨187409370531555049469602405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249879160708740065959469873 187409370531555049469602405)
    ·
      refine ⟨35139256974666571775550451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187409370531555049469602405 35139256974666571775550451)
      ·
        refine ⟨52708885461999857663325677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35139256974666571775550451 52708885461999857663325677)
        ·
          refine ⟨19765832048249946623747129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52708885461999857663325677 19765832048249946623747129)
          ·
            refine ⟨14824374036187459967810347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19765832048249946623747129 14824374036187459967810347)
            ·
              refine ⟨22236561054281189951715521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14824374036187459967810347 22236561054281189951715521)
              ·
                refine ⟨16677420790710892463786641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22236561054281189951715521 16677420790710892463786641)
                ·
                  refine ⟨12508065593033169347839981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16677420790710892463786641 12508065593033169347839981)
                  ·
                    refine ⟨4690524597387438505439993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12508065593033169347839981 4690524597387438505439993)
                    ·
                      refine ⟨3517893448040578879079995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690524597387438505439993 3517893448040578879079995)
                      ·
                        rfl

theorem cell23_6851073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_6851073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851073 prefixEnd_6851073 := by exact prefixLift 6851073
  have htrace : WordTrace (prefixWord ++ tailWord_6851073) baseStart_6851073 baseEnd_6851073 := by
    simpa [prefixWord, tailWord_6851073, baseEnd_6851073] using wordTrace_append hprefix tailTrace_6851073
  have hstable : (prefixWord ++ tailWord_6851073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851073).length < 2 ^ (prefixWord ++ tailWord_6851073).sum := by decide
  have hdescent : baseEnd_6851073 < baseStart_6851073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851123 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 1, 2, 3]
def baseStart_6851123 : Nat := 118140960795 + 6851123 * 2 ^ 59
def prefixEnd_6851123 : Nat := 4983230072969 + 3 ^ 40 * 6851123 * 2
def baseEnd_6851123 : Nat := 3517919122073303683454765

theorem tailTrace_6851123 : CollatzResearch.WordTrace tailWord_6851123 prefixEnd_6851123 3517919122073303683454765 := by
  unfold tailWord_6851123
  simp only [CollatzResearch.WordTrace]
  refine ⟨249880984358558924498790023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166587322905705949665860015 249880984358558924498790023)
  ·
    refine ⟨374821476537838386748185035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249880984358558924498790023 374821476537838386748185035)
    ·
      refine ⟨562232214806757580122277553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374821476537838386748185035 562232214806757580122277553)
      ·
        refine ⟨421674161105068185091708165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562232214806757580122277553 421674161105068185091708165)
        ·
          refine ⟨79063905207200284704695281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421674161105068185091708165 79063905207200284704695281)
          ·
            refine ⟨59297928905400213528521461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79063905207200284704695281 59297928905400213528521461)
            ·
              refine ⟨5559180834881270018298887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59297928905400213528521461 5559180834881270018298887)
              ·
                refine ⟨8338771252321905027448331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559180834881270018298887 8338771252321905027448331)
                ·
                  refine ⟨12508156878482857541172497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338771252321905027448331 12508156878482857541172497)
                  ·
                    refine ⟨9381117658862143155879373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12508156878482857541172497 9381117658862143155879373)
                    ·
                      refine ⟨3517919122073303683454765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9381117658862143155879373 3517919122073303683454765)
                      ·
                        rfl

theorem cell23_6851123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 2, 3].length) (baseStart_6851123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851123 prefixEnd_6851123 := by exact prefixLift 6851123
  have htrace : WordTrace (prefixWord ++ tailWord_6851123) baseStart_6851123 baseEnd_6851123 := by
    simpa [prefixWord, tailWord_6851123, baseEnd_6851123] using wordTrace_append hprefix tailTrace_6851123
  have hstable : (prefixWord ++ tailWord_6851123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851123).length < 2 ^ (prefixWord ++ tailWord_6851123).sum := by decide
  have hdescent : baseEnd_6851123 < baseStart_6851123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851136 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_6851136 : Nat := 118140960795 + 6851136 * 2 ^ 59
def prefixEnd_6851136 : Nat := 4983230072969 + 3 ^ 40 * 6851136 * 2
def baseEnd_6851136 : Nat := 3517925797321812132592205

theorem tailTrace_6851136 : CollatzResearch.WordTrace tailWord_6851136 prefixEnd_6851136 3517925797321812132592205 := by
  unfold tailWord_6851136
  simp only [CollatzResearch.WordTrace]
  refine ⟨124940729253755913859506631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166587639005007885146008841 124940729253755913859506631)
  ·
    refine ⟨187411093880633870789259947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124940729253755913859506631 187411093880633870789259947)
    ·
      refine ⟨281116640820950806183889921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187411093880633870789259947 281116640820950806183889921)
      ·
        refine ⟨210837480615713104637917441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281116640820950806183889921 210837480615713104637917441)
        ·
          refine ⟨158128110461784828478438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210837480615713104637917441 158128110461784828478438081)
          ·
            refine ⟨118596082846338621358828561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158128110461784828478438081 118596082846338621358828561)
            ·
              refine ⟨88947062134753966019121421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118596082846338621358828561 88947062134753966019121421)
              ·
                refine ⟨33355148300532737257170533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88947062134753966019121421 33355148300532737257170533)
                ·
                  refine ⟨6254090306349888235719475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33355148300532737257170533 6254090306349888235719475)
                  ·
                    refine ⟨9381135459524832353579213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6254090306349888235719475 9381135459524832353579213)
                    ·
                      refine ⟨3517925797321812132592205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9381135459524832353579213 3517925797321812132592205)
                      ·
                        rfl

theorem cell23_6851136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_6851136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851136 prefixEnd_6851136 := by exact prefixLift 6851136
  have htrace : WordTrace (prefixWord ++ tailWord_6851136) baseStart_6851136 baseEnd_6851136 := by
    simpa [prefixWord, tailWord_6851136, baseEnd_6851136] using wordTrace_append hprefix tailTrace_6851136
  have hstable : (prefixWord ++ tailWord_6851136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851136).length < 2 ^ (prefixWord ++ tailWord_6851136).sum := by decide
  have hdescent : baseEnd_6851136 < baseStart_6851136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851137 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6851137 : Nat := 118140960795 + 6851137 * 2 ^ 59
def prefixEnd_6851137 : Nat := 4983230072969 + 3 ^ 40 * 6851137 * 2
def baseEnd_6851137 : Nat := 3517926310802466628679701

theorem tailTrace_6851137 : CollatzResearch.WordTrace tailWord_6851137 prefixEnd_6851137 3517926310802466628679701 := by
  unfold tailWord_6851137
  simp only [CollatzResearch.WordTrace]
  refine ⟨249881494980508204889799665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166587663320338803259866443 249881494980508204889799665)
  ·
    refine ⟨187411121235381153667349749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249881494980508204889799665 187411121235381153667349749)
    ·
      refine ⟨17569792615816983156314039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187411121235381153667349749 17569792615816983156314039)
      ·
        refine ⟨26354688923725474734471059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17569792615816983156314039 26354688923725474734471059)
        ·
          refine ⟨39532033385588212101706589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26354688923725474734471059 39532033385588212101706589)
          ·
            refine ⟨14824512519595579538139971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39532033385588212101706589 14824512519595579538139971)
            ·
              refine ⟨22236768779393369307209957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14824512519595579538139971 22236768779393369307209957)
              ·
                refine ⟨4169394146136256745101867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22236768779393369307209957 4169394146136256745101867)
                ·
                  refine ⟨6254091219204385117652801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169394146136256745101867 6254091219204385117652801)
                  ·
                    refine ⟨4690568414403288838239601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254091219204385117652801 4690568414403288838239601)
                    ·
                      refine ⟨3517926310802466628679701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690568414403288838239601 3517926310802466628679701)
                      ·
                        rfl

theorem cell23_6851137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6851137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851137 prefixEnd_6851137 := by exact prefixLift 6851137
  have htrace : WordTrace (prefixWord ++ tailWord_6851137) baseStart_6851137 baseEnd_6851137 := by
    simpa [prefixWord, tailWord_6851137, baseEnd_6851137] using wordTrace_append hprefix tailTrace_6851137
  have hstable : (prefixWord ++ tailWord_6851137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851137).length < 2 ^ (prefixWord ++ tailWord_6851137).sum := by decide
  have hdescent : baseEnd_6851137 < baseStart_6851137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851153 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_6851153 : Nat := 118140960795 + 6851153 * 2 ^ 59
def prefixEnd_6851153 : Nat := 4983230072969 + 3 ^ 40 * 6851153 * 2
def baseEnd_6851153 : Nat := 3517934526492938566079627

theorem tailTrace_6851153 : CollatzResearch.WordTrace tailWord_6851153 prefixEnd_6851153 3517934526492938566079627 := by
  unfold tailWord_6851153
  simp only [CollatzResearch.WordTrace]
  refine ⟨249882078548450239622382113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166588052365633493081588075 249882078548450239622382113)
  ·
    refine ⟨187411558911337679716786585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249882078548450239622382113 187411558911337679716786585)
    ·
      refine ⟨140558669183503259787589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187411558911337679716786585 140558669183503259787589939)
      ·
        refine ⟨210838003775254889681384909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140558669183503259787589939 210838003775254889681384909)
        ·
          refine ⟨79064251415720583630519341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210838003775254889681384909 79064251415720583630519341)
          ·
            refine ⟨29649094280895218861444753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79064251415720583630519341 29649094280895218861444753)
            ·
              refine ⟨22236820710671414146083565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29649094280895218861444753 22236820710671414146083565)
              ·
                refine ⟨8338807766501780304781337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22236820710671414146083565 8338807766501780304781337)
                ·
                  refine ⟨6254105824876335228586003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8338807766501780304781337 6254105824876335228586003)
                  ·
                    refine ⟨9381158737314502842879005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6254105824876335228586003 9381158737314502842879005)
                    ·
                      refine ⟨3517934526492938566079627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9381158737314502842879005 3517934526492938566079627)
                      ·
                        rfl

theorem cell23_6851153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_6851153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851153 prefixEnd_6851153 := by exact prefixLift 6851153
  have htrace : WordTrace (prefixWord ++ tailWord_6851153) baseStart_6851153 baseEnd_6851153 := by
    simpa [prefixWord, tailWord_6851153, baseEnd_6851153] using wordTrace_append hprefix tailTrace_6851153
  have hstable : (prefixWord ++ tailWord_6851153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851153).length < 2 ^ (prefixWord ++ tailWord_6851153).sum := by decide
  have hdescent : baseEnd_6851153 < baseStart_6851153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851159 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_6851159 : Nat := 118140960795 + 6851159 * 2 ^ 59
def prefixEnd_6851159 : Nat := 4983230072969 + 3 ^ 40 * 6851159 * 2
def baseEnd_6851159 : Nat := 3517937607376865542604599

theorem tailTrace_6851159 : CollatzResearch.WordTrace tailWord_6851159 prefixEnd_6851159 3517937607376865542604599 := by
  unfold tailWord_6851159
  simp only [CollatzResearch.WordTrace]
  refine ⟨249882297386428502647100531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166588198257619001764733687 249882297386428502647100531)
  ·
    refine ⟨374823446079642753970650797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249882297386428502647100531 374823446079642753970650797)
    ·
      refine ⟨140558792279866032738994049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374823446079642753970650797 140558792279866032738994049)
      ·
        refine ⟨105419094209899524554245537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140558792279866032738994049 105419094209899524554245537)
        ·
          refine ⟨79064320657424643415684153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105419094209899524554245537 79064320657424643415684153)
          ·
            refine ⟨59298240493068482561763115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79064320657424643415684153 59298240493068482561763115)
            ·
              refine ⟨88947360739602723842644673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59298240493068482561763115 88947360739602723842644673)
              ·
                refine ⟨66710520554702042881983505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88947360739602723842644673 66710520554702042881983505)
                ·
                  refine ⟨50032890416026532161487629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66710520554702042881983505 50032890416026532161487629)
                  ·
                    refine ⟨18762333906009949560557861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50032890416026532161487629 18762333906009949560557861)
                    ·
                      refine ⟨3517937607376865542604599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18762333906009949560557861 3517937607376865542604599)
                      ·
                        rfl

theorem cell23_6851159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_6851159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851159 prefixEnd_6851159 := by exact prefixLift 6851159
  have htrace : WordTrace (prefixWord ++ tailWord_6851159) baseStart_6851159 baseEnd_6851159 := by
    simpa [prefixWord, tailWord_6851159, baseEnd_6851159] using wordTrace_append hprefix tailTrace_6851159
  have hstable : (prefixWord ++ tailWord_6851159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851159).length < 2 ^ (prefixWord ++ tailWord_6851159).sum := by decide
  have hdescent : baseEnd_6851159 < baseStart_6851159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3]
def baseStart_6851179 : Nat := 118140960795 + 6851179 * 2 ^ 59
def prefixEnd_6851179 : Nat := 4983230072969 + 3 ^ 40 * 6851179 * 2
def baseEnd_6851179 : Nat := 3517947876989955464354507

theorem tailTrace_6851179 : CollatzResearch.WordTrace tailWord_6851179 prefixEnd_6851179 3517947876989955464354507 := by
  unfold tailWord_6851179
  simp only [CollatzResearch.WordTrace]
  refine ⟨249883026846356046062828591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166588684564237364041885727 249883026846356046062828591)
  ·
    refine ⟨374824540269534069094242887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249883026846356046062828591 374824540269534069094242887)
    ·
      refine ⟨562236810404301103641364331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374824540269534069094242887 562236810404301103641364331)
      ·
        refine ⟨843355215606451655462046497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562236810404301103641364331 843355215606451655462046497)
        ·
          refine ⟨632516411704838741596534873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843355215606451655462046497 632516411704838741596534873)
          ·
            refine ⟨474387308778629056197401155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632516411704838741596534873 474387308778629056197401155)
            ·
              refine ⟨711580963167943584296101733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474387308778629056197401155 711580963167943584296101733)
              ·
                refine ⟨133421430593989422055519075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711580963167943584296101733 133421430593989422055519075)
                ·
                  refine ⟨200132145890984133083278613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133421430593989422055519075 200132145890984133083278613)
                  ·
                    refine ⟨9381194338639881238278685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200132145890984133083278613 9381194338639881238278685)
                    ·
                      refine ⟨3517947876989955464354507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9381194338639881238278685 3517947876989955464354507)
                      ·
                        rfl

theorem cell23_6851179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].length) (baseStart_6851179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851179 prefixEnd_6851179 := by exact prefixLift 6851179
  have htrace : WordTrace (prefixWord ++ tailWord_6851179) baseStart_6851179 baseEnd_6851179 := by
    simpa [prefixWord, tailWord_6851179, baseEnd_6851179] using wordTrace_append hprefix tailTrace_6851179
  have hstable : (prefixWord ++ tailWord_6851179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851179).length < 2 ^ (prefixWord ++ tailWord_6851179).sum := by decide
  have hdescent : baseEnd_6851179 < baseStart_6851179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851180 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_6851180 : Nat := 118140960795 + 6851180 * 2 ^ 59
def prefixEnd_6851180 : Nat := 4983230072969 + 3 ^ 40 * 6851180 * 2
def baseEnd_6851180 : Nat := 3517948390470609960442003

theorem tailTrace_6851180 : CollatzResearch.WordTrace tailWord_6851180 prefixEnd_6851180 3517948390470609960442003 := by
  unfold tailWord_6851180
  simp only [CollatzResearch.WordTrace]
  refine ⟨124941531659676211616807497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166588708879568282155743329 124941531659676211616807497)
  ·
    refine ⟨93706148744757158712605623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124941531659676211616807497 93706148744757158712605623)
    ·
      refine ⟨140559223117135738068908435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93706148744757158712605623 140559223117135738068908435)
      ·
        refine ⟨210838834675703607103362653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140559223117135738068908435 210838834675703607103362653)
        ·
          refine ⟨79064563003388852663760995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210838834675703607103362653 79064563003388852663760995)
          ·
            refine ⟨118596844505083278995641493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79064563003388852663760995 118596844505083278995641493)
            ·
              refine ⟨5559227086175778702920695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118596844505083278995641493 5559227086175778702920695)
              ·
                refine ⟨8338840629263668054381043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559227086175778702920695 8338840629263668054381043)
                ·
                  refine ⟨12508260943895502081571565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338840629263668054381043 12508260943895502081571565)
                  ·
                    refine ⟨4690597853960813280589337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12508260943895502081571565 4690597853960813280589337)
                    ·
                      refine ⟨3517948390470609960442003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690597853960813280589337 3517948390470609960442003)
                      ·
                        rfl

theorem cell23_6851180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_6851180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851180 prefixEnd_6851180 := by exact prefixLift 6851180
  have htrace : WordTrace (prefixWord ++ tailWord_6851180) baseStart_6851180 baseEnd_6851180 := by
    simpa [prefixWord, tailWord_6851180, baseEnd_6851180] using wordTrace_append hprefix tailTrace_6851180
  have hstable : (prefixWord ++ tailWord_6851180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851180).length < 2 ^ (prefixWord ++ tailWord_6851180).sum := by decide
  have hdescent : baseEnd_6851180 < baseStart_6851180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851279 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_6851279 : Nat := 118140960795 + 6851279 * 2 ^ 59
def prefixEnd_6851279 : Nat := 4983230072969 + 3 ^ 40 * 6851279 * 2
def baseEnd_6851279 : Nat := 3517999225055405073104047

theorem tailTrace_6851279 : CollatzResearch.WordTrace tailWord_6851279 prefixEnd_6851279 3517999225055405073104047 := by
  unfold tailWord_6851279
  simp only [CollatzResearch.WordTrace]
  refine ⟨249886674145993763141468891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166591116097329175427645927 249886674145993763141468891)
  ·
    refine ⟨374830011218990644712203337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249886674145993763141468891 374830011218990644712203337)
    ·
      refine ⟨281122508414242983534152503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374830011218990644712203337 281122508414242983534152503)
      ·
        refine ⟨421683762621364475301228755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281122508414242983534152503 421683762621364475301228755)
        ·
          refine ⟨632525643932046712951843133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421683762621364475301228755 632525643932046712951843133)
          ·
            refine ⟨237197116474517517356941175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632525643932046712951843133 237197116474517517356941175)
            ·
              refine ⟨355795674711776276035411763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237197116474517517356941175 355795674711776276035411763)
              ·
                refine ⟨533693512067664414053117645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355795674711776276035411763 533693512067664414053117645)
                ·
                  refine ⟨200135067025374155269919117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533693512067664414053117645 200135067025374155269919117)
                  ·
                    refine ⟨75050650134515308226219669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200135067025374155269919117 75050650134515308226219669)
                    ·
                      refine ⟨3517999225055405073104047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75050650134515308226219669 3517999225055405073104047)
                      ·
                        rfl

theorem cell23_6851279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_6851279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851279 prefixEnd_6851279 := by exact prefixLift 6851279
  have htrace : WordTrace (prefixWord ++ tailWord_6851279) baseStart_6851279 baseEnd_6851279 := by
    simpa [prefixWord, tailWord_6851279, baseEnd_6851279] using wordTrace_append hprefix tailTrace_6851279
  have hstable : (prefixWord ++ tailWord_6851279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851279).length < 2 ^ (prefixWord ++ tailWord_6851279).sum := by decide
  have hdescent : baseEnd_6851279 < baseStart_6851279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851343 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 5, 2]
def baseStart_6851343 : Nat := 118140960795 + 6851343 * 2 ^ 59
def prefixEnd_6851343 : Nat := 4983230072969 + 3 ^ 40 * 6851343 * 2
def baseEnd_6851343 : Nat := 3518032087817292822703753

theorem tailTrace_6851343 : CollatzResearch.WordTrace tailWord_6851343 prefixEnd_6851343 3518032087817292822703753 := by
  unfold tailWord_6851343
  simp only [CollatzResearch.WordTrace]
  refine ⟨249889008417761902071798683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166592672278507934714532455 249889008417761902071798683)
  ·
    refine ⟨374833512626642853107698025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249889008417761902071798683 374833512626642853107698025)
    ·
      refine ⟨281125134469982139830773519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374833512626642853107698025 281125134469982139830773519)
      ·
        refine ⟨421687701704973209746160279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281125134469982139830773519 421687701704973209746160279)
        ·
          refine ⟨632531552557459814619240419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421687701704973209746160279 632531552557459814619240419)
          ·
            refine ⟨948797328836189721928860629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632531552557459814619240419 948797328836189721928860629)
            ·
              refine ⟨22237437394598196607707671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 948797328836189721928860629 22237437394598196607707671)
              ·
                refine ⟨33356156091897294911561507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22237437394598196607707671 33356156091897294911561507)
                ·
                  refine ⟨50034234137845942367342261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33356156091897294911561507 50034234137845942367342261)
                  ·
                    refine ⟨4690709450423057096938337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50034234137845942367342261 4690709450423057096938337)
                    ·
                      refine ⟨3518032087817292822703753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690709450423057096938337 3518032087817292822703753)
                      ·
                        rfl

theorem cell23_6851343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5, 2].length) (baseStart_6851343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851343 prefixEnd_6851343 := by exact prefixLift 6851343
  have htrace : WordTrace (prefixWord ++ tailWord_6851343) baseStart_6851343 baseEnd_6851343 := by
    simpa [prefixWord, tailWord_6851343, baseEnd_6851343] using wordTrace_append hprefix tailTrace_6851343
  have hstable : (prefixWord ++ tailWord_6851343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851343).length < 2 ^ (prefixWord ++ tailWord_6851343).sum := by decide
  have hdescent : baseEnd_6851343 < baseStart_6851343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851357 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 6]
def baseStart_6851357 : Nat := 118140960795 + 6851357 * 2 ^ 59
def prefixEnd_6851357 : Nat := 4983230072969 + 3 ^ 40 * 6851357 * 2
def baseEnd_6851357 : Nat := 390893252949606196436521

theorem tailTrace_6851357 : CollatzResearch.WordTrace tailWord_6851357 prefixEnd_6851357 390893252949606196436521 := by
  unfold tailWord_6851357
  simp only [CollatzResearch.WordTrace]
  refine ⟨249889519039711182462808325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166593012693140788308538883 249889519039711182462808325)
  ·
    refine ⟨46854284819945846711776561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249889519039711182462808325 46854284819945846711776561)
    ·
      refine ⟨35140713614959385033832421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46854284819945846711776561 35140713614959385033832421)
      ·
        refine ⟨6588883802804884693843579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35140713614959385033832421 6588883802804884693843579)
        ·
          refine ⟨9883325704207327040765369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588883802804884693843579 9883325704207327040765369)
          ·
            refine ⟨7412494278155495280574027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9883325704207327040765369 7412494278155495280574027)
            ·
              refine ⟨11118741417233242920861041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7412494278155495280574027 11118741417233242920861041)
              ·
                refine ⟨8339056062924932190645781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11118741417233242920861041 8339056062924932190645781)
                ·
                  refine ⟨390893252949606196436521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8339056062924932190645781 390893252949606196436521)
                  ·
                    rfl

theorem cell23_6851357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_6851357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851357 prefixEnd_6851357 := by exact prefixLift 6851357
  have htrace : WordTrace (prefixWord ++ tailWord_6851357) baseStart_6851357 baseEnd_6851357 := by
    simpa [prefixWord, tailWord_6851357, baseEnd_6851357] using wordTrace_append hprefix tailTrace_6851357
  have hstable : (prefixWord ++ tailWord_6851357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851357).length < 2 ^ (prefixWord ++ tailWord_6851357).sum := by decide
  have hdescent : baseEnd_6851357 < baseStart_6851357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851410 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_6851410 : Nat := 118140960795 + 6851410 * 2 ^ 59
def prefixEnd_6851410 : Nat := 4983230072969 + 3 ^ 40 * 6851410 * 2
def baseEnd_6851410 : Nat := 3518066491021144060565945

theorem tailTrace_6851410 : CollatzResearch.WordTrace tailWord_6851410 prefixEnd_6851410 3518066491021144060565945 := by
  unfold tailWord_6851410
  simp only [CollatzResearch.WordTrace]
  refine ⟨62472863027129793128621921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166594301405679448342991789 62472863027129793128621921)
  ·
    refine ⟨46854647270347344846466441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62472863027129793128621921 46854647270347344846466441)
    ·
      refine ⟨35140985452760508634849831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46854647270347344846466441 35140985452760508634849831)
      ·
        refine ⟨52711478179140762952274747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35140985452760508634849831 52711478179140762952274747)
        ·
          refine ⟨79067217268711144428412121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52711478179140762952274747 79067217268711144428412121)
          ·
            refine ⟨59300412951533358321309091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79067217268711144428412121 59300412951533358321309091)
            ·
              refine ⟨88950619427300037481963637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59300412951533358321309091 88950619427300037481963637)
              ·
                refine ⟨8339120571309378513934091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88950619427300037481963637 8339120571309378513934091)
                ·
                  refine ⟨12508680856964067770901137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339120571309378513934091 12508680856964067770901137)
                  ·
                    refine ⟨9381510642723050828175853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12508680856964067770901137 9381510642723050828175853)
                    ·
                      refine ⟨3518066491021144060565945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9381510642723050828175853 3518066491021144060565945)
                      ·
                        rfl

theorem cell23_6851410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_6851410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851410 prefixEnd_6851410 := by exact prefixLift 6851410
  have htrace : WordTrace (prefixWord ++ tailWord_6851410) baseStart_6851410 baseEnd_6851410 := by
    simpa [prefixWord, tailWord_6851410, baseEnd_6851410] using wordTrace_append hprefix tailTrace_6851410
  have hstable : (prefixWord ++ tailWord_6851410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851410).length < 2 ^ (prefixWord ++ tailWord_6851410).sum := by decide
  have hdescent : baseEnd_6851410 < baseStart_6851410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851433 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 9, 2]
def baseStart_6851433 : Nat := 118140960795 + 6851433 * 2 ^ 59
def prefixEnd_6851433 : Nat := 4983230072969 + 3 ^ 40 * 6851433 * 2
def baseEnd_6851433 : Nat := 3518078301076197470578339

theorem tailTrace_6851433 : CollatzResearch.WordTrace tailWord_6851433 prefixEnd_6851433 3518078301076197470578339 := by
  unfold tailWord_6851433
  simp only [CollatzResearch.WordTrace]
  refine ⟨249892290987435847442574953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166594860658290564961716635 249892290987435847442574953)
  ·
    refine ⟨187419218240576885581931215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249892290987435847442574953 187419218240576885581931215)
    ·
      refine ⟨281128827360865328372896823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187419218240576885581931215 281128827360865328372896823)
      ·
        refine ⟨421693241041297992559345235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281128827360865328372896823 421693241041297992559345235)
        ·
          refine ⟨632539861561946988839017853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421693241041297992559345235 632539861561946988839017853)
          ·
            refine ⟨237202448085730120814631695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632539861561946988839017853 237202448085730120814631695)
            ·
              refine ⟨355803672128595181221947543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237202448085730120814631695 355803672128595181221947543)
              ·
                refine ⟨533705508192892771832921315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355803672128595181221947543 533705508192892771832921315)
                ·
                  refine ⟨800558262289339157749381973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533705508192892771832921315 800558262289339157749381973)
                  ·
                    refine ⟨4690771068101596627437785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 800558262289339157749381973 4690771068101596627437785)
                    ·
                      refine ⟨3518078301076197470578339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690771068101596627437785 3518078301076197470578339)
                      ·
                        rfl

theorem cell23_6851433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9, 2].length) (baseStart_6851433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851433 prefixEnd_6851433 := by exact prefixLift 6851433
  have htrace : WordTrace (prefixWord ++ tailWord_6851433) baseStart_6851433 baseEnd_6851433 := by
    simpa [prefixWord, tailWord_6851433, baseEnd_6851433] using wordTrace_append hprefix tailTrace_6851433
  have hstable : (prefixWord ++ tailWord_6851433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851433).length < 2 ^ (prefixWord ++ tailWord_6851433).sum := by decide
  have hdescent : baseEnd_6851433 < baseStart_6851433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851456 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_6851456 : Nat := 118140960795 + 6851456 * 2 ^ 59
def prefixEnd_6851456 : Nat := 4983230072969 + 3 ^ 40 * 6851456 * 2
def baseEnd_6851456 : Nat := 1172696703710416960196911

theorem tailTrace_6851456 : CollatzResearch.WordTrace tailWord_6851456 prefixEnd_6851456 1172696703710416960196911 := by
  unfold tailWord_6851456
  simp only [CollatzResearch.WordTrace]
  refine ⟨124946564933176261185331111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166595419910901681580441481 124946564933176261185331111)
  ·
    refine ⟨187419847399764391777996667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124946564933176261185331111 187419847399764391777996667)
    ·
      refine ⟨281129771099646587666995001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187419847399764391777996667 281129771099646587666995001)
      ·
        refine ⟨210847328324734940750246251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281129771099646587666995001 210847328324734940750246251)
        ·
          refine ⟨316270992487102411125369377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210847328324734940750246251 316270992487102411125369377)
          ·
            refine ⟨237203244365326808344027033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316270992487102411125369377 237203244365326808344027033)
            ·
              refine ⟨177902433273995106258020275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237203244365326808344027033 177902433273995106258020275)
              ·
                refine ⟨266853649910992659387030413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177902433273995106258020275 266853649910992659387030413)
                ·
                  refine ⟨100070118716622247270136405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266853649910992659387030413 100070118716622247270136405)
                  ·
                    refine ⟨1172696703710416960196911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100070118716622247270136405 1172696703710416960196911)
                    ·
                      rfl

theorem cell23_6851456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_6851456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851456 prefixEnd_6851456 := by exact prefixLift 6851456
  have htrace : WordTrace (prefixWord ++ tailWord_6851456) baseStart_6851456 baseEnd_6851456 := by
    simpa [prefixWord, tailWord_6851456, baseEnd_6851456] using wordTrace_append hprefix tailTrace_6851456
  have hstable : (prefixWord ++ tailWord_6851456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851456).length < 2 ^ (prefixWord ++ tailWord_6851456).sum := by decide
  have hdescent : baseEnd_6851456 < baseStart_6851456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851490 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6851490 : Nat := 118140960795 + 6851490 * 2 ^ 59
def prefixEnd_6851490 : Nat := 4983230072969 + 3 ^ 40 * 6851490 * 2
def baseEnd_6851490 : Nat := 1172702523157834582521859

theorem tailTrace_6851490 : CollatzResearch.WordTrace tailWord_6851490 prefixEnd_6851490 1172702523157834582521859 := by
  unfold tailWord_6851490
  simp only [CollatzResearch.WordTrace]
  refine ⟨62473592487057336544349981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166596246632152897451599949 62473592487057336544349981)
  ·
    refine ⟨23427597182646501204131243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62473592487057336544349981 23427597182646501204131243)
    ·
      refine ⟨35141395773969751806196865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23427597182646501204131243 35141395773969751806196865)
      ·
        refine ⟨26356046830477313854647649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35141395773969751806196865 26356046830477313854647649)
        ·
          refine ⟨19767035122857985390985737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26356046830477313854647649 19767035122857985390985737)
          ·
            refine ⟨14825276342143489043239303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19767035122857985390985737 14825276342143489043239303)
            ·
              refine ⟨22237914513215233564858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14825276342143489043239303 22237914513215233564858955)
              ·
                refine ⟨33356871769822850347288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22237914513215233564858955 33356871769822850347288433)
                ·
                  refine ⟨25017653827367137760466325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33356871769822850347288433 25017653827367137760466325)
                  ·
                    refine ⟨1172702523157834582521859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25017653827367137760466325 1172702523157834582521859)
                    ·
                      rfl

theorem cell23_6851490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6851490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851490 prefixEnd_6851490 := by exact prefixLift 6851490
  have htrace : WordTrace (prefixWord ++ tailWord_6851490) baseStart_6851490 baseEnd_6851490 := by
    simpa [prefixWord, tailWord_6851490, baseEnd_6851490] using wordTrace_append hprefix tailTrace_6851490
  have hstable : (prefixWord ++ tailWord_6851490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851490).length < 2 ^ (prefixWord ++ tailWord_6851490).sum := by decide
  have hdescent : baseEnd_6851490 < baseStart_6851490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851497 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 2, 2, 2]
def baseStart_6851497 : Nat := 118140960795 + 6851497 * 2 ^ 59
def prefixEnd_6851497 : Nat := 4983230072969 + 3 ^ 40 * 6851497 * 2
def baseEnd_6851497 : Nat := 3518111163838085220178045

theorem tailTrace_6851497 : CollatzResearch.WordTrace tailWord_6851497 prefixEnd_6851497 3518111163838085220178045 := by
  unfold tailWord_6851497
  simp only [CollatzResearch.WordTrace]
  refine ⟨249894625259203986372904745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166596416839469324248603163 249894625259203986372904745)
  ·
    refine ⟨187420968944402989779678559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249894625259203986372904745 187420968944402989779678559)
    ·
      refine ⟨281131453416604484669517839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187420968944402989779678559 281131453416604484669517839)
      ·
        refine ⟨421697180124906727004276759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281131453416604484669517839 421697180124906727004276759)
        ·
          refine ⟨632545770187360090506415139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421697180124906727004276759 632545770187360090506415139)
          ·
            refine ⟨948818655281040135759622709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632545770187360090506415139 948818655281040135759622709)
            ·
              refine ⟨88951748932597512727464629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 948818655281040135759622709 88951748932597512727464629)
              ·
                refine ⟨8339226462431016818199809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88951748932597512727464629 8339226462431016818199809)
                ·
                  refine ⟨6254419846823262613649857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339226462431016818199809 6254419846823262613649857)
                  ·
                    refine ⟨4690814885117446960237393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254419846823262613649857 4690814885117446960237393)
                    ·
                      refine ⟨3518111163838085220178045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4690814885117446960237393 3518111163838085220178045)
                      ·
                        rfl

theorem cell23_6851497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2, 2].length) (baseStart_6851497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851497 prefixEnd_6851497 := by exact prefixLift 6851497
  have htrace : WordTrace (prefixWord ++ tailWord_6851497) baseStart_6851497 baseEnd_6851497 := by
    simpa [prefixWord, tailWord_6851497, baseEnd_6851497] using wordTrace_append hprefix tailTrace_6851497
  have hstable : (prefixWord ++ tailWord_6851497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851497).length < 2 ^ (prefixWord ++ tailWord_6851497).sum := by decide
  have hdescent : baseEnd_6851497 < baseStart_6851497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851520 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 5]
def baseStart_6851520 : Nat := 118140960795 + 6851520 * 2 ^ 59
def prefixEnd_6851520 : Nat := 4983230072969 + 3 ^ 40 * 6851520 * 2
def baseEnd_6851520 : Nat := 390902552654793181132271

theorem tailTrace_6851520 : CollatzResearch.WordTrace tailWord_6851520 prefixEnd_6851520 390902552654793181132271 := by
  unfold tailWord_6851520
  simp only [CollatzResearch.WordTrace]
  refine ⟨124947732069060330650496007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166596976092080440867328009 124947732069060330650496007)
  ·
    refine ⟨187421598103590495975744011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124947732069060330650496007 187421598103590495975744011)
    ·
      refine ⟨281132397155385743963616017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187421598103590495975744011 281132397155385743963616017)
      ·
        refine ⟨210849297866539307972712013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281132397155385743963616017 210849297866539307972712013)
        ·
          refine ⟨79068486699952240489767005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210849297866539307972712013 79068486699952240489767005)
          ·
            refine ⟨29650682512482090183662627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79068486699952240489767005 29650682512482090183662627)
            ·
              refine ⟨44476023768723135275493941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29650682512482090183662627 44476023768723135275493941)
              ·
                refine ⟨4169627228317793932077557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44476023768723135275493941 4169627228317793932077557)
                ·
                  refine ⟨390902552654793181132271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169627228317793932077557 390902552654793181132271)
                  ·
                    rfl

theorem cell23_6851520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 5].length) (baseStart_6851520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851520 prefixEnd_6851520 := by exact prefixLift 6851520
  have htrace : WordTrace (prefixWord ++ tailWord_6851520) baseStart_6851520 baseEnd_6851520 := by
    simpa [prefixWord, tailWord_6851520, baseEnd_6851520] using wordTrace_append hprefix tailTrace_6851520
  have hstable : (prefixWord ++ tailWord_6851520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851520).length < 2 ^ (prefixWord ++ tailWord_6851520).sum := by decide
  have hdescent : baseEnd_6851520 < baseStart_6851520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851610 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_6851610 : Nat := 118140960795 + 6851610 * 2 ^ 59
def prefixEnd_6851610 : Nat := 4983230072969 + 3 ^ 40 * 6851610 * 2
def baseEnd_6851610 : Nat := 390907687461338142007225

theorem tailTrace_6851610 : CollatzResearch.WordTrace tailWord_6851610 prefixEnd_6851610 390907687461338142007225 := by
  unfold tailWord_6851610
  simp only [CollatzResearch.WordTrace]
  refine ⟨62474686676948651667942071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166599164471863071114512189 62474686676948651667942071)
  ·
    refine ⟨93712030015422977501913107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62474686676948651667942071 93712030015422977501913107)
    ·
      refine ⟨140568045023134466252869661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93712030015422977501913107 140568045023134466252869661)
      ·
        refine ⟨52713016883675424844826123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140568045023134466252869661 52713016883675424844826123)
        ·
          refine ⟨79069525325513137267239185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52713016883675424844826123 79069525325513137267239185)
          ·
            refine ⟨59302143994134852950429389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79069525325513137267239185 59302143994134852950429389)
            ·
              refine ⟨22238303997800569856411021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59302143994134852950429389 22238303997800569856411021)
              ·
                refine ⟨8339363999175213696154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22238303997800569856411021 8339363999175213696154133)
                ·
                  refine ⟨390907687461338142007225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8339363999175213696154133 390907687461338142007225)
                  ·
                    rfl

theorem cell23_6851610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_6851610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851610 prefixEnd_6851610 := by exact prefixLift 6851610
  have htrace : WordTrace (prefixWord ++ tailWord_6851610) baseStart_6851610 baseEnd_6851610 := by
    simpa [prefixWord, tailWord_6851610, baseEnd_6851610] using wordTrace_append hprefix tailTrace_6851610
  have hstable : (prefixWord ++ tailWord_6851610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851610).length < 2 ^ (prefixWord ++ tailWord_6851610).sum := by decide
  have hdescent : baseEnd_6851610 < baseStart_6851610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851694 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6851694 : Nat := 118140960795 + 6851694 * 2 ^ 59
def prefixEnd_6851694 : Nat := 4983230072969 + 3 ^ 40 * 6851694 * 2
def baseEnd_6851694 : Nat := 3518212319527020949414639

theorem tailTrace_6851694 : CollatzResearch.WordTrace tailWord_6851694 prefixEnd_6851694 3518212319527020949414639 := by
  unfold tailWord_6851694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31237726304936286127228267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166601206959660192678550757 31237726304936286127228267)
  ·
    refine ⟨46856589457404429190842401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31237726304936286127228267 46856589457404429190842401)
    ·
      refine ⟨35142442093053321893131801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46856589457404429190842401 35142442093053321893131801)
      ·
        refine ⟨26356831569789991419848851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35142442093053321893131801 26356831569789991419848851)
        ·
          refine ⟨39535247354684987129773277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26356831569789991419848851 39535247354684987129773277)
          ·
            refine ⟨14825717758006870173664979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39535247354684987129773277 14825717758006870173664979)
            ·
              refine ⟨22238576637010305260497469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14825717758006870173664979 22238576637010305260497469)
              ·
                refine ⟨8339466238878864472686551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22238576637010305260497469 8339466238878864472686551)
                ·
                  refine ⟨12509199358318296709029827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339466238878864472686551 12509199358318296709029827)
                  ·
                    refine ⟨18763799037477445063544741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12509199358318296709029827 18763799037477445063544741)
                    ·
                      refine ⟨3518212319527020949414639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18763799037477445063544741 3518212319527020949414639)
                      ·
                        rfl

theorem cell23_6851694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6851694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851694 prefixEnd_6851694 := by exact prefixLift 6851694
  have htrace : WordTrace (prefixWord ++ tailWord_6851694) baseStart_6851694 baseEnd_6851694 := by
    simpa [prefixWord, tailWord_6851694, baseEnd_6851694] using wordTrace_append hprefix tailTrace_6851694
  have hstable : (prefixWord ++ tailWord_6851694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851694).length < 2 ^ (prefixWord ++ tailWord_6851694).sum := by decide
  have hdescent : baseEnd_6851694 < baseStart_6851694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851770 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_6851770 : Nat := 118140960795 + 6851770 * 2 ^ 59
def prefixEnd_6851770 : Nat := 4983230072969 + 3 ^ 40 * 6851770 * 2
def baseEnd_6851770 : Nat := 3518251344056762652064289

theorem tailTrace_6851770 : CollatzResearch.WordTrace tailWord_6851770 prefixEnd_6851770 3518251344056762652064289 := by
  unfold tailWord_6851770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62476145596803738499398191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166603054924809969331728509 62476145596803738499398191)
  ·
    refine ⟨93714218395205607749097287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62476145596803738499398191 93714218395205607749097287)
    ·
      refine ⟨140571327592808411623645931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93714218395205607749097287 140571327592808411623645931)
      ·
        refine ⟨210856991389212617435468897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140571327592808411623645931 210856991389212617435468897)
        ·
          refine ⟨158142743541909463076601673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210856991389212617435468897 158142743541909463076601673)
          ·
            refine ⟨118607057656432097307451255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158142743541909463076601673 118607057656432097307451255)
            ·
              refine ⟨177910586484648145961176883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118607057656432097307451255 177910586484648145961176883)
              ·
                refine ⟨266865879726972218941765325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177910586484648145961176883 266865879726972218941765325)
                ·
                  refine ⟨100074704897614582103161997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266865879726972218941765325 100074704897614582103161997)
                  ·
                    refine ⟨37528014336605468288685749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100074704897614582103161997 37528014336605468288685749)
                    ·
                      refine ⟨3518251344056762652064289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37528014336605468288685749 3518251344056762652064289)
                      ·
                        rfl

theorem cell23_6851770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_6851770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851770 prefixEnd_6851770 := by exact prefixLift 6851770
  have htrace : WordTrace (prefixWord ++ tailWord_6851770) baseStart_6851770 baseEnd_6851770 := by
    simpa [prefixWord, tailWord_6851770, baseEnd_6851770] using wordTrace_append hprefix tailTrace_6851770
  have hstable : (prefixWord ++ tailWord_6851770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851770).length < 2 ^ (prefixWord ++ tailWord_6851770).sum := by decide
  have hdescent : baseEnd_6851770 < baseStart_6851770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851782 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6851782 : Nat := 118140960795 + 6851782 * 2 ^ 59
def prefixEnd_6851782 : Nat := 4983230072969 + 3 ^ 40 * 6851782 * 2
def baseEnd_6851782 : Nat := 3518257505824616605114235

theorem tailTrace_6851782 : CollatzResearch.WordTrace tailWord_6851782 prefixEnd_6851782 3518257505824616605114235 := by
  unfold tailWord_6851782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809531876974108751469675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166603346708780986698019733 7809531876974108751469675)
  ·
    refine ⟨11714297815461163127204513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7809531876974108751469675 11714297815461163127204513)
    ·
      refine ⟨8785723361595872345403385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11714297815461163127204513 8785723361595872345403385)
      ·
        refine ⟨6589292521196904259052539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8785723361595872345403385 6589292521196904259052539)
        ·
          refine ⟨9883938781795356388578809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589292521196904259052539 9883938781795356388578809)
          ·
            refine ⟨7412954086346517291434107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9883938781795356388578809 7412954086346517291434107)
            ·
              refine ⟨11119431129519775937151161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7412954086346517291434107 11119431129519775937151161)
              ·
                refine ⟨8339573347139831952863371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11119431129519775937151161 8339573347139831952863371)
                ·
                  refine ⟨12509360020709747929295057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339573347139831952863371 12509360020709747929295057)
                  ·
                    refine ⟨9382020015532310946971293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12509360020709747929295057 9382020015532310946971293)
                    ·
                      refine ⟨3518257505824616605114235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382020015532310946971293 3518257505824616605114235)
                      ·
                        rfl

theorem cell23_6851782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6851782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851782 prefixEnd_6851782 := by exact prefixLift 6851782
  have htrace : WordTrace (prefixWord ++ tailWord_6851782) baseStart_6851782 baseEnd_6851782 := by
    simpa [prefixWord, tailWord_6851782, baseEnd_6851782] using wordTrace_append hprefix tailTrace_6851782
  have hstable : (prefixWord ++ tailWord_6851782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851782).length < 2 ^ (prefixWord ++ tailWord_6851782).sum := by decide
  have hdescent : baseEnd_6851782 < baseStart_6851782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851805 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6851805 : Nat := 118140960795 + 6851805 * 2 ^ 59
def prefixEnd_6851805 : Nat := 4983230072969 + 3 ^ 40 * 6851805 * 2
def baseEnd_6851805 : Nat := 3518269315879670015126629

theorem tailTrace_6851805 : CollatzResearch.WordTrace tailWord_6851805 prefixEnd_6851805 3518269315879670015126629 := by
  unfold tailWord_6851805
  simp only [CollatzResearch.WordTrace]
  refine ⟨249905858942088154975116869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166603905961392103316744579 249905858942088154975116869)
  ·
    refine ⟨46857348551641529057834413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249905858942088154975116869 46857348551641529057834413)
    ·
      refine ⟨17571505706865573396687905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46857348551641529057834413 17571505706865573396687905)
      ·
        refine ⟨13178629280149180047515929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17571505706865573396687905 13178629280149180047515929)
        ·
          refine ⟨9883971960111885035636947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13178629280149180047515929 9883971960111885035636947)
          ·
            refine ⟨14825957940167827553455421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9883971960111885035636947 14825957940167827553455421)
            ·
              refine ⟨5559734227562935332545783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14825957940167827553455421 5559734227562935332545783)
              ·
                refine ⟨8339601341344402998818675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559734227562935332545783 8339601341344402998818675)
                ·
                  refine ⟨12509402012016604498228013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339601341344402998818675 12509402012016604498228013)
                  ·
                    refine ⟨4691025754506226686835505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12509402012016604498228013 4691025754506226686835505)
                    ·
                      refine ⟨3518269315879670015126629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691025754506226686835505 3518269315879670015126629)
                      ·
                        rfl

theorem cell23_6851805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6851805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851805 prefixEnd_6851805 := by exact prefixLift 6851805
  have htrace : WordTrace (prefixWord ++ tailWord_6851805) baseStart_6851805 baseEnd_6851805 := by
    simpa [prefixWord, tailWord_6851805, baseEnd_6851805] using wordTrace_append hprefix tailTrace_6851805
  have hstable : (prefixWord ++ tailWord_6851805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851805).length < 2 ^ (prefixWord ++ tailWord_6851805).sum := by decide
  have hdescent : baseEnd_6851805 < baseStart_6851805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851818 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_6851818 : Nat := 118140960795 + 6851818 * 2 ^ 59
def prefixEnd_6851818 : Nat := 4983230072969 + 3 ^ 40 * 6851818 * 2
def baseEnd_6851818 : Nat := 3518275991128178464264069

theorem tailTrace_6851818 : CollatzResearch.WordTrace tailWord_6851818 prefixEnd_6851818 3518275991128178464264069 := by
  unfold tailWord_6851818
  simp only [CollatzResearch.WordTrace]
  refine ⟨62476583272760264548835027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166604222060694038796893405 62476583272760264548835027)
  ·
    refine ⟨93714874909140396823252541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62476583272760264548835027 93714874909140396823252541)
    ·
      refine ⟨35143078090927648808719703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93714874909140396823252541 35143078090927648808719703)
      ·
        refine ⟨52714617136391473213079555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35143078090927648808719703 52714617136391473213079555)
        ·
          refine ⟨79071925704587209819619333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52714617136391473213079555 79071925704587209819619333)
          ·
            refine ⟨14825986069610101841178625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79071925704587209819619333 14825986069610101841178625)
            ·
              refine ⟨11119489552207576380883969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14825986069610101841178625 11119489552207576380883969)
              ·
                refine ⟨8339617164155682285662977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11119489552207576380883969 8339617164155682285662977)
                ·
                  refine ⟨6254712873116761714247233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339617164155682285662977 6254712873116761714247233)
                  ·
                    refine ⟨4691034654837571285685425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254712873116761714247233 4691034654837571285685425)
                    ·
                      refine ⟨3518275991128178464264069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691034654837571285685425 3518275991128178464264069)
                      ·
                        rfl

theorem cell23_6851818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_6851818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851818 prefixEnd_6851818 := by exact prefixLift 6851818
  have htrace : WordTrace (prefixWord ++ tailWord_6851818) baseStart_6851818 baseEnd_6851818 := by
    simpa [prefixWord, tailWord_6851818, baseEnd_6851818] using wordTrace_append hprefix tailTrace_6851818
  have hstable : (prefixWord ++ tailWord_6851818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851818).length < 2 ^ (prefixWord ++ tailWord_6851818).sum := by decide
  have hdescent : baseEnd_6851818 < baseStart_6851818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851828 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6851828 : Nat := 118140960795 + 6851828 * 2 ^ 59
def prefixEnd_6851828 : Nat := 4983230072969 + 3 ^ 40 * 6851828 * 2
def baseEnd_6851828 : Nat := 1172760375311574475046341

theorem tailTrace_6851828 : CollatzResearch.WordTrace tailWord_6851828 prefixEnd_6851828 1172760375311574475046341 := by
  unfold tailWord_6851828
  simp only [CollatzResearch.WordTrace]
  refine ⟨124953348910502414951602069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166604465214003219935469425 124953348910502414951602069)
  ·
    refine ⟨5857188230179800700856347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124953348910502414951602069 5857188230179800700856347)
    ·
      refine ⟨8785782345269701051284521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857188230179800700856347 8785782345269701051284521)
      ·
        refine ⟨6589336758952275788463391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8785782345269701051284521 6589336758952275788463391)
        ·
          refine ⟨9884005138428413682695087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589336758952275788463391 9884005138428413682695087)
          ·
            refine ⟨14826007707642620524042631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884005138428413682695087 14826007707642620524042631)
            ·
              refine ⟨22239011561463930786063947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14826007707642620524042631 22239011561463930786063947)
              ·
                refine ⟨33358517342195896179095921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22239011561463930786063947 33358517342195896179095921)
                ·
                  refine ⟨25018888006646922134321941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33358517342195896179095921 25018888006646922134321941)
                  ·
                    refine ⟨1172760375311574475046341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25018888006646922134321941 1172760375311574475046341)
                    ·
                      rfl

theorem cell23_6851828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6851828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851828 prefixEnd_6851828 := by exact prefixLift 6851828
  have htrace : WordTrace (prefixWord ++ tailWord_6851828) baseStart_6851828 baseEnd_6851828 := by
    simpa [prefixWord, tailWord_6851828, baseEnd_6851828] using wordTrace_append hprefix tailTrace_6851828
  have hstable : (prefixWord ++ tailWord_6851828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851828).length < 2 ^ (prefixWord ++ tailWord_6851828).sum := by decide
  have hdescent : baseEnd_6851828 < baseStart_6851828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851854 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_6851854 : Nat := 118140960795 + 6851854 * 2 ^ 59
def prefixEnd_6851854 : Nat := 4983230072969 + 3 ^ 40 * 6851854 * 2
def baseEnd_6851854 : Nat := 1172764825477246774471301

theorem tailTrace_6851854 : CollatzResearch.WordTrace tailWord_6851854 prefixEnd_6851854 1172764825477246774471301 := by
  unfold tailWord_6851854
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238455764863829542956327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166605097412607090895767077 31238455764863829542956327)
  ·
    refine ⟨46857683647295744314434491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31238455764863829542956327 46857683647295744314434491)
    ·
      refine ⟨70286525470943616471651737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46857683647295744314434491 70286525470943616471651737)
      ·
        refine ⟨52714894103207712353738803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70286525470943616471651737 52714894103207712353738803)
        ·
          refine ⟨79072341154811568530608205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52714894103207712353738803 79072341154811568530608205)
          ·
            refine ⟨29652127933054338198978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79072341154811568530608205 29652127933054338198978077)
            ·
              refine ⟨11119547974895376824616779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29652127933054338198978077 11119547974895376824616779)
              ·
                refine ⟨16679321962343065236925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11119547974895376824616779 16679321962343065236925169)
                ·
                  refine ⟨12509491471757298927693877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16679321962343065236925169 12509491471757298927693877)
                  ·
                    refine ⟨1172764825477246774471301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12509491471757298927693877 1172764825477246774471301)
                    ·
                      rfl

theorem cell23_6851854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_6851854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851854 prefixEnd_6851854 := by exact prefixLift 6851854
  have htrace : WordTrace (prefixWord ++ tailWord_6851854) baseStart_6851854 baseEnd_6851854 := by
    simpa [prefixWord, tailWord_6851854, baseEnd_6851854] using wordTrace_append hprefix tailTrace_6851854
  have hstable : (prefixWord ++ tailWord_6851854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851854).length < 2 ^ (prefixWord ++ tailWord_6851854).sum := by decide
  have hdescent : baseEnd_6851854 < baseStart_6851854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851857 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_6851857 : Nat := 118140960795 + 6851857 * 2 ^ 59
def prefixEnd_6851857 : Nat := 4983230072969 + 3 ^ 40 * 6851857 * 2
def baseEnd_6851857 : Nat := 3518296016873703811676389

theorem tailTrace_6851857 : CollatzResearch.WordTrace tailWord_6851857 prefixEnd_6851857 3518296016873703811676389 := by
  unfold tailWord_6851857
  simp only [CollatzResearch.WordTrace]
  refine ⟨249907755537899767856009825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166605170358599845237339883 249907755537899767856009825)
  ·
    refine ⟨187430816653424825892007369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249907755537899767856009825 187430816653424825892007369)
    ·
      refine ⟨140573112490068619419005527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187430816653424825892007369 140573112490068619419005527)
      ·
        refine ⟨210859668735102929128508291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140573112490068619419005527 210859668735102929128508291)
        ·
          refine ⟨316289503102654393692762437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210859668735102929128508291 316289503102654393692762437)
          ·
            refine ⟨59304281831747698817392957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316289503102654393692762437 59304281831747698817392957)
            ·
              refine ⟨22239105686905387056522359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59304281831747698817392957 22239105686905387056522359)
              ·
                refine ⟨33358658530358080584783539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22239105686905387056522359 33358658530358080584783539)
                ·
                  refine ⟨50037987795537120877175309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33358658530358080584783539 50037987795537120877175309)
                  ·
                    refine ⟨18764245423326420328940741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50037987795537120877175309 18764245423326420328940741)
                    ·
                      refine ⟨3518296016873703811676389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18764245423326420328940741 3518296016873703811676389)
                      ·
                        rfl

theorem cell23_6851857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_6851857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851857 prefixEnd_6851857 := by exact prefixLift 6851857
  have htrace : WordTrace (prefixWord ++ tailWord_6851857) baseStart_6851857 baseEnd_6851857 := by
    simpa [prefixWord, tailWord_6851857, baseEnd_6851857] using wordTrace_append hprefix tailTrace_6851857
  have hstable : (prefixWord ++ tailWord_6851857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851857).length < 2 ^ (prefixWord ++ tailWord_6851857).sum := by decide
  have hdescent : baseEnd_6851857 < baseStart_6851857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851867 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 7, 4]
def baseStart_6851867 : Nat := 118140960795 + 6851867 * 2 ^ 59
def prefixEnd_6851867 : Nat := 4983230072969 + 3 ^ 40 * 6851867 * 2
def baseEnd_6851867 : Nat := 1172767050560082924183781

theorem tailTrace_6851867 : CollatzResearch.WordTrace tailWord_6851867 prefixEnd_6851867 1172767050560082924183781 := by
  unfold tailWord_6851867
  simp only [CollatzResearch.WordTrace]
  refine ⟨249908120267863539563873855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166605413511909026375915903 249908120267863539563873855)
  ·
    refine ⟨374862180401795309345810783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249908120267863539563873855 374862180401795309345810783)
    ·
      refine ⟨562293270602692964018716175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374862180401795309345810783 562293270602692964018716175)
      ·
        refine ⟨843439905904039446028074263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562293270602692964018716175 843439905904039446028074263)
        ·
          refine ⟨1265159858856059169042111395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843439905904039446028074263 1265159858856059169042111395)
          ·
            refine ⟨1897739788284088753563167093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265159858856059169042111395 1897739788284088753563167093)
            ·
              refine ⟨177913105151633320646546915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1897739788284088753563167093 177913105151633320646546915)
              ·
                refine ⟨266869657727449980969820373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177913105151633320646546915 266869657727449980969820373)
                ·
                  refine ⟨6254757602987108928980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266869657727449980969820373 6254757602987108928980165)
                  ·
                    refine ⟨1172767050560082924183781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6254757602987108928980165 1172767050560082924183781)
                    ·
                      rfl

theorem cell23_6851867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 4].length) (baseStart_6851867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851867 prefixEnd_6851867 := by exact prefixLift 6851867
  have htrace : WordTrace (prefixWord ++ tailWord_6851867) baseStart_6851867 baseEnd_6851867 := by
    simpa [prefixWord, tailWord_6851867, baseEnd_6851867] using wordTrace_append hprefix tailTrace_6851867
  have hstable : (prefixWord ++ tailWord_6851867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851867).length < 2 ^ (prefixWord ++ tailWord_6851867).sum := by decide
  have hdescent : baseEnd_6851867 < baseStart_6851867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851907 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3]
def baseStart_6851907 : Nat := 118140960795 + 6851907 * 2 ^ 59
def prefixEnd_6851907 : Nat := 4983230072969 + 3 ^ 40 * 6851907 * 2
def baseEnd_6851907 : Nat := 3518321690906428616051159

theorem tailTrace_6851907 : CollatzResearch.WordTrace tailWord_6851907 prefixEnd_6851907 3518321690906428616051159 := by
  unfold tailWord_6851907
  simp only [CollatzResearch.WordTrace]
  refine ⟨249909579187718626395329975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166606386125145750930219983 249909579187718626395329975)
  ·
    refine ⟨374864368781577939592994963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249909579187718626395329975 374864368781577939592994963)
    ·
      refine ⟨562296553172366909389492445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374864368781577939592994963 562296553172366909389492445)
      ·
        refine ⟨210861207439637591021059667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 562296553172366909389492445 210861207439637591021059667)
        ·
          refine ⟨316291811159456386531589501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210861207439637591021059667 316291811159456386531589501)
          ·
            refine ⟨118609429184796144949346063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316291811159456386531589501 118609429184796144949346063)
            ·
              refine ⟨177914143777194217424019095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118609429184796144949346063 177914143777194217424019095)
              ·
                refine ⟨266871215665791326136028643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177914143777194217424019095 266871215665791326136028643)
                ·
                  refine ⟨400306823498686989204042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266871215665791326136028643 400306823498686989204042965)
                  ·
                    refine ⟨9382191175750476309469757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 400306823498686989204042965 9382191175750476309469757)
                    ·
                      refine ⟨3518321690906428616051159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382191175750476309469757 3518321690906428616051159)
                      ·
                        rfl

theorem cell23_6851907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_6851907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851907 prefixEnd_6851907 := by exact prefixLift 6851907
  have htrace : WordTrace (prefixWord ++ tailWord_6851907) baseStart_6851907 baseEnd_6851907 := by
    simpa [prefixWord, tailWord_6851907, baseEnd_6851907] using wordTrace_append hprefix tailTrace_6851907
  have hstable : (prefixWord ++ tailWord_6851907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851907).length < 2 ^ (prefixWord ++ tailWord_6851907).sum := by decide
  have hdescent : baseEnd_6851907 < baseStart_6851907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851964 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_6851964 : Nat := 118140960795 + 6851964 * 2 ^ 59
def prefixEnd_6851964 : Nat := 4983230072969 + 3 ^ 40 * 6851964 * 2
def baseEnd_6851964 : Nat := 3518350959303734893038397

theorem tailTrace_6851964 : CollatzResearch.WordTrace tailWord_6851964 prefixEnd_6851964 3518350959303734893038397 := by
  unfold tailWord_6851964
  simp only [CollatzResearch.WordTrace]
  refine ⟨124955829074256062565077473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166607772099008083420103297 124955829074256062565077473)
  ·
    refine ⟨93716871805692046923808105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124955829074256062565077473 93716871805692046923808105)
    ·
      refine ⟨70287653854269035192856079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93716871805692046923808105 70287653854269035192856079)
      ·
        refine ⟨105431480781403552789284119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70287653854269035192856079 105431480781403552789284119)
        ·
          refine ⟨158147221172105329183926179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105431480781403552789284119 158147221172105329183926179)
          ·
            refine ⟨237220831758157993775889269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158147221172105329183926179 237220831758157993775889269)
            ·
              refine ⟨22239452977327311916489619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237220831758157993775889269 22239452977327311916489619)
              ·
                refine ⟨33359179465990967874734429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22239452977327311916489619 33359179465990967874734429)
                ·
                  refine ⟨12509692299746612953025411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33359179465990967874734429 12509692299746612953025411)
                  ·
                    refine ⟨18764538449619919429538117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12509692299746612953025411 18764538449619919429538117)
                    ·
                      refine ⟨3518350959303734893038397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18764538449619919429538117 3518350959303734893038397)
                      ·
                        rfl

theorem cell23_6851964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_6851964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851964 prefixEnd_6851964 := by exact prefixLift 6851964
  have htrace : WordTrace (prefixWord ++ tailWord_6851964) baseStart_6851964 baseEnd_6851964 := by
    simpa [prefixWord, tailWord_6851964, baseEnd_6851964] using wordTrace_append hprefix tailTrace_6851964
  have hstable : (prefixWord ++ tailWord_6851964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851964).length < 2 ^ (prefixWord ++ tailWord_6851964).sum := by decide
  have hdescent : baseEnd_6851964 < baseStart_6851964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6851994 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6851994 : Nat := 118140960795 + 6851994 * 2 ^ 59
def prefixEnd_6851994 : Nat := 4983230072969 + 3 ^ 40 * 6851994 * 2
def baseEnd_6851994 : Nat := 3518366363723369775663259

theorem tailTrace_6851994 : CollatzResearch.WordTrace tailWord_6851994 prefixEnd_6851994 3518366363723369775663259 := by
  unfold tailWord_6851994
  simp only [CollatzResearch.WordTrace]
  refine ⟨62478188084600860063436759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166608501558935626835831357 62478188084600860063436759)
  ·
    refine ⟨93717282126901290095155139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62478188084600860063436759 93717282126901290095155139)
    ·
      refine ⟨140575923190351935142732709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93717282126901290095155139 140575923190351935142732709)
      ·
        refine ⟨26357985598190987839262383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140575923190351935142732709 26357985598190987839262383)
        ·
          refine ⟨39536978397286481758893575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26357985598190987839262383 39536978397286481758893575)
          ·
            refine ⟨59305467595929722638340363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39536978397286481758893575 59305467595929722638340363)
            ·
              refine ⟨88958201393894583957510545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59305467595929722638340363 88958201393894583957510545)
              ·
                refine ⟨66718651045420937968132909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88958201393894583957510545 66718651045420937968132909)
                ·
                  refine ⟨25019494142032851738049841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66718651045420937968132909 25019494142032851738049841)
                  ·
                    refine ⟨18764620606524638803537381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25019494142032851738049841 18764620606524638803537381)
                    ·
                      refine ⟨3518366363723369775663259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18764620606524638803537381 3518366363723369775663259)
                      ·
                        rfl

theorem cell23_6851994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6851994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6851994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6851994 prefixEnd_6851994 := by exact prefixLift 6851994
  have htrace : WordTrace (prefixWord ++ tailWord_6851994) baseStart_6851994 baseEnd_6851994 := by
    simpa [prefixWord, tailWord_6851994, baseEnd_6851994] using wordTrace_append hprefix tailTrace_6851994
  have hstable : (prefixWord ++ tailWord_6851994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6851994).length < 2 ^ (prefixWord ++ tailWord_6851994).sum := by decide
  have hdescent : baseEnd_6851994 < baseStart_6851994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6851994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852008 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6852008 : Nat := 118140960795 + 6852008 * 2 ^ 59
def prefixEnd_6852008 : Nat := 4983230072969 + 3 ^ 40 * 6852008 * 2
def baseEnd_6852008 : Nat := 1172791184150844240296065

theorem tailTrace_6852008 : CollatzResearch.WordTrace tailWord_6852008 prefixEnd_6852008 1172791184150844240296065 := by
  unfold tailWord_6852008
  simp only [CollatzResearch.WordTrace]
  refine ⟨124956631480176360322378339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166608841973568480429837785 124956631480176360322378339)
  ·
    refine ⟨187434947220264540483567509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124956631480176360322378339 187434947220264540483567509)
    ·
      refine ⟨8786013150949900335167227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187434947220264540483567509 8786013150949900335167227)
      ·
        refine ⟨13179019726424850502750841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786013150949900335167227 13179019726424850502750841)
        ·
          refine ⟨9884264794818637877063131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13179019726424850502750841 9884264794818637877063131)
          ·
            refine ⟨14826397192227956815594697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884264794818637877063131 14826397192227956815594697)
            ·
              refine ⟨11119797894170967611696023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14826397192227956815594697 11119797894170967611696023)
              ·
                refine ⟨16679696841256451417544035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11119797894170967611696023 16679696841256451417544035)
                ·
                  refine ⟨25019545261884677126316053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16679696841256451417544035 25019545261884677126316053)
                  ·
                    refine ⟨1172791184150844240296065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25019545261884677126316053 1172791184150844240296065)
                    ·
                      rfl

theorem cell23_6852008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6852008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852008 prefixEnd_6852008 := by exact prefixLift 6852008
  have htrace : WordTrace (prefixWord ++ tailWord_6852008) baseStart_6852008 baseEnd_6852008 := by
    simpa [prefixWord, tailWord_6852008, baseEnd_6852008] using wordTrace_append hprefix tailTrace_6852008
  have hstable : (prefixWord ++ tailWord_6852008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852008).length < 2 ^ (prefixWord ++ tailWord_6852008).sum := by decide
  have hdescent : baseEnd_6852008 < baseStart_6852008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852021 : List Nat := [1, 3, 3, 2, 2, 2, 3, 7]
def baseStart_6852021 : Nat := 118140960795 + 6852021 * 2 ^ 59
def prefixEnd_6852021 : Nat := 4983230072969 + 3 ^ 40 * 6852021 * 2
def baseEnd_6852021 : Nat := 130310378803742265556505

theorem tailTrace_6852021 : CollatzResearch.WordTrace tailWord_6852021 prefixEnd_6852021 130310378803742265556505 := by
  unfold tailWord_6852021
  simp only [CollatzResearch.WordTrace]
  refine ⟨249913737109305623864979917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166609158072870415909986611 249913737109305623864979917)
  ·
    refine ⟨93717651415989608949367469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249913737109305623864979917 93717651415989608949367469)
    ·
      refine ⟨35144119280996103356012801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93717651415989608949367469 35144119280996103356012801)
      ·
        refine ⟨26358089460747077517009601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35144119280996103356012801 26358089460747077517009601)
        ·
          refine ⟨19768567095560308137757201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26358089460747077517009601 19768567095560308137757201)
          ·
            refine ⟨14826425321670231103317901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19768567095560308137757201 14826425321670231103317901)
            ·
              refine ⟨5559909495626336663744213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14826425321670231103317901 5559909495626336663744213)
              ·
                refine ⟨130310378803742265556505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5559909495626336663744213 130310378803742265556505)
                ·
                  rfl

theorem cell23_6852021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 7].length) (baseStart_6852021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852021 prefixEnd_6852021 := by exact prefixLift 6852021
  have htrace : WordTrace (prefixWord ++ tailWord_6852021) baseStart_6852021 baseEnd_6852021 := by
    simpa [prefixWord, tailWord_6852021, baseEnd_6852021] using wordTrace_append hprefix tailTrace_6852021
  have hstable : (prefixWord ++ tailWord_6852021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852021).length < 2 ^ (prefixWord ++ tailWord_6852021).sum := by decide
  have hdescent : baseEnd_6852021 < baseStart_6852021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852065 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_6852065 : Nat := 118140960795 + 6852065 * 2 ^ 59
def prefixEnd_6852065 : Nat := 4983230072969 + 3 ^ 40 * 6852065 * 2
def baseEnd_6852065 : Nat := 3518402820849838997875433

theorem tailTrace_6852065 : CollatzResearch.WordTrace tailWord_6852065 prefixEnd_6852065 3518402820849838997875433 := by
  unfold tailWord_6852065
  simp only [CollatzResearch.WordTrace]
  refine ⟨249915341921146219379581649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166610227947430812919721099 249915341921146219379581649)
  ·
    refine ⟨187436506440859664534686237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249915341921146219379581649 187436506440859664534686237)
    ·
      refine ⟨70288689915322374200507339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187436506440859664534686237 70288689915322374200507339)
      ·
        refine ⟨105433034872983561300761009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70288689915322374200507339 105433034872983561300761009)
        ·
          refine ⟨79074776154737670975570757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105433034872983561300761009 79074776154737670975570757)
          ·
            refine ⟨14826520529013313307919517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79074776154737670975570757 14826520529013313307919517)
            ·
              refine ⟨5559945198379992490469819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14826520529013313307919517 5559945198379992490469819)
              ·
                refine ⟨8339917797569988735704729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559945198379992490469819 8339917797569988735704729)
                ·
                  refine ⟨6254938348177491551778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339917797569988735704729 6254938348177491551778547)
                  ·
                    refine ⟨9382407522266237327667821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6254938348177491551778547 9382407522266237327667821)
                    ·
                      refine ⟨3518402820849838997875433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382407522266237327667821 3518402820849838997875433)
                      ·
                        rfl

theorem cell23_6852065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_6852065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852065 prefixEnd_6852065 := by exact prefixLift 6852065
  have htrace : WordTrace (prefixWord ++ tailWord_6852065) baseStart_6852065 baseEnd_6852065 := by
    simpa [prefixWord, tailWord_6852065, baseEnd_6852065] using wordTrace_append hprefix tailTrace_6852065
  have hstable : (prefixWord ++ tailWord_6852065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852065).length < 2 ^ (prefixWord ++ tailWord_6852065).sum := by decide
  have hdescent : baseEnd_6852065 < baseStart_6852065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852088 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_6852088 : Nat := 118140960795 + 6852088 * 2 ^ 59
def prefixEnd_6852088 : Nat := 4983230072969 + 3 ^ 40 * 6852088 * 2
def baseEnd_6852088 : Nat := 3518414630904892407887827

theorem tailTrace_6852088 : CollatzResearch.WordTrace tailWord_6852088 prefixEnd_6852088 3518414630904892407887827 := by
  unfold tailWord_6852088
  simp only [CollatzResearch.WordTrace]
  refine ⟨124958090400031447153834459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166610787200041929538445945 124958090400031447153834459)
  ·
    refine ⟨187437135600047170730751689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124958090400031447153834459 187437135600047170730751689)
    ·
      refine ⟨140577851700035378048063767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187437135600047170730751689 140577851700035378048063767)
      ·
        refine ⟨210866777550053067072095651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140577851700035378048063767 210866777550053067072095651)
        ·
          refine ⟨316300166325079600608143477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210866777550053067072095651 316300166325079600608143477)
          ·
            refine ⟨29653140592976212557013451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316300166325079600608143477 29653140592976212557013451)
            ·
              refine ⟨44479710889464318835520177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653140592976212557013451 44479710889464318835520177)
              ·
                refine ⟨33359783167098239126640133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44479710889464318835520177 33359783167098239126640133)
                ·
                  refine ⟨6254959343830919836245025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33359783167098239126640133 6254959343830919836245025)
                  ·
                    refine ⟨4691219507873189877183769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254959343830919836245025 4691219507873189877183769)
                    ·
                      refine ⟨3518414630904892407887827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691219507873189877183769 3518414630904892407887827)
                      ·
                        rfl

theorem cell23_6852088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_6852088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852088 prefixEnd_6852088 := by exact prefixLift 6852088
  have htrace : WordTrace (prefixWord ++ tailWord_6852088) baseStart_6852088 baseEnd_6852088 := by
    simpa [prefixWord, tailWord_6852088, baseEnd_6852088] using wordTrace_append hprefix tailTrace_6852088
  have hstable : (prefixWord ++ tailWord_6852088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852088).length < 2 ^ (prefixWord ++ tailWord_6852088).sum := by decide
  have hdescent : baseEnd_6852088 < baseStart_6852088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852116 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6852116 : Nat := 118140960795 + 6852116 * 2 ^ 59
def prefixEnd_6852116 : Nat := 4983230072969 + 3 ^ 40 * 6852116 * 2
def baseEnd_6852116 : Nat := 3518429008363218298337699

theorem tailTrace_6852116 : CollatzResearch.WordTrace tailWord_6852116 prefixEnd_6852116 3518429008363218298337699 := by
  unfold tailWord_6852116
  simp only [CollatzResearch.WordTrace]
  refine ⟨124958601021980727544844101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166611468029307636726458801 124958601021980727544844101)
  ·
    refine ⟨23429737691621386414658269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124958601021980727544844101 23429737691621386414658269)
    ·
      refine ⟨8786151634358019905496851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23429737691621386414658269 8786151634358019905496851)
      ·
        refine ⟨13179227451537029858245277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786151634358019905496851 13179227451537029858245277)
        ·
          refine ⟨4942210294326386196841979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13179227451537029858245277 4942210294326386196841979)
          ·
            refine ⟨7413315441489579295262969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942210294326386196841979 7413315441489579295262969)
            ·
              refine ⟨5559986581117184471447227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7413315441489579295262969 5559986581117184471447227)
              ·
                refine ⟨8339979871675776707170841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559986581117184471447227 8339979871675776707170841)
                ·
                  refine ⟨6254984903756832530378131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339979871675776707170841 6254984903756832530378131)
                  ·
                    refine ⟨9382477355635248795567197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6254984903756832530378131 9382477355635248795567197)
                    ·
                      refine ⟨3518429008363218298337699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382477355635248795567197 3518429008363218298337699)
                      ·
                        rfl

theorem cell23_6852116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6852116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852116 prefixEnd_6852116 := by exact prefixLift 6852116
  have htrace : WordTrace (prefixWord ++ tailWord_6852116) baseStart_6852116 baseEnd_6852116 := by
    simpa [prefixWord, tailWord_6852116, baseEnd_6852116] using wordTrace_append hprefix tailTrace_6852116
  have hstable : (prefixWord ++ tailWord_6852116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852116).length < 2 ^ (prefixWord ++ tailWord_6852116).sum := by decide
  have hdescent : baseEnd_6852116 < baseStart_6852116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852171 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 3, 4]
def baseStart_6852171 : Nat := 118140960795 + 6852171 * 2 ^ 59
def prefixEnd_6852171 : Nat := 4983230072969 + 3 ^ 40 * 6852171 * 2
def baseEnd_6852171 : Nat := 1172819083266405194383315

theorem tailTrace_6852171 : CollatzResearch.WordTrace tailWord_6852171 prefixEnd_6852171 1172819083266405194383315 := by
  unfold tailWord_6852171
  simp only [CollatzResearch.WordTrace]
  refine ⟨249919208058762199482940367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166612805372508132988626911 249919208058762199482940367)
  ·
    refine ⟨374878812088143299224410551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249919208058762199482940367 374878812088143299224410551)
    ·
      refine ⟨562318218132214948836615827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374878812088143299224410551 562318218132214948836615827)
      ·
        refine ⟨843477327198322423254923741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562318218132214948836615827 843477327198322423254923741)
        ·
          refine ⟨316303997699370908720596403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 843477327198322423254923741 316303997699370908720596403)
          ·
            refine ⟨474455996549056363080894605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316303997699370908720596403 474455996549056363080894605)
            ·
              refine ⟨177920998705896136155335477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474455996549056363080894605 177920998705896136155335477)
              ·
                refine ⟨16680093628677762764562701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177920998705896136155335477 16680093628677762764562701)
                ·
                  refine ⟨6255035110754161036711013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16680093628677762764562701 6255035110754161036711013)
                  ·
                    refine ⟨1172819083266405194383315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255035110754161036711013 1172819083266405194383315)
                    ·
                      rfl

theorem cell23_6852171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 4].length) (baseStart_6852171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852171 prefixEnd_6852171 := by exact prefixLift 6852171
  have htrace : WordTrace (prefixWord ++ tailWord_6852171) baseStart_6852171 baseEnd_6852171 := by
    simpa [prefixWord, tailWord_6852171, baseEnd_6852171] using wordTrace_append hprefix tailTrace_6852171
  have hstable : (prefixWord ++ tailWord_6852171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852171).length < 2 ^ (prefixWord ++ tailWord_6852171).sum := by decide
  have hdescent : baseEnd_6852171 < baseStart_6852171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852178 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_6852178 : Nat := 118140960795 + 6852178 * 2 ^ 59
def prefixEnd_6852178 : Nat := 4983230072969 + 3 ^ 40 * 6852178 * 2
def baseEnd_6852178 : Nat := 3518460844163797055762413

theorem tailTrace_6852178 : CollatzResearch.WordTrace tailWord_6852178 prefixEnd_6852178 3518460844163797055762413 := by
  unfold tailWord_6852178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62479865842434209919611297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166612975579824559785630125 62479865842434209919611297)
  ·
    refine ⟨46859899381825657439708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62479865842434209919611297 46859899381825657439708473)
    ·
      refine ⟨35144924536369243079781355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46859899381825657439708473 35144924536369243079781355)
      ·
        refine ⟨52717386804553864619672033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35144924536369243079781355 52717386804553864619672033)
        ·
          refine ⟨39538040103415398464754025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52717386804553864619672033 39538040103415398464754025)
          ·
            refine ⟨29653530077561548848565519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39538040103415398464754025 29653530077561548848565519)
            ·
              refine ⟨44480295116342323272848279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653530077561548848565519 44480295116342323272848279)
              ·
                refine ⟨66720442674513484909272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44480295116342323272848279 66720442674513484909272419)
                ·
                  refine ⟨100080664011770227363908629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66720442674513484909272419 100080664011770227363908629)
                  ·
                    refine ⟨4691281125551729407683217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100080664011770227363908629 4691281125551729407683217)
                    ·
                      refine ⟨3518460844163797055762413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691281125551729407683217 3518460844163797055762413)
                      ·
                        rfl

theorem cell23_6852178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_6852178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852178 prefixEnd_6852178 := by exact prefixLift 6852178
  have htrace : WordTrace (prefixWord ++ tailWord_6852178) baseStart_6852178 baseEnd_6852178 := by
    simpa [prefixWord, tailWord_6852178, baseEnd_6852178] using wordTrace_append hprefix tailTrace_6852178
  have hstable : (prefixWord ++ tailWord_6852178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852178).length < 2 ^ (prefixWord ++ tailWord_6852178).sum := by decide
  have hdescent : baseEnd_6852178 < baseStart_6852178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852181 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6852181 : Nat := 118140960795 + 6852181 * 2 ^ 59
def prefixEnd_6852181 : Nat := 4983230072969 + 3 ^ 40 * 6852181 * 2
def baseEnd_6852181 : Nat := 3518462384605760544024899

theorem tailTrace_6852181 : CollatzResearch.WordTrace tailWord_6852181 prefixEnd_6852181 3518462384605760544024899 := by
  unfold tailWord_6852181
  simp only [CollatzResearch.WordTrace]
  refine ⟨249919572788725971190804397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166613048525817314127202931 249919572788725971190804397)
  ·
    refine ⟨93719839795772239196551649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249919572788725971190804397 93719839795772239196551649)
    ·
      refine ⟨70289879846829179397413737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93719839795772239196551649 70289879846829179397413737)
      ·
        refine ⟨52717409885121884548060303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70289879846829179397413737 52717409885121884548060303)
        ·
          refine ⟨79076114827682826822090455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52717409885121884548060303 79076114827682826822090455)
          ·
            refine ⟨118614172241524240233135683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79076114827682826822090455 118614172241524240233135683)
            ·
              refine ⟨177921258362286360349703525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118614172241524240233135683 177921258362286360349703525)
              ·
                refine ⟨33360235942928692565569411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177921258362286360349703525 33360235942928692565569411)
                ·
                  refine ⟨50040353914393038848354117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33360235942928692565569411 50040353914393038848354117)
                  ·
                    refine ⟨9382566358948694784066397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50040353914393038848354117 9382566358948694784066397)
                    ·
                      refine ⟨3518462384605760544024899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382566358948694784066397 3518462384605760544024899)
                      ·
                        rfl

theorem cell23_6852181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6852181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852181 prefixEnd_6852181 := by exact prefixLift 6852181
  have htrace : WordTrace (prefixWord ++ tailWord_6852181) baseStart_6852181 baseEnd_6852181 := by
    simpa [prefixWord, tailWord_6852181, baseEnd_6852181] using wordTrace_append hprefix tailTrace_6852181
  have hstable : (prefixWord ++ tailWord_6852181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852181).length < 2 ^ (prefixWord ++ tailWord_6852181).sum := by decide
  have hdescent : baseEnd_6852181 < baseStart_6852181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852184 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 10]
def baseStart_6852184 : Nat := 118140960795 + 6852184 * 2 ^ 59
def prefixEnd_6852184 : Nat := 4983230072969 + 3 ^ 40 * 6852184 * 2
def baseEnd_6852184 : Nat := 390940436116413781365265

theorem tailTrace_6852184 : CollatzResearch.WordTrace tailWord_6852184 prefixEnd_6852184 390940436116413781365265 := by
  unfold tailWord_6852184
  simp only [CollatzResearch.WordTrace]
  refine ⟨124959841103857551351581803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166613121471810068468775737 124959841103857551351581803)
  ·
    refine ⟨187439761655786327027372705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124959841103857551351581803 187439761655786327027372705)
    ·
      refine ⟨140579821241839745270529529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187439761655786327027372705 140579821241839745270529529)
      ·
        refine ⟨105434865931379808952897147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140579821241839745270529529 105434865931379808952897147)
        ·
          refine ⟨158152298897069713429345721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105434865931379808952897147 158152298897069713429345721)
          ·
            refine ⟨118614224172802285072009291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158152298897069713429345721 118614224172802285072009291)
            ·
              refine ⟨177921336259203427608013937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118614224172802285072009291 177921336259203427608013937)
              ·
                refine ⟨133441002194402570706010453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177921336259203427608013937 133441002194402570706010453)
                ·
                  refine ⟨390940436116413781365265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133441002194402570706010453 390940436116413781365265)
                  ·
                    rfl

theorem cell23_6852184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_6852184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852184 prefixEnd_6852184 := by exact prefixLift 6852184
  have htrace : WordTrace (prefixWord ++ tailWord_6852184) baseStart_6852184 baseEnd_6852184 := by
    simpa [prefixWord, tailWord_6852184, baseEnd_6852184] using wordTrace_append hprefix tailTrace_6852184
  have hstable : (prefixWord ++ tailWord_6852184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852184).length < 2 ^ (prefixWord ++ tailWord_6852184).sum := by decide
  have hdescent : baseEnd_6852184 < baseStart_6852184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852188 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6852188 : Nat := 118140960795 + 6852188 * 2 ^ 59
def prefixEnd_6852188 : Nat := 4983230072969 + 3 ^ 40 * 6852188 * 2
def baseEnd_6852188 : Nat := 1172821992990114005545789

theorem tailTrace_6852188 : CollatzResearch.WordTrace tailWord_6852188 prefixEnd_6852188 1172821992990114005545789 := by
  unfold tailWord_6852188
  simp only [CollatzResearch.WordTrace]
  refine ⟨124959914049850305693154609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166613218733133740924206145 124959914049850305693154609)
  ·
    refine ⟨93719935537387729269865957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124959914049850305693154609 93719935537387729269865957)
    ·
      refine ⟨17572487913260199238099867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93719935537387729269865957 17572487913260199238099867)
      ·
        refine ⟨26358731869890298857149801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17572487913260199238099867 26358731869890298857149801)
        ·
          refine ⟨19769048902417724142862351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26358731869890298857149801 19769048902417724142862351)
          ·
            refine ⟨29653573353626586214293527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19769048902417724142862351 29653573353626586214293527)
            ·
              refine ⟨44480360030439879321440291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653573353626586214293527 44480360030439879321440291)
              ·
                refine ⟨66720540045659818982160437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44480360030439879321440291 66720540045659818982160437)
                ·
                  refine ⟨6255050629280608029577541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66720540045659818982160437 6255050629280608029577541)
                  ·
                    refine ⟨1172821992990114005545789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255050629280608029577541 1172821992990114005545789)
                    ·
                      rfl

theorem cell23_6852188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6852188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852188 prefixEnd_6852188 := by exact prefixLift 6852188
  have htrace : WordTrace (prefixWord ++ tailWord_6852188) baseStart_6852188 baseEnd_6852188 := by
    simpa [prefixWord, tailWord_6852188, baseEnd_6852188] using wordTrace_append hprefix tailTrace_6852188
  have hstable : (prefixWord ++ tailWord_6852188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852188).length < 2 ^ (prefixWord ++ tailWord_6852188).sum := by decide
  have hdescent : baseEnd_6852188 < baseStart_6852188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852221 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6852221 : Nat := 118140960795 + 6852221 * 2 ^ 59
def prefixEnd_6852221 : Nat := 4983230072969 + 3 ^ 40 * 6852221 * 2
def baseEnd_6852221 : Nat := 3518482923831940387524715

theorem tailTrace_6852221 : CollatzResearch.WordTrace tailWord_6852221 prefixEnd_6852221 3518482923831940387524715 := by
  unfold tailWord_6852221
  simp only [CollatzResearch.WordTrace]
  refine ⟨249921031708581058022260517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166614021139054038681507011 249921031708581058022260517)
  ·
    refine ⟨46860193445358948379173847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249921031708581058022260517 46860193445358948379173847)
    ·
      refine ⟨70290290168038422568760771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46860193445358948379173847 70290290168038422568760771)
      ·
        refine ⟨105435435252057633853141157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70290290168038422568760771 105435435252057633853141157)
        ·
          refine ⟨19769144109760806347463967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105435435252057633853141157 19769144109760806347463967)
          ·
            refine ⟨29653716164641209521195951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19769144109760806347463967 29653716164641209521195951)
            ·
              refine ⟨44480574246961814281793927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653716164641209521195951 44480574246961814281793927)
              ·
                refine ⟨66720861370442721422690891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44480574246961814281793927 66720861370442721422690891)
                ·
                  refine ⟨100081292055664082134036337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66720861370442721422690891 100081292055664082134036337)
                  ·
                    refine ⟨75060969041748061600527253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100081292055664082134036337 75060969041748061600527253)
                    ·
                      refine ⟨3518482923831940387524715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75060969041748061600527253 3518482923831940387524715)
                      ·
                        rfl

theorem cell23_6852221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6852221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852221 prefixEnd_6852221 := by exact prefixLift 6852221
  have htrace : WordTrace (prefixWord ++ tailWord_6852221) baseStart_6852221 baseEnd_6852221 := by
    simpa [prefixWord, tailWord_6852221, baseEnd_6852221] using wordTrace_append hprefix tailTrace_6852221
  have hstable : (prefixWord ++ tailWord_6852221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852221).length < 2 ^ (prefixWord ++ tailWord_6852221).sum := by decide
  have hdescent : baseEnd_6852221 < baseStart_6852221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852248 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_6852248 : Nat := 118140960795 + 6852248 * 2 ^ 59
def prefixEnd_6852248 : Nat := 4983230072969 + 3 ^ 40 * 6852248 * 2
def baseEnd_6852248 : Nat := 1172832262603203927295697

theorem tailTrace_6852248 : CollatzResearch.WordTrace tailWord_6852248 prefixEnd_6852248 1172832262603203927295697 := by
  unfold tailWord_6852248
  simp only [CollatzResearch.WordTrace]
  refine ⟨124961008239741620816746699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166614677652988827755662265 124961008239741620816746699)
  ·
    refine ⟨187441512359612431225120049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124961008239741620816746699 187441512359612431225120049)
    ·
      refine ⟨140581134269709323418840037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187441512359612431225120049 140581134269709323418840037)
      ·
        refine ⟨26358962675570498141032507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140581134269709323418840037 26358962675570498141032507)
        ·
          refine ⟨39538444013355747211548761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26358962675570498141032507 39538444013355747211548761)
          ·
            refine ⟨29653833010016810408661571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39538444013355747211548761 29653833010016810408661571)
            ·
              refine ⟨44480749515025215612992357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653833010016810408661571 44480749515025215612992357)
              ·
                refine ⟨8340140534067227927436067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44480749515025215612992357 8340140534067227927436067)
                ·
                  refine ⟨12510210801100841891154101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340140534067227927436067 12510210801100841891154101)
                  ·
                    refine ⟨1172832262603203927295697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12510210801100841891154101 1172832262603203927295697)
                    ·
                      rfl

theorem cell23_6852248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_6852248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852248 prefixEnd_6852248 := by exact prefixLift 6852248
  have htrace : WordTrace (prefixWord ++ tailWord_6852248) baseStart_6852248 baseEnd_6852248 := by
    simpa [prefixWord, tailWord_6852248, baseEnd_6852248] using wordTrace_append hprefix tailTrace_6852248
  have hstable : (prefixWord ++ tailWord_6852248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852248).length < 2 ^ (prefixWord ++ tailWord_6852248).sum := by decide
  have hdescent : baseEnd_6852248 < baseStart_6852248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852261 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_6852261 : Nat := 118140960795 + 6852261 * 2 ^ 59
def prefixEnd_6852261 : Nat := 4983230072969 + 3 ^ 40 * 6852261 * 2
def baseEnd_6852261 : Nat := 1172834487686040077008177

theorem tailTrace_6852261 : CollatzResearch.WordTrace tailWord_6852261 prefixEnd_6852261 1172834487686040077008177 := by
  unfold tailWord_6852261
  simp only [CollatzResearch.WordTrace]
  refine ⟨249922490628436144853716637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166614993752290763235811091 249922490628436144853716637)
  ·
    refine ⟨93720933985663554320143739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249922490628436144853716637 93720933985663554320143739)
    ·
      refine ⟨140581400978495331480215609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93720933985663554320143739 140581400978495331480215609)
      ·
        refine ⟨105436050733871498610161707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140581400978495331480215609 105436050733871498610161707)
        ·
          refine ⟨158154076100807247915242561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105436050733871498610161707 158154076100807247915242561)
          ·
            refine ⟨118615557075605435936431921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158154076100807247915242561 118615557075605435936431921)
            ·
              refine ⟨88961667806704076952323941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118615557075605435936431921 88961667806704076952323941)
              ·
                refine ⟨16680312713757014428560739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88961667806704076952323941 16680312713757014428560739)
                ·
                  refine ⟨25020469070635521642841109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16680312713757014428560739 25020469070635521642841109)
                  ·
                    refine ⟨1172834487686040077008177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25020469070635521642841109 1172834487686040077008177)
                    ·
                      rfl

theorem cell23_6852261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_6852261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852261 prefixEnd_6852261 := by exact prefixLift 6852261
  have htrace : WordTrace (prefixWord ++ tailWord_6852261) baseStart_6852261 baseEnd_6852261 := by
    simpa [prefixWord, tailWord_6852261, baseEnd_6852261] using wordTrace_append hprefix tailTrace_6852261
  have hstable : (prefixWord ++ tailWord_6852261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852261).length < 2 ^ (prefixWord ++ tailWord_6852261).sum := by decide
  have hdescent : baseEnd_6852261 < baseStart_6852261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852279 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_6852279 : Nat := 118140960795 + 6852279 * 2 ^ 59
def prefixEnd_6852279 : Nat := 4983230072969 + 3 ^ 40 * 6852279 * 2
def baseEnd_6852279 : Nat := 3518512705709901160599449

theorem tailTrace_6852279 : CollatzResearch.WordTrace tailWord_6852279 prefixEnd_6852279 3518512705709901160599449 := by
  unfold tailWord_6852279
  simp only [CollatzResearch.WordTrace]
  refine ⟨249923147142370933927871891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166615431428247289285247927 249923147142370933927871891)
  ·
    refine ⟨374884720713556400891807837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249923147142370933927871891 374884720713556400891807837)
    ·
      refine ⟨140581770267583650334427939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374884720713556400891807837 140581770267583650334427939)
      ·
        refine ⟨210872655401375475501641909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140581770267583650334427939 210872655401375475501641909)
        ·
          refine ⟨19769311443878950828278929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210872655401375475501641909 19769311443878950828278929)
          ·
            refine ⟨14826983582909213121209197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19769311443878950828278929 14826983582909213121209197)
            ·
              refine ⟨5560118843590954920453449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14826983582909213121209197 5560118843590954920453449)
              ·
                refine ⟨4170089132693216190340087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5560118843590954920453449 4170089132693216190340087)
                ·
                  refine ⟨6255133699039824285510131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170089132693216190340087 6255133699039824285510131)
                  ·
                    refine ⟨9382700548559736428265197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6255133699039824285510131 9382700548559736428265197)
                    ·
                      refine ⟨3518512705709901160599449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382700548559736428265197 3518512705709901160599449)
                      ·
                        rfl

theorem cell23_6852279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_6852279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852279 prefixEnd_6852279 := by exact prefixLift 6852279
  have htrace : WordTrace (prefixWord ++ tailWord_6852279) baseStart_6852279 baseEnd_6852279 := by
    simpa [prefixWord, tailWord_6852279, baseEnd_6852279] using wordTrace_append hprefix tailTrace_6852279
  have hstable : (prefixWord ++ tailWord_6852279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852279).length < 2 ^ (prefixWord ++ tailWord_6852279).sum := by decide
  have hdescent : baseEnd_6852279 < baseStart_6852279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852281 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6852281 : Nat := 118140960795 + 6852281 * 2 ^ 59
def prefixEnd_6852281 : Nat := 4983230072969 + 3 ^ 40 * 6852281 * 2
def baseEnd_6852281 : Nat := 3518513732671210152774439

theorem tailTrace_6852281 : CollatzResearch.WordTrace tailWord_6852281 prefixEnd_6852281 3518513732671210152774439 := by
  unfold tailWord_6852281
  simp only [CollatzResearch.WordTrace]
  refine ⟨249923220088363688269444697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166615480058909125512963131 249923220088363688269444697)
  ·
    refine ⟨187442415066272766202083523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249923220088363688269444697 187442415066272766202083523)
    ·
      refine ⟨281163622599409149303125285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187442415066272766202083523 281163622599409149303125285)
      ·
        refine ⟨52718179237389215494335991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281163622599409149303125285 52718179237389215494335991)
        ·
          refine ⟨79077268856083823241503987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52718179237389215494335991 79077268856083823241503987)
          ·
            refine ⟨118615903284125734862255981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79077268856083823241503987 118615903284125734862255981)
            ·
              refine ⟨44480963731547150573345993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118615903284125734862255981 44480963731547150573345993)
              ·
                refine ⟨33360722798660362930009495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44480963731547150573345993 33360722798660362930009495)
                ·
                  refine ⟨50041084197990544395014243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33360722798660362930009495 50041084197990544395014243)
                  ·
                    refine ⟨75061626296985816592521365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50041084197990544395014243 75061626296985816592521365)
                    ·
                      refine ⟨3518513732671210152774439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75061626296985816592521365 3518513732671210152774439)
                      ·
                        rfl

theorem cell23_6852281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6852281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852281 prefixEnd_6852281 := by exact prefixLift 6852281
  have htrace : WordTrace (prefixWord ++ tailWord_6852281) baseStart_6852281 baseEnd_6852281 := by
    simpa [prefixWord, tailWord_6852281, baseEnd_6852281] using wordTrace_append hprefix tailTrace_6852281
  have hstable : (prefixWord ++ tailWord_6852281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852281).length < 2 ^ (prefixWord ++ tailWord_6852281).sum := by decide
  have hdescent : baseEnd_6852281 < baseStart_6852281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852288 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_6852288 : Nat := 118140960795 + 6852288 * 2 ^ 59
def prefixEnd_6852288 : Nat := 4983230072969 + 3 ^ 40 * 6852288 * 2
def baseEnd_6852288 : Nat := 3518517327035791625386907

theorem tailTrace_6852288 : CollatzResearch.WordTrace tailWord_6852288 prefixEnd_6852288 3518517327035791625386907 := by
  unfold tailWord_6852288
  simp only [CollatzResearch.WordTrace]
  refine ⟨124961737699669164232474759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166615650266225552309966345 124961737699669164232474759)
  ·
    refine ⟨187442606549503746348712139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124961737699669164232474759 187442606549503746348712139)
    ·
      refine ⟨281163909824255619523068209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187442606549503746348712139 281163909824255619523068209)
      ·
        refine ⟨210872932368191714642301157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281163909824255619523068209 210872932368191714642301157)
        ·
          refine ⟨39538674819035946495431467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210872932368191714642301157 39538674819035946495431467)
          ·
            refine ⟨59308012228553919743147201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39538674819035946495431467 59308012228553919743147201)
            ·
              refine ⟨44481009171415439807360401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59308012228553919743147201 44481009171415439807360401)
              ·
                refine ⟨33360756878561579855520301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44481009171415439807360401 33360756878561579855520301)
                ·
                  refine ⟨12510283829460592445820113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33360756878561579855520301 12510283829460592445820113)
                  ·
                    refine ⟨9382712872095444334365085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12510283829460592445820113 9382712872095444334365085)
                    ·
                      refine ⟨3518517327035791625386907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382712872095444334365085 3518517327035791625386907)
                      ·
                        rfl

theorem cell23_6852288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_6852288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852288 prefixEnd_6852288 := by exact prefixLift 6852288
  have htrace : WordTrace (prefixWord ++ tailWord_6852288) baseStart_6852288 baseEnd_6852288 := by
    simpa [prefixWord, tailWord_6852288, baseEnd_6852288] using wordTrace_append hprefix tailTrace_6852288
  have hstable : (prefixWord ++ tailWord_6852288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852288).length < 2 ^ (prefixWord ++ tailWord_6852288).sum := by decide
  have hdescent : baseEnd_6852288 < baseStart_6852288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852305 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_6852305 : Nat := 118140960795 + 6852305 * 2 ^ 59
def prefixEnd_6852305 : Nat := 4983230072969 + 3 ^ 40 * 6852305 * 2
def baseEnd_6852305 : Nat := 3518526056206918058874329

theorem tailTrace_6852305 : CollatzResearch.WordTrace tailWord_6852305 prefixEnd_6852305 3518526056206918058874329 := by
  unfold tailWord_6852305
  simp only [CollatzResearch.WordTrace]
  refine ⟨249924095440276740368318369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166616063626851160245545579 249924095440276740368318369)
  ·
    refine ⟨187443071580207555276238777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249924095440276740368318369 187443071580207555276238777)
    ·
      refine ⟨140582303685155666457179083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187443071580207555276238777 140582303685155666457179083)
      ·
        refine ⟨210873455527733499685768625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140582303685155666457179083 210873455527733499685768625)
        ·
          refine ⟨158155091645800124764326469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210873455527733499685768625 158155091645800124764326469)
          ·
            refine ⟨29654079683587523393311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158155091645800124764326469 29654079683587523393311213)
            ·
              refine ⟨11120279881345321272491705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29654079683587523393311213 11120279881345321272491705)
              ·
                refine ⟨8340209911008990954368779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11120279881345321272491705 8340209911008990954368779)
                ·
                  refine ⟨12510314866513486431553169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340209911008990954368779 12510314866513486431553169)
                  ·
                    refine ⟨9382736149885114823664877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12510314866513486431553169 9382736149885114823664877)
                    ·
                      refine ⟨3518526056206918058874329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9382736149885114823664877 3518526056206918058874329)
                      ·
                        rfl

theorem cell23_6852305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_6852305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852305 prefixEnd_6852305 := by exact prefixLift 6852305
  have htrace : WordTrace (prefixWord ++ tailWord_6852305) baseStart_6852305 baseEnd_6852305 := by
    simpa [prefixWord, tailWord_6852305, baseEnd_6852305] using wordTrace_append hprefix tailTrace_6852305
  have hstable : (prefixWord ++ tailWord_6852305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852305).length < 2 ^ (prefixWord ++ tailWord_6852305).sum := by decide
  have hdescent : baseEnd_6852305 < baseStart_6852305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852308 : List Nat := [2, 4, 1, 3, 1, 1, 2, 9]
def baseStart_6852308 : Nat := 118140960795 + 6852308 * 2 ^ 59
def prefixEnd_6852308 : Nat := 4983230072969 + 3 ^ 40 * 6852308 * 2
def baseEnd_6852308 : Nat := 130315836912921538782845

theorem tailTrace_6852308 : CollatzResearch.WordTrace tailWord_6852308 prefixEnd_6852308 130315836912921538782845 := by
  unfold tailWord_6852308
  simp only [CollatzResearch.WordTrace]
  refine ⟨124962102429632935940338789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166616136572843914587118385 124962102429632935940338789)
  ·
    refine ⟨23430394205556175488813523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124962102429632935940338789 23430394205556175488813523)
    ·
      refine ⟨35145591308334263233220285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430394205556175488813523 35145591308334263233220285)
      ·
        refine ⟨13179596740625348712457607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35145591308334263233220285 13179596740625348712457607)
        ·
          refine ⟨19769395110938023068686411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13179596740625348712457607 19769395110938023068686411)
          ·
            refine ⟨29654092666407034603029617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19769395110938023068686411 29654092666407034603029617)
            ·
              refine ⟨22240569499805275952272213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29654092666407034603029617 22240569499805275952272213)
              ·
                refine ⟨130315836912921538782845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22240569499805275952272213 130315836912921538782845)
                ·
                  rfl

theorem cell23_6852308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 9].length) (baseStart_6852308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852308 prefixEnd_6852308 := by exact prefixLift 6852308
  have htrace : WordTrace (prefixWord ++ tailWord_6852308) baseStart_6852308 baseEnd_6852308 := by
    simpa [prefixWord, tailWord_6852308, baseEnd_6852308] using wordTrace_append hprefix tailTrace_6852308
  have hstable : (prefixWord ++ tailWord_6852308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852308).length < 2 ^ (prefixWord ++ tailWord_6852308).sum := by decide
  have hdescent : baseEnd_6852308 < baseStart_6852308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852331 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_6852331 : Nat := 118140960795 + 6852331 * 2 ^ 59
def prefixEnd_6852331 : Nat := 4983230072969 + 3 ^ 40 * 6852331 * 2
def baseEnd_6852331 : Nat := 3518539406703934957149209

theorem tailTrace_6852331 : CollatzResearch.WordTrace tailWord_6852331 prefixEnd_6852331 3518539406703934957149209 := by
  unfold tailWord_6852331
  simp only [CollatzResearch.WordTrace]
  refine ⟨249925043738182546808764847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166616695825455031205843231 249925043738182546808764847)
  ·
    refine ⟨374887565607273820213147271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249925043738182546808764847 374887565607273820213147271)
    ·
      refine ⟨562331348410910730319720907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374887565607273820213147271 562331348410910730319720907)
      ·
        refine ⟨843497022616366095479581361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562331348410910730319720907 843497022616366095479581361)
        ·
          refine ⟨632622766962274571609686021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843497022616366095479581361 632622766962274571609686021)
          ·
            refine ⟨118616768805426482176816129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632622766962274571609686021 118616768805426482176816129)
            ·
              refine ⟨88962576604069861632612097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118616768805426482176816129 88962576604069861632612097)
              ·
                refine ⟨66721932453052396224459073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88962576604069861632612097 66721932453052396224459073)
                ·
                  refine ⟨50041449339789297168344305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66721932453052396224459073 50041449339789297168344305)
                  ·
                    refine ⟨37531087004841972876258229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50041449339789297168344305 37531087004841972876258229)
                    ·
                      refine ⟨3518539406703934957149209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37531087004841972876258229 3518539406703934957149209)
                      ·
                        rfl

theorem cell23_6852331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_6852331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852331 prefixEnd_6852331 := by exact prefixLift 6852331
  have htrace : WordTrace (prefixWord ++ tailWord_6852331) baseStart_6852331 baseEnd_6852331 := by
    simpa [prefixWord, tailWord_6852331, baseEnd_6852331] using wordTrace_append hprefix tailTrace_6852331
  have hstable : (prefixWord ++ tailWord_6852331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852331).length < 2 ^ (prefixWord ++ tailWord_6852331).sum := by decide
  have hdescent : baseEnd_6852331 < baseStart_6852331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852351 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 8]
def baseStart_6852351 : Nat := 118140960795 + 6852351 * 2 ^ 59
def prefixEnd_6852351 : Nat := 4983230072969 + 3 ^ 40 * 6852351 * 2
def baseEnd_6852351 : Nat := 1172849892105674959633039

theorem tailTrace_6852351 : CollatzResearch.WordTrace tailWord_6852351 prefixEnd_6852351 1172849892105674959633039 := by
  unfold tailWord_6852351
  simp only [CollatzResearch.WordTrace]
  refine ⟨249925773198110090224492907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166617182132073393482995271 249925773198110090224492907)
  ·
    refine ⟨374888659797165135336739361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249925773198110090224492907 374888659797165135336739361)
    ·
      refine ⟨281166494847873851502554521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374888659797165135336739361 281166494847873851502554521)
      ·
        refine ⟨210874871135905388626915891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281166494847873851502554521 210874871135905388626915891)
        ·
          refine ⟨316312306703858082940373837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210874871135905388626915891 316312306703858082940373837)
          ·
            refine ⟨118617115013946781102640189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316312306703858082940373837 118617115013946781102640189)
            ·
              refine ⟨44481418130230042913490071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118617115013946781102640189 44481418130230042913490071)
              ·
                refine ⟨66722127195345064370235107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44481418130230042913490071 66722127195345064370235107)
                ·
                  refine ⟨100083190793017596555352661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66722127195345064370235107 100083190793017596555352661)
                  ·
                    refine ⟨1172849892105674959633039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100083190793017596555352661 1172849892105674959633039)
                    ·
                      rfl

theorem cell23_6852351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_6852351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852351 prefixEnd_6852351 := by exact prefixLift 6852351
  have htrace : WordTrace (prefixWord ++ tailWord_6852351) baseStart_6852351 baseEnd_6852351 := by
    simpa [prefixWord, tailWord_6852351, baseEnd_6852351] using wordTrace_append hprefix tailTrace_6852351
  have hstable : (prefixWord ++ tailWord_6852351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852351).length < 2 ^ (prefixWord ++ tailWord_6852351).sum := by decide
  have hdescent : baseEnd_6852351 < baseStart_6852351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852465 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_6852465 : Nat := 118140960795 + 6852465 * 2 ^ 59
def prefixEnd_6852465 : Nat := 4983230072969 + 3 ^ 40 * 6852465 * 2
def baseEnd_6852465 : Nat := 3518608213111637432873593

theorem tailTrace_6852465 : CollatzResearch.WordTrace tailWord_6852465 prefixEnd_6852465 3518608213111637432873593 := by
  unfold tailWord_6852465
  simp only [CollatzResearch.WordTrace]
  refine ⟨249929931119697087694142849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166619954079798058462761899 249929931119697087694142849)
  ·
    refine ⟨187447448339772815770607137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249929931119697087694142849 187447448339772815770607137)
    ·
      refine ⟨140585586254829611827955353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187447448339772815770607137 140585586254829611827955353)
      ·
        refine ⟨105439189691122208870966515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140585586254829611827955353 105439189691122208870966515)
        ·
          refine ⟨158158784536683313306449773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105439189691122208870966515 158158784536683313306449773)
          ·
            refine ⟨59309544201256242489918665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158158784536683313306449773 59309544201256242489918665)
            ·
              refine ⟨44482158150942181867438999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59309544201256242489918665 44482158150942181867438999)
              ·
                refine ⟨66723237226413272801158499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44482158150942181867438999 66723237226413272801158499)
                ·
                  refine ⟨100084855839619909201737749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66723237226413272801158499 100084855839619909201737749)
                  ·
                    refine ⟨4691477617482183243831457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100084855839619909201737749 4691477617482183243831457)
                    ·
                      refine ⟨3518608213111637432873593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691477617482183243831457 3518608213111637432873593)
                      ·
                        rfl

theorem cell23_6852465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_6852465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852465 prefixEnd_6852465 := by exact prefixLift 6852465
  have htrace : WordTrace (prefixWord ++ tailWord_6852465) baseStart_6852465 baseEnd_6852465 := by
    simpa [prefixWord, tailWord_6852465, baseEnd_6852465] using wordTrace_append hprefix tailTrace_6852465
  have hstable : (prefixWord ++ tailWord_6852465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852465).length < 2 ^ (prefixWord ++ tailWord_6852465).sum := by decide
  have hdescent : baseEnd_6852465 < baseStart_6852465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852492 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_6852492 : Nat := 118140960795 + 6852492 * 2 ^ 59
def prefixEnd_6852492 : Nat := 4983230072969 + 3 ^ 40 * 6852492 * 2
def baseEnd_6852492 : Nat := 1172874025696436275745323

theorem tailTrace_6852492 : CollatzResearch.WordTrace tailWord_6852492 prefixEnd_6852492 1172874025696436275745323 := by
  unfold tailWord_6852492
  simp only [CollatzResearch.WordTrace]
  refine ⟨124965457945299635652687865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166620610593732847536917153 124965457945299635652687865)
  ·
    refine ⟨93724093458974726739515899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124965457945299635652687865 93724093458974726739515899)
    ·
      refine ⟨140586140188462090109273849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93724093458974726739515899 140586140188462090109273849)
      ·
        refine ⟨105439605141346567581955387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140586140188462090109273849 105439605141346567581955387)
        ·
          refine ⟨158159407712019851372933081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105439605141346567581955387 158159407712019851372933081)
          ·
            refine ⟨118619555784014888529699811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158159407712019851372933081 118619555784014888529699811)
            ·
              refine ⟨177929333676022332794549717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118619555784014888529699811 177929333676022332794549717)
              ·
                refine ⟨4170218758031773424872259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177929333676022332794549717 4170218758031773424872259)
                ·
                  refine ⟨6255328137047660137308389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170218758031773424872259 6255328137047660137308389)
                  ·
                    refine ⟨1172874025696436275745323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255328137047660137308389 1172874025696436275745323)
                    ·
                      rfl

theorem cell23_6852492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_6852492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852492 prefixEnd_6852492 := by exact prefixLift 6852492
  have htrace : WordTrace (prefixWord ++ tailWord_6852492) baseStart_6852492 baseEnd_6852492 := by
    simpa [prefixWord, tailWord_6852492, baseEnd_6852492] using wordTrace_append hprefix tailTrace_6852492
  have hstable : (prefixWord ++ tailWord_6852492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852492).length < 2 ^ (prefixWord ++ tailWord_6852492).sum := by decide
  have hdescent : baseEnd_6852492 < baseStart_6852492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852509 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6852509 : Nat := 118140960795 + 6852509 * 2 ^ 59
def prefixEnd_6852509 : Nat := 4983230072969 + 3 ^ 40 * 6852509 * 2
def baseEnd_6852509 : Nat := 1172876935420145086907797

theorem tailTrace_6852509 : CollatzResearch.WordTrace tailWord_6852509 prefixEnd_6852509 1172876935420145086907797 := by
  unfold tailWord_6852509
  simp only [CollatzResearch.WordTrace]
  refine ⟨249931535931537683208744581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166621023954358455472496387 249931535931537683208744581)
  ·
    refine ⟨46862162987163315601639609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249931535931537683208744581 46862162987163315601639609)
    ·
      refine ⟨35146622240372486701229707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46862162987163315601639609 35146622240372486701229707)
      ·
        refine ⟨52719933360558730051844561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35146622240372486701229707 52719933360558730051844561)
        ·
          refine ⟨39539950020419047538883421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52719933360558730051844561 39539950020419047538883421)
          ·
            refine ⟨14827481257657142827081283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39539950020419047538883421 14827481257657142827081283)
            ·
              refine ⟨22241221886485714240621925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14827481257657142827081283 22241221886485714240621925)
              ·
                refine ⟨4170229103716071420116611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22241221886485714240621925 4170229103716071420116611)
                ·
                  refine ⟨6255343655574107130174917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170229103716071420116611 6255343655574107130174917)
                  ·
                    refine ⟨1172876935420145086907797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255343655574107130174917 1172876935420145086907797)
                    ·
                      rfl

theorem cell23_6852509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6852509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852509 prefixEnd_6852509 := by exact prefixLift 6852509
  have htrace : WordTrace (prefixWord ++ tailWord_6852509) baseStart_6852509 baseEnd_6852509 := by
    simpa [prefixWord, tailWord_6852509, baseEnd_6852509] using wordTrace_append hprefix tailTrace_6852509
  have hstable : (prefixWord ++ tailWord_6852509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852509).length < 2 ^ (prefixWord ++ tailWord_6852509).sum := by decide
  have hdescent : baseEnd_6852509 < baseStart_6852509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852535 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 1, 5]
def baseStart_6852535 : Nat := 118140960795 + 6852535 * 2 ^ 59
def prefixEnd_6852535 : Nat := 4983230072969 + 3 ^ 40 * 6852535 * 2
def baseEnd_6852535 : Nat := 1172881385585817386332757

theorem tailTrace_6852535 : CollatzResearch.WordTrace tailWord_6852535 prefixEnd_6852535 1172881385585817386332757 := by
  unfold tailWord_6852535
  simp only [CollatzResearch.WordTrace]
  refine ⟨249932484229443489649191059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166621656152962326432794039 249932484229443489649191059)
  ·
    refine ⟨374898726344165234473786589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249932484229443489649191059 374898726344165234473786589)
    ·
      refine ⟨140587022379061962927669971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374898726344165234473786589 140587022379061962927669971)
      ·
        refine ⟨210880533568592944391504957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140587022379061962927669971 210880533568592944391504957)
        ·
          refine ⟨79080200088222354146814359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210880533568592944391504957 79080200088222354146814359)
          ·
            refine ⟨118620300132333531220221539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79080200088222354146814359 118620300132333531220221539)
            ·
              refine ⟨177930450198500296830332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118620300132333531220221539 177930450198500296830332309)
              ·
                refine ⟨8340489853054701413921827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177930450198500296830332309 8340489853054701413921827)
                ·
                  refine ⟨12510734779582052120882741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340489853054701413921827 12510734779582052120882741)
                  ·
                    refine ⟨1172881385585817386332757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12510734779582052120882741 1172881385585817386332757)
                    ·
                      rfl

theorem cell23_6852535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_6852535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852535 prefixEnd_6852535 := by exact prefixLift 6852535
  have htrace : WordTrace (prefixWord ++ tailWord_6852535) baseStart_6852535 baseEnd_6852535 := by
    simpa [prefixWord, tailWord_6852535, baseEnd_6852535] using wordTrace_append hprefix tailTrace_6852535
  have hstable : (prefixWord ++ tailWord_6852535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852535).length < 2 ^ (prefixWord ++ tailWord_6852535).sum := by decide
  have hdescent : baseEnd_6852535 < baseStart_6852535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852552 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_6852552 : Nat := 118140960795 + 6852552 * 2 ^ 59
def prefixEnd_6852552 : Nat := 4983230072969 + 3 ^ 40 * 6852552 * 2
def baseEnd_6852552 : Nat := 1172884295309526197495231

theorem tailTrace_6852552 : CollatzResearch.WordTrace tailWord_6852552 prefixEnd_6852552 1172884295309526197495231 := by
  unfold tailWord_6852552
  simp only [CollatzResearch.WordTrace]
  refine ⟨124966552135190950776279955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166622069513587934368373273 124966552135190950776279955)
  ·
    refine ⟨187449828202786426164419933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124966552135190950776279955 187449828202786426164419933)
    ·
      refine ⟨70293685576044909811657475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187449828202786426164419933 70293685576044909811657475)
      ·
        refine ⟨105440528364067364717486213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70293685576044909811657475 105440528364067364717486213)
        ·
          refine ⟨19770099068262630884528665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105440528364067364717486213 19770099068262630884528665)
          ·
            refine ⟨14827574301196973163396499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19770099068262630884528665 14827574301196973163396499)
            ·
              refine ⟨22241361451795459745094749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14827574301196973163396499 22241361451795459745094749)
              ·
                refine ⟨8340510544423297404410531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22241361451795459745094749 8340510544423297404410531)
                ·
                  refine ⟨12510765816634946106615797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340510544423297404410531 12510765816634946106615797)
                  ·
                    refine ⟨1172884295309526197495231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12510765816634946106615797 1172884295309526197495231)
                    ·
                      rfl

theorem cell23_6852552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_6852552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852552 prefixEnd_6852552 := by exact prefixLift 6852552
  have htrace : WordTrace (prefixWord ++ tailWord_6852552) baseStart_6852552 baseEnd_6852552 := by
    simpa [prefixWord, tailWord_6852552, baseEnd_6852552] using wordTrace_append hprefix tailTrace_6852552
  have hstable : (prefixWord ++ tailWord_6852552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852552).length < 2 ^ (prefixWord ++ tailWord_6852552).sum := by decide
  have hdescent : baseEnd_6852552 < baseStart_6852552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852575 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_6852575 : Nat := 118140960795 + 6852575 * 2 ^ 59
def prefixEnd_6852575 : Nat := 4983230072969 + 3 ^ 40 * 6852575 * 2
def baseEnd_6852575 : Nat := 3518664695983632002498087

theorem tailTrace_6852575 : CollatzResearch.WordTrace tailWord_6852575 prefixEnd_6852575 3518664695983632002498087 := by
  unfold tailWord_6852575
  simp only [CollatzResearch.WordTrace]
  refine ⟨249933943149298576480647179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166622628766199050987098119 249933943149298576480647179)
  ·
    refine ⟨374900914723947864720970769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249933943149298576480647179 374900914723947864720970769)
    ·
      refine ⟨281175686042960898540728077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374900914723947864720970769 281175686042960898540728077)
      ·
        refine ⟨105440882266110336952773029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281175686042960898540728077 105440882266110336952773029)
        ·
          refine ⟨19770165424895688178644943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105440882266110336952773029 19770165424895688178644943)
          ·
            refine ⟨29655248137343532267967415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19770165424895688178644943 29655248137343532267967415)
            ·
              refine ⟨44482872206015298401951123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29655248137343532267967415 44482872206015298401951123)
              ·
                refine ⟨66724308309022947602926685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44482872206015298401951123 66724308309022947602926685)
                ·
                  refine ⟨25021615615883605351097507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66724308309022947602926685 25021615615883605351097507)
                  ·
                    refine ⟨37532423423825408026646261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25021615615883605351097507 37532423423825408026646261)
                    ·
                      refine ⟨3518664695983632002498087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37532423423825408026646261 3518664695983632002498087)
                      ·
                        rfl

theorem cell23_6852575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_6852575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852575 prefixEnd_6852575 := by exact prefixLift 6852575
  have htrace : WordTrace (prefixWord ++ tailWord_6852575) baseStart_6852575 baseEnd_6852575 := by
    simpa [prefixWord, tailWord_6852575, baseEnd_6852575] using wordTrace_append hprefix tailTrace_6852575
  have hstable : (prefixWord ++ tailWord_6852575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852575).length < 2 ^ (prefixWord ++ tailWord_6852575).sum := by decide
  have hdescent : baseEnd_6852575 < baseStart_6852575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852592 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_6852592 : Nat := 118140960795 + 6852592 * 2 ^ 59
def prefixEnd_6852592 : Nat := 4983230072969 + 3 ^ 40 * 6852592 * 2
def baseEnd_6852592 : Nat := 3518673425154758435985509

theorem tailTrace_6852592 : CollatzResearch.WordTrace tailWord_6852592 prefixEnd_6852592 3518673425154758435985509 := by
  unfold tailWord_6852592
  simp only [CollatzResearch.WordTrace]
  refine ⟨124967281595118494192008015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166623042126824658922677353 124967281595118494192008015)
  ·
    refine ⟨187450922392677741288012023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124967281595118494192008015 187450922392677741288012023)
    ·
      refine ⟨281176383589016611932018035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187450922392677741288012023 281176383589016611932018035)
      ·
        refine ⟨421764575383524917898027053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281176383589016611932018035 421764575383524917898027053)
        ·
          refine ⟨158161715768821844211760145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421764575383524917898027053 158161715768821844211760145)
          ·
            refine ⟨118621286826616383158820109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158161715768821844211760145 118621286826616383158820109)
            ·
              refine ⟨44482982559981143684557541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118621286826616383158820109 44482982559981143684557541)
              ·
                refine ⟨8340559229996464440854539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44482982559981143684557541 8340559229996464440854539)
                ·
                  refine ⟨12510838844994696661281809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340559229996464440854539 12510838844994696661281809)
                  ·
                    refine ⟨9383129133746022495961357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12510838844994696661281809 9383129133746022495961357)
                    ·
                      refine ⟨3518673425154758435985509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9383129133746022495961357 3518673425154758435985509)
                      ·
                        rfl

theorem cell23_6852592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_6852592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852592 prefixEnd_6852592 := by exact prefixLift 6852592
  have htrace : WordTrace (prefixWord ++ tailWord_6852592) baseStart_6852592 baseEnd_6852592 := by
    simpa [prefixWord, tailWord_6852592, baseEnd_6852592] using wordTrace_append hprefix tailTrace_6852592
  have hstable : (prefixWord ++ tailWord_6852592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852592).length < 2 ^ (prefixWord ++ tailWord_6852592).sum := by decide
  have hdescent : baseEnd_6852592 < baseStart_6852592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852639 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_6852639 : Nat := 118140960795 + 6852639 * 2 ^ 59
def prefixEnd_6852639 : Nat := 4983230072969 + 3 ^ 40 * 6852639 * 2
def baseEnd_6852639 : Nat := 3518697558745519752097793

theorem tailTrace_6852639 : CollatzResearch.WordTrace tailWord_6852639 prefixEnd_6852639 3518697558745519752097793 := by
  unfold tailWord_6852639
  simp only [CollatzResearch.WordTrace]
  refine ⟨249936277421066715410976971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166624184947377810273984647 249936277421066715410976971)
  ·
    refine ⟨374904416131600073116465457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249936277421066715410976971 374904416131600073116465457)
    ·
      refine ⟨281178312098700054837349093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374904416131600073116465457 281178312098700054837349093)
      ·
        refine ⟨52720933518506260282002955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281178312098700054837349093 52720933518506260282002955)
        ·
          refine ⟨79081400277759390423004433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52720933518506260282002955 79081400277759390423004433)
          ·
            refine ⟨59311050208319542817253325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79081400277759390423004433 59311050208319542817253325)
            ·
              refine ⟨22241643828119828556469997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59311050208319542817253325 22241643828119828556469997)
              ·
                refine ⟨8340616435544935708676249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22241643828119828556469997 8340616435544935708676249)
                ·
                  refine ⟨6255462326658701781507187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8340616435544935708676249 6255462326658701781507187)
                  ·
                    refine ⟨9383193489988052672260781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6255462326658701781507187 9383193489988052672260781)
                    ·
                      refine ⟨3518697558745519752097793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9383193489988052672260781 3518697558745519752097793)
                      ·
                        rfl

theorem cell23_6852639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_6852639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852639 prefixEnd_6852639 := by exact prefixLift 6852639
  have htrace : WordTrace (prefixWord ++ tailWord_6852639) baseStart_6852639 baseEnd_6852639 := by
    simpa [prefixWord, tailWord_6852639, baseEnd_6852639] using wordTrace_append hprefix tailTrace_6852639
  have hstable : (prefixWord ++ tailWord_6852639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852639).length < 2 ^ (prefixWord ++ tailWord_6852639).sum := by decide
  have hdescent : baseEnd_6852639 < baseStart_6852639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852696 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_6852696 : Nat := 118140960795 + 6852696 * 2 ^ 59
def prefixEnd_6852696 : Nat := 4983230072969 + 3 ^ 40 * 6852696 * 2
def baseEnd_6852696 : Nat := 3518726827142826029085031

theorem tailTrace_6852696 : CollatzResearch.WordTrace tailWord_6852696 prefixEnd_6852696 3518726827142826029085031 := by
  unfold tailWord_6852696
  simp only [CollatzResearch.WordTrace]
  refine ⟨124969178190930107072900971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166625570921240142763867961 124969178190930107072900971)
  ·
    refine ⟨187453767286395160609351457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124969178190930107072900971 187453767286395160609351457)
    ·
      refine ⟨140590325464796370457013593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187453767286395160609351457 140590325464796370457013593)
      ·
        refine ⟨105442744098597277842760195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140590325464796370457013593 105442744098597277842760195)
        ·
          refine ⟨158164116147895916764140293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105442744098597277842760195 158164116147895916764140293)
          ·
            refine ⟨29655771777730484393276305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158164116147895916764140293 29655771777730484393276305)
            ·
              refine ⟨22241828833297863294957229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29655771777730484393276305 22241828833297863294957229)
              ·
                refine ⟨8340685812486698735608961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22241828833297863294957229 8340685812486698735608961)
                ·
                  refine ⟨6255514359365024051706721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8340685812486698735608961 6255514359365024051706721)
                  ·
                    refine ⟨4691635769523768038780041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6255514359365024051706721 4691635769523768038780041)
                    ·
                      refine ⟨3518726827142826029085031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691635769523768038780041 3518726827142826029085031)
                      ·
                        rfl

theorem cell23_6852696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_6852696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852696 prefixEnd_6852696 := by exact prefixLift 6852696
  have htrace : WordTrace (prefixWord ++ tailWord_6852696) baseStart_6852696 baseEnd_6852696 := by
    simpa [prefixWord, tailWord_6852696, baseEnd_6852696] using wordTrace_append hprefix tailTrace_6852696
  have hstable : (prefixWord ++ tailWord_6852696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852696).length < 2 ^ (prefixWord ++ tailWord_6852696).sum := by decide
  have hdescent : baseEnd_6852696 < baseStart_6852696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852719 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 5]
def baseStart_6852719 : Nat := 118140960795 + 6852719 * 2 ^ 59
def prefixEnd_6852719 : Nat := 4983230072969 + 3 ^ 40 * 6852719 * 2
def baseEnd_6852719 : Nat := 390970959688653271010825

theorem tailTrace_6852719 : CollatzResearch.WordTrace tailWord_6852719 prefixEnd_6852719 390970959688653271010825 := by
  unfold tailWord_6852719
  simp only [CollatzResearch.WordTrace]
  refine ⟨249939195260776889073889211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166626130173851259382592807 249939195260776889073889211)
  ·
    refine ⟨374908792891165333610833817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249939195260776889073889211 374908792891165333610833817)
    ·
      refine ⟨281181594668374000208125363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374908792891165333610833817 281181594668374000208125363)
      ·
        refine ⟨421772392002561000312188045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281181594668374000208125363 421772392002561000312188045)
        ·
          refine ⟨158164647000960375117070517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421772392002561000312188045 158164647000960375117070517)
          ·
            refine ⟨14827935656340035167225361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158164647000960375117070517 14827935656340035167225361)
            ·
              refine ⟨11120951742255026375419021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14827935656340035167225361 11120951742255026375419021)
              ·
                refine ⟨4170356903345634890782133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11120951742255026375419021 4170356903345634890782133)
                ·
                  refine ⟨390970959688653271010825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4170356903345634890782133 390970959688653271010825)
                  ·
                    rfl

theorem cell23_6852719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 5].length) (baseStart_6852719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852719 prefixEnd_6852719 := by exact prefixLift 6852719
  have htrace : WordTrace (prefixWord ++ tailWord_6852719) baseStart_6852719 baseEnd_6852719 := by
    simpa [prefixWord, tailWord_6852719, baseEnd_6852719] using wordTrace_append hprefix tailTrace_6852719
  have hstable : (prefixWord ++ tailWord_6852719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852719).length < 2 ^ (prefixWord ++ tailWord_6852719).sum := by decide
  have hdescent : baseEnd_6852719 < baseStart_6852719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852792 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 6]
def baseStart_6852792 : Nat := 118140960795 + 6852792 * 2 ^ 59
def prefixEnd_6852792 : Nat := 4983230072969 + 3 ^ 40 * 6852792 * 2
def baseEnd_6852792 : Nat := 390975124587295294831621

theorem tailTrace_6852792 : CollatzResearch.WordTrace tailWord_6852792 prefixEnd_6852792 390975124587295294831621 := by
  unfold tailWord_6852792
  simp only [CollatzResearch.WordTrace]
  refine ⟨124970928894756211270648315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166627905193008281694197753 124970928894756211270648315)
  ·
    refine ⟨187456393342134316905972473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124970928894756211270648315 187456393342134316905972473)
    ·
      refine ⟨140592295006600737679479355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187456393342134316905972473 140592295006600737679479355)
      ·
        refine ⟨210888442509901106519219033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140592295006600737679479355 210888442509901106519219033)
        ·
          refine ⟨158166331882425829889414275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210888442509901106519219033 158166331882425829889414275)
          ·
            refine ⟨237249497823638744834121413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158166331882425829889414275 237249497823638744834121413)
            ·
              refine ⟨44484280841932264656397765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237249497823638744834121413 44484280841932264656397765)
              ·
                refine ⟨8340802657862299623074581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44484280841932264656397765 8340802657862299623074581)
                ·
                  refine ⟨390975124587295294831621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8340802657862299623074581 390975124587295294831621)
                  ·
                    rfl

theorem cell23_6852792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_6852792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852792 prefixEnd_6852792 := by exact prefixLift 6852792
  have htrace : WordTrace (prefixWord ++ tailWord_6852792) baseStart_6852792 baseEnd_6852792 := by
    simpa [prefixWord, tailWord_6852792, baseEnd_6852792] using wordTrace_append hprefix tailTrace_6852792
  have hstable : (prefixWord ++ tailWord_6852792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852792).length < 2 ^ (prefixWord ++ tailWord_6852792).sum := by decide
  have hdescent : baseEnd_6852792 < baseStart_6852792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852890 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_6852890 : Nat := 118140960795 + 6852890 * 2 ^ 59
def prefixEnd_6852890 : Nat := 4983230072969 + 3 ^ 40 * 6852890 * 2
def baseEnd_6852890 : Nat := 1172942147463266090019713

theorem tailTrace_6852890 : CollatzResearch.WordTrace tailWord_6852890 prefixEnd_6852890 1172942147463266090019713 := by
  unfold tailWord_6852890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62486358035789346319591031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166630288095438256852242749 62486358035789346319591031)
  ·
    refine ⟨93729537053684019479386547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62486358035789346319591031 93729537053684019479386547)
    ·
      refine ⟨140594305580526029219079821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93729537053684019479386547 140594305580526029219079821)
      ·
        refine ⟨52722864592697260957154933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140594305580526029219079821 52722864592697260957154933)
        ·
          refine ⟨4942768555565368214733275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52722864592697260957154933 4942768555565368214733275)
          ·
            refine ⟨7414152833348052322099913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942768555565368214733275 7414152833348052322099913)
            ·
              refine ⟨5560614625011039241574935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414152833348052322099913 5560614625011039241574935)
              ·
                refine ⟨8340921937516558862362403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560614625011039241574935 8340921937516558862362403)
                ·
                  refine ⟨12511382906274838293543605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340921937516558862362403 12511382906274838293543605)
                  ·
                    refine ⟨1172942147463266090019713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12511382906274838293543605 1172942147463266090019713)
                    ·
                      rfl

theorem cell23_6852890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_6852890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852890 prefixEnd_6852890 := by exact prefixLift 6852890
  have htrace : WordTrace (prefixWord ++ tailWord_6852890) baseStart_6852890 baseEnd_6852890 := by
    simpa [prefixWord, tailWord_6852890, baseEnd_6852890] using wordTrace_append hprefix tailTrace_6852890
  have hstable : (prefixWord ++ tailWord_6852890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852890).length < 2 ^ (prefixWord ++ tailWord_6852890).sum := by decide
  have hdescent : baseEnd_6852890 < baseStart_6852890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852893 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6852893 : Nat := 118140960795 + 6852893 * 2 ^ 59
def prefixEnd_6852893 : Nat := 4983230072969 + 3 ^ 40 * 6852893 * 2
def baseEnd_6852893 : Nat := 3518827982831761758321625

theorem tailTrace_6852893 : CollatzResearch.WordTrace tailWord_6852893 prefixEnd_6852893 3518827982831761758321625 := by
  unfold tailWord_6852893
  simp only [CollatzResearch.WordTrace]
  refine ⟨249945541562146516790723333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166630361041431011193815555 249945541562146516790723333)
  ·
    refine ⟨46864789042902471898260625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249945541562146516790723333 46864789042902471898260625)
    ·
      refine ⟨35148591782176853923695469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46864789042902471898260625 35148591782176853923695469)
      ·
        refine ⟨13180721918316320221385801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35148591782176853923695469 13180721918316320221385801)
        ·
          refine ⟨9885541438737240166039351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13180721918316320221385801 9885541438737240166039351)
          ·
            refine ⟨14828312158105860249059027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9885541438737240166039351 14828312158105860249059027)
            ·
              refine ⟨22242468237158790373588541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14828312158105860249059027 22242468237158790373588541)
              ·
                refine ⟨8340925588934546390095703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22242468237158790373588541 8340925588934546390095703)
                ·
                  refine ⟨12511388383401819585143555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8340925588934546390095703 12511388383401819585143555)
                  ·
                    refine ⟨18767082575102729377715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12511388383401819585143555 18767082575102729377715333)
                    ·
                      refine ⟨3518827982831761758321625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18767082575102729377715333 3518827982831761758321625)
                      ·
                        rfl

theorem cell23_6852893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6852893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852893 prefixEnd_6852893 := by exact prefixLift 6852893
  have htrace : WordTrace (prefixWord ++ tailWord_6852893) baseStart_6852893 baseEnd_6852893 := by
    simpa [prefixWord, tailWord_6852893, baseEnd_6852893] using wordTrace_append hprefix tailTrace_6852893
  have hstable : (prefixWord ++ tailWord_6852893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852893).length < 2 ^ (prefixWord ++ tailWord_6852893).sum := by decide
  have hdescent : baseEnd_6852893 < baseStart_6852893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852912 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_6852912 : Nat := 118140960795 + 6852912 * 2 ^ 59
def prefixEnd_6852912 : Nat := 4983230072969 + 3 ^ 40 * 6852912 * 2
def baseEnd_6852912 : Nat := 1172945912988065727994679

theorem tailTrace_6852912 : CollatzResearch.WordTrace tailWord_6852912 prefixEnd_6852912 1172945912988065727994679 := by
  unfold tailWord_6852912
  simp only [CollatzResearch.WordTrace]
  refine ⟨124973117274538841517832495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166630823032718455357109993 124973117274538841517832495)
  ·
    refine ⟨187459675911808262276748743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124973117274538841517832495 187459675911808262276748743)
    ·
      refine ⟨281189513867712393415123115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187459675911808262276748743 281189513867712393415123115)
      ·
        refine ⟨421784270801568590122684673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281189513867712393415123115 421784270801568590122684673)
        ·
          refine ⟨316338203101176442592013505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421784270801568590122684673 316338203101176442592013505)
          ·
            refine ⟨237253652325882331944010129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316338203101176442592013505 237253652325882331944010129)
            ·
              refine ⟨177940239244411748958007597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237253652325882331944010129 177940239244411748958007597)
              ·
                refine ⟨66727589716654405859252849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177940239244411748958007597 66727589716654405859252849)
                ·
                  refine ⟨50045692287490804394439637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66727589716654405859252849 50045692287490804394439637)
                  ·
                    refine ⟨1172945912988065727994679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50045692287490804394439637 1172945912988065727994679)
                    ·
                      rfl

theorem cell23_6852912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_6852912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852912 prefixEnd_6852912 := by exact prefixLift 6852912
  have htrace : WordTrace (prefixWord ++ tailWord_6852912) baseStart_6852912 baseEnd_6852912 := by
    simpa [prefixWord, tailWord_6852912, baseEnd_6852912] using wordTrace_append hprefix tailTrace_6852912
  have hstable : (prefixWord ++ tailWord_6852912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852912).length < 2 ^ (prefixWord ++ tailWord_6852912).sum := by decide
  have hdescent : baseEnd_6852912 < baseStart_6852912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852936 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_6852936 : Nat := 118140960795 + 6852936 * 2 ^ 59
def prefixEnd_6852936 : Nat := 4983230072969 + 3 ^ 40 * 6852936 * 2
def baseEnd_6852936 : Nat := 3518850062499905090083927

theorem tailTrace_6852936 : CollatzResearch.WordTrace tailWord_6852936 prefixEnd_6852936 3518850062499905090083927 := by
  unfold tailWord_6852936
  simp only [CollatzResearch.WordTrace]
  refine ⟨124973554950495367567269331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166631406600660490089692441 124973554950495367567269331)
  ·
    refine ⟨187460332425743051350903997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124973554950495367567269331 187460332425743051350903997)
    ·
      refine ⟨70297624659653644256588999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187460332425743051350903997 70297624659653644256588999)
      ·
        refine ⟨105446436989480466384883499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70297624659653644256588999 105446436989480466384883499)
        ·
          refine ⟨158169655484220699577325249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105446436989480466384883499 158169655484220699577325249)
          ·
            refine ⟨118627241613165524682993937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158169655484220699577325249 118627241613165524682993937)
            ·
              refine ⟨88970431209874143512245453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118627241613165524682993937 88970431209874143512245453)
              ·
                refine ⟨33363911703702803817092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88970431209874143512245453 33363911703702803817092045)
                ·
                  refine ⟨12511466888888551431409517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33363911703702803817092045 12511466888888551431409517)
                  ·
                    refine ⟨4691800083333206786778569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12511466888888551431409517 4691800083333206786778569)
                    ·
                      refine ⟨3518850062499905090083927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691800083333206786778569 3518850062499905090083927)
                      ·
                        rfl

theorem cell23_6852936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_6852936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852936 prefixEnd_6852936 := by exact prefixLift 6852936
  have htrace : WordTrace (prefixWord ++ tailWord_6852936) baseStart_6852936 baseEnd_6852936 := by
    simpa [prefixWord, tailWord_6852936, baseEnd_6852936] using wordTrace_append hprefix tailTrace_6852936
  have hstable : (prefixWord ++ tailWord_6852936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852936).length < 2 ^ (prefixWord ++ tailWord_6852936).sum := by decide
  have hdescent : baseEnd_6852936 < baseStart_6852936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6852969 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_6852969 : Nat := 118140960795 + 6852969 * 2 ^ 59
def prefixEnd_6852969 : Nat := 4983230072969 + 3 ^ 40 * 6852969 * 2
def baseEnd_6852969 : Nat := 3518867007361503460971275

theorem tailTrace_6852969 : CollatzResearch.WordTrace tailWord_6852969 prefixEnd_6852969 3518867007361503460971275 := by
  unfold tailWord_6852969
  simp only [CollatzResearch.WordTrace]
  refine ⟨249948313509871181770489961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166632209006580787846993307 249948313509871181770489961)
  ·
    refine ⟨187461235132403386327867471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249948313509871181770489961 187461235132403386327867471)
    ·
      refine ⟨281191852698605079491801207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187461235132403386327867471 281191852698605079491801207)
      ·
        refine ⟨421787779047907619237701811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281191852698605079491801207 421787779047907619237701811)
        ·
          refine ⟨632681668571861428856552717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421787779047907619237701811 632681668571861428856552717)
          ·
            refine ⟨237255625714448035821207269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632681668571861428856552717 237255625714448035821207269)
            ·
              refine ⟨44485429821459006716476363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237255625714448035821207269 44485429821459006716476363)
              ·
                refine ⟨66728144732188510074714545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44485429821459006716476363 66728144732188510074714545)
                ·
                  refine ⟨50046108549141382556035909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66728144732188510074714545 50046108549141382556035909)
                  ·
                    refine ⟨9383645352964009229256733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50046108549141382556035909 9383645352964009229256733)
                    ·
                      refine ⟨3518867007361503460971275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9383645352964009229256733 3518867007361503460971275)
                      ·
                        rfl

theorem cell23_6852969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_6852969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6852969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6852969 prefixEnd_6852969 := by exact prefixLift 6852969
  have htrace : WordTrace (prefixWord ++ tailWord_6852969) baseStart_6852969 baseEnd_6852969 := by
    simpa [prefixWord, tailWord_6852969, baseEnd_6852969] using wordTrace_append hprefix tailTrace_6852969
  have hstable : (prefixWord ++ tailWord_6852969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6852969).length < 2 ^ (prefixWord ++ tailWord_6852969).sum := by decide
  have hdescent : baseEnd_6852969 < baseStart_6852969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6852969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853029 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_6853029 : Nat := 118140960795 + 6853029 * 2 ^ 59
def prefixEnd_6853029 : Nat := 4983230072969 + 3 ^ 40 * 6853029 * 2
def baseEnd_6853029 : Nat := 3518897816200773226220999

theorem tailTrace_6853029 : CollatzResearch.WordTrace tailWord_6853029 prefixEnd_6853029 3518897816200773226220999 := by
  unfold tailWord_6853029
  simp only [CollatzResearch.WordTrace]
  refine ⟨249950501889653812017674141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166633667926435874678449427 249950501889653812017674141)
  ·
    refine ⟨93731438208620179506627803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249950501889653812017674141 93731438208620179506627803)
    ·
      refine ⟨140597157312930269259941705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93731438208620179506627803 140597157312930269259941705)
      ·
        refine ⟨105447867984697701944956279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140597157312930269259941705 105447867984697701944956279)
        ·
          refine ⟨158171801977046552917434419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105447867984697701944956279 158171801977046552917434419)
          ·
            refine ⟨237257702965569829376151629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158171801977046552917434419 237257702965569829376151629)
            ·
              refine ⟨88971638612088686016056861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237257702965569829376151629 88971638612088686016056861)
              ·
                refine ⟨33364364479533257256021323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88971638612088686016056861 33364364479533257256021323)
                ·
                  refine ⟨50046546719299885884031985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33364364479533257256021323 50046546719299885884031985)
                  ·
                    refine ⟨37534910039474914413023989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50046546719299885884031985 37534910039474914413023989)
                    ·
                      refine ⟨3518897816200773226220999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37534910039474914413023989 3518897816200773226220999)
                      ·
                        rfl

theorem cell23_6853029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_6853029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853029 prefixEnd_6853029 := by exact prefixLift 6853029
  have htrace : WordTrace (prefixWord ++ tailWord_6853029) baseStart_6853029 baseEnd_6853029 := by
    simpa [prefixWord, tailWord_6853029, baseEnd_6853029] using wordTrace_append hprefix tailTrace_6853029
  have hstable : (prefixWord ++ tailWord_6853029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853029).length < 2 ^ (prefixWord ++ tailWord_6853029).sum := by decide
  have hdescent : baseEnd_6853029 < baseStart_6853029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853034 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6853034 : Nat := 118140960795 + 6853034 * 2 ^ 59
def prefixEnd_6853034 : Nat := 4983230072969 + 3 ^ 40 * 6853034 * 2
def baseEnd_6853034 : Nat := 3518900383604045706658477

theorem tailTrace_6853034 : CollatzResearch.WordTrace tailWord_6853034 prefixEnd_6853034 3518900383604045706658477 := by
  unfold tailWord_6853034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62487671063658924467901539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166633789503090465247737437 62487671063658924467901539)
  ·
    refine ⟨93731506595488386701852309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62487671063658924467901539 93731506595488386701852309)
    ·
      refine ⟨4393664371663518126649327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93731506595488386701852309 4393664371663518126649327)
      ·
        refine ⟨6590496557495277189973991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393664371663518126649327 6590496557495277189973991)
        ·
          refine ⟨9885744836242915784960987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590496557495277189973991 9885744836242915784960987)
          ·
            refine ⟨14828617254364373677441481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9885744836242915784960987 14828617254364373677441481)
            ·
              refine ⟨11121462940773280258081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14828617254364373677441481 11121462940773280258081111)
              ·
                refine ⟨16682194411159920387121667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121462940773280258081111 16682194411159920387121667)
                ·
                  refine ⟨25023291616739880580682501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16682194411159920387121667 25023291616739880580682501)
                  ·
                    refine ⟨4691867178138727608877969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25023291616739880580682501 4691867178138727608877969)
                    ·
                      refine ⟨3518900383604045706658477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691867178138727608877969 3518900383604045706658477)
                      ·
                        rfl

theorem cell23_6853034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6853034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853034 prefixEnd_6853034 := by exact prefixLift 6853034
  have htrace : WordTrace (prefixWord ++ tailWord_6853034) baseStart_6853034 baseEnd_6853034 := by
    simpa [prefixWord, tailWord_6853034, baseEnd_6853034] using wordTrace_append hprefix tailTrace_6853034
  have hstable : (prefixWord ++ tailWord_6853034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853034).length < 2 ^ (prefixWord ++ tailWord_6853034).sum := by decide
  have hdescent : baseEnd_6853034 < baseStart_6853034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853053 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6853053 : Nat := 118140960795 + 6853053 * 2 ^ 59
def prefixEnd_6853053 : Nat := 4983230072969 + 3 ^ 40 * 6853053 * 2
def baseEnd_6853053 : Nat := 1172970046578827044106963

theorem tailTrace_6853053 : CollatzResearch.WordTrace tailWord_6853053 prefixEnd_6853053 1172970046578827044106963 := by
  unfold tailWord_6853053
  simp only [CollatzResearch.WordTrace]
  refine ⟨249951377241566864116547813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166634251494377909411031875 249951377241566864116547813)
  ·
    refine ⟨46865883232793787021852715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249951377241566864116547813 46865883232793787021852715)
    ·
      refine ⟨70298824849190680532779073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46865883232793787021852715 70298824849190680532779073)
      ·
        refine ⟨52724118636893010399584305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70298824849190680532779073 52724118636893010399584305)
        ·
          refine ⟨39543088977669757799688229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52724118636893010399584305 39543088977669757799688229)
          ·
            refine ⟨7414329183313079587441543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39543088977669757799688229 7414329183313079587441543)
            ·
              refine ⟨11121493774969619381162315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7414329183313079587441543 11121493774969619381162315)
              ·
                refine ⟨16682240662454429071743473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121493774969619381162315 16682240662454429071743473)
                ·
                  refine ⟨12511680496840821803807605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16682240662454429071743473 12511680496840821803807605)
                  ·
                    refine ⟨1172970046578827044106963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12511680496840821803807605 1172970046578827044106963)
                    ·
                      rfl

theorem cell23_6853053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6853053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853053 prefixEnd_6853053 := by exact prefixLift 6853053
  have htrace : WordTrace (prefixWord ++ tailWord_6853053) baseStart_6853053 baseEnd_6853053 := by
    simpa [prefixWord, tailWord_6853053, baseEnd_6853053] using wordTrace_append hprefix tailTrace_6853053
  have hstable : (prefixWord ++ tailWord_6853053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853053).length < 2 ^ (prefixWord ++ tailWord_6853053).sum := by decide
  have hdescent : baseEnd_6853053 < baseStart_6853053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853056 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2]
def baseStart_6853056 : Nat := 118140960795 + 6853056 * 2 ^ 59
def prefixEnd_6853056 : Nat := 4983230072969 + 3 ^ 40 * 6853056 * 2
def baseEnd_6853056 : Nat := 3518911680178444620583375

theorem tailTrace_6853056 : CollatzResearch.WordTrace tailWord_6853056 prefixEnd_6853056 3518911680178444620583375 := by
  unfold tailWord_6853056
  simp only [CollatzResearch.WordTrace]
  refine ⟨124975743330277997814453511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166634324440370663752604681 124975743330277997814453511)
  ·
    refine ⟨187463614995416996721680267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124975743330277997814453511 187463614995416996721680267)
    ·
      refine ⟨281195422493125495082520401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187463614995416996721680267 281195422493125495082520401)
      ·
        refine ⟨210896566869844121311890301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281195422493125495082520401 210896566869844121311890301)
        ·
          refine ⟨79086212576191545491958863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210896566869844121311890301 79086212576191545491958863)
          ·
            refine ⟨118629318864287318237938295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79086212576191545491958863 118629318864287318237938295)
            ·
              refine ⟨177943978296430977356907443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118629318864287318237938295 177943978296430977356907443)
              ·
                refine ⟨266915967444646466035361165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177943978296430977356907443 266915967444646466035361165)
                ·
                  refine ⟨100093487791742424763260437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266915967444646466035361165 100093487791742424763260437)
                  ·
                    refine ⟨4691882240237926160777833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100093487791742424763260437 4691882240237926160777833)
                    ·
                      refine ⟨3518911680178444620583375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4691882240237926160777833 3518911680178444620583375)
                      ·
                        rfl

theorem cell23_6853056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_6853056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853056 prefixEnd_6853056 := by exact prefixLift 6853056
  have htrace : WordTrace (prefixWord ++ tailWord_6853056) baseStart_6853056 baseEnd_6853056 := by
    simpa [prefixWord, tailWord_6853056, baseEnd_6853056] using wordTrace_append hprefix tailTrace_6853056
  have hstable : (prefixWord ++ tailWord_6853056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853056).length < 2 ^ (prefixWord ++ tailWord_6853056).sum := by decide
  have hdescent : baseEnd_6853056 < baseStart_6853056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853066 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_6853066 : Nat := 118140960795 + 6853066 * 2 ^ 59
def prefixEnd_6853066 : Nat := 4983230072969 + 3 ^ 40 * 6853066 * 2
def baseEnd_6853066 : Nat := 1172972271661663193819443

theorem tailTrace_6853066 : CollatzResearch.WordTrace tailWord_6853066 prefixEnd_6853066 1172972271661663193819443 := by
  unfold tailWord_6853066
  simp only [CollatzResearch.WordTrace]
  refine ⟨62487962847629941834192763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166634567593679844891180701 62487962847629941834192763)
  ·
    refine ⟨93731944271444912751289145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62487962847629941834192763 93731944271444912751289145)
    ·
      refine ⟨70298958203583684563466859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93731944271444912751289145 70298958203583684563466859)
      ·
        refine ⟨105448437305375526845200289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70298958203583684563466859 105448437305375526845200289)
        ·
          refine ⟨79086327979031645133900217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105448437305375526845200289 79086327979031645133900217)
          ·
            refine ⟨59314745984273733850425163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79086327979031645133900217 59314745984273733850425163)
            ·
              refine ⟨88972118976410600775637745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59314745984273733850425163 88972118976410600775637745)
              ·
                refine ⟨66729089232307950581728309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88972118976410600775637745 66729089232307950581728309)
                ·
                  refine ⟨6255852115528870367037029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66729089232307950581728309 6255852115528870367037029)
                  ·
                    refine ⟨1172972271661663193819443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255852115528870367037029 1172972271661663193819443)
                    ·
                      rfl

theorem cell23_6853066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_6853066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853066 prefixEnd_6853066 := by exact prefixLift 6853066
  have htrace : WordTrace (prefixWord ++ tailWord_6853066) baseStart_6853066 baseEnd_6853066 := by
    simpa [prefixWord, tailWord_6853066, baseEnd_6853066] using wordTrace_append hprefix tailTrace_6853066
  have hstable : (prefixWord ++ tailWord_6853066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853066).length < 2 ^ (prefixWord ++ tailWord_6853066).sum := by decide
  have hdescent : baseEnd_6853066 < baseStart_6853066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853099 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_6853099 : Nat := 118140960795 + 6853099 * 2 ^ 59
def prefixEnd_6853099 : Nat := 4983230072969 + 3 ^ 40 * 6853099 * 2
def baseEnd_6853099 : Nat := 3518933759846587952345677

theorem tailTrace_6853099 : CollatzResearch.WordTrace tailWord_6853099 prefixEnd_6853099 3518933759846587952345677 := by
  unfold tailWord_6853099
  simp only [CollatzResearch.WordTrace]
  refine ⟨249953054999400213972722351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166635369999600142648481567 249953054999400213972722351)
  ·
    refine ⟨374929582499100320959083527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249953054999400213972722351 374929582499100320959083527)
    ·
      refine ⟨562394373748650481438625291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374929582499100320959083527 562394373748650481438625291)
      ·
        refine ⟨843591560622975722157937937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562394373748650481438625291 843591560622975722157937937)
        ·
          refine ⟨632693670467231791618453453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843591560622975722157937937 632693670467231791618453453)
          ·
            refine ⟨237260126425211921856920045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632693670467231791618453453 237260126425211921856920045)
            ·
              refine ⟨88972547409454470696345017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237260126425211921856920045 88972547409454470696345017)
              ·
                refine ⟨66729410557090853022258763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88972547409454470696345017 66729410557090853022258763)
                ·
                  refine ⟨100094115835636279533388145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66729410557090853022258763 100094115835636279533388145)
                  ·
                    refine ⟨75070586876727209650041109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100094115835636279533388145 75070586876727209650041109)
                    ·
                      refine ⟨3518933759846587952345677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75070586876727209650041109 3518933759846587952345677)
                      ·
                        rfl

theorem cell23_6853099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_6853099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853099 prefixEnd_6853099 := by exact prefixLift 6853099
  have htrace : WordTrace (prefixWord ++ tailWord_6853099) baseStart_6853099 baseEnd_6853099 := by
    simpa [prefixWord, tailWord_6853099, baseEnd_6853099] using wordTrace_append hprefix tailTrace_6853099
  have hstable : (prefixWord ++ tailWord_6853099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853099).length < 2 ^ (prefixWord ++ tailWord_6853099).sum := by decide
  have hdescent : baseEnd_6853099 < baseStart_6853099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853160 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6853160 : Nat := 118140960795 + 6853160 * 2 ^ 59
def prefixEnd_6853160 : Nat := 4983230072969 + 3 ^ 40 * 6853160 * 2
def baseEnd_6853160 : Nat := 1172988360722170737894299

theorem tailTrace_6853160 : CollatzResearch.WordTrace tailWord_6853160 prefixEnd_6853160 1172988360722170737894299 := by
  unfold tailWord_6853160
  simp only [CollatzResearch.WordTrace]
  refine ⟨124977639926089610695346467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166636853234786147593795289 124977639926089610695346467)
  ·
    refine ⟨187466459889134416043019701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124977639926089610695346467 187466459889134416043019701)
    ·
      refine ⟨17574980614606351504033097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187466459889134416043019701 17574980614606351504033097)
      ·
        refine ⟨13181235460954763628024823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17574980614606351504033097 13181235460954763628024823)
        ·
          refine ⟨19771853191432145442037235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13181235460954763628024823 19771853191432145442037235)
          ·
            refine ⟨29657779787148218163055853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19771853191432145442037235 29657779787148218163055853)
            ·
              refine ⟨11121667420180581811145945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29657779787148218163055853 11121667420180581811145945)
              ·
                refine ⟨8341250565135436358359459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11121667420180581811145945 8341250565135436358359459)
                ·
                  refine ⟨12511875847703154537539189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341250565135436358359459 12511875847703154537539189)
                  ·
                    refine ⟨1172988360722170737894299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12511875847703154537539189 1172988360722170737894299)
                    ·
                      rfl

theorem cell23_6853160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6853160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853160 prefixEnd_6853160 := by exact prefixLift 6853160
  have htrace : WordTrace (prefixWord ++ tailWord_6853160) baseStart_6853160 baseEnd_6853160 := by
    simpa [prefixWord, tailWord_6853160, baseEnd_6853160] using wordTrace_append hprefix tailTrace_6853160
  have hstable : (prefixWord ++ tailWord_6853160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853160).length < 2 ^ (prefixWord ++ tailWord_6853160).sum := by decide
  have hdescent : baseEnd_6853160 < baseStart_6853160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853230 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6853230 : Nat := 118140960795 + 6853230 * 2 ^ 59
def prefixEnd_6853230 : Nat := 4983230072969 + 3 ^ 40 * 6853230 * 2
def baseEnd_6853230 : Nat := 3519001025812326939807575

theorem tailTrace_6853230 : CollatzResearch.WordTrace tailWord_6853230 prefixEnd_6853230 3519001025812326939807575 := by
  unfold tailWord_6853230
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244729120240702918217643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166638555307950415563827429 31244729120240702918217643)
  ·
    refine ⟨46867093680361054377326465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31244729120240702918217643 46867093680361054377326465)
    ·
      refine ⟨35150320260270790782994849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46867093680361054377326465 35150320260270790782994849)
      ·
        refine ⟨26362740195203093087246137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35150320260270790782994849 26362740195203093087246137)
        ·
          refine ⟨19772055146402319815434603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26362740195203093087246137 19772055146402319815434603)
          ·
            refine ⟨29658082719603479723151905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19772055146402319815434603 29658082719603479723151905)
            ·
              refine ⟨22243562039702609792363929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29658082719603479723151905 22243562039702609792363929)
              ·
                refine ⟨16682671529776957344272947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22243562039702609792363929 16682671529776957344272947)
                ·
                  refine ⟨25024007294665436016409421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16682671529776957344272947 25024007294665436016409421)
                  ·
                    refine ⟨9384002735499538506153533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25024007294665436016409421 9384002735499538506153533)
                    ·
                      refine ⟨3519001025812326939807575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384002735499538506153533 3519001025812326939807575)
                      ·
                        rfl

theorem cell23_6853230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6853230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853230 prefixEnd_6853230 := by exact prefixLift 6853230
  have htrace : WordTrace (prefixWord ++ tailWord_6853230) baseStart_6853230 baseEnd_6853230 := by
    simpa [prefixWord, tailWord_6853230, baseEnd_6853230] using wordTrace_append hprefix tailTrace_6853230
  have hstable : (prefixWord ++ tailWord_6853230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853230).length < 2 ^ (prefixWord ++ tailWord_6853230).sum := by decide
  have hdescent : baseEnd_6853230 < baseStart_6853230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853234 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_6853234 : Nat := 118140960795 + 6853234 * 2 ^ 59
def prefixEnd_6853234 : Nat := 4983230072969 + 3 ^ 40 * 6853234 * 2
def baseEnd_6853234 : Nat := 3519003079734944924157557

theorem tailTrace_6853234 : CollatzResearch.WordTrace tailWord_6853234 prefixEnd_6853234 3519003079734944924157557 := by
  unfold tailWord_6853234
  simp only [CollatzResearch.WordTrace]
  refine ⟨62489494713477783007221689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166638652569274088019257837 62489494713477783007221689)
  ·
    refine ⟨46867121035108337255416267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62489494713477783007221689 46867121035108337255416267)
    ·
      refine ⟨70300681552662505883124401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46867121035108337255416267 70300681552662505883124401)
      ·
        refine ⟨52725511164496879412343301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70300681552662505883124401 52725511164496879412343301)
        ·
          refine ⟨9886033343343164889814369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52725511164496879412343301 9886033343343164889814369)
          ·
            refine ⟨7414525007507373667360777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9886033343343164889814369 7414525007507373667360777)
            ·
              refine ⟨5560893755630530250520583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414525007507373667360777 5560893755630530250520583)
              ·
                refine ⟨8341340633445795375780875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560893755630530250520583 8341340633445795375780875)
                ·
                  refine ⟨12512010950168693063671313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341340633445795375780875 12512010950168693063671313)
                  ·
                    refine ⟨9384008212626519797753485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12512010950168693063671313 9384008212626519797753485)
                    ·
                      refine ⟨3519003079734944924157557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384008212626519797753485 3519003079734944924157557)
                      ·
                        rfl

theorem cell23_6853234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_6853234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853234 prefixEnd_6853234 := by exact prefixLift 6853234
  have htrace : WordTrace (prefixWord ++ tailWord_6853234) baseStart_6853234 baseEnd_6853234 := by
    simpa [prefixWord, tailWord_6853234, baseEnd_6853234] using wordTrace_append hprefix tailTrace_6853234
  have hstable : (prefixWord ++ tailWord_6853234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853234).length < 2 ^ (prefixWord ++ tailWord_6853234).sum := by decide
  have hdescent : baseEnd_6853234 < baseStart_6853234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853240 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_6853240 : Nat := 118140960795 + 6853240 * 2 ^ 59
def prefixEnd_6853240 : Nat := 4983230072969 + 3 ^ 40 * 6853240 * 2
def baseEnd_6853240 : Nat := 3519006160618871900682529

theorem tailTrace_6853240 : CollatzResearch.WordTrace tailWord_6853240 prefixEnd_6853240 3519006160618871900682529 := by
  unfold tailWord_6853240
  simp only [CollatzResearch.WordTrace]
  refine ⟨124979098845944697526802587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166638798461259596702403449 124979098845944697526802587)
  ·
    refine ⟨187468648268917046290203881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124979098845944697526802587 187468648268917046290203881)
    ·
      refine ⟨140601486201687784717652911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187468648268917046290203881 140601486201687784717652911)
      ·
        refine ⟨210902229302531677076479367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140601486201687784717652911 210902229302531677076479367)
        ·
          refine ⟨316353343953797515614719051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210902229302531677076479367 316353343953797515614719051)
          ·
            refine ⟨474530015930696273422078577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316353343953797515614719051 474530015930696273422078577)
            ·
              refine ⟨355897511948022205066558933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474530015930696273422078577 355897511948022205066558933)
              ·
                refine ⟨8341347936281770431247475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 355897511948022205066558933 8341347936281770431247475)
                ·
                  refine ⟨12512021904422655646871213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341347936281770431247475 12512021904422655646871213)
                  ·
                    refine ⟨4692008214158495867576705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12512021904422655646871213 4692008214158495867576705)
                    ·
                      refine ⟨3519006160618871900682529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692008214158495867576705 3519006160618871900682529)
                      ·
                        rfl

theorem cell23_6853240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_6853240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853240 prefixEnd_6853240 := by exact prefixLift 6853240
  have htrace : WordTrace (prefixWord ++ tailWord_6853240) baseStart_6853240 baseEnd_6853240 := by
    simpa [prefixWord, tailWord_6853240, baseEnd_6853240] using wordTrace_append hprefix tailTrace_6853240
  have hstable : (prefixWord ++ tailWord_6853240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853240).length < 2 ^ (prefixWord ++ tailWord_6853240).sum := by decide
  have hdescent : baseEnd_6853240 < baseStart_6853240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853360 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2]
def baseStart_6853360 : Nat := 118140960795 + 6853360 * 2 ^ 59
def prefixEnd_6853360 : Nat := 4983230072969 + 3 ^ 40 * 6853360 * 2
def baseEnd_6853360 : Nat := 3519067778297411431181977

theorem tailTrace_6853360 : CollatzResearch.WordTrace tailWord_6853360 prefixEnd_6853360 3519067778297411431181977 := by
  unfold tailWord_6853360
  simp only [CollatzResearch.WordTrace]
  refine ⟨124981287225727327773986767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166641716300969770365315689 124981287225727327773986767)
  ·
    refine ⟨187471930838590991660980151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124981287225727327773986767 187471930838590991660980151)
    ·
      refine ⟨281207896257886487491470227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187471930838590991660980151 281207896257886487491470227)
      ·
        refine ⟨421811844386829731237205341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281207896257886487491470227 421811844386829731237205341)
        ·
          refine ⟨158179441645061149213952003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421811844386829731237205341 158179441645061149213952003)
          ·
            refine ⟨237269162467591723820928005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158179441645061149213952003 237269162467591723820928005)
            ·
              refine ⟨44487967962673448216424001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237269162467591723820928005 44487967962673448216424001)
              ·
                refine ⟨33365975972005086162318001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44487967962673448216424001 33365975972005086162318001)
                ·
                  refine ⟨25024481979003814621738501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33365975972005086162318001 25024481979003814621738501)
                  ·
                    refine ⟨4692090371063215241575969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25024481979003814621738501 4692090371063215241575969)
                    ·
                      refine ⟨3519067778297411431181977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692090371063215241575969 3519067778297411431181977)
                      ·
                        rfl

theorem cell23_6853360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2].length) (baseStart_6853360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853360 prefixEnd_6853360 := by exact prefixLift 6853360
  have htrace : WordTrace (prefixWord ++ tailWord_6853360) baseStart_6853360 baseEnd_6853360 := by
    simpa [prefixWord, tailWord_6853360, baseEnd_6853360] using wordTrace_append hprefix tailTrace_6853360
  have hstable : (prefixWord ++ tailWord_6853360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853360).length < 2 ^ (prefixWord ++ tailWord_6853360).sum := by decide
  have hdescent : baseEnd_6853360 < baseStart_6853360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853363 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3]
def baseStart_6853363 : Nat := 118140960795 + 6853363 * 2 ^ 59
def prefixEnd_6853363 : Nat := 4983230072969 + 3 ^ 40 * 6853363 * 2
def baseEnd_6853363 : Nat := 3519069318739374919444463

theorem tailTrace_6853363 : CollatzResearch.WordTrace tailWord_6853363 prefixEnd_6853363 3519069318739374919444463 := by
  unfold tailWord_6853363
  simp only [CollatzResearch.WordTrace]
  refine ⟨249962683870443787060332743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166641789246962524706888495 249962683870443787060332743)
  ·
    refine ⟨374944025805665680590499115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249962683870443787060332743 374944025805665680590499115)
    ·
      refine ⟨562416038708498520885748673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374944025805665680590499115 562416038708498520885748673)
      ·
        refine ⟨421812029031373890664311505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562416038708498520885748673 421812029031373890664311505)
        ·
          refine ⟨316359021773530417998233629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421812029031373890664311505 316359021773530417998233629)
          ·
            refine ⟨118634633165073906749337611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316359021773530417998233629 118634633165073906749337611)
            ·
              refine ⟨177951949747610860124006417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118634633165073906749337611 177951949747610860124006417)
              ·
                refine ⟨133463962310708145093004813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177951949747610860124006417 133463962310708145093004813)
                ·
                  refine ⟨50048985866515554409876805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133463962310708145093004813 50048985866515554409876805)
                  ·
                    refine ⟨9384184849971666451851901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50048985866515554409876805 9384184849971666451851901)
                    ·
                      refine ⟨3519069318739374919444463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384184849971666451851901 3519069318739374919444463)
                      ·
                        rfl

theorem cell23_6853363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_6853363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853363 prefixEnd_6853363 := by exact prefixLift 6853363
  have htrace : WordTrace (prefixWord ++ tailWord_6853363) baseStart_6853363 baseEnd_6853363 := by
    simpa [prefixWord, tailWord_6853363, baseEnd_6853363] using wordTrace_append hprefix tailTrace_6853363
  have hstable : (prefixWord ++ tailWord_6853363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853363).length < 2 ^ (prefixWord ++ tailWord_6853363).sum := by decide
  have hdescent : baseEnd_6853363 < baseStart_6853363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853380 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6853380 : Nat := 118140960795 + 6853380 * 2 ^ 59
def prefixEnd_6853380 : Nat := 4983230072969 + 3 ^ 40 * 6853380 * 2
def baseEnd_6853380 : Nat := 3519078047910501352931885

theorem tailTrace_6853380 : CollatzResearch.WordTrace tailWord_6853380 prefixEnd_6853380 3519078047910501352931885 := by
  unfold tailWord_6853380
  simp only [CollatzResearch.WordTrace]
  refine ⟨124981651955691099481850797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166642202607588132642467729 124981651955691099481850797)
  ·
    refine ⟨46868119483384162305694049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124981651955691099481850797 46868119483384162305694049)
    ·
      refine ⟨35151089612538121729270537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46868119483384162305694049 35151089612538121729270537)
      ·
        refine ⟨26363317209403591296952903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35151089612538121729270537 26363317209403591296952903)
        ·
          refine ⟨39544975814105386945429355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26363317209403591296952903 39544975814105386945429355)
          ·
            refine ⟨59317463721158080418144033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39544975814105386945429355 59317463721158080418144033)
            ·
              refine ⟨44488097790868560313608025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59317463721158080418144033 44488097790868560313608025)
              ·
                refine ⟨33366073343151420235206019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44488097790868560313608025 33366073343151420235206019)
                ·
                  refine ⟨50049110014727130352809029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33366073343151420235206019 50049110014727130352809029)
                  ·
                    refine ⟨9384208127761336941151693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50049110014727130352809029 9384208127761336941151693)
                    ·
                      refine ⟨3519078047910501352931885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384208127761336941151693 3519078047910501352931885)
                      ·
                        rfl

theorem cell23_6853380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6853380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853380 prefixEnd_6853380 := by exact prefixLift 6853380
  have htrace : WordTrace (prefixWord ++ tailWord_6853380) baseStart_6853380 baseEnd_6853380 := by
    simpa [prefixWord, tailWord_6853380, baseEnd_6853380] using wordTrace_append hprefix tailTrace_6853380
  have hstable : (prefixWord ++ tailWord_6853380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853380).length < 2 ^ (prefixWord ++ tailWord_6853380).sum := by decide
  have hdescent : baseEnd_6853380 < baseStart_6853380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853404 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6853404 : Nat := 118140960795 + 6853404 * 2 ^ 59
def prefixEnd_6853404 : Nat := 4983230072969 + 3 ^ 40 * 6853404 * 2
def baseEnd_6853404 : Nat := 1173030123815403086343925

theorem tailTrace_6853404 : CollatzResearch.WordTrace tailWord_6853404 prefixEnd_6853404 1173030123815403086343925 := by
  unfold tailWord_6853404
  simp only [CollatzResearch.WordTrace]
  refine ⟨124982089631647625531287633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166642786175530167375050177 124982089631647625531287633)
  ·
    refine ⟨93736567223735719148465725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124982089631647625531287633 93736567223735719148465725)
    ·
      refine ⟨35151212708900894680674647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93736567223735719148465725 35151212708900894680674647)
      ·
        refine ⟨52726819063351342021011971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35151212708900894680674647 52726819063351342021011971)
        ·
          refine ⟨79090228595027013031517957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52726819063351342021011971 79090228595027013031517957)
          ·
            refine ⟨14829417861567564943409617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79090228595027013031517957 14829417861567564943409617)
            ·
              refine ⟨11122063396175673707557213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14829417861567564943409617 11122063396175673707557213)
              ·
                refine ⟨4170773773565877640333955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11122063396175673707557213 4170773773565877640333955)
                ·
                  refine ⟨6256160660348816460500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170773773565877640333955 6256160660348816460500933)
                  ·
                    refine ⟨1173030123815403086343925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256160660348816460500933 1173030123815403086343925)
                    ·
                      rfl

theorem cell23_6853404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6853404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853404 prefixEnd_6853404 := by exact prefixLift 6853404
  have htrace : WordTrace (prefixWord ++ tailWord_6853404) baseStart_6853404 baseEnd_6853404 := by
    simpa [prefixWord, tailWord_6853404, baseEnd_6853404] using wordTrace_append hprefix tailTrace_6853404
  have hstable : (prefixWord ++ tailWord_6853404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853404).length < 2 ^ (prefixWord ++ tailWord_6853404).sum := by decide
  have hdescent : baseEnd_6853404 < baseStart_6853404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853421 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6853421 : Nat := 118140960795 + 6853421 * 2 ^ 59
def prefixEnd_6853421 : Nat := 4983230072969 + 3 ^ 40 * 6853421 * 2
def baseEnd_6853421 : Nat := 1173033033539111897506399

theorem tailTrace_6853421 : CollatzResearch.WordTrace tailWord_6853421 prefixEnd_6853421 1173033033539111897506399 := by
  unfold tailWord_6853421
  simp only [CollatzResearch.WordTrace]
  refine ⟨249964799304233662965944117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166643199536155775310629411 249964799304233662965944117)
  ·
    refine ⟨23434199934771905903057261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249964799304233662965944117 23434199934771905903057261)
    ·
      refine ⟨8787824975539464713646473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23434199934771905903057261 8787824975539464713646473)
      ·
        refine ⟨6590868731654598535234855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8787824975539464713646473 6590868731654598535234855)
        ·
          refine ⟨9886303097481897802852283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590868731654598535234855 9886303097481897802852283)
          ·
            refine ⟨14829454646222846704278425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9886303097481897802852283 14829454646222846704278425)
            ·
              refine ⟨11122090984667135028208819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14829454646222846704278425 11122090984667135028208819)
              ·
                refine ⟨16683136477000702542313229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11122090984667135028208819 16683136477000702542313229)
                ·
                  refine ⟨6256176178875263453367461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16683136477000702542313229 6256176178875263453367461)
                  ·
                    refine ⟨1173033033539111897506399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256176178875263453367461 1173033033539111897506399)
                    ·
                      rfl

theorem cell23_6853421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6853421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853421 prefixEnd_6853421 := by exact prefixLift 6853421
  have htrace : WordTrace (prefixWord ++ tailWord_6853421) baseStart_6853421 baseEnd_6853421 := by
    simpa [prefixWord, tailWord_6853421, baseEnd_6853421] using wordTrace_append hprefix tailTrace_6853421
  have hstable : (prefixWord ++ tailWord_6853421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853421).length < 2 ^ (prefixWord ++ tailWord_6853421).sum := by decide
  have hdescent : baseEnd_6853421 < baseStart_6853421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853427 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 3]
def baseStart_6853427 : Nat := 118140960795 + 6853427 * 2 ^ 59
def prefixEnd_6853427 : Nat := 4983230072969 + 3 ^ 40 * 6853427 * 2
def baseEnd_6853427 : Nat := 3519102181501262669044169

theorem tailTrace_6853427 : CollatzResearch.WordTrace tailWord_6853427 prefixEnd_6853427 3519102181501262669044169 := by
  unfold tailWord_6853427
  simp only [CollatzResearch.WordTrace]
  refine ⟨249965018142211925990662535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166643345428141283993775023 249965018142211925990662535)
  ·
    refine ⟨374947527213317888985993803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249965018142211925990662535 374947527213317888985993803)
    ·
      refine ⟨562421290819976833478990705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374947527213317888985993803 562421290819976833478990705)
      ·
        refine ⟨421815968114982625109243029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562421290819976833478990705 421815968114982625109243029)
        ·
          refine ⟨19772623505389810551995767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 421815968114982625109243029 19772623505389810551995767)
          ·
            refine ⟨29658935258084715827993651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19772623505389810551995767 29658935258084715827993651)
            ·
              refine ⟨44488402887127073741990477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29658935258084715827993651 44488402887127073741990477)
              ·
                refine ⟨16683151082672652653246429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44488402887127073741990477 16683151082672652653246429)
                ·
                  refine ⟨6256181656002244744967411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16683151082672652653246429 6256181656002244744967411)
                  ·
                    refine ⟨9384272484003367117451117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6256181656002244744967411 9384272484003367117451117)
                    ·
                      refine ⟨3519102181501262669044169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384272484003367117451117 3519102181501262669044169)
                      ·
                        rfl

theorem cell23_6853427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_6853427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853427 prefixEnd_6853427 := by exact prefixLift 6853427
  have htrace : WordTrace (prefixWord ++ tailWord_6853427) baseStart_6853427 baseEnd_6853427 := by
    simpa [prefixWord, tailWord_6853427, baseEnd_6853427] using wordTrace_append hprefix tailTrace_6853427
  have hstable : (prefixWord ++ tailWord_6853427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853427).length < 2 ^ (prefixWord ++ tailWord_6853427).sum := by decide
  have hdescent : baseEnd_6853427 < baseStart_6853427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853480 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6853480 : Nat := 118140960795 + 6853480 * 2 ^ 59
def prefixEnd_6853480 : Nat := 4983230072969 + 3 ^ 40 * 6853480 * 2
def baseEnd_6853480 : Nat := 3519129395975950961681425

theorem tailTrace_6853480 : CollatzResearch.WordTrace tailWord_6853480 prefixEnd_6853480 3519129395975950961681425 := by
  unfold tailWord_6853480
  simp only [CollatzResearch.WordTrace]
  refine ⟨124983475605509958021170947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166644634140679944028227929 124983475605509958021170947)
  ·
    refine ⟨187475213408264937031756421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124983475605509958021170947 187475213408264937031756421)
    ·
      refine ⟨35151602514049675693454329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187475213408264937031756421 35151602514049675693454329)
      ·
        refine ⟨26363701885537256770090747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35151602514049675693454329 26363701885537256770090747)
        ·
          refine ⟨39545552828305885155136121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26363701885537256770090747 39545552828305885155136121)
          ·
            refine ⟨29659164621229413866352091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39545552828305885155136121 29659164621229413866352091)
            ·
              refine ⟨44488746931844120799528137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29659164621229413866352091 44488746931844120799528137)
              ·
                refine ⟨33366560198883090599646103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44488746931844120799528137 33366560198883090599646103)
                ·
                  refine ⟨50049840298324635899469155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33366560198883090599646103 50049840298324635899469155)
                  ·
                    refine ⟨75074760447486953849203733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50049840298324635899469155 75074760447486953849203733)
                    ·
                      refine ⟨3519129395975950961681425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75074760447486953849203733 3519129395975950961681425)
                      ·
                        rfl

theorem cell23_6853480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6853480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853480 prefixEnd_6853480 := by exact prefixLift 6853480
  have htrace : WordTrace (prefixWord ++ tailWord_6853480) baseStart_6853480 baseEnd_6853480 := by
    simpa [prefixWord, tailWord_6853480, baseEnd_6853480] using wordTrace_append hprefix tailTrace_6853480
  have hstable : (prefixWord ++ tailWord_6853480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853480).length < 2 ^ (prefixWord ++ tailWord_6853480).sum := by decide
  have hdescent : baseEnd_6853480 < baseStart_6853480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_6853500 : Nat := 118140960795 + 6853500 * 2 ^ 59
def prefixEnd_6853500 : Nat := 4983230072969 + 3 ^ 40 * 6853500 * 2
def baseEnd_6853500 : Nat := 3519139665589040883431333

theorem tailTrace_6853500 : CollatzResearch.WordTrace tailWord_6853500 prefixEnd_6853500 3519139665589040883431333 := by
  unfold tailWord_6853500
  simp only [CollatzResearch.WordTrace]
  refine ⟨124983840335473729729034977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166645120447298306305379969 124983840335473729729034977)
  ·
    refine ⟨93737880251605297296776233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124983840335473729729034977 93737880251605297296776233)
    ·
      refine ⟨70303410188703972972582175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93737880251605297296776233 70303410188703972972582175)
      ·
        refine ⟨105455115283055959458873263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70303410188703972972582175 105455115283055959458873263)
        ·
          refine ⟨158182672924583939188309895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105455115283055959458873263 158182672924583939188309895)
          ·
            refine ⟨237274009386875908782464843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158182672924583939188309895 237274009386875908782464843)
            ·
              refine ⟨355911014080313863173697265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237274009386875908782464843 355911014080313863173697265)
              ·
                refine ⟨266933260560235397380272949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355911014080313863173697265 266933260560235397380272949)
                ·
                  refine ⟨25024993177522068504400589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266933260560235397380272949 25024993177522068504400589)
                  ·
                    refine ⟨9384372441570775689150221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25024993177522068504400589 9384372441570775689150221)
                    ·
                      refine ⟨3519139665589040883431333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384372441570775689150221 3519139665589040883431333)
                      ·
                        rfl

theorem cell23_6853500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_6853500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853500 prefixEnd_6853500 := by exact prefixLift 6853500
  have htrace : WordTrace (prefixWord ++ tailWord_6853500) baseStart_6853500 baseEnd_6853500 := by
    simpa [prefixWord, tailWord_6853500, baseEnd_6853500] using wordTrace_append hprefix tailTrace_6853500
  have hstable : (prefixWord ++ tailWord_6853500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853500).length < 2 ^ (prefixWord ++ tailWord_6853500).sum := by decide
  have hdescent : baseEnd_6853500 < baseStart_6853500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853535 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 1, 2, 2]
def baseStart_6853535 : Nat := 118140960795 + 6853535 * 2 ^ 59
def prefixEnd_6853535 : Nat := 4983230072969 + 3 ^ 40 * 6853535 * 2
def baseEnd_6853535 : Nat := 3519157637411948246493673

theorem tailTrace_6853535 : CollatzResearch.WordTrace tailWord_6853535 prefixEnd_6853535 3519157637411948246493673 := by
  unfold tailWord_6853535
  simp only [CollatzResearch.WordTrace]
  refine ⟨249968957225820660435594059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166645971483880440290396039 249968957225820660435594059)
  ·
    refine ⟨374953435838730990653391089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249968957225820660435594059 374953435838730990653391089)
    ·
      refine ⟨281215076879048242990043317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374953435838730990653391089 281215076879048242990043317)
      ·
        refine ⟨26363913457410772780316561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281215076879048242990043317 26363913457410772780316561)
        ·
          refine ⟨19772935093058079585237421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26363913457410772780316561 19772935093058079585237421)
          ·
            refine ⟨7414850659896779844464033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19772935093058079585237421 7414850659896779844464033)
            ·
              refine ⟨5561137994922584883348025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414850659896779844464033 5561137994922584883348025)
              ·
                refine ⟨4170853496191938662511019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561137994922584883348025 4170853496191938662511019)
                ·
                  refine ⟨6256280244287907993766529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170853496191938662511019 6256280244287907993766529)
                  ·
                    refine ⟨4692210183215930995324897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6256280244287907993766529 4692210183215930995324897)
                    ·
                      refine ⟨3519157637411948246493673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692210183215930995324897 3519157637411948246493673)
                      ·
                        rfl

theorem cell23_6853535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_6853535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853535 prefixEnd_6853535 := by exact prefixLift 6853535
  have htrace : WordTrace (prefixWord ++ tailWord_6853535) baseStart_6853535 baseEnd_6853535 := by
    simpa [prefixWord, tailWord_6853535, baseEnd_6853535] using wordTrace_append hprefix tailTrace_6853535
  have hstable : (prefixWord ++ tailWord_6853535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853535).length < 2 ^ (prefixWord ++ tailWord_6853535).sum := by decide
  have hdescent : baseEnd_6853535 < baseStart_6853535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853540 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6853540 : Nat := 118140960795 + 6853540 * 2 ^ 59
def prefixEnd_6853540 : Nat := 4983230072969 + 3 ^ 40 * 6853540 * 2
def baseEnd_6853540 : Nat := 3519160204815220726931149

theorem tailTrace_6853540 : CollatzResearch.WordTrace tailWord_6853540 prefixEnd_6853540 3519160204815220726931149 := by
  unfold tailWord_6853540
  simp only [CollatzResearch.WordTrace]
  refine ⟨124984569795401273144763037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166646093060535030859684049 124984569795401273144763037)
  ·
    refine ⟨46869213673275477429286139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124984569795401273144763037 46869213673275477429286139)
    ·
      refine ⟨70303820509913216143929209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46869213673275477429286139 70303820509913216143929209)
      ·
        refine ⟨52727865382434912107946907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70303820509913216143929209 52727865382434912107946907)
        ·
          refine ⟨79091798073652368161920361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52727865382434912107946907 79091798073652368161920361)
          ·
            refine ⟨59318848555239276121440271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79091798073652368161920361 59318848555239276121440271)
            ·
              refine ⟨88978272832858914182160407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59318848555239276121440271 88978272832858914182160407)
              ·
                refine ⟨133467409249288371273240611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88978272832858914182160407 133467409249288371273240611)
                ·
                  refine ⟨200201113873932556909860917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133467409249288371273240611 200201113873932556909860917)
                  ·
                    refine ⟨18768854425681177210299461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200201113873932556909860917 18768854425681177210299461)
                    ·
                      refine ⟨3519160204815220726931149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18768854425681177210299461 3519160204815220726931149)
                      ·
                        rfl

theorem cell23_6853540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6853540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853540 prefixEnd_6853540 := by exact prefixLift 6853540
  have htrace : WordTrace (prefixWord ++ tailWord_6853540) baseStart_6853540 baseEnd_6853540 := by
    simpa [prefixWord, tailWord_6853540, baseEnd_6853540] using wordTrace_append hprefix tailTrace_6853540
  have hstable : (prefixWord ++ tailWord_6853540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853540).length < 2 ^ (prefixWord ++ tailWord_6853540).sum := by decide
  have hdescent : baseEnd_6853540 < baseStart_6853540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853558 : List Nat := [5, 1, 4, 1, 1, 1, 3, 7]
def baseStart_6853558 : Nat := 118140960795 + 6853558 * 2 ^ 59
def prefixEnd_6853558 : Nat := 4983230072969 + 3 ^ 40 * 6853558 * 2
def baseEnd_6853558 : Nat := 130339609165444505796521

theorem tailTrace_6853558 : CollatzResearch.WordTrace tailWord_6853558 prefixEnd_6853558 130339609165444505796521 := by
  unfold tailWord_6853558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623112256546083460230083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166646530736491556909120885 15623112256546083460230083)
  ·
    refine ⟨23434668384819125190345125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15623112256546083460230083 23434668384819125190345125)
    ·
      refine ⟨4394000322153585973189711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23434668384819125190345125 4394000322153585973189711)
      ·
        refine ⟨6591000483230378959784567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394000322153585973189711 6591000483230378959784567)
        ·
          refine ⟨9886500724845568439676851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591000483230378959784567 9886500724845568439676851)
          ·
            refine ⟨14829751087268352659515277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9886500724845568439676851 14829751087268352659515277)
            ·
              refine ⟨5561156657725632247318229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14829751087268352659515277 5561156657725632247318229)
              ·
                refine ⟨130339609165444505796521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5561156657725632247318229 130339609165444505796521)
                ·
                  rfl

theorem cell23_6853558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_6853558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853558 prefixEnd_6853558 := by exact prefixLift 6853558
  have htrace : WordTrace (prefixWord ++ tailWord_6853558) baseStart_6853558 baseEnd_6853558 := by
    simpa [prefixWord, tailWord_6853558, baseEnd_6853558] using wordTrace_append hprefix tailTrace_6853558
  have hstable : (prefixWord ++ tailWord_6853558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853558).length < 2 ^ (prefixWord ++ tailWord_6853558).sum := by decide
  have hdescent : baseEnd_6853558 < baseStart_6853558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853580 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 9]
def baseStart_6853580 : Nat := 118140960795 + 6853580 * 2 ^ 59
def prefixEnd_6853580 : Nat := 4983230072969 + 3 ^ 40 * 6853580 * 2
def baseEnd_6853580 : Nat := 391020082671266730047885

theorem tailTrace_6853580 : CollatzResearch.WordTrace tailWord_6853580 prefixEnd_6853580 391020082671266730047885 := by
  unfold tailWord_6853580
  simp only [CollatzResearch.WordTrace]
  refine ⟨124985299255328816560491097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166647065673771755413988129 124985299255328816560491097)
  ·
    refine ⟨93738974441496612420368323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124985299255328816560491097 93738974441496612420368323)
    ·
      refine ⟨140608461662244918630552485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93738974441496612420368323 140608461662244918630552485)
      ·
        refine ⟨26364086561670922243228591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140608461662244918630552485 26364086561670922243228591)
        ·
          refine ⟨39546129842506383364842887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26364086561670922243228591 39546129842506383364842887)
          ·
            refine ⟨59319194763759575047264331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39546129842506383364842887 59319194763759575047264331)
            ·
              refine ⟨88978792145639362570896497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59319194763759575047264331 88978792145639362570896497)
              ·
                refine ⟨66734094109229521928172373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88978792145639362570896497 66734094109229521928172373)
                ·
                  refine ⟨391020082671266730047885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66734094109229521928172373 391020082671266730047885)
                  ·
                    rfl

theorem cell23_6853580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_6853580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853580 prefixEnd_6853580 := by exact prefixLift 6853580
  have htrace : WordTrace (prefixWord ++ tailWord_6853580) baseStart_6853580 baseEnd_6853580 := by
    simpa [prefixWord, tailWord_6853580, baseEnd_6853580] using wordTrace_append hprefix tailTrace_6853580
  have hstable : (prefixWord ++ tailWord_6853580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853580).length < 2 ^ (prefixWord ++ tailWord_6853580).sum := by decide
  have hdescent : baseEnd_6853580 < baseStart_6853580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853597 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 7]
def baseStart_6853597 : Nat := 118140960795 + 6853597 * 2 ^ 59
def prefixEnd_6853597 : Nat := 4983230072969 + 3 ^ 40 * 6853597 * 2
def baseEnd_6853597 : Nat := 391021052579169667102043

theorem tailTrace_6853597 : CollatzResearch.WordTrace tailWord_6853597 prefixEnd_6853597 391021052579169667102043 := by
  unfold tailWord_6853597
  simp only [CollatzResearch.WordTrace]
  refine ⟨249971218551596045024351045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166647479034397363349567363 249971218551596045024351045)
  ·
    refine ⟨46869603478424258442065821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249971218551596045024351045 46869603478424258442065821)
    ·
      refine ⟨17576101304409096915774683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46869603478424258442065821 17576101304409096915774683)
      ·
        refine ⟨26364151956613645373662025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17576101304409096915774683 26364151956613645373662025)
        ·
          refine ⟨19773113967460234030246519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26364151956613645373662025 19773113967460234030246519)
          ·
            refine ⟨29659670951190351045369779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19773113967460234030246519 29659670951190351045369779)
            ·
              refine ⟨44489506426785526568054669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29659670951190351045369779 44489506426785526568054669)
              ·
                refine ⟨16683564910044572463020501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44489506426785526568054669 16683564910044572463020501)
                ·
                  refine ⟨391021052579169667102043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16683564910044572463020501 391021052579169667102043)
                  ·
                    rfl

theorem cell23_6853597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_6853597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853597 prefixEnd_6853597 := by exact prefixLift 6853597
  have htrace : WordTrace (prefixWord ++ tailWord_6853597) baseStart_6853597 baseEnd_6853597 := by
    simpa [prefixWord, tailWord_6853597, baseEnd_6853597] using wordTrace_append hprefix tailTrace_6853597
  have hstable : (prefixWord ++ tailWord_6853597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853597).length < 2 ^ (prefixWord ++ tailWord_6853597).sum := by decide
  have hdescent : baseEnd_6853597 < baseStart_6853597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853647 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 6, 2]
def baseStart_6853647 : Nat := 118140960795 + 6853647 * 2 ^ 59
def prefixEnd_6853647 : Nat := 4983230072969 + 3 ^ 40 * 6853647 * 2
def baseEnd_6853647 : Nat := 3519215147245251808293157

theorem tailTrace_6853647 : CollatzResearch.WordTrace tailWord_6853647 prefixEnd_6853647 3519215147245251808293157 := by
  unfold tailWord_6853647
  simp only [CollatzResearch.WordTrace]
  refine ⟨249973042201414903563671195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166648694800943269042447463 249973042201414903563671195)
  ·
    refine ⟨374959563302122355345506793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249973042201414903563671195 374959563302122355345506793)
    ·
      refine ⟨281219672476591766509130095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374959563302122355345506793 281219672476591766509130095)
      ·
        refine ⟨421829508714887649763695143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281219672476591766509130095 421829508714887649763695143)
        ·
          refine ⟨632744263072331474645542715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421829508714887649763695143 632744263072331474645542715)
          ·
            refine ⟨949116394608497211968314073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632744263072331474645542715 949116394608497211968314073)
            ·
              refine ⟨711837295956372908976235555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949116394608497211968314073 711837295956372908976235555)
              ·
                refine ⟨1067755943934559363464353333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711837295956372908976235555 1067755943934559363464353333)
                ·
                  refine ⟨100102119743864940324783125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067755943934559363464353333 100102119743864940324783125)
                  ·
                    refine ⟨4692286862993669077724209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100102119743864940324783125 4692286862993669077724209)
                    ·
                      refine ⟨3519215147245251808293157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692286862993669077724209 3519215147245251808293157)
                      ·
                        rfl

theorem cell23_6853647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6, 2].length) (baseStart_6853647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853647 prefixEnd_6853647 := by exact prefixLift 6853647
  have htrace : WordTrace (prefixWord ++ tailWord_6853647) baseStart_6853647 baseEnd_6853647 := by
    simpa [prefixWord, tailWord_6853647, baseEnd_6853647] using wordTrace_append hprefix tailTrace_6853647
  have hstable : (prefixWord ++ tailWord_6853647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853647).length < 2 ^ (prefixWord ++ tailWord_6853647).sum := by decide
  have hdescent : baseEnd_6853647 < baseStart_6853647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853717 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_6853717 : Nat := 118140960795 + 6853717 * 2 ^ 59
def prefixEnd_6853717 : Nat := 4983230072969 + 3 ^ 40 * 6853717 * 2
def baseEnd_6853717 : Nat := 1173083696963688844805945

theorem tailTrace_6853717 : CollatzResearch.WordTrace tailWord_6853717 prefixEnd_6853717 1173083696963688844805945 := by
  unfold tailWord_6853717
  simp only [CollatzResearch.WordTrace]
  refine ⟨249975595311161305518719405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166650396874107537012479603 249975595311161305518719405)
  ·
    refine ⟨93740848241685489569519777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249975595311161305518719405 93740848241685489569519777)
    ·
      refine ⟨70305636181264117177139833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93740848241685489569519777 70305636181264117177139833)
      ·
        refine ⟨52729227135948087882854875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70305636181264117177139833 52729227135948087882854875)
        ·
          refine ⟨79093840703922131824282313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52729227135948087882854875 79093840703922131824282313)
          ·
            refine ⟨59320380527941598868211735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79093840703922131824282313 59320380527941598868211735)
            ·
              refine ⟨88980570791912398302317603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59320380527941598868211735 88980570791912398302317603)
              ·
                refine ⟨133470856187868597453476405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88980570791912398302317603 133470856187868597453476405)
                ·
                  refine ⟨12512892767612681011263413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133470856187868597453476405 12512892767612681011263413)
                  ·
                    refine ⟨1173083696963688844805945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12512892767612681011263413 1173083696963688844805945)
                    ·
                      rfl

theorem cell23_6853717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_6853717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853717 prefixEnd_6853717 := by exact prefixLift 6853717
  have htrace : WordTrace (prefixWord ++ tailWord_6853717) baseStart_6853717 baseEnd_6853717 := by
    simpa [prefixWord, tailWord_6853717, baseEnd_6853717] using wordTrace_append hprefix tailTrace_6853717
  have hstable : (prefixWord ++ tailWord_6853717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853717).length < 2 ^ (prefixWord ++ tailWord_6853717).sum := by decide
  have hdescent : baseEnd_6853717 < baseStart_6853717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853741 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_6853741 : Nat := 118140960795 + 6853741 * 2 ^ 59
def prefixEnd_6853741 : Nat := 4983230072969 + 3 ^ 40 * 6853741 * 2
def baseEnd_6853741 : Nat := 3519263414426774440517725

theorem tailTrace_6853741 : CollatzResearch.WordTrace tailWord_6853741 prefixEnd_6853741 3519263414426774440517725 := by
  unfold tailWord_6853741
  simp only [CollatzResearch.WordTrace]
  refine ⟨249976470663074357617593077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166650980442049571745062051 249976470663074357617593077)
  ·
    refine ⟨23435294124663221026649351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249976470663074357617593077 23435294124663221026649351)
    ·
      refine ⟨35152941186994831539974027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23435294124663221026649351 35152941186994831539974027)
      ·
        refine ⟨52729411780492247309961041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35152941186994831539974027 52729411780492247309961041)
        ·
          refine ⟨39547058835369185482470781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52729411780492247309961041 39547058835369185482470781)
          ·
            refine ⟨14830147063263444555926543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39547058835369185482470781 14830147063263444555926543)
            ·
              refine ⟨22245220594895166833889815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830147063263444555926543 22245220594895166833889815)
              ·
                refine ⟨33367830892342750250834723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22245220594895166833889815 33367830892342750250834723)
                ·
                  refine ⟨50051746338514125376252085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33367830892342750250834723 50051746338514125376252085)
                  ·
                    refine ⟨4692351219235699254023633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50051746338514125376252085 4692351219235699254023633)
                    ·
                      refine ⟨3519263414426774440517725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692351219235699254023633 3519263414426774440517725)
                      ·
                        rfl

theorem cell23_6853741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_6853741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853741 prefixEnd_6853741 := by exact prefixLift 6853741
  have htrace : WordTrace (prefixWord ++ tailWord_6853741) baseStart_6853741 baseEnd_6853741 := by
    simpa [prefixWord, tailWord_6853741, baseEnd_6853741] using wordTrace_append hprefix tailTrace_6853741
  have hstable : (prefixWord ++ tailWord_6853741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853741).length < 2 ^ (prefixWord ++ tailWord_6853741).sum := by decide
  have hdescent : baseEnd_6853741 < baseStart_6853741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853767 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_6853767 : Nat := 118140960795 + 6853767 * 2 ^ 59
def prefixEnd_6853767 : Nat := 4983230072969 + 3 ^ 40 * 6853767 * 2
def baseEnd_6853767 : Nat := 3519276764923791338792605

theorem tailTrace_6853767 : CollatzResearch.WordTrace tailWord_6853767 prefixEnd_6853767 3519276764923791338792605 := by
  unfold tailWord_6853767
  simp only [CollatzResearch.WordTrace]
  refine ⟨249977418960980164058039555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166651612640653442705359703 249977418960980164058039555)
  ·
    refine ⟨374966128441470246087059333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249977418960980164058039555 374966128441470246087059333)
    ·
      refine ⟨70306149082775671141323625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374966128441470246087059333 70306149082775671141323625)
      ·
        refine ⟨52729611812081753355992719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70306149082775671141323625 52729611812081753355992719)
        ·
          refine ⟨79094417718122630033989079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52729611812081753355992719 79094417718122630033989079)
          ·
            refine ⟨118641626577183945050983619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79094417718122630033989079 118641626577183945050983619)
            ·
              refine ⟨177962439865775917576475429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118641626577183945050983619 177962439865775917576475429)
              ·
                refine ⟨33367957474832984545589143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177962439865775917576475429 33367957474832984545589143)
                ·
                  refine ⟨50051936212249476818383715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33367957474832984545589143 50051936212249476818383715)
                  ·
                    refine ⟨75077904318374215227575573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50051936212249476818383715 75077904318374215227575573)
                    ·
                      refine ⟨3519276764923791338792605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75077904318374215227575573 3519276764923791338792605)
                      ·
                        rfl

theorem cell23_6853767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_6853767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853767 prefixEnd_6853767 := by exact prefixLift 6853767
  have htrace : WordTrace (prefixWord ++ tailWord_6853767) baseStart_6853767 baseEnd_6853767 := by
    simpa [prefixWord, tailWord_6853767, baseEnd_6853767] using wordTrace_append hprefix tailTrace_6853767
  have hstable : (prefixWord ++ tailWord_6853767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853767).length < 2 ^ (prefixWord ++ tailWord_6853767).sum := by decide
  have hdescent : baseEnd_6853767 < baseStart_6853767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853774 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6853774 : Nat := 118140960795 + 6853774 * 2 ^ 59
def prefixEnd_6853774 : Nat := 4983230072969 + 3 ^ 40 * 6853774 * 2
def baseEnd_6853774 : Nat := 3519280359288372811405073

theorem tailTrace_6853774 : CollatzResearch.WordTrace tailWord_6853774 prefixEnd_6853774 3519280359288372811405073 := by
  unfold tailWord_6853774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31247209283994350531693047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166651782847969869502362917 31247209283994350531693047)
  ·
    refine ⟨46870813925991525797539571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31247209283994350531693047 46870813925991525797539571)
    ·
      refine ⟨70306220888987288696309357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46870813925991525797539571 70306220888987288696309357)
      ·
        refine ⟨26364832833370233261116009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70306220888987288696309357 26364832833370233261116009)
        ·
          refine ⟨19773624625027674945837007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26364832833370233261116009 19773624625027674945837007)
          ·
            refine ⟨29660436937541512418755511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19773624625027674945837007 29660436937541512418755511)
            ·
              refine ⟨44490655406312268628133267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29660436937541512418755511 44490655406312268628133267)
              ·
                refine ⟨66735983109468402942199901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44490655406312268628133267 66735983109468402942199901)
                ·
                  refine ⟨25025993666050651103324963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66735983109468402942199901 25025993666050651103324963)
                  ·
                    refine ⟨37538990499075976654987445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25025993666050651103324963 37538990499075976654987445)
                    ·
                      refine ⟨3519280359288372811405073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37538990499075976654987445 3519280359288372811405073)
                      ·
                        rfl

theorem cell23_6853774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6853774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853774 prefixEnd_6853774 := by exact prefixLift 6853774
  have htrace : WordTrace (prefixWord ++ tailWord_6853774) baseStart_6853774 baseEnd_6853774 := by
    simpa [prefixWord, tailWord_6853774, baseEnd_6853774] using wordTrace_append hprefix tailTrace_6853774
  have hstable : (prefixWord ++ tailWord_6853774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853774).length < 2 ^ (prefixWord ++ tailWord_6853774).sum := by decide
  have hdescent : baseEnd_6853774 < baseStart_6853774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853784 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6853784 : Nat := 118140960795 + 6853784 * 2 ^ 59
def prefixEnd_6853784 : Nat := 4983230072969 + 3 ^ 40 * 6853784 * 2
def baseEnd_6853784 : Nat := 3519285494094917772280027

theorem tailTrace_6853784 : CollatzResearch.WordTrace tailWord_6853784 prefixEnd_6853784 3519285494094917772280027 := by
  unfold tailWord_6853784
  simp only [CollatzResearch.WordTrace]
  refine ⟨124989019500959287980704203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166652026001279050640938937 124989019500959287980704203)
  ·
    refine ⟨187483529251438931971056305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124989019500959287980704203 187483529251438931971056305)
    ·
      refine ⟨140612646938579198978292229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187483529251438931971056305 140612646938579198978292229)
      ·
        refine ⟨26364871300983599808429793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140612646938579198978292229 26364871300983599808429793)
        ·
          refine ⟨19773653475737699856322345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26364871300983599808429793 19773653475737699856322345)
          ·
            refine ⟨14830240106803274892241759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19773653475737699856322345 14830240106803274892241759)
            ·
              refine ⟨22245360160204912338362639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830240106803274892241759 22245360160204912338362639)
              ·
                refine ⟨33368040240307368507543959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22245360160204912338362639 33368040240307368507543959)
                ·
                  refine ⟨50052060360461052761315939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33368040240307368507543959 50052060360461052761315939)
                  ·
                    refine ⟨75078090540691579141973909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50052060360461052761315939 75078090540691579141973909)
                    ·
                      refine ⟨3519285494094917772280027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75078090540691579141973909 3519285494094917772280027)
                      ·
                        rfl

theorem cell23_6853784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6853784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853784 prefixEnd_6853784 := by exact prefixLift 6853784
  have htrace : WordTrace (prefixWord ++ tailWord_6853784) baseStart_6853784 baseEnd_6853784 := by
    simpa [prefixWord, tailWord_6853784, baseEnd_6853784] using wordTrace_append hprefix tailTrace_6853784
  have hstable : (prefixWord ++ tailWord_6853784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853784).length < 2 ^ (prefixWord ++ tailWord_6853784).sum := by decide
  have hdescent : baseEnd_6853784 < baseStart_6853784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853788 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6853788 : Nat := 118140960795 + 6853788 * 2 ^ 59
def prefixEnd_6853788 : Nat := 4983230072969 + 3 ^ 40 * 6853788 * 2
def baseEnd_6853788 : Nat := 3519287548017535756630009

theorem tailTrace_6853788 : CollatzResearch.WordTrace tailWord_6853788 prefixEnd_6853788 3519287548017535756630009 := by
  unfold tailWord_6853788
  simp only [CollatzResearch.WordTrace]
  refine ⟨124989092446952042322277009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166652123262602723096369345 124989092446952042322277009)
  ·
    refine ⟨93741819335214031741707757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124989092446952042322277009 93741819335214031741707757)
    ·
      refine ⟨35153182250705261903140409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93741819335214031741707757 35153182250705261903140409)
      ·
        refine ⟨26364886688028946427355307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35153182250705261903140409 26364886688028946427355307)
        ·
          refine ⟨39547330032043419641032961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26364886688028946427355307 39547330032043419641032961)
          ·
            refine ⟨29660497524032564730774721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39547330032043419641032961 29660497524032564730774721)
            ·
              refine ⟨22245373143024423548081041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29660497524032564730774721 22245373143024423548081041)
              ·
                refine ⟨16684029857268317661060781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22245373143024423548081041 16684029857268317661060781)
                ·
                  refine ⟨6256511196475619122897793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16684029857268317661060781 6256511196475619122897793)
                  ·
                    refine ⟨4692383397356714342173345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6256511196475619122897793 4692383397356714342173345)
                    ·
                      refine ⟨3519287548017535756630009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692383397356714342173345 3519287548017535756630009)
                      ·
                        rfl

theorem cell23_6853788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6853788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853788 prefixEnd_6853788 := by exact prefixLift 6853788
  have htrace : WordTrace (prefixWord ++ tailWord_6853788) baseStart_6853788 baseEnd_6853788 := by
    simpa [prefixWord, tailWord_6853788, baseEnd_6853788] using wordTrace_append hprefix tailTrace_6853788
  have hstable : (prefixWord ++ tailWord_6853788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853788).length < 2 ^ (prefixWord ++ tailWord_6853788).sum := by decide
  have hdescent : baseEnd_6853788 < baseStart_6853788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853821 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6853821 : Nat := 118140960795 + 6853821 * 2 ^ 59
def prefixEnd_6853821 : Nat := 4983230072969 + 3 ^ 40 * 6853821 * 2
def baseEnd_6853821 : Nat := 3519304492879134127517357

theorem tailTrace_6853821 : CollatzResearch.WordTrace tailWord_6853821 prefixEnd_6853821 3519304492879134127517357 := by
  unfold tailWord_6853821
  simp only [CollatzResearch.WordTrace]
  refine ⟨249979388502784531280505317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166652925668523020853670211 249979388502784531280505317)
  ·
    refine ⟨46871135344272099615094747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249979388502784531280505317 46871135344272099615094747)
    ·
      refine ⟨70306703016408149422642121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46871135344272099615094747 70306703016408149422642121)
      ·
        refine ⟨52730027262306112066981591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70306703016408149422642121 52730027262306112066981591)
        ·
          refine ⟨79095040893459168100472387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52730027262306112066981591 79095040893459168100472387)
          ·
            refine ⟨118642561340188752150708581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79095040893459168100472387 118642561340188752150708581)
            ·
              refine ⟨22245480251285391028257859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118642561340188752150708581 22245480251285391028257859)
              ·
                refine ⟨33368220376928086542386789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22245480251285391028257859 33368220376928086542386789)
                ·
                  refine ⟨6256541320674016226697523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33368220376928086542386789 6256541320674016226697523)
                  ·
                    refine ⟨9384811981011024340046285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6256541320674016226697523 9384811981011024340046285)
                    ·
                      refine ⟨3519304492879134127517357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9384811981011024340046285 3519304492879134127517357)
                      ·
                        rfl

theorem cell23_6853821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6853821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853821 prefixEnd_6853821 := by exact prefixLift 6853821
  have htrace : WordTrace (prefixWord ++ tailWord_6853821) baseStart_6853821 baseEnd_6853821 := by
    simpa [prefixWord, tailWord_6853821, baseEnd_6853821] using wordTrace_append hprefix tailTrace_6853821
  have hstable : (prefixWord ++ tailWord_6853821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853821).length < 2 ^ (prefixWord ++ tailWord_6853821).sum := by decide
  have hdescent : baseEnd_6853821 < baseStart_6853821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853848 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_6853848 : Nat := 118140960795 + 6853848 * 2 ^ 59
def prefixEnd_6853848 : Nat := 4983230072969 + 3 ^ 40 * 6853848 * 2
def baseEnd_6853848 : Nat := 3519318356856805521879733

theorem tailTrace_6853848 : CollatzResearch.WordTrace tailWord_6853848 prefixEnd_6853848 3519318356856805521879733 := by
  unfold tailWord_6853848
  simp only [CollatzResearch.WordTrace]
  refine ⟨124990186636843357445869099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166653582182457809927825465 124990186636843357445869099)
  ·
    refine ⟨187485279955265036168803649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124990186636843357445869099 187485279955265036168803649)
    ·
      refine ⟨140613959966448777126602737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187485279955265036168803649 140613959966448777126602737)
      ·
        refine ⟨105460469974836582844952053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140613959966448777126602737 105460469974836582844952053)
        ·
          refine ⟨9886919060140929641714255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105460469974836582844952053 9886919060140929641714255)
          ·
            refine ⟨14830378590211394462571383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9886919060140929641714255 14830378590211394462571383)
            ·
              refine ⟨22245567885317091693857075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830378590211394462571383 22245567885317091693857075)
              ·
                refine ⟨33368351827975637540785613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22245567885317091693857075 33368351827975637540785613)
                ·
                  refine ⟨12513131935490864077794605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33368351827975637540785613 12513131935490864077794605)
                  ·
                    refine ⟨4692424475809074029172977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12513131935490864077794605 4692424475809074029172977)
                    ·
                      refine ⟨3519318356856805521879733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4692424475809074029172977 3519318356856805521879733)
                      ·
                        rfl

theorem cell23_6853848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_6853848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853848 prefixEnd_6853848 := by exact prefixLift 6853848
  have htrace : WordTrace (prefixWord ++ tailWord_6853848) baseStart_6853848 baseEnd_6853848 := by
    simpa [prefixWord, tailWord_6853848, baseEnd_6853848] using wordTrace_append hprefix tailTrace_6853848
  have hstable : (prefixWord ++ tailWord_6853848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853848).length < 2 ^ (prefixWord ++ tailWord_6853848).sum := by decide
  have hdescent : baseEnd_6853848 < baseStart_6853848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853864 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6853864 : Nat := 118140960795 + 6853864 * 2 ^ 59
def prefixEnd_6853864 : Nat := 4983230072969 + 3 ^ 40 * 6853864 * 2
def baseEnd_6853864 : Nat := 3519326572547277459279659

theorem tailTrace_6853864 : CollatzResearch.WordTrace tailWord_6853864 prefixEnd_6853864 3519326572547277459279659 := by
  unfold tailWord_6853864
  simp only [CollatzResearch.WordTrace]
  refine ⟨124990478420814374812160323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166653971227752499749547097 124990478420814374812160323)
  ·
    refine ⟨187485717631221562218240485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124990478420814374812160323 187485717631221562218240485)
    ·
      refine ⟨35153572055854042915920091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187485717631221562218240485 35153572055854042915920091)
      ·
        refine ⟨52730358083781064373880137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35153572055854042915920091 52730358083781064373880137)
        ·
          refine ⟨39547768562835798280410103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52730358083781064373880137 39547768562835798280410103)
          ·
            refine ⟨59321652844253697420615155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39547768562835798280410103 59321652844253697420615155)
            ·
              refine ⟨88982479266380546130922733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59321652844253697420615155 88982479266380546130922733)
              ·
                refine ⟨33368429724892704799096025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88982479266380546130922733 33368429724892704799096025)
                ·
                  refine ⟨25026322293669528599322019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33368429724892704799096025 25026322293669528599322019)
                  ·
                    refine ⟨37539483440504292898983029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25026322293669528599322019 37539483440504292898983029)
                    ·
                      refine ⟨3519326572547277459279659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37539483440504292898983029 3519326572547277459279659)
                      ·
                        rfl

theorem cell23_6853864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6853864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853864 prefixEnd_6853864 := by exact prefixLift 6853864
  have htrace : WordTrace (prefixWord ++ tailWord_6853864) baseStart_6853864 baseEnd_6853864 := by
    simpa [prefixWord, tailWord_6853864, baseEnd_6853864] using wordTrace_append hprefix tailTrace_6853864
  have hstable : (prefixWord ++ tailWord_6853864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853864).length < 2 ^ (prefixWord ++ tailWord_6853864).sum := by decide
  have hdescent : baseEnd_6853864 < baseStart_6853864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853961 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_6853961 : Nat := 118140960795 + 6853961 * 2 ^ 59
def prefixEnd_6853961 : Nat := 4983230072969 + 3 ^ 40 * 6853961 * 2
def baseEnd_6853961 : Nat := 1173125460056921193255571

theorem tailTrace_6853961 : CollatzResearch.WordTrace tailWord_6853961 prefixEnd_6853961 1173125460056921193255571 := by
  unfold tailWord_6853961
  simp only [CollatzResearch.WordTrace]
  refine ⟨249984494722277335190601737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166656329814851556793734491 249984494722277335190601737)
  ·
    refine ⟨187488371041708001392951303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249984494722277335190601737 187488371041708001392951303)
    ·
      refine ⟨281232556562562002089426955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187488371041708001392951303 281232556562562002089426955)
      ·
        refine ⟨421848834843843003134140433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281232556562562002089426955 421848834843843003134140433)
        ·
          refine ⟨316386626132882252350605325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421848834843843003134140433 316386626132882252350605325)
          ·
            refine ⟨118644984799830844631476997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316386626132882252350605325 118644984799830844631476997)
            ·
              refine ⟨22245934649968283368401937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118644984799830844631476997 22245934649968283368401937)
              ·
                refine ⟨16684450987476212526301453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22245934649968283368401937 16684450987476212526301453)
                ·
                  refine ⟨6256669120303579697363045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16684450987476212526301453 6256669120303579697363045)
                  ·
                    refine ⟨1173125460056921193255571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256669120303579697363045 1173125460056921193255571)
                    ·
                      rfl

theorem cell23_6853961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_6853961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853961 prefixEnd_6853961 := by exact prefixLift 6853961
  have htrace : WordTrace (prefixWord ++ tailWord_6853961) baseStart_6853961 baseEnd_6853961 := by
    simpa [prefixWord, tailWord_6853961, baseEnd_6853961] using wordTrace_append hprefix tailTrace_6853961
  have hstable : (prefixWord ++ tailWord_6853961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853961).length < 2 ^ (prefixWord ++ tailWord_6853961).sum := by decide
  have hdescent : baseEnd_6853961 < baseStart_6853961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6853971 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3]
def baseStart_6853971 : Nat := 118140960795 + 6853971 * 2 ^ 59
def prefixEnd_6853971 : Nat := 4983230072969 + 3 ^ 40 * 6853971 * 2
def baseEnd_6853971 : Nat := 3519381514977308540641667

theorem tailTrace_6853971 : CollatzResearch.WordTrace tailWord_6853971 prefixEnd_6853971 3519381514977308540641667 := by
  unfold tailWord_6853971
  simp only [CollatzResearch.WordTrace]
  refine ⟨249984859452241106898465767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166656572968160737932310511 249984859452241106898465767)
  ·
    refine ⟨374977289178361660347698651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249984859452241106898465767 374977289178361660347698651)
    ·
      refine ⟨562465933767542490521547977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374977289178361660347698651 562465933767542490521547977)
      ·
        refine ⟨421849450325656867891160983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562465933767542490521547977 421849450325656867891160983)
        ·
          refine ⟨632774175488485301836741475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421849450325656867891160983 632774175488485301836741475)
          ·
            refine ⟨949161263232727952755112213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632774175488485301836741475 949161263232727952755112213)
            ·
              refine ⟨44491934214034122785395885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 949161263232727952755112213 44491934214034122785395885)
              ·
                refine ⟨16684475330262796044523457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44491934214034122785395885 16684475330262796044523457)
                ·
                  refine ⟨12513356497697097033392593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16684475330262796044523457 12513356497697097033392593)
                  ·
                    refine ⟨9385017373272822775044445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12513356497697097033392593 9385017373272822775044445)
                    ·
                      refine ⟨3519381514977308540641667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9385017373272822775044445 3519381514977308540641667)
                      ·
                        rfl

theorem cell23_6853971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_6853971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6853971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6853971 prefixEnd_6853971 := by exact prefixLift 6853971
  have htrace : WordTrace (prefixWord ++ tailWord_6853971) baseStart_6853971 baseEnd_6853971 := by
    simpa [prefixWord, tailWord_6853971, baseEnd_6853971] using wordTrace_append hprefix tailTrace_6853971
  have hstable : (prefixWord ++ tailWord_6853971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6853971).length < 2 ^ (prefixWord ++ tailWord_6853971).sum := by decide
  have hdescent : baseEnd_6853971 < baseStart_6853971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6853971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
